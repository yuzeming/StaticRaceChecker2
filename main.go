package main

import (
	"fmt"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/cha"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"os"
	"reflect"
	"sort"
	"strings"
	"sync"
)

const _UseTestCase_ = true
const _debug_print_ = false
const _ChaCallGraph_ = false
const _detailreport_ = true

type RecordField struct {
	ins      ssa.Instruction
	value    ssa.Value
	Field    int
	isWrite  bool
	isAtomic bool
}

type Result struct {
	field [2]RecordField
	ctx   [2]ContextList
}

type CheckerRunner struct {
	//temp info
	RecordSet_Field  []RecordField
	RecordSet_Array  []RecordField
	RecordSet_Basic  []RecordField
	RecordSet_Map    []RecordField
	PairSet          [][2]RecordField
	ReachablePairSet [][2]RecordField

	FastFreeVarMap map[*ssa.FreeVar]ssa.Value

	//input
	prog *ssa.Program
	pkgs []*ssa.Package

	//post-dominator tree
	post_idom map[*ssa.Function]map[*ssa.BasicBlock]*ssa.BasicBlock

	//Result
	ResultMux sync.Mutex
	ResultSet map[ssa.Value][]*Result
}

func (r *CheckerRunner) AddFreeVarMap(a *ssa.FreeVar, b ssa.Value) {
	if r.FastFreeVarMap == nil {
		r.FastFreeVarMap = make(map[*ssa.FreeVar]ssa.Value)
	}
	r.FastFreeVarMap[a] = b
}

func (r *CheckerRunner) LockupFreeVar(a *ssa.FreeVar) (ret ssa.Value) {
	if r.FastFreeVarMap == nil {
		r.FastFreeVarMap = make(map[*ssa.FreeVar]ssa.Value)
	}
	ret = r.FastFreeVarMap[a]
	for ret != nil {
		a2, isFreeVal := ret.(*ssa.FreeVar)
		if isFreeVal {
			ret2, ok := r.FastFreeVarMap[a2]
			if ok {
				ret = ret2
			} else {
				return ret
			}
		} else {
			return ret
		}
	}
	return ret
}

func GetValue(a ssa.Value) ssa.Value {
	switch b := a.(type) {
	case *ssa.UnOp:
		return GetValue(b.X)
	case *ssa.FieldAddr:
		return GetValue(b.X)
	}
	return a
}

func (r *CheckerRunner) FastSame(a ssa.Value, b ssa.Value) bool {
	a = GetValue(a)
	b = GetValue(b)
	if fa, isok := a.(*ssa.FreeVar); isok {
		a = r.LockupFreeVar(fa)
	}
	if fb, isok := b.(*ssa.FreeVar); isok {
		b = r.LockupFreeVar(fb)
	}
	return a == b || reflect.DeepEqual(a, b)
}

func GetAnnoFunctionList(fn *ssa.Function) (anfn []*ssa.Function) {
	anfn = append(anfn, fn)
	for _, x := range fn.AnonFuncs {
		anfn = append(anfn, GetAnnoFunctionList(x)...)
	}
	return anfn
}

func (r *CheckerRunner) RacePairsAnalyzerRun() {
	prog := r.prog
	pkgs := r.pkgs
	var mainpkgs []*ssa.Package
	for _, pkg := range pkgs {
		if pkg != nil {
			if pkg.Func("main") != nil {
				mainpkgs = append(mainpkgs, pkg)
			}
			if testpkg := prog.CreateTestMainPackage(pkg); testpkg != nil {
				mainpkgs = append(mainpkgs, testpkg)
			}
		}
	}

	var callGraph *callgraph.Graph

	cg2 := cha.CallGraph(prog)

	if len(mainpkgs) == 0 || _ChaCallGraph_ {
		//println("No Main Package Found")
		callGraph = cg2
	} else {
		config := &pointer.Config{
			Mains:          mainpkgs,
			BuildCallGraph: true,
		}
		result, err := pointer.Analyze(config)
		if err != nil {
			//println("Panic At pointer.Analyze")
			callGraph = cg2
		} else {
			callGraph = result.CallGraph
		}
	}

	FuncsList := ssautil.AllFunctions(prog)

	pkgset := make(map[*ssa.Package]bool)
	for _, pkg := range pkgs {
		pkgset[pkg] = true
	}

	for fn := range FuncsList {
		if fn.Blocks != nil && fn.Pkg != nil && pkgset[fn.Pkg] && fn.Name() != "init" {
			r.runFunc1(fn)
		}

		if pkgset[fn.Pkg] && callGraph.Nodes[fn] == nil && fn.Parent() == nil {
			//println("dead code", fn.String())
			//Add fake cg node to improve cover
			annoFnSet := make(map[*ssa.Function]bool)
			for _, fn := range GetAnnoFunctionList(fn) {
				annoFnSet[fn] = true
			}

			//copy nodes
			for k := range annoFnSet {
				if callGraph.Nodes[k] == nil {
					callGraph.CreateNode(k)
				}
			}

			//copy edges
			for k := range annoFnSet {
				node := cg2.Nodes[k]
				for _, edge := range node.Out {
					if calleefn := edge.Callee.Func; annoFnSet[calleefn] {
						callgraph.AddEdge(callGraph.Nodes[k], edge.Site, callGraph.Nodes[calleefn])
					}
				}
			}

			//Add A fake edge from node to fn
			callgraph.AddEdge(callGraph.Root, nil, callGraph.Nodes[fn])
		}
	}

	if _debug_print_ {
		println("Field")
		for i, r := range r.RecordSet_Field {
			println(i, toString(prog, r.ins))
		}

		println("Array")
		for i, r := range r.RecordSet_Array {
			println(i, toString(prog, r.ins), r.ins.String(), r.value.String(), r.isWrite)
		}

		println("Basic")
		for i, r := range r.RecordSet_Basic {
			println(i, toString(prog, r.ins), r.ins.String(), r.value.String(), r.isWrite)
		}

		println("Map")
		for i, r := range r.RecordSet_Map {
			println(i, toString(prog, r.ins), r.ins.String(), r.value.String(), r.isWrite)
		}
	}

	var wg sync.WaitGroup
	var tmp_pair [4][][2]RecordField
	for i, pair := range [][]RecordField{r.RecordSet_Field, r.RecordSet_Array, r.RecordSet_Basic, r.RecordSet_Map} {
		wg.Add(1)
		go func(i int, pair []RecordField) {
			tmp_pair[i] = r.GenPair(pair)
			wg.Done()
		}(i, pair)
	}
	wg.Wait()

	for i := range tmp_pair {
		r.PairSet = append(r.PairSet, tmp_pair[i]...)
	}

	if _debug_print_ {
		println("PairSet")
		for i, r := range r.PairSet {
			println(i, toString(prog, r[0].ins), "\n", toString(prog, r[1].ins))
		}
	}

	if false {
		var edges []string
		_ = callgraph.GraphVisitEdges(callGraph, func(edge *callgraph.Edge) error {
			caller := edge.Caller.Func
			edges = append(edges, fmt.Sprint(caller, " --> ", edge.Callee.Func))
			return nil
		})

		// Print the edges in sorted order.
		sort.Strings(edges)
		for _, edge := range edges {
			fmt.Println(edge)
		}
	}

	MX := 64
	if _debug_print_ {
		MX = 1
	}
	ch := make(chan int, MX)
	var mu sync.Mutex

	for _, x := range r.PairSet {
		r1 := x
		ch <- 1
		go func() {
			if CheckReachablePair(callGraph, r1) {
				mu.Lock()
				r.ReachablePairSet = append(r.ReachablePairSet, r1)
				mu.Unlock()
			}
			<-ch
		}()
	}

	for i := 0; i < MX; i++ {
		ch <- 1
	}

	if _debug_print_ {
		println("Reachable Pair")
		for i, r := range r.ReachablePairSet {
			println(i, toString(prog, r[0].ins), "\n", toString(prog, r[1].ins))
		}
	}

	for i := 0; i < MX; i++ {
		<-ch
	}

	for _, x := range r.ReachablePairSet {
		r1 := x
		ch <- 1
		go func() {
			r.CheckHappendBefore(prog, callGraph, r1)
			<-ch
		}()
	}

	for i := 0; i < MX; i++ {
		ch <- 1
	}
}

func isInAnnoFunc(ins ssa.Instruction) bool {
	return ins.Parent().Parent() != nil
}

func hasPos(ins ssa.Instruction) bool {
	return ins.Pos() != token.NoPos
}

func (r *CheckerRunner) GenPair(RecordSet []RecordField) (ret [][2]RecordField) {
	for i := range RecordSet {
		if pi := RecordSet[i]; pi.isWrite {
			for j := range RecordSet {
				if pj := RecordSet[j]; !pj.isWrite || i < j {
					if reflect.DeepEqual(pi.value.Type(), pj.value.Type()) &&
						pi.Field == pj.Field &&
						pi.ins.Block() != pj.ins.Block() &&
						(!pi.isAtomic || !pj.isAtomic) &&
						(isInAnnoFunc(pi.ins) || isInAnnoFunc(pj.ins)) &&
						r.FastSame(pi.value, pj.value) &&
						hasPos(pi.ins) && hasPos(pj.ins) {
						ret = append(ret, [2]RecordField{pi, pj})
					}
				}
			}
		}
	}
	return ret
}

func GetParent(fn *ssa.Function) *ssa.Function {
	for fn.Parent() != nil {
		fn = fn.Parent()
	}
	return fn
}

func CheckReachablePair(cg *callgraph.Graph, field [2]RecordField) bool {
	//println((*field[0].ins).Parent().Name(), (*field[1].ins).Parent().Name())

	node1 := cg.Nodes[field[0].ins.Parent()]
	node2 := cg.Nodes[field[1].ins.Parent()]

	if node1 == nil || node2 == nil {
		return false
	}

	startpoint := cg.Root
	if tmp := GetParent(node1.Func); tmp == GetParent(node2.Func) {
		startpoint = cg.Nodes[tmp]
	}

	seen := make(map[*callgraph.Node]int)
	var queue []*callgraph.Node

	queue = append(queue, startpoint)
	seen[startpoint] = 1

	for i := 0; i < len(queue); i++ {
		now := queue[i]
		state := seen[now]
		for _, e := range now.Out {
			new_state := state
			if _, isGo := e.Site.(*ssa.Go); isGo && !BlackFuncList[e.Site.Common().Value.String()] {
				new_state = 2
			}
			if seen[e.Callee] < new_state {
				seen[e.Callee] = new_state
				queue = append(queue, e.Callee)
			}
		}
	}

	return seen[node1]+seen[node2] >= 3 // Go + reachable
}

func isWrite(instruction ssa.Instruction, address ssa.Value) bool {
	switch i := instruction.(type) {
	case *ssa.Store:
		return i.Addr == address
	}
	return false
}

func toString(prog *ssa.Program, op ssa.Instruction) string {
	return (*prog.Fset).Position((op).Pos()).String()
}

func toStringValue(prog *ssa.Program, val ssa.Value) string {
	return (*prog.Fset).Position(val.Pos()).String()
}

func (r *CheckerRunner) analysisInstrs(instrs ssa.Instruction) {
	switch ins := instrs.(type) {
	case *ssa.FieldAddr:
		ref := *ins.Referrers()
		for i := range ref {
			tmp := RecordField{ref[i], ins.X, ins.Field, isWrite(ref[i], ins), false}
			r.RecordSet_Field = append(r.RecordSet_Field, tmp)
		}
	case *ssa.IndexAddr:
		ref := *ins.Referrers()
		for i := range ref {
			tmp := RecordField{ref[i], ins.X, 0, isWrite(ref[i], ins), false}
			r.RecordSet_Array = append(r.RecordSet_Array, tmp)
		}
	case *ssa.Alloc:
		elem := ins.Type().Underlying().(*types.Pointer).Elem()
		if _, ok := elem.(*types.Basic); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				if _, ok := ref[i].(*ssa.Call); ok {
					continue // for atomic call
				}
				tmp := RecordField{ref[i], ins, 0, isWrite(ref[i], ins), false}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp)
			}
		}
		if _, ok := elem.(*types.Array); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				tmp := RecordField{ref[i], ins, 0, isWrite(ref[i], ins), false}
				r.RecordSet_Array = append(r.RecordSet_Array, tmp)
			}
		}
		if _, ok := elem.(*types.Struct); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				tmp := RecordField{ref[i], ins, 0, isWrite(ref[i], ins), false}
				r.RecordSet_Field = append(r.RecordSet_Field, tmp)
			}
		}
		if _, ok := elem.(*types.Map); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				tmp := RecordField{ref[i], ins, 0, isWrite(ref[i], ins), false}
				r.RecordSet_Map = append(r.RecordSet_Map, tmp)
			}
		}
	case *ssa.MakeClosure:
		freevar := ins.Fn.(*ssa.Function).FreeVars
		for i := range ins.Bindings {
			r.AddFreeVarMap(freevar[i], ins.Bindings[i])
		}
	case *ssa.Call:
		fn := ins.Call.Value.String()
		if strings.HasPrefix(fn, "sync/atomic.") {
			fn2 := fn[12:]
			switch fn2 {
			case "AddInt32", "AddInt64", "AddUint32", "AddUint64", "AddUintptr":
				//func AddInt64(addr *int64, delta int64) (new int64)
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, true}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp)
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, false}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp2)
			case "CompareAndSwapInt32", "CompareAndSwapInt64", "CompareAndSwapPointer", "CompareAndSwapUint32", "CompareAndSwapUint64", "CompareAndSwapUintptr":
				//func CompareAndSwapInt32(addr *int32, old, new int32) (swapped bool)
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, true}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp)
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, true}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp2)
			case "LoadInt32", "LoadInt64", "LoadPointer", "LoadUint32", "LoadUint64", "LoadUintptr":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, false, true}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp)
			case "StoreInt32", "StoreInt64", "StorePointer", "StoreUint32", "StoreUint64", "StoreUintptr":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, true}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp)
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, false}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp2)
			case "SwapPointer", "SwapUint32", "SwapUint64", "SwapUintptr":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, true}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp)
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, true, true}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp2)
			}
		} else {
			switch fn {
			case "builtin delete": // map delete
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, false}
				r.RecordSet_Map = append(r.RecordSet_Map, tmp)
			case "builtin append":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, false}
				r.RecordSet_Array = append(r.RecordSet_Array, tmp)
				switch ins.Call.Args[1].Type().(type) {
				case *types.Basic:
					tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, false}
					r.RecordSet_Basic = append(r.RecordSet_Basic, tmp2)
				default:
					tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, false}
					r.RecordSet_Array = append(r.RecordSet_Array, tmp2)
				}
			case "builtin len":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, false, false}
				r.RecordSet_Array = append(r.RecordSet_Array, tmp)
			case "(*os.File).Write", "(*os.File).Read":
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, fn == "(*os.File).Write", false}
				r.RecordSet_Array = append(r.RecordSet_Array, tmp2)
				fallthrough
			case "(*os.File).Close":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, false}
				r.RecordSet_Basic = append(r.RecordSet_Basic, tmp)
			}
		}

	case *ssa.MapUpdate:
		tmp := RecordField{instrs, ins.Map, 0, true, false}
		r.RecordSet_Map = append(r.RecordSet_Map, tmp)
	case *ssa.Lookup:
		tmp := RecordField{instrs, ins.X, 0, false, false}
		r.RecordSet_Map = append(r.RecordSet_Map, tmp)
	default:
	}
}

func (r *CheckerRunner) visitBasicBlock(fnname string, bb *ssa.BasicBlock) {
	for i := range bb.Instrs {
		r.analysisInstrs(bb.Instrs[i])
	}
	for _, bb := range bb.Dominees() {
		r.visitBasicBlock(fnname, bb)
	}
}

func (r *CheckerRunner) runFunc1(fn *ssa.Function) {
	fnname := fn.Name()
	if strings.HasPrefix(fnname, "Benchmark") {
		return
	}
	if _debug_print_ {
		println("runFunc1", fnname, fn)
	}
	r.visitBasicBlock(fnname, fn.Blocks[0])

	for _, freevar := range fn.FreeVars {
		ref := *freevar.Referrers()
		for i := range ref {
			switch ref[i].(type) {
			case *ssa.Field:
			case *ssa.FieldAddr:
			case *ssa.Index:
			case *ssa.IndexAddr:
			case *ssa.Call:
			case *ssa.MapUpdate:
			case *ssa.Lookup:
			default:
				elem := freevar.Type().Underlying().(*types.Pointer).Elem()
				if _, ok := elem.(*types.Basic); ok {
					tmp := RecordField{ref[i], freevar, 0, isWrite(ref[i], freevar), false}
					r.RecordSet_Basic = append(r.RecordSet_Basic, tmp)
				}
				if _, ok := elem.(*types.Array); ok {
					tmp := RecordField{ref[i], freevar, 0, isWrite(ref[i], freevar), false}
					r.RecordSet_Array = append(r.RecordSet_Array, tmp)
				}
				if _, ok := elem.(*types.Struct); ok {
					tmp := RecordField{ref[i], freevar, 0, isWrite(ref[i], freevar), false}
					r.RecordSet_Field = append(r.RecordSet_Field, tmp)
				}
				if _, ok := elem.(*types.Map); ok {
					tmp := RecordField{ref[i], freevar, 0, isWrite(ref[i], freevar), false}
					r.RecordSet_Map = append(r.RecordSet_Map, tmp)
				}
			}
		}
	}
}

type ContextList []ssa.Instruction
type SyncMutexItem struct {
	value     ssa.Value
	inst      ssa.Instruction
	op        int
	deferCall bool
}

type SyncMutexList []SyncMutexItem

func GenContextPath(start, end *callgraph.Node) (ret ContextList) {
	tmp := PathSearch(start, end)
	for _, edge := range tmp {
		if edge.Site != nil {
			ret = append(ret, edge.Site)
		}
	}
	return ret
}

var BlackFuncList = map[string]bool{
	"(*testing.T).Run":           true,
	"(*testing.B).Run":           true,
	"(*testing.M).Run":           true,
	"workqueue.ParallelizeUntil": true,
	"(*syncmap.Map).Range":       true,
}

func PathSearch(start, end *callgraph.Node) (ret []*callgraph.Edge) {
	que := make([]*callgraph.Node, 0, 32)
	seen := make(map[*callgraph.Node]bool)
	from := make(map[*callgraph.Node]*callgraph.Edge)
	que = append(que, start)
	seen[start] = true
	for i := 0; i < len(que); i++ {
		n := que[i]
		if n == end {
			for j := 0; n != start; j++ {
				ret = append(ret, from[n])
				n = from[n].Caller
			}
			for i, j := 0, len(ret)-1; i < j; i, j = i+1, j-1 {
				ret[i], ret[j] = ret[j], ret[i]
			}
			return ret
		}
		for _, e := range n.Out {
			if fn := e.Callee.Func.String(); !seen[e.Callee] && !BlackFuncList[fn] { // don't go into (*testing.T).Run, it's not parallel
				seen[e.Callee] = true
				from[e.Callee] = e
				que = append(que, e.Callee)
			}
		}
	}
	return
}

func CleanDefer(x SyncMutexList) (ret SyncMutexList) {
	for i := range x {
		x[i].deferCall = false
	}
	return x
}

func (r *CheckerRunner) GetSyncValue(instr ssa.Instruction, dir int, op1 ssa.Instruction, icase *int) (ret SyncMutexList) {
	switch ins := instr.(type) {
	case *ssa.Send:
		return SyncMutexList{SyncMutexItem{value: ins.Chan, deferCall: false, op: 1}} //1 for send
	case *ssa.Select:
		if !ins.Blocking && dir == 1 {
			return nil
		}
		ret = nil
		if dir == 1 {
			for _, state := range ins.States {
				ret = append(ret, SyncMutexItem{state.Chan, nil, int(state.Dir), false})
			}
		} else {
			if *icase == -1 {
				return nil
			}
			tmp := *icase
			*icase = -1
			return SyncMutexList{SyncMutexItem{ins.States[tmp].Chan, nil, int(ins.States[tmp].Dir), false}} //2 for recv
		}
	case *ssa.UnOp:
		if ins.Op == token.ARROW {
			return SyncMutexList{SyncMutexItem{ins.X, nil, 2, false}} //2 for recv
		}
	case *ssa.Call:
		sig := ins.Call.Value.String()
		switch sig {
		case "(*sync.WaitGroup).Done":
			return SyncMutexList{SyncMutexItem{ins.Call.Args[0], ins, 20, false}} //20 for Done
		case "(*sync.WaitGroup).Wait":
			return SyncMutexList{SyncMutexItem{ins.Call.Args[0], ins, 21, false}} //21 for Wait
		case "builtin close":
			if _, ischen := ins.Call.Args[0].Type().(*types.Chan); ischen {
				return SyncMutexList{SyncMutexItem{ins.Call.Args[0], ins, 3, false}} //3 for close chan
			}
		case "(*golang.org/x/sync/errgroup.Group).Wait":
			fn, ok := ins.Call.Value.(*ssa.Function)
			if dir == 1 && ok {
				return CleanDefer(r.GetBefore(fn.Blocks[0].Instrs[0], op1))
			}
			if dir == -1 && ok {
				return CleanDefer(r.GetAfter(fn.Blocks[0].Instrs[0], op1))
			}
			return nil
		}
		if (strings.HasSuffix(sig, ").Lock") || strings.HasSuffix(sig, ").RLock")) && len(ins.Call.Args) == 1 {
			return SyncMutexList{SyncMutexItem{value: ins.Call.Args[0], deferCall: false, op: 10}} //10 for Lock
		}
		if (strings.HasSuffix(sig, ").Unlock") || strings.HasSuffix(sig, ").RUnlock")) && len(ins.Call.Args) == 1 {
			return SyncMutexList{SyncMutexItem{value: ins.Call.Args[0], deferCall: false, op: 11}} //11 for Unlock
		}
		return SyncMutexList{SyncMutexItem{nil, ins, 31, false}} //31 for normal call

	case *ssa.Defer:
		sig := ins.Call.Value.String()
		switch sig {
		case "(*sync.WaitGroup).Done":
			return SyncMutexList{SyncMutexItem{ins.Call.Args[0], ins, 20, true}} //20 for Done
		case "(*sync.WaitGroup).Wait":
			return SyncMutexList{SyncMutexItem{ins.Call.Args[0], ins, 21, true}} //21 for Wait
		case "builtin close":
			if _, ischen := ins.Call.Args[0].Type().(*types.Chan); ischen {
				return SyncMutexList{SyncMutexItem{ins.Call.Args[0], ins, 3, true}} //3 for close chan
			}
		case "(*golang.org/x/sync/errgroup.Group).Wait":
			fn, ok := ins.Call.Value.(*ssa.Function)
			if dir == 1 && ok {
				return CleanDefer(r.GetBefore(fn.Blocks[0].Instrs[0], op1))
			}
			if dir == -1 && ok {
				return CleanDefer(r.GetAfter(fn.Blocks[0].Instrs[0], op1))
			}
			return nil
		}
		if (strings.HasSuffix(sig, ").Lock") || strings.HasSuffix(sig, ").RLock")) && len(ins.Call.Args) == 1 {
			return SyncMutexList{SyncMutexItem{value: ins.Call.Args[0], deferCall: true, op: 10}} //10 for Lock
		}
		if (strings.HasSuffix(sig, ").Unlock") || strings.HasSuffix(sig, ").RUnlock")) && len(ins.Call.Args) == 1 {
			return SyncMutexList{SyncMutexItem{value: ins.Call.Args[0], deferCall: true, op: 11}} //11 for Unlock
		}
	case *ssa.Go:
		return SyncMutexList{SyncMutexItem{nil, ins, 30, false}} //30 for GoCall
	default:
		if reflect.DeepEqual(op1, instr) {
			return SyncMutexList{SyncMutexItem{nil, ins, 40, false}} // 40 for just match in set
		}
	}
	return nil
}

func (r *CheckerRunner) GetBefore(start ssa.Instruction, op1 ssa.Instruction) (sync SyncMutexList) {
	bb := start.Block()
	match := false
	icase := -1
	for bb != nil {
		for i := len(bb.Instrs) - 1; i >= 0; i-- {
			if match {
				if tmp := r.GetSyncValue(bb.Instrs[i], -1, op1, &icase); tmp != nil {
					sync = append(sync, tmp...)
				}
			} else {
				match = reflect.DeepEqual(bb.Instrs[i], start)
			}
		}
		if bb.Comment == "select.body" {
			next_block := bb.Preds[0]
			icmp := next_block.Instrs[len(next_block.Instrs)-2].(*ssa.BinOp)
			icase = int(icmp.Y.(*ssa.Const).Int64())
		}
		bb = bb.Idom()
	}
	return sync
}

func (r *CheckerRunner) GetAfter(start ssa.Instruction, op ssa.Instruction) (sync SyncMutexList) {
	bb := start.Block()
	match := false

	var que []*ssa.BasicBlock
	var seen = make(map[*ssa.BasicBlock]bool)
	que = append(que, bb)
	seen[bb] = true
	for i := 0; i < len(que); i++ {
		bb = que[i]
		for i := range bb.Instrs {
			if match {
				icase := -1
				if tmp := r.GetSyncValue(bb.Instrs[i], 1, op, &icase); tmp != nil {
					sync = append(sync, tmp...)
				}
			} else {
				match = reflect.DeepEqual(bb.Instrs[i], start)
			}
		}
		for _, succ := range bb.Succs {
			if !seen[succ] {
				seen[succ] = true
				que = append(que, succ)
			}
		}
	}
	return sync
}

func FilterDefer(buf SyncMutexList) (bf, af SyncMutexList) {
	for _, x := range buf {
		if x.deferCall {
			af = append(af, x)
		} else {
			bf = append(bf, x)
		}
	}
	return bf, af
}

func (r *CheckerRunner) GetBeforeAfertSet(cl ContextList, op1 ssa.Instruction) [2]SyncMutexList {
	seenGo := false
	var BeforeSet, AfterSet SyncMutexList
	for j := len(cl) - 1; j >= 0; j-- {
		ins := cl[j]
		tmp := r.GetBefore(ins, op1)
		if _, isGo := ins.(*ssa.Go); seenGo || isGo {
			seenGo = true
		}
		bf, af := FilterDefer(tmp)
		BeforeSet = append(BeforeSet, bf...)
		if !seenGo {
			AfterSet = append(AfterSet, af...)
			AfterSet = append(AfterSet, r.GetAfter(ins, op1)...)
		}
	}
	return [2]SyncMutexList{BeforeSet, AfterSet}
}

func CheckReachableInstr(start, end ssa.Instruction) bool {
	if start.Block().Parent() != end.Block().Parent() {
		return false
	}
	bb := start.Block()
	match := false

	var que []*ssa.BasicBlock
	var seen = make(map[*ssa.BasicBlock]bool)
	que = append(que, bb)
	seen[bb] = true
	for i := 0; i < len(que); i++ {
		bb = que[i]
		for i := range bb.Instrs {
			if match && reflect.DeepEqual(bb.Instrs[i], end) {
				return true
			} else {
				if !match && reflect.DeepEqual(bb.Instrs[i], start) {
					match = true
					// clean seen map, re-visit every block
					seen = make(map[*ssa.BasicBlock]bool)
				}
			}
		}
		for _, succ := range bb.Succs {
			if !seen[succ] {
				seen[succ] = true
				que = append(que, succ)
			}
		}
	}
	return false
}

func isCopyToHeap(call, ins ssa.Instruction) bool {
	if ins2, ok := ins.(*ssa.Store); ok {
		addr := GetValue(ins2.Addr)
		if addr2, ok2 := addr.(*ssa.Alloc); ok2 {
			return CheckReachableInstr(call, addr2)
		}
	}
	return false
}

func FindGoCallInAfterSet(ctx1 ContextList, afterSet SyncMutexList, instr2 ssa.Instruction) bool {
	for _, call := range ctx1 {
		if _, isgo := call.(*ssa.Go); isgo {
			for _, item := range afterSet {
				if item.inst != nil && item.inst.Pos() == call.Pos() && (isCopyToHeap(call, instr2) || !CheckReachableInstr(call, instr2)) {
					return true
				}
			}
		}
		if _, iscall := call.(*ssa.Call); iscall {
			for _, item := range afterSet {
				if item.inst != nil && item.inst.Pos() == call.Pos() && (isCopyToHeap(call, instr2) || !CheckReachableInstr(call, instr2)) {
					return true
				}
			}
		}
	}
	return false
}

// item_B Happens before or sync with item_A
func (r *CheckerRunner) HappensBeforeFromSet(beforeList SyncMutexList, afterList SyncMutexList) bool {
	//Find Chan
	for _, itemB := range beforeList {
		if itemB.op < 10 { // is a chan
			for _, itemA := range afterList {
				if itemA.op < 10 && itemA.op != itemB.op && r.FastSame(itemA.value, itemB.value) {
					return true
				}
			}
		}
	}

	// Find Wg
	for _, itemB := range beforeList {
		if itemB.op == 21 { // is a Wg.Wait
			for _, itemA := range afterList {
				if itemA.op == 20 && r.FastSame(itemA.value, itemB.value) { // is a Wg.Done
					return true
				}
			}
		}
	}

	return false
}

func PrintCtx(prog *ssa.Program, ctx ContextList) {
	for i, c := range ctx {
		fmt.Println("\t#", i, (*prog.Fset).Position(c.Pos()).String(), c.String())
	}
}

func (r *CheckerRunner) ReportRaceWithCtx(prog *ssa.Program, field [2]RecordField, ctx [2]ContextList) {
	r.ResultMux.Lock()
	defer r.ResultMux.Unlock()

	if r.ResultSet == nil {
		r.ResultSet = make(map[ssa.Value][]*Result)
	}

	val := GetValue(field[0].value)
	if freeval, ok := val.(*ssa.FreeVar); ok {
		val = r.LockupFreeVar(freeval)
	}
	r.ResultSet[val] = append(r.ResultSet[val], &Result{field: field, ctx: ctx})
}

func hasGoCall(start int, ctx ContextList) bool {
	for i := start; i < len(ctx); i++ {
		if _, ok := ctx[i].(*ssa.Go); ok {
			return true
		}
	}
	return false
}

func CalcMutexMap(set SyncMutexList) (ret map[ssa.Value]int) {
	ret = make(map[ssa.Value]int)
	for _, item := range set {
		if item.op == 10 || item.op == 11 {
			value := GetValue(item.value)
			//println(value)
			if _, ok := ret[value]; !ok {
				ret[value] = 0
			}
			if item.op == 10 { //lock
				ret[value]++
			} else { //item.op ==11 //unlock
				ret[value]--
			}
		}
	}

	return ret
}

func (r *CheckerRunner) hasSameLock(set1, set2 SyncMutexList) bool {
	Map1 := CalcMutexMap(set1)
	Map2 := CalcMutexMap(set2)
	for k1, v1 := range Map1 {
		for k2, v2 := range Map2 {
			if v1 > 0 && v2 > 0 && r.FastSame(k1, k2) {
				return true
			}
		}
	}
	return false
}

func GetLastOp(ctx1, ctx2 ContextList) (p1, p2 int) {
	p1, p2 = 0, 0
	for p1 < len(ctx1) && p2 < len(ctx2) {
		fn := ctx1[p1].Parent()
		for p1+1 < len(ctx1) && ctx1[p1+1].Parent() == fn {
			p1++
		}
		for p2+1 < len(ctx2) && ctx2[p2+1].Parent() == fn {
			p2++
		}
		if p1+1 < len(ctx1) && p2+1 < len(ctx2) && ctx1[p1+1].Parent() == ctx2[p2+1].Parent() {
			p1++
			p2++
		} else {
			break
		}
	}
	return p1, p2
}

func (r *CheckerRunner) CheckHappendBefore(prog *ssa.Program, cg *callgraph.Graph, field [2]RecordField) {
	node1 := cg.Nodes[field[0].ins.Parent()]
	node2 := cg.Nodes[field[1].ins.Parent()]

	if node1 == nil || node2 == nil {
		return
	}

	startpoint := cg.Root
	if tmp := GetParent(node1.Func); tmp == GetParent(node2.Func) {
		startpoint = cg.Nodes[tmp]
	}

	ctx1 := append(GenContextPath(startpoint, node1), field[0].ins)
	ctx2 := append(GenContextPath(startpoint, node2), field[1].ins)

	lastOp1, lastOp2 := GetLastOp(ctx1, ctx2)
	if !CheckReachableInstr(ctx1[lastOp1], ctx2[lastOp2]) && !CheckReachableInstr(ctx2[lastOp2], ctx1[lastOp1]) {
		if _debug_print_ {
			println("Reason: lastOp")
		}
		return
	}

	if !hasGoCall(lastOp1, ctx1) && !hasGoCall(lastOp2, ctx2) {
		return
	}

	set1 := r.GetBeforeAfertSet(ctx1, field[1].ins)
	set2 := r.GetBeforeAfertSet(ctx2, field[0].ins)

	if len(ctx1) == len(ctx2) {
		isSame := true
		for i := len(ctx1) - 2; i >= 0; i-- {
			if ctx1[i] != ctx2[i] {
				isSame = false
				break
			}
		}
		if isSame {
			if _debug_print_ {
				println("Reason: Same Ctx")
			}
			return
		}
	}

	flag := false
	elem := GetValue(field[0].value).Type().Underlying()
	for p, ok := elem.(*types.Pointer); ok; p, ok = elem.(*types.Pointer) {
		elem = p.Elem()
	}
	switch elem.(type) {
	case *types.Slice:
		flag = true
	case *types.Basic:
		flag = true
	case *types.Named:
		flag = true
	case *types.Struct:
		flag = true
	}

	if flag && r.hasSameLock(set1[0], set2[0]) {
		if _debug_print_ {
			println("Reason: Same Clock")
		}
		return
	}

	if FindGoCallInAfterSet(ctx1, set2[1], field[1].ins) {
		if _debug_print_ {
			println("Reason: FindGoCallInAfterSet1")
		}
		return
	}

	if FindGoCallInAfterSet(ctx2, set1[1], field[0].ins) {
		if _debug_print_ {
			println("Reason: FindGoCallInAfterSet2")
		}
		return
	}

	if r.HappensBeforeFromSet(set1[0], set2[1]) {
		if _debug_print_ {
			println("Reason: HappensBeforeFromSet1")
		}
		return
	}
	if r.HappensBeforeFromSet(set2[0], set1[1]) {
		if _debug_print_ {
			println("Reason: HappensBeforeFromSet2")
		}
		return
	}

	r.ReportRaceWithCtx(prog, field, [2]ContextList{ctx1, ctx2})
}

func (r *CheckerRunner) PrintResult() {
	for k, v := range r.ResultSet {
		fmt.Println("Race Found:[ZZZ]", toStringValue(r.prog, k), k.String())
		if _detailreport_ {
			for _, c := range v {
				fmt.Println(toString(r.prog, c.field[0].ins), "Func:", c.field[0].ins.Parent().Name())
				PrintCtx(r.prog, c.ctx[0])
				fmt.Println("------------")
				fmt.Println(toString(r.prog, c.field[1].ins), "Func:", c.field[1].ins.Parent().Name())
				PrintCtx(r.prog, c.ctx[1])
				fmt.Println("============")
			}
		}
	}
}

func main() {
	fmt.Fprintln(os.Stderr, "Run for [ZZZ]:", os.Args[1])
	cfg := packages.Config{Mode: packages.LoadAllSyntax, Tests: _UseTestCase_}
	initial, err := packages.Load(&cfg, os.Args[1])
	if err != nil {
		return
		//log.Fatal(err)
	}
	pkgerr := 0
	packages.Visit(initial, nil, func(pkg *packages.Package) {
		pkgerr += len(pkg.Errors)
	})

	if (pkgerr > 0 && !_debug_print_) || packages.PrintErrors(initial) > 0 {
		return
	}

	if _UseTestCase_ {

		// For example, when using the go command, loading "fmt" with Tests=true
		// returns four packages, with IDs "fmt" (the standard package),
		// "fmt [fmt.test]" (the package as compiled for the test),
		// "fmt_test" (the test functions from source files in package fmt_test),
		// and "fmt.test" (the test binary).

		initial2 := initial[:0]
		for i := range initial {
			if strings.HasSuffix(initial[i].ID, "]") {
				initial2 = append(initial2, initial[i])
			}
		}
		initial = initial2
	}

	// Create SSA packages for well-typed packages and their dependencies.
	prog, pkgs := ssautil.AllPackages(initial, 0)

	if len(pkgs) > 1000 {
		return
	}

	// Build SSA code for the whole program.
	prog.Build()

	runner := &CheckerRunner{
		prog: prog,
		pkgs: pkgs,
	}

	runner.RacePairsAnalyzerRun()
	runner.PrintResult()
}
