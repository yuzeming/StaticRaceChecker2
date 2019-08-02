package main

import (
	"flag"
	"fmt"
	"go/parser"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/callgraph/cha"
	"golang.org/x/tools/go/packages"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"io/ioutil"
	"log"
	"os"
	"path"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"sync"
)

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
	// config
	indexStart int
	recursive  bool

	useTestCase  bool
	debugPrint   bool
	chaCallGraph bool
	detailReport bool
	printCtx     bool
	path         string
	whitelist    string

	//temp info
	MuteMap map[int]bool

	RecordsetField   []RecordField
	RecordSetArray   []RecordField
	RecordsetBasic   []RecordField
	RecordsetMap     []RecordField
	PairSet          [][2]RecordField
	ReachablePairSet [][2]RecordField
	lastIns          ssa.Instruction

	FastFreeVarMap map[*ssa.FreeVar]ssa.Value

	//input
	prog *ssa.Program
	pkgs []*ssa.Package

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

func GetValueAndFid(a ssa.Value) (ssa.Value, int) {
	switch b := a.(type) {
	case *ssa.UnOp:
		return GetValueAndFid(b.X)
	case *ssa.FieldAddr:
		x, y := GetValueAndFid(b.X)
		return x, (y << 4) + b.Field
	case *ssa.Slice:
		return b.X, 0
	}
	return a, 0
}

func GetValue(a ssa.Value) ssa.Value {
	v, _ := GetValueAndFid(a)
	return v
}

func (r *CheckerRunner) FastSame(a ssa.Value, b ssa.Value) bool {
	a, fid1 := GetValueAndFid(a)
	b, fid2 := GetValueAndFid(b)
	if fa, isok := a.(*ssa.FreeVar); isok {
		a = r.LockupFreeVar(fa)
	}
	if fb, isok2 := b.(*ssa.FreeVar); isok2 {
		b = r.LockupFreeVar(fb)
	}
	return a == b && fid1 == fid2
}

func GetAnnoFunctionList(fn *ssa.Function) (anfn []*ssa.Function) {
	anfn = append(anfn, fn)
	for _, x := range fn.AnonFuncs {
		anfn = append(anfn, GetAnnoFunctionList(x)...)
	}
	return anfn
}

func (r *CheckerRunner) BuildMuteMap() {
	r.MuteMap = make(map[int]bool)
	fset := token.NewFileSet()
	r.prog.Fset.Iterate(func(file *token.File) bool {
		f, err := parser.ParseFile(fset, file.Name(), nil, parser.ParseComments)
		if err != nil {
			return false
		}
		for _, cg := range f.Comments {
			for _, c := range cg.List {
				if strings.HasPrefix(strings.TrimLeft(c.Text, "/ "), "[MUTE]") {
					r.MuteMap[int(c.Pos())-fset.Position(c.Pos()).Column] = true
				}
			}
		}
		return true
	})
}

func (r *CheckerRunner) CheckInMuteMap(pos token.Pos) bool {
	p := int(pos) - r.prog.Fset.Position(pos).Column
	return !r.MuteMap[p]
}

func (r *CheckerRunner) RacePairsAnalyzerRun() {
	prog := r.prog
	pkgs := r.pkgs

	r.BuildMuteMap()

	var mainPkgs []*ssa.Package
	for _, pkg := range pkgs {
		if pkg != nil {
			if pkg.Func("main") != nil {
				mainPkgs = append(mainPkgs, pkg)
			}
			if testpkg := prog.CreateTestMainPackage(pkg); testpkg != nil {
				mainPkgs = append(mainPkgs, testpkg)
			}
		}
	}

	var callGraph *callgraph.Graph

	cg2 := cha.CallGraph(prog)

	if len(mainPkgs) == 0 || r.chaCallGraph {
		//println("No Main Package Found")
		callGraph = cg2
	} else {
		config := &pointer.Config{
			Mains:          mainPkgs,
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

	pkgMap := make(map[*ssa.Package]bool)
	for _, pkg := range pkgs {
		pkgMap[pkg] = true
	}

	for fn := range FuncsList {
		if fn.Blocks != nil && fn.Pkg != nil && fn.Name() != "init" && pkgMap[fn.Pkg] {
			r.runFunc1(fn)

			if callGraph.Nodes[fn] == nil && fn.Parent() == nil {
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
	}

	if r.debugPrint {
		println("Field")
		for i, r := range r.RecordsetField {
			println(i, toString(prog, r.ins))
		}

		println("Array")
		for i, r := range r.RecordSetArray {
			println(i, toString(prog, r.ins), r.ins.String(), r.value.String(), r.isWrite)
		}

		println("Basic")
		for i, r := range r.RecordsetBasic {
			println(i, toString(prog, r.ins), r.ins.String(), r.value.String(), r.isWrite)
		}

		println("Map")
		for i, r := range r.RecordsetMap {
			println(i, toString(prog, r.ins), r.ins.String(), r.value.String(), r.isWrite)
		}
	}

	var wg sync.WaitGroup
	var tmpPair [4][][2]RecordField
	for i, pair := range [][]RecordField{r.RecordsetField, r.RecordSetArray, r.RecordsetBasic, r.RecordsetMap} {
		wg.Add(1)
		go func(i int, pair []RecordField) {
			tmpPair[i] = r.GenPair(pair)
			wg.Done()
		}(i, pair)
	}
	wg.Wait()

	for i := range tmpPair {
		r.PairSet = append(r.PairSet, tmpPair[i]...)
	}

	if r.debugPrint {
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
	if r.debugPrint {
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

	if r.debugPrint {
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

func (r *CheckerRunner) GenPair(RecordSet []RecordField) (ret [][2]RecordField) {
	for i := range RecordSet {
		if pi := RecordSet[i]; r.CheckInMuteMap(pi.ins.Pos()) && r.CheckInMuteMap(GetValue(pi.value).Pos()) {
			for j := range RecordSet {
				if pj := RecordSet[j]; i < j {
					if r.CheckInMuteMap(pj.ins.Pos()) &&
						(pi.isWrite || pj.isWrite) &&
						//	reflect.DeepEqual(pi.value.Type(), pj.value.Type()) &&
						pi.Field == pj.Field &&
						pi.ins.Block() != pj.ins.Block() &&
						(!pi.isAtomic || !pj.isAtomic) &&
						(isInAnnoFunc(pi.ins) || isInAnnoFunc(pj.ins)) &&
						r.FastSame(pi.value, pj.value) { //&&
						//hasPos(pi.ins) && hasPos(pj.ins)

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
			newState := state
			if _, isGo := e.Site.(*ssa.Go); isGo && !BlackFuncList[e.Site.Common().Value.String()] {
				newState = 2
			}
			if seen[e.Callee] < newState {
				seen[e.Callee] = newState
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

func (r *CheckerRunner) AppendRecord(re []RecordField, t RecordField) []RecordField {
	if len(re) == 0 || re[len(re)-1].ins != r.lastIns || re[len(re)-1].value != t.value { // just append
		re = append(re, t)
	} else if re[len(re)-1].isWrite && !t.isWrite {
		return re
	} else { // re[len(re)-1] is Read
		re[len(re)-1] = t // replace the last item
	}
	return re
}

func (r *CheckerRunner) AddOperation(ins ssa.Instruction, v ssa.Value, field int, isW bool, isA bool) {
	if _, is := ins.(*ssa.MakeClosure); is {
		return
	}
	v, fid := GetValueAndFid(v)
	tmp := RecordField{ins, v, (fid << 4) + field, isW, isA}

	switch v.(type) {
	case *ssa.Alloc, *ssa.FreeVar:
		//ok
	default:
		return
	}

	loop := true
	elem := v.Type().Underlying()
	for loop {
		loop = false
		elem = elem.(*types.Pointer).Elem()
		switch elem.(type) {
		case *types.Basic:
			r.RecordsetBasic = r.AppendRecord(r.RecordsetBasic, tmp)
		case *types.Array, *types.Slice:
			r.RecordSetArray = r.AppendRecord(r.RecordSetArray, tmp)
		case *types.Struct, *types.Named:
			r.RecordsetField = r.AppendRecord(r.RecordsetField, tmp)
		case *types.Map:
			r.RecordsetMap = r.AppendRecord(r.RecordsetMap, tmp)
		case *types.Pointer:
			loop = true
		}
	}
}

func (r *CheckerRunner) analysisInstrs(instrs ssa.Instruction) {
	switch ins := instrs.(type) {
	case *ssa.FieldAddr:
		ref := *ins.Referrers()
		for i := range ref {
			r.AddOperation(ref[i], ins.X, ins.Field, isWrite(ref[i], ins), false)
		}
	case *ssa.IndexAddr:
		ref := *ins.Referrers()
		for i := range ref {
			r.AddOperation(ref[i], ins.X, 0, isWrite(ref[i], ins), false)
		}
	case *ssa.Alloc:
		if !ins.Heap {
			return
		}

		elem := ins.Type().Underlying().(*types.Pointer).Elem()
		if _, ok := elem.(*types.Basic); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				if _, ok := ref[i].(*ssa.Call); ok {
					continue // for atomic call
				}
				r.AddOperation(ref[i], ins, 0, isWrite(ref[i], ins), false)
			}
		} else {
			ref := *ins.Referrers()
			for i := range ref {
				r.AddOperation(ref[i], ins, 0, isWrite(ref[i], ins), false)
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
				r.AddOperation(instrs, ins.Call.Args[0], 0, true, true)
				r.AddOperation(instrs, ins.Call.Args[1], 0, false, false)
			case "CompareAndSwapInt32", "CompareAndSwapInt64", "CompareAndSwapPointer", "CompareAndSwapUint32", "CompareAndSwapUint64", "CompareAndSwapUintptr":
				//func CompareAndSwapInt32(addr *int32, old, new int32) (swapped bool)
				r.AddOperation(instrs, ins.Call.Args[0], 0, true, true)
				r.AddOperation(instrs, ins.Call.Args[1], 0, false, true)
			case "LoadInt32", "LoadInt64", "LoadPointer", "LoadUint32", "LoadUint64", "LoadUintptr":
				r.AddOperation(instrs, ins.Call.Args[0], 0, false, true)
			case "StoreInt32", "StoreInt64", "StorePointer", "StoreUint32", "StoreUint64", "StoreUintptr":
				r.AddOperation(instrs, ins.Call.Args[0], 0, true, true)
				r.AddOperation(instrs, ins.Call.Args[1], 0, false, false)
			case "SwapPointer", "SwapUint32", "SwapUint64", "SwapUintptr":
				r.AddOperation(instrs, ins.Call.Args[0], 0, true, true)
				r.AddOperation(instrs, ins.Call.Args[1], 0, true, true)
			}
		} else {
			switch fn {
			case "builtin delete": // map delete
				r.AddOperation(instrs, ins.Call.Args[0], 0, true, false)
				r.AddOperation(instrs, ins.Call.Args[1], 0, false, false)
			case "builtin append":
				//r.AddOperation(instrs, ins.Call.Args[0], 0, false, false)
				r.AddOperation(instrs, ins.Call.Args[1], 0, false, false)
			case "builtin len":
				r.AddOperation(instrs, ins.Call.Args[0], 0, false, false)
			case "(*os.File).Write", "(*os.File).Read":
				r.AddOperation(instrs, ins.Call.Args[1], 0, fn != "(*os.File).Write", false)
				fallthrough
			case "(*os.File).Close":
				r.AddOperation(instrs, ins.Call.Args[0], 99, true, false) // this modify the stat of file, not the file pointer
			}
		}

	case *ssa.MapUpdate:
		r.AddOperation(instrs, ins.Map, 0, true, false)
		r.AddOperation(instrs, ins.Key, 0, false, false)
		r.AddOperation(instrs, ins.Value, 0, false, false)
	case *ssa.Lookup:
		r.AddOperation(instrs, ins.X, 0, false, false)
		r.AddOperation(instrs, ins.Index, 0, false, false)
	default:
	}
	r.lastIns = instrs
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
	if r.debugPrint {
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
			case *ssa.MakeClosure:
			default:
				r.AddOperation(ref[i], freevar, 0, isWrite(ref[i], freevar), false)
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

func SetDeferFlag(x SyncMutexList, flag bool) (ret SyncMutexList) {
	for i := range x {
		x[i].deferCall = flag
	}
	return x
}

func isSmallFunc(fn *ssa.Function) bool {
	return len(fn.Params) == 0 && len(fn.FreeVars) > 0 && len(fn.Blocks) == 1 && len(fn.Blocks[0].Instrs) < 20
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
		}
		if (strings.HasSuffix(sig, ").Lock") || strings.HasSuffix(sig, ").RLock")) && len(ins.Call.Args) == 1 {
			return SyncMutexList{SyncMutexItem{value: ins.Call.Args[0], deferCall: false, op: 10}} //10 for Lock
		}
		if (strings.HasSuffix(sig, ").Unlock") || strings.HasSuffix(sig, ").RUnlock")) && len(ins.Call.Args) == 1 {
			return SyncMutexList{SyncMutexItem{value: ins.Call.Args[0], deferCall: false, op: 11}} //11 for Unlock
		}

		closure, ok := ins.Call.Value.(*ssa.MakeClosure)
		if ok {
			fn, ok2 := closure.Fn.(*ssa.Function)
			if ok2 && isSmallFunc(fn) {
				return SetDeferFlag(r.GetAfter(fn.Blocks[0].Instrs[0], op1), false)
			}
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
		}
		if (strings.HasSuffix(sig, ").Lock") || strings.HasSuffix(sig, ").RLock")) && len(ins.Call.Args) == 1 {
			return SyncMutexList{SyncMutexItem{value: ins.Call.Args[0], deferCall: true, op: 10}} //10 for Lock
		}
		if (strings.HasSuffix(sig, ").Unlock") || strings.HasSuffix(sig, ").RUnlock")) && len(ins.Call.Args) == 1 {
			return SyncMutexList{SyncMutexItem{value: ins.Call.Args[0], deferCall: true, op: 11}} //11 for Unlock
		}

		closure, ok := ins.Call.Value.(*ssa.MakeClosure)
		if ok {
			fn, ok2 := closure.Fn.(*ssa.Function)
			if ok2 && isSmallFunc(fn) {
				return SetDeferFlag(r.GetAfter(fn.Blocks[0].Instrs[0], op1), true)
			}
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
			nextBlock := bb.Preds[0]
			icmp := nextBlock.Instrs[len(nextBlock.Instrs)-2].(*ssa.BinOp)
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
		if r.debugPrint {
			println("Reason: lastOp")
		}
		return
	}

	if !hasGoCall(lastOp1, ctx1) && !hasGoCall(lastOp2, ctx2) {
		return
	}

	if len(ctx1) == len(ctx2) {
		isSame := true
		for i := len(ctx1) - 2; i >= 0; i-- {
			if ctx1[i] != ctx2[i] {
				isSame = false
				break
			}
		}
		if isSame {
			if r.debugPrint {
				println("Reason: Same Ctx")
			}
			return
		}
	}

	set1 := r.GetBeforeAfertSet(ctx1, field[1].ins)
	set2 := r.GetBeforeAfertSet(ctx2, field[0].ins)

	if r.hasSameLock(set1[0], set2[0]) {
		if r.debugPrint {
			println("Reason: Same Lock")
		}
		return
	}

	if FindGoCallInAfterSet(ctx1, set2[1], field[1].ins) {
		if r.debugPrint {
			println("Reason: FindGoCallInAfterSet1")
		}
		return
	}

	if FindGoCallInAfterSet(ctx2, set1[1], field[0].ins) {
		if r.debugPrint {
			println("Reason: FindGoCallInAfterSet2")
		}
		return
	}

	if r.HappensBeforeFromSet(set1[0], set2[1]) {
		if r.debugPrint {
			println("Reason: HappensBeforeFromSet1")
		}
		return
	}
	if r.HappensBeforeFromSet(set2[0], set1[1]) {
		if r.debugPrint {
			println("Reason: HappensBeforeFromSet2")
		}
		return
	}

	r.ReportRaceWithCtx(prog, field, [2]ContextList{ctx1, ctx2})
}

type ValueList []ssa.Value

func (s ValueList) Len() int           { return len(s) }
func (s ValueList) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }
func (s ValueList) Less(i, j int) bool { return s[i].Pos() < s[j].Pos() }

func (r *CheckerRunner) PrintResult() int {
	r.ResultMux.Lock()
	defer r.ResultMux.Unlock()
	var varlist ValueList
	for k := range r.ResultSet {
		varlist = append(varlist, k)
	}
	sort.Sort(varlist)

	for i := range varlist {
		k := varlist[i+r.indexStart]
		v := r.ResultSet[k]
		fmt.Printf("----------Bug[%d]----------\n", i)
		fmt.Printf("Type: Data Race \tReason: Two goroutines access the same variable concurrently and at least one of the accesses is a write. \n")
		fmt.Printf("Variable: %s \tFunction: %s \nPosition:%s\n", k.String(), k.Parent().Name(), toStringValue(r.prog, k))
		for j := range v {
			p1, p2 := v[j].field[0], v[j].field[1]
			fmt.Printf("Access1: %s @ %s\tAtomic:%t\tWrite:%t\n", p1.ins.String(), toString(r.prog, p1.ins), p1.isAtomic, p1.isWrite)
			if r.printCtx {
				PrintCtx(r.prog, v[j].ctx[0])
			}
			fmt.Printf("Access2: %s @ %s\tAtomic:%t\tWrite:%t\n", p2.ins.String(), toString(r.prog, p2.ins), p2.isAtomic, p2.isWrite)
			if r.printCtx {
				PrintCtx(r.prog, v[j].ctx[1])
			}
			if !r.detailReport {
				if len(v) > 1 {
					fmt.Printf("\t and more %d race ...\n", len(v)-1)
				}
				break
			} else {
				fmt.Printf("=====\n")
			}
		}

		//fmt.Printf("Race Found:[ZZZ]", toStringValue(r.prog, k), k.String(), k.Parent().Name())
		//if _detailreport_ {
		//	for _, c := range v {
		//		fmt.Println(toString(r.prog, c.field[0].ins), "Func:", c.field[0].ins.Parent().Name())
		//		PrintCtx(r.prog, c.ctx[0])
		//		fmt.Println("------------")
		//		fmt.Println(toString(r.prog, c.field[1].ins), "Func:", c.field[1].ins.Parent().Name())
		//		PrintCtx(r.prog, c.ctx[1])
		//		fmt.Println("============")
		//	}
		//}
	}
	return len(varlist)
}

func Run(conf *CheckerRunner, path string) int {
	runner := *conf
	runner.path = path

	cfg := packages.Config{Mode: packages.LoadAllSyntax, Tests: runner.useTestCase}
	initial, err := packages.Load(&cfg, runner.path)
	if err != nil {
		log.Fatal(err)
		return 0
	}
	pkgerr := 0
	packages.Visit(initial, nil, func(pkg *packages.Package) {
		pkgerr += len(pkg.Errors)
	})

	if (pkgerr > 0 && !runner.debugPrint) || packages.PrintErrors(initial) > 0 {
		return 0
	}

	if runner.useTestCase {
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

	// Build SSA code for the whole program.
	prog.Build()

	runner.prog = prog
	runner.pkgs = pkgs

	runner.RacePairsAnalyzerRun()
	return runner.PrintResult()
}

func HasGoFileInDir(path1 string) bool {
	files, err := ioutil.ReadDir(path1)
	if err != nil {
		return false
	}
	for _, f := range files {
		if !f.IsDir() && strings.HasSuffix(f.Name(), ".go") {
			return true
		}
	}
	return false
}

func main() {
	conf := &CheckerRunner{}
	flag.BoolVar(&conf.useTestCase, "t", true, "include test code")
	flag.BoolVar(&conf.chaCallGraph, "p", false, "use cha call graph only")
	flag.BoolVar(&conf.debugPrint, "debug", false, "print debug info to stderr")
	flag.BoolVar(&conf.detailReport, "d", false, "report all race pair")
	flag.BoolVar(&conf.printCtx, "c", false, "report context for every race pair")
	flag.StringVar(&conf.path, "path", "", "Path to  package ( must under %GOPATH% dir )")
	flag.BoolVar(&conf.recursive, "r", false, "recursive entry subdir")
	//flag.StringVar(&conf.whitelist,"whitelist","","Add a whitelist file ( format: FileName:LineNumber )")
	flag.Parse()

	if conf.path == "" {
		flag.PrintDefaults()
		return
	}

	var dirlist []string
	if conf.recursive {
		gopath, _ := os.LookupEnv("GOPATH")
		gosrc := path.Join(gopath, "src")
		err := filepath.Walk(path.Join(gosrc, conf.path), func(path1 string, info os.FileInfo, err error) error {
			//println(path1)
			if !info.IsDir() {
				return nil
			}

			if err != nil || info.Name()[0] == '.' || info.Name() == "vendor" {
				return filepath.SkipDir
			}
			if HasGoFileInDir(path1) {
				dirlist = append(dirlist, path1[len(gosrc)+1:])
			}
			return nil
		})
		if err != nil {
			log.Fatal(err)
		}
	} else {
		dirlist = append(dirlist, conf.path)
	}

	for _, p := range dirlist {
		tmp := Run(conf, p)
		conf.indexStart += tmp
	}

}
