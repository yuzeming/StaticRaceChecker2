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
	"log"
	"os"
	"reflect"
	"sort"
	"strings"
	"sync"
)

const _debug_print_ = false
const _IGNORE_TIMEOUT = false
const _ReqOneInAnnoFunc_ = true
const _ReqFastSame_ = true
const _UseTestCase_ = true
const _ChaCallGraph_ = false

type RecordField struct {
	ins      *ssa.Instruction
	value    ssa.Value
	Field    int
	isWrite  bool
	isAtomic bool
}

var FastFreeVarMap = make(map[*ssa.FreeVar]*ssa.Value)

func AddFreeVarMap(a *ssa.FreeVar, b *ssa.Value) {
	FastFreeVarMap[a] = b
}

func LockupFreeVar(a *ssa.FreeVar) (ret *ssa.Value) {
	ret = FastFreeVarMap[a]
	for ret != nil {
		a2, isFreeVal := (*ret).(*ssa.FreeVar)
		if isFreeVal {
			ret2, ok := FastFreeVarMap[a2]
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

func GetValue(a *ssa.Value) *ssa.Value {
	switch b := (*a).(type) {
	case *ssa.UnOp:
		return GetValue(&b.X)
	case *ssa.FieldAddr:
		return GetValue(&b.X)
	}
	return a
}

func FastSame(a *ssa.Value, b *ssa.Value) bool {
	a = GetValue(a)
	b = GetValue(b)
	if fa, isok := (*a).(*ssa.FreeVar); isok {
		a = LockupFreeVar(fa)
	}
	if fb, isok := (*b).(*ssa.FreeVar); isok {
		b = LockupFreeVar(fb)
	}
	return a == b || reflect.DeepEqual(a, b)
}

var RecordSet_Field []RecordField
var RecordSet_Array []RecordField
var RecordSet_Basic []RecordField
var RecordSet_Map []RecordField

var PairSet [][2]RecordField

func GetAnnoFunctionList(fn *ssa.Function) (anfn []*ssa.Function) {
	anfn = append(anfn, fn)
	for _, x := range fn.AnonFuncs {
		anfn = append(anfn, GetAnnoFunctionList(x)...)
	}
	return anfn
}

func RacePairsAnalyzerRun(prog *ssa.Program, pkgs []*ssa.Package) {
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
			runFunc1(fn)
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
		for i, r := range RecordSet_Field {
			println(i, toString(prog, r.ins))
		}

		println("Array")
		for i, r := range RecordSet_Array {
			println(i, toString(prog, r.ins), (*r.ins).String(), r.value.String(), r.isWrite)
		}

		println("Basic")
		for i, r := range RecordSet_Basic {
			println(i, toString(prog, r.ins), (*r.ins).String(), r.value.String(), r.isWrite)
		}

		println("Map")
		for i, r := range RecordSet_Map {
			println(i, toString(prog, r.ins), (*r.ins).String(), r.value.String(), r.isWrite)
		}
	}

	PairSet = append(PairSet, GenPair(RecordSet_Field)...)
	PairSet = append(PairSet, GenPair(RecordSet_Array)...)
	PairSet = append(PairSet, GenPair(RecordSet_Basic)...)
	PairSet = append(PairSet, GenPair(RecordSet_Map)...)

	if _debug_print_ {
		println("PairSet")
		for i, r := range PairSet {
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

	ReachablePairSet := PairSet[:0]
	for _, r := range PairSet {
		if CheckReachablePair(callGraph, r) {
			ReachablePairSet = append(ReachablePairSet, r)
		}
	}

	if _debug_print_ {
		println("Reachable Pair")
		for i, r := range ReachablePairSet {
			println(i, toString(prog, r[0].ins), "\n", toString(prog, r[1].ins))
		}
	}

	for _, r := range ReachablePairSet {
		CheckHappendBefore(prog, callGraph, r)
	}
}

func isInAnnoFunc(ins *ssa.Instruction) bool {
	return (*ins).Parent().Parent() != nil
}

func hasPos(ins *ssa.Instruction) bool {
	return (*ins).Pos() != token.NoPos
}

func GenPair(RecordSet []RecordField) (ret [][2]RecordField) {
	for i := range RecordSet {
		if pi := RecordSet[i]; pi.isWrite {
			for j := range RecordSet {
				if pj := RecordSet[j]; !pj.isWrite || i < j {
					if reflect.DeepEqual(pi.value.Type(), pj.value.Type()) &&
						pi.Field == pj.Field &&
						(*pi.ins).Block() != (*pj.ins).Block() &&
						(!pi.isAtomic || !pj.isAtomic) &&
						(!_ReqOneInAnnoFunc_ || isInAnnoFunc(pi.ins) || isInAnnoFunc(pj.ins)) &&
						(!_ReqFastSame_ || FastSame(&pi.value, &pj.value)) &&
						hasPos(pi.ins) && hasPos((pj.ins)) {
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

	node1 := cg.Nodes[(*field[0].ins).Parent()]
	node2 := cg.Nodes[(*field[1].ins).Parent()]

	if node1 == nil || node2 == nil {
		//println("nil x2 exit")
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
			if _, isGo := e.Site.(*ssa.Go); isGo {
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

func toString(pass *ssa.Program, op *ssa.Instruction) string {
	return (*pass.Fset).Position((*op).Pos()).String()
}

func toStringValue(pass *ssa.Program, val *ssa.Value) string {
	return (*pass.Fset).Position((*val).Pos()).String()
}

func analysisInstrs(instrs *ssa.Instruction) {
	switch ins := (*instrs).(type) {
	//case *ssa.Field:
	//	ref := *ins.Referrers()
	//	for i := range ref {
	//		tmp := RecordField{&ref[i], ins.X, ins.Field, false, isWrite(ref[i], ins), false}
	//		RecordSet_Field = append(RecordSet_Field, tmp)
	//	}
	case *ssa.FieldAddr:
		ref := *ins.Referrers()
		for i := range ref {
			tmp := RecordField{&ref[i], ins.X, ins.Field, isWrite(ref[i], ins), false}
			RecordSet_Field = append(RecordSet_Field, tmp)
		}
	//case *ssa.Index:
	//	ref := *ins.Referrers()
	//	for i := range ref {
	//		tmp := RecordField{&ref[i], ins.X, 0, false, isWrite(ref[i], ins), false}
	//		RecordSet_Array = append(RecordSet_Array, tmp)
	//	}
	case *ssa.IndexAddr:
		ref := *ins.Referrers()
		for i := range ref {
			tmp := RecordField{&ref[i], ins.X, 0, isWrite(ref[i], ins), false}
			RecordSet_Array = append(RecordSet_Array, tmp)
		}
	case *ssa.Alloc:
		elem := ins.Type().Underlying().(*types.Pointer).Elem()
		if _, ok := elem.(*types.Basic); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				if _, ok := ref[i].(*ssa.Call); ok {
					continue // for atomic call
				}
				tmp := RecordField{&ref[i], ins, 0, isWrite(ref[i], ins), false}
				RecordSet_Basic = append(RecordSet_Basic, tmp)
			}
		}
		if _, ok := elem.(*types.Array); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				tmp := RecordField{&ref[i], ins, 0, isWrite(ref[i], ins), false}
				RecordSet_Array = append(RecordSet_Array, tmp)
			}
		}
		if _, ok := elem.(*types.Struct); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				tmp := RecordField{&ref[i], ins, 0, isWrite(ref[i], ins), false}
				RecordSet_Field = append(RecordSet_Field, tmp)
			}
		}
		if _, ok := elem.(*types.Map); ok && ins.Heap {
			ref := *ins.Referrers()
			for i := range ref {
				tmp := RecordField{&ref[i], ins, 0, isWrite(ref[i], ins), false}
				RecordSet_Map = append(RecordSet_Map, tmp)
			}
		}
	case *ssa.MakeClosure:
		freevar := ins.Fn.(*ssa.Function).FreeVars
		for i := range ins.Bindings {
			AddFreeVarMap(freevar[i], &ins.Bindings[i])
		}
	case *ssa.Call:
		fn := ins.Call.Value.String()
		if strings.HasPrefix(fn, "sync/atomic.") {
			fn2 := fn[12:]
			switch fn2 {
			case "AddInt32", "AddInt64", "AddUint32", "AddUint64", "AddUintptr":
				//func AddInt64(addr *int64, delta int64) (new int64)
				fallthrough
			case "CompareAndSwapInt32", "CompareAndSwapInt64", "CompareAndSwapPointer", "CompareAndSwapUint32", "CompareAndSwapUint64", "CompareAndSwapUintptr":
				//func CompareAndSwapInt32(addr *int32, old, new int32) (swapped bool)
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, true}
				RecordSet_Basic = append(RecordSet_Basic, tmp)
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, true}
				RecordSet_Basic = append(RecordSet_Basic, tmp2)
			case "LoadInt32", "LoadInt64", "LoadPointer", "LoadUint32", "LoadUint64", "LoadUintptr":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, false, true}
				RecordSet_Basic = append(RecordSet_Basic, tmp)
			case "StoreInt32", "StoreInt64", "StorePointer", "StoreUint32", "StoreUint64", "StoreUintptr":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, true}
				RecordSet_Basic = append(RecordSet_Basic, tmp)
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, false}
				RecordSet_Basic = append(RecordSet_Basic, tmp2)
			case "SwapPointer", "SwapUint32", "SwapUint64", "SwapUintptr":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, true}
				RecordSet_Basic = append(RecordSet_Basic, tmp)
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, true, true}
				RecordSet_Basic = append(RecordSet_Basic, tmp2)
			}
		} else {
			switch fn {
			case "builtin delete": // map delete
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, false}
				RecordSet_Map = append(RecordSet_Map, tmp)
			case "builtin append":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, false}
				RecordSet_Array = append(RecordSet_Array, tmp)
				switch ins.Call.Args[1].Type().(type) {
				case *types.Basic:
					tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, false}
					RecordSet_Basic = append(RecordSet_Basic, tmp2)
				default:
					tmp2 := RecordField{instrs, ins.Call.Args[1], 0, false, false}
					RecordSet_Array = append(RecordSet_Array, tmp2)
				}
			case "(*os.File).Write", "(*os.File).Read":
				tmp2 := RecordField{instrs, ins.Call.Args[1], 0, fn == "(*os.File).Write", false}
				RecordSet_Array = append(RecordSet_Array, tmp2)
				fallthrough
			case "(*os.File).Close":
				tmp := RecordField{instrs, ins.Call.Args[0], 0, true, false}
				RecordSet_Basic = append(RecordSet_Basic, tmp)
			}
		}

	case *ssa.MapUpdate:
		tmp := RecordField{instrs, ins.Map, 0, true, false}
		RecordSet_Map = append(RecordSet_Map, tmp)
	case *ssa.Lookup:
		tmp := RecordField{instrs, ins.X, 0, false, false}
		RecordSet_Map = append(RecordSet_Map, tmp)
	default:
	}
}

func visitBasicBlock(fnname string, bb *ssa.BasicBlock) {
	for i := range bb.Instrs {
		analysisInstrs(&bb.Instrs[i])
	}
	for _, bb := range bb.Dominees() {
		visitBasicBlock(fnname, bb)
	}
}

func runFunc1(fn *ssa.Function) {
	fnname := fn.String()
	if _debug_print_ {
		println("runFunc1", fnname, fn)
	}
	visitBasicBlock(fnname, fn.Blocks[0])

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
					tmp := RecordField{&ref[i], freevar, 0, isWrite(ref[i], freevar), false}
					RecordSet_Basic = append(RecordSet_Basic, tmp)
				}
				if _, ok := elem.(*types.Array); ok {
					tmp := RecordField{&ref[i], freevar, 0, isWrite(ref[i], freevar), false}
					RecordSet_Array = append(RecordSet_Array, tmp)
				}
				if _, ok := elem.(*types.Struct); ok {
					tmp := RecordField{&ref[i], freevar, 0, isWrite(ref[i], freevar), false}
					RecordSet_Field = append(RecordSet_Field, tmp)
				}
				if _, ok := elem.(*types.Map); ok {
					tmp := RecordField{&ref[i], freevar, 0, isWrite(ref[i], freevar), false}
					RecordSet_Map = append(RecordSet_Map, tmp)
				}
			}
		}
	}
}

type ContextList []ssa.Instruction
type SyncMutexItem struct {
	value     ssa.Value
	gocall    *ssa.CallCommon
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
			if !seen[e.Callee] && e.Callee.Func.String() != "(*testing.T).Run" { // don't go into (*testing.T).Run, it's not parallel
				seen[e.Callee] = true
				from[e.Callee] = e
				que = append(que, e.Callee)
			}
		}

	}
	return
}

func hasTimeoutState(states []*ssa.SelectState) bool {
	for _, state := range states {
		if call, ok := state.Chan.(*ssa.Call); ok {
			if call.Value().Name() == "time.After" {
				return true
			}
		}
	}
	return false
}

func CleanDefer(x SyncMutexList) (ret SyncMutexList) {
	for i := range x {
		x[i].deferCall = false
	}
	return x
}

func GetSyncValue(instr *ssa.Instruction, dir int) (ret SyncMutexList) {
	switch ins := (*instr).(type) {
	case *ssa.Send:
		return SyncMutexList{SyncMutexItem{value: ins.Chan, deferCall: false, op: 1}} //1 for send
	case *ssa.Select:
		if !ins.Blocking || (!_IGNORE_TIMEOUT && hasTimeoutState(ins.States)) {
			return nil
		}
		ret = nil
		for _, state := range ins.States {
			ret = append(ret, SyncMutexItem{state.Chan, nil, int(state.Dir), false})
		}
	case *ssa.UnOp:
		if ins.Op == token.ARROW {
			return SyncMutexList{SyncMutexItem{ins.X, nil, 2, false}} //2 for recv
		}
	case *ssa.Call:
		sig := ins.Call.Value.String()
		switch sig {
		//case "(*sync.Mutex).Lock":
		//	return SyncMutexList{SyncMutexItem{value:ins.Call.Args[0],deferCall:false,op:10}} //10 for Lock
		//case "(*sync.Mutex).Unlock":
		//	return SyncMutexList{SyncMutexItem{value:ins.Call.Args[0],deferCall:false,op:11}} //11 for Unlock
		case "(*sync.WaitGroup).Done":
			return SyncMutexList{SyncMutexItem{ins.Call.Args[0], &ins.Call, 20, false}} //20 for Done
		case "(*sync.WaitGroup).Wait":
			return SyncMutexList{SyncMutexItem{ins.Call.Args[0], &ins.Call, 21, false}} //21 for Wait
		case "builtin close":
			if _, ischen := ins.Call.Args[0].Type().(*types.Chan); ischen {
				return SyncMutexList{SyncMutexItem{ins.Call.Args[0], &ins.Call, 3, false}} //21 for close chan
			}
		case "(*golang.org/x/sync/errgroup.Group).Wait":
			fn, ok := ins.Call.Value.(*ssa.Function)
			if dir == 1 && ok {
				return CleanDefer(GetBefore(fn.Blocks[0].Instrs[0]))
			}
			if dir == -1 && ok {
				return CleanDefer(GetAfter(fn.Blocks[0].Instrs[0]))
			}
			return nil
		default:
			return SyncMutexList{SyncMutexItem{nil, &ins.Call, 31, false}} //31 for normal call
		}
	case *ssa.Defer:
		sig := ins.Call.Value.String()
		switch sig {
		//case "(*sync.Mutex).Lock":
		//	panic("Call Lock in defer???")
		//case "(*sync.Mutex).Unlock":
		//	return SyncMutexList{SyncMutexItem{value:ins.Call.Args[0],deferCall:true,op:11}} //11 for Unlock
		case "(*sync.WaitGroup).Done":
			return SyncMutexList{SyncMutexItem{ins.Call.Args[0], &ins.Call, 20, true}} //20 for Done
		case "(*sync.WaitGroup).Wait":
			return SyncMutexList{SyncMutexItem{ins.Call.Args[0], &ins.Call, 21, true}} //21 for Wait
		case "builtin close":
			if _, ischen := ins.Call.Args[0].Type().(*types.Chan); ischen {
				return SyncMutexList{SyncMutexItem{ins.Call.Args[0], &ins.Call, 3, true}} //21 for close chan
			}
		case "(*golang.org/x/sync/errgroup.Group).Wait":
			fn, ok := ins.Call.Value.(*ssa.Function)
			if dir == 1 && ok {
				return CleanDefer(GetBefore(fn.Blocks[0].Instrs[0]))
			}
			if dir == -1 && ok {
				return CleanDefer(GetAfter(fn.Blocks[0].Instrs[0]))
			}
			return nil
		}
	case *ssa.Go:
		return SyncMutexList{SyncMutexItem{nil, &ins.Call, 30, false}} //30 for GoCall
	}
	return nil
}

func GetBefore(start ssa.Instruction) (sync SyncMutexList) {

	bb := start.Block()
	match := false

	for bb != nil {
		for i := len(bb.Instrs) - 1; i >= 0; i-- {
			if match {
				if tmp := GetSyncValue(&bb.Instrs[i], -1); tmp != nil {
					sync = append(sync, tmp...)
				}
			} else {
				match = reflect.DeepEqual(bb.Instrs[i], start)
			}
		}
		bb = bb.Idom()
	}
	return sync
}

func GetAfter(start ssa.Instruction) (sync SyncMutexList) {
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
				if tmp := GetSyncValue(&bb.Instrs[i], 1); tmp != nil {
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

func GetBeforeAfertSet(cl ContextList) [2]SyncMutexList {
	seenGo := false
	var BeforeSet, AfterSet SyncMutexList
	for j := len(cl) - 1; j >= 0; j-- {
		ins := cl[j]
		tmp := GetBefore(ins)
		if _, isGo := ins.(*ssa.Go); seenGo || isGo {
			seenGo = true
		}
		bf, af := FilterDefer(tmp)
		BeforeSet = append(BeforeSet, bf...)
		if !seenGo {
			AfterSet = append(AfterSet, af...)
			AfterSet = append(AfterSet, GetAfter(ins)...)
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
		addr := GetValue(&ins2.Addr)
		if addr2, ok2 := (*addr).(*ssa.Alloc); ok2 {
			return CheckReachableInstr(call, addr2)
		}
	}
	return false
}

func FindGoCallInAfterSet(ctx1 ContextList, afterSet SyncMutexList, instr2 *ssa.Instruction) bool {
	for _, call := range ctx1 {
		call2, isgo := call.(*ssa.Go)
		if isgo {
			for _, item := range afterSet {
				if item.gocall != nil && item.gocall.Pos() == (*call2).Common().Pos() && (isCopyToHeap(call, *instr2) || !CheckReachableInstr(call, *instr2)) {
					return true
				}
			}
		}
		call3, iscall := call.(*ssa.Call)
		if iscall {
			for _, item := range afterSet {
				if item.gocall != nil && item.gocall.Pos() == (*call3).Common().Pos() && (isCopyToHeap(call, *instr2) || !CheckReachableInstr(call, *instr2)) {
					return true
				}
			}
		}

	}
	return false
}

// item_B Happens before or sync with item_A
func HappensBeforeFromSet(beforeList SyncMutexList, afterList SyncMutexList) bool {
	//Find Chan
	for _, itemB := range beforeList {
		if itemB.op < 10 { // is a chan
			for _, itemA := range afterList {
				if itemA.op < 10 && itemA.op != itemB.op && FastSame(&itemA.value, &itemB.value) {
					return true
				}
			}
		}
	}

	// Find Wg
	for _, itemB := range beforeList {
		if itemB.op == 21 { // is a Wg.Wait
			for _, itemA := range afterList {
				if itemA.op == 20 && FastSame(&itemA.value, &itemB.value) { // is a Wg.Done
					return true
				}
			}
		}
	}

	return false
}

func PrintCtx(prog *ssa.Program, ctx ContextList) {
	for i, c := range ctx {
		println("\t#", i, (*prog.Fset).Position(c.Pos()).String(), c.String())
	}
}

type Result struct {
	field [2]RecordField
	ctx   [2]ContextList
}

var ResultSet = make(map[ssa.Value][]*Result)
var outputMux sync.Mutex

func ReportRaceWithCtx(prog *ssa.Program, field [2]RecordField, ctx [2]ContextList) {
	outputMux.Lock()
	defer outputMux.Unlock()

	val := GetValue(&field[0].value)
	ResultSet[*val] = append(ResultSet[*val], &Result{field: field, ctx: ctx})

	//println("Race Found:[ZZZ]")
	//println(toString(prog, field[0].ins), "Func:", (*field[0].ins).Parent().Name())
	//PrintCtx(prog, ctx[0])
	//println("============")
	//println(toString(prog, field[1].ins), "Func:", (*field[1].ins).Parent().Name())
	//PrintCtx(prog, ctx[1])
	//println("============")
}

func hasGoCall(ctx ContextList) bool {
	for i := range ctx {
		if _, ok := ctx[i].(*ssa.Go); ok {
			return true
		}
	}
	return false
}

func hasGoInLoop(ctx ContextList) bool {
	x := len(ctx)
	for i := 0; i < x-1; i++ {
		if _, ok := ctx[i].(*ssa.Go); ok && CheckReachableInstr(ctx[i], ctx[i]) {
			return true
		}
	}
	return false
}

func CheckHappendBefore(prog *ssa.Program, cg *callgraph.Graph, field [2]RecordField) {
	node1 := cg.Nodes[(*field[0].ins).Parent()]
	node2 := cg.Nodes[(*field[1].ins).Parent()]

	if node1 == nil || node2 == nil {
		return
	}

	startpoint := cg.Root
	if tmp := GetParent(node1.Func); tmp == GetParent(node2.Func) {
		startpoint = cg.Nodes[tmp]
	}

	ctx1 := append(GenContextPath(startpoint, node1), *field[0].ins)
	ctx2 := append(GenContextPath(startpoint, node2), *field[1].ins)

	set1 := GetBeforeAfertSet(ctx1)
	set2 := GetBeforeAfertSet(ctx2)

	if len(ctx1) == len(ctx2) {
		isSame := true
		for i := len(ctx1) - 2; i >= 0; i-- {
			if ctx1[i] != ctx2[i] {
				isSame = false
				break
			}
		}
		if isSame && !hasGoInLoop(ctx1) {
			return
		}
	}

	if !hasGoCall(ctx1) && !hasGoCall(ctx2) {
		return
	}

	if FindGoCallInAfterSet(ctx1, set2[1], field[1].ins) ||
		FindGoCallInAfterSet(ctx2, set1[1], field[0].ins) ||
		HappensBeforeFromSet(set1[0], set2[1]) ||
		HappensBeforeFromSet(set2[0], set1[1]) {
		// this ok, no nothing
	} else {
		ReportRaceWithCtx(prog, field, [2]ContextList{ctx1, ctx2})
	}
}

func main() {
	//println("Run for [ZZZ]:", os.Args[1])
	cfg := packages.Config{Mode: packages.LoadAllSyntax, Tests: _UseTestCase_}
	initial, err := packages.Load(&cfg, os.Args[1])
	if err != nil {
		log.Fatal(err)
	}
	if packages.PrintErrors(initial) > 0 {
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

	// Build SSA code for the whole program.
	prog.Build()
	RacePairsAnalyzerRun(prog, pkgs)

	for k, v := range ResultSet {
		println("Race Found:[ZZZ]", toStringValue(prog, &k))
		for _, c := range v {
			println(toString(prog, c.field[0].ins), "Func:", (*c.field[0].ins).Parent().Name())
			//PrintCtx(prog, ctx[0])
			//println("============")
			println(toString(prog, c.field[1].ins), "Func:", (*c.field[1].ins).Parent().Name())
			//PrintCtx(prog, ctx[1])
			println("============")
		}
	}

}
