package main

import (
	"fmt"
	"go/token"
	"go/types"
	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/analysis/passes/buildssa"
	"golang.org/x/tools/go/analysis/singlechecker"
	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/pointer"
	"golang.org/x/tools/go/ssa"
	"reflect"
	"sort"
)

type RecordField struct {
	ins     *ssa.Instruction
	value   ssa.Value
	Field   int
	isAddr  bool
	isWrite bool
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

var PairSet_Field [][2]RecordField
var PairSet_Array [][2]RecordField
var PairSet_Basic [][2]RecordField

var RacePairsAnalyzer = &analysis.Analyzer{
	Name:     "RacePairsAnalyzer",
	Doc:      "....",
	Run:      RacePairsAnalyzerRun,
	Requires: []*analysis.Analyzer{buildssa.Analyzer},
}

func RacePairsAnalyzerRun(pass *analysis.Pass) (interface{}, error) {
	println("Pass run")
	ssainput := pass.ResultOf[buildssa.Analyzer].(*buildssa.SSA)

	for _, fn := range ssainput.SrcFuncs {
		runFunc1(pass, fn)
	}

	println("Field")
	for i, r := range RecordSet_Field {
		println(i, toString(pass, r.ins))
	}

	println("Array")
	for i, r := range RecordSet_Array {
		println(i, toString(pass, r.ins), (*r.ins).String(), r.value.String(), r.isWrite)
	}

	println("Basic")
	for i, r := range RecordSet_Basic {
		println(i, toString(pass, r.ins), (*r.ins).String(), r.value.String(), r.isWrite)
	}

	PairSet_Field = GenPair(RecordSet_Field)
	PairSet_Array = GenPair(RecordSet_Array)
	PairSet_Basic = GenPair(RecordSet_Basic)

	println("Field Pair")
	for i, r := range PairSet_Field {
		println(i, toString(pass, r[0].ins), "\n", toString(pass, r[1].ins))
	}

	println("Array Pair")
	for i, r := range PairSet_Array {
		println(i, toString(pass, r[0].ins), "\n", toString(pass, r[1].ins))
	}

	println("Basic Pair")
	for i, r := range PairSet_Basic {
		println(i, toString(pass, r[0].ins), "\n", toString(pass, r[1].ins))
	}

	var testmain = ssainput.Pkg.Prog.CreateTestMainPackage(ssainput.Pkg)
	var pkglist = []*ssa.Package{ssainput.Pkg}
	if testmain != nil {
		pkglist = append(pkglist, testmain)
	}

	config := &pointer.Config{
		Mains:          pkglist,
		BuildCallGraph: true,
	}

	result, err := pointer.Analyze(config)

	if err != nil {
		panic(err) // internal error in pointer analysis
	}

	var edges []string
	_ = callgraph.GraphVisitEdges(result.CallGraph, func(edge *callgraph.Edge) error {
		caller := edge.Caller.Func
		edges = append(edges, fmt.Sprint(caller, " --> ", edge.Callee.Func))
		return nil
	})

	// Print the edges in sorted order.
	sort.Strings(edges)
	for _, edge := range edges {
		fmt.Println(edge)
	}

	fmt.Println()

	println("Field Pair")
	Reachable_PairSet_Field := PairSet_Field[:0]
	for _, r := range PairSet_Field {
		if CheckReachablePair(result.CallGraph, r) {
			Reachable_PairSet_Field = append(Reachable_PairSet_Field, r)
		}
	}

	println("Array Pair")
	ReachablePairSetArray := PairSet_Array[:0]
	for _, r := range PairSet_Array {
		if CheckReachablePair(result.CallGraph, r) {
			ReachablePairSetArray = append(ReachablePairSetArray, r)
		}
	}

	println("Basic Pair")
	ReachablePairsetBasic := PairSet_Basic[:0]
	for _, r := range PairSet_Basic {
		if CheckReachablePair(result.CallGraph, r) {
			ReachablePairsetBasic = append(ReachablePairsetBasic, r)
		}
	}

	println("Reachable Field Pair")
	for i, r := range Reachable_PairSet_Field {
		println(i, toString(pass, r[0].ins), "\n", toString(pass, r[1].ins))
	}

	println("Reachable Array Pair")
	for i, r := range ReachablePairSetArray {
		println(i, toString(pass, r[0].ins), "\n", toString(pass, r[1].ins))
	}

	println("Reachable Basic Pair")
	for i, r := range ReachablePairsetBasic {
		println(i, toString(pass, r[0].ins), "\n", toString(pass, r[1].ins))
	}

	config2 := &pointer.Config{
		Mains:          pkglist,
		BuildCallGraph: true,
	}
	for _, r := range Reachable_PairSet_Field {
		if r[0].isAddr && r[1].isAddr {
			config2.AddQuery(r[0].value)
			config2.AddQuery(r[1].value)
		}
	}

	for _, r := range ReachablePairSetArray {
		if r[0].isAddr && r[1].isAddr {
			config2.AddQuery(r[0].value)
			config2.AddQuery(r[1].value)
		}
	}
	for _, r := range ReachablePairsetBasic {
		if r[0].isAddr && r[1].isAddr {
			config2.AddQuery(r[0].value)
			config2.AddQuery(r[1].value)
		}
	}

	result2, err2 := pointer.Analyze(config2)

	if err2 != nil {
		panic(err) // internal error in pointer analysis
	}

	println("Alising Field Pair")
	AlisingPairsetField := Reachable_PairSet_Field[:0]
	for i, r := range Reachable_PairSet_Field {
		if r[0].isAddr && r[1].isAddr && result2.Queries[r[0].value].PointsTo().Intersects(result2.Queries[r[1].value].PointsTo()) {
			println(i, toString(pass, r[0].ins), "\n -", toString(pass, r[1].ins))
			AlisingPairsetField = append(AlisingPairsetField, r)
		} else {
			println("Remove Pair", i)
		}
	}

	println("Alising Array Pair")
	AlisingPairsetArray := ReachablePairSetArray[:0]
	for i, r := range ReachablePairSetArray {
		if r[0].isAddr && r[1].isAddr && result2.Queries[r[0].value].PointsTo().Intersects(result2.Queries[r[1].value].PointsTo()) {
			println(i, toString(pass, r[0].ins), "\n - ", toString(pass, r[1].ins))
			AlisingPairsetArray = append(AlisingPairsetArray, r)
		} else {
			println("Remove Pair", i)
		}
	}

	println("Alising Basic Pair")
	AlisingPairsetBasic := ReachablePairsetBasic[:0]
	for i, r := range ReachablePairsetBasic {
		if r[0].isAddr && r[1].isAddr && result2.Queries[r[0].value].PointsTo().Intersects(result2.Queries[r[1].value].PointsTo()) {
			println(i, toString(pass, r[0].ins), "\n - ", toString(pass, r[1].ins))
			AlisingPairsetBasic = append(AlisingPairsetBasic, r)
		} else {
			println("Remove Pair", i)
		}
	}

	for _, r := range AlisingPairsetField {
		CheckHappendBefore(pass, result.CallGraph, r)
	}

	for _, r := range AlisingPairsetArray {
		CheckHappendBefore(pass, result.CallGraph, r)
	}
	for _, r := range AlisingPairsetBasic {
		CheckHappendBefore(pass, result.CallGraph, r)
	}
	return nil, nil
}

func GenPair(RecordSet []RecordField) (ret [][2]RecordField) {
	for i := range RecordSet {
		if pi := RecordSet[i]; pi.isWrite {
			for j := range RecordSet {
				if pj := RecordSet[j]; !pj.isWrite || i < j {
					if reflect.DeepEqual(pi.value.Type(), pj.value.Type()) && pi.Field == pj.Field && (*pi.ins).Block() != (*pj.ins).Block() {
						ret = append(ret, [2]RecordField{pi, pj})
					}
				}
			}
		}
	}
	return ret
}

func CheckReachablePair(cg *callgraph.Graph, field [2]RecordField) bool {
	node1 := cg.Nodes[(*field[0].ins).Parent()]
	node2 := cg.Nodes[(*field[1].ins).Parent()]

	if node1 == nil || node2 == nil {
		return false
	}

	startpoint := cg.Root
	if _, ok := field[0].value.(*ssa.Alloc); ok {
		startpoint = cg.Nodes[(*field[0].ins).Parent()]
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

func toString(pass *analysis.Pass, op *ssa.Instruction) string {
	return (*pass.Fset).Position((*op).Pos()).String()
}

func analysisInstrs(instrs *ssa.Instruction) {
	switch ins := (*instrs).(type) {
	case *ssa.Field:
		ref := *ins.Referrers()
		for i := range ref {
			tmp := RecordField{&ref[i], ins.X, ins.Field, false, isWrite(ref[i], ins)}
			RecordSet_Field = append(RecordSet_Field, tmp)
		}
	case *ssa.FieldAddr:
		ref := *ins.Referrers()
		for i := range ref {
			tmp := RecordField{&ref[i], ins.X, ins.Field, true, isWrite(ref[i], ins)}
			RecordSet_Field = append(RecordSet_Field, tmp)
		}
	case *ssa.Index:
		ref := *ins.Referrers()
		for i := range ref {
			tmp := RecordField{&ref[i], ins.X, 0, false, isWrite(ref[i], ins)}
			RecordSet_Array = append(RecordSet_Array, tmp)
		}
	case *ssa.IndexAddr:
		ref := *ins.Referrers()
		for i := range ref {
			tmp := RecordField{&ref[i], ins.X, 0, true, isWrite(ref[i], ins)}
			RecordSet_Array = append(RecordSet_Array, tmp)
		}
	case *ssa.Alloc:
		if p, ok := ins.Type().Underlying().(*types.Pointer).Elem().(*types.Basic); ok && ins.Heap {
			println(p.Name())
			ref := *ins.Referrers()
			for i := range ref {
				tmp := RecordField{&ref[i], ins, 0, true, isWrite(ref[i], ins)}
				RecordSet_Basic = append(RecordSet_Basic, tmp)
			}
		}
	case *ssa.MakeClosure:
		freevar := ins.Fn.(*ssa.Function).FreeVars
		for i := range ins.Bindings {
			AddFreeVarMap(freevar[i], &ins.Bindings[i])
		}
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

func runFunc1(pass *analysis.Pass, fn *ssa.Function) {
	fnname := fn.String()
	println(fnname)
	visitBasicBlock(fnname, fn.Blocks[0])

	for _, freevar := range fn.FreeVars {
		ref := *freevar.Referrers()
		for i := range ref {
			switch ref[i].(type) {
			case *ssa.Field:
			case *ssa.FieldAddr:
			case *ssa.Index:
			case *ssa.IndexAddr:

			default:
				tmp := RecordField{&ref[i], freevar, 0, true, isWrite(ref[i], freevar)}
				RecordSet_Basic = append(RecordSet_Basic, tmp)
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

func GenContextPath(cg *callgraph.Graph, end *callgraph.Node) (ret []ContextList) {
	seen := make(map[*callgraph.Node]bool)
	var dfs func(node *callgraph.Node)
	var dfs2 func(deep int, node *callgraph.Node)
	dfs = func(node *callgraph.Node) {
		if seen[node] {
			return
		}
		seen[node] = true
		for _, p := range node.In {
			dfs(p.Caller)
		}
	}
	dfs(end)

	var _MAX_DEEP_ = 30
	var _MAX_ITEM_ = 10

	var cl = make(ContextList, _MAX_DEEP_)
	dfs2 = func(deep int, n *callgraph.Node) {
		if !seen[n] || deep >= _MAX_DEEP_ {
			return
		}
		if n == end {
			var cl2 = make(ContextList, deep-1)
			for i := 1; i < deep; i++ {
				cl2[i-1] = cl[i]
			}
			ret = append(ret, cl2)
			if len(ret) >= _MAX_ITEM_ {
				_MAX_DEEP_ = 0
			}
			return
		}
		seen[n] = false
		for _, p := range n.Out {
			switch x := p.Site.(type) {
			case *ssa.Go:
				cl[deep] = x
			case *ssa.Call:
				cl[deep] = x
			case *ssa.Defer:

			}

			dfs2(deep+1, p.Callee)
		}
		seen[n] = true
	}
	dfs2(0, cg.Root)
	return ret
}

func GetSyncValue(instr *ssa.Instruction) (ret SyncMutexList) {
	switch ins := (*instr).(type) {
	case *ssa.Send:
		return SyncMutexList{SyncMutexItem{value: ins.Chan, deferCall: false, op: 1}} //1 for send
	case *ssa.Select:
		if !ins.Blocking {
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
				if tmp := GetSyncValue(&bb.Instrs[i]); tmp != nil {
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
				if tmp := GetSyncValue(&bb.Instrs[i]); tmp != nil {
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

func FindGoCallInAfterSet(ctx1 ContextList, afterSet SyncMutexList, instr2 *ssa.Instruction) bool {
	for _, call := range ctx1 {
		call2, isgo := call.(*ssa.Go)
		if !isgo {
			continue
		}
		for _, item := range afterSet {
			if item.gocall != nil && item.gocall == (*call2).Common() && !CheckReachableInstr(call, *instr2) {
				return true
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

func PrintCtx(pass *analysis.Pass, ctx ContextList) {
	for i, c := range ctx {
		println("\t#", i, (*pass.Fset).Position(c.Pos()).String(), c.String())
	}
}

func ReportRaceWithCtx(pass *analysis.Pass, field [2]RecordField, ctx [2]ContextList) {
	println("Race Found:[ZZZ]")
	println(toString(pass, field[0].ins))
	PrintCtx(pass, ctx[0])
	println("============")
	println(toString(pass, field[1].ins))
	PrintCtx(pass, ctx[1])
	println("============")
}

func CheckHappendBefore(pass *analysis.Pass, cg *callgraph.Graph, field [2]RecordField) {
	node1 := cg.Nodes[(*field[0].ins).Parent()]
	node2 := cg.Nodes[(*field[1].ins).Parent()]

	if node1 == nil || node2 == nil {
		return
	}

	contextlist1 := GenContextPath(cg, node1)
	for i := range contextlist1 {
		contextlist1[i] = append(contextlist1[i], *field[0].ins)
	}

	contextlist2 := GenContextPath(cg, node2)
	for i := range contextlist2 {
		contextlist2[i] = append(contextlist2[i], *field[1].ins)
	}

	var BASet1, BASet2 [][2]SyncMutexList

	for i := range contextlist1 {
		BASet1 = append(BASet1, GetBeforeAfertSet(contextlist1[i]))
	}

	for i := range contextlist2 {
		BASet2 = append(BASet2, GetBeforeAfertSet(contextlist2[i]))
	}

	for i, set1 := range BASet1 {
		ctx1 := contextlist1[i]
		for j, set2 := range BASet2 {
			ctx2 := contextlist2[j]

			flag := 0
			//Find Go1 in Afterset2
			if FindGoCallInAfterSet(ctx1, set2[1], field[1].ins) {
				flag = 1
				continue
			}
			//Find Go2 in Afterset1
			if FindGoCallInAfterSet(ctx2, set1[1], field[0].ins) {
				flag = -1
				continue
			}

			if HappensBeforeFromSet(set1[0], set2[1]) {
				flag = 1
				continue
			}

			if HappensBeforeFromSet(set2[0], set1[1]) {
				flag = -1
				continue
			}

			if flag == 0 {
				ReportRaceWithCtx(pass, field, [2]ContextList{ctx1, ctx2})
				return
			}
		}
	}
}

func main() {
	singlechecker.Main(RacePairsAnalyzer)
}
