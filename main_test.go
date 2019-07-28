package main

import (
	"fmt"
	"golang.org/x/tools/go/loader"
	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/ssa/ssautil"
	"sort"
	"testing"
)

func GetProgAndPkgs(t *testing.T, myprog string) (prog *ssa.Program, pkgs []*ssa.Package) {
	var conf loader.Config
	file, err := conf.ParseFile("myprog.go", myprog)
	if err != nil {
		t.Fatalf(fmt.Sprintf("%v", err))
	}

	conf.CreateFromFiles("main", file)

	iprog, err := conf.Load()
	if err != nil {
		t.Fatalf(fmt.Sprintf("%v", err))
	}

	pkgs = make([]*ssa.Package, 1)
	prog = ssautil.CreateProgram(iprog, 0)
	pkgs[0] = prog.Package(iprog.Created[0].Pkg)

	prog.Build()
	return prog, pkgs
}

type SimpleResult map[int]PairList
type PairList []PairInt
type PairInt struct {
	x, y int
}

func (s PairList) Len() int           { return len(s) }
func (s PairList) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }
func (s PairList) Less(i, j int) bool { return s[i].x < s[j].x || s[i].x == s[j].x && s[i].y < s[j].y }

func SortPairMap(sr *SimpleResult) {
	for k, v := range *sr {
		for _, tmp := range v {
			if tmp.x > tmp.y {
				tmp.x, tmp.y = tmp.y, tmp.x
			}
		}
		sort.Sort(v)
		(*sr)[k] = v
	}
}

func CmpResult(t *testing.T, runner *CheckerRunner, expected SimpleResult) {
	recv := make(SimpleResult)
	for k, v := range runner.ResultSet {
		key := runner.prog.Fset.Position(k.Pos()).Line
		var vu PairList
		for _, c := range v {
			tmp := PairInt{
				runner.prog.Fset.Position(c.field[0].ins.Pos()).Line,
				runner.prog.Fset.Position(c.field[1].ins.Pos()).Line,
			}
			vu = append(vu, tmp)
		}
		recv[key] = vu
	}
	SortPairMap(&recv)
	SortPairMap(&expected)

	for k, v := range recv {
		if len(v) != len(expected[k]) {
			t.Errorf("diff len %v:%v - %v", k, len(v), len(expected[k]))
		} else {
			for i := range v {
				if v[i] != expected[k][i] {
					t.Errorf("diff v %v %v", v[i], expected[k][i])
				}
			}
		}
	}
	for k := range expected {
		if recv[k] == nil {
			t.Errorf("not found key %v: %v", k, expected[k])
		}
	}
}

func RunTestCase(t *testing.T, myprog string, except SimpleResult) {
	prog, pkgs := GetProgAndPkgs(t, myprog)
	r := &CheckerRunner{prog: prog, pkgs: pkgs}
	r.RacePairsAnalyzerRun()

	r.PrintResult()

	CmpResult(t, r, except)
}

func TestA(t *testing.T) {
	myprog := `package main
	func Foo(){
	a:=1
	go func() {
		a = 2
	}()
	go func() {
		a = 3
	}()
	println(a)
}
`
	RunTestCase(t, myprog, SimpleResult{
		3: {{5, 8}, {5, 10}, {8, 10}}, // LineNo of Alloc, [ReadA, WriteA,...]
	})
}

func TestB(t *testing.T) {
	myprog := `package main
import "os"
func RaceBar(){
	a:=1
	if len(os.Args) == 1 {
		go func() {
			a = 2
			print(a)
		}()
	} else {
		a = 3
		print(a)
	}
}
`
	RunTestCase(t, myprog, SimpleResult{})
}

func TestC(t *testing.T) {
	myprog := `package main
func CallLater(fn func()){
	fn()
}

func GoLater(fn func()){
	go fn()
}

func RaceFoo(){
	a:=1
	CallLater( func() {
		a++
	})
	GoLater(func() {
		a--
	})
	println(a)
}

func main() {
	RaceFoo()
}
`
	RunTestCase(t, myprog, SimpleResult{
		11: {{16, 18}}, // LineNo of Alloc, [ReadA, WriteA,...]
	})
}
