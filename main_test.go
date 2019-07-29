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
		for i := range v {
			if v[i].x > v[i].y {
				v[i].x, v[i].y = v[i].y, v[i].x
			}
		}
		sort.Sort(v)
		(*sr)[k] = v
	}
}

func CmpResult(t *testing.T, runner *CheckerRunner, expected SimpleResult, zero int) {
	recv := make(SimpleResult)
	for k, v := range runner.ResultSet {
		key := runner.prog.Fset.Position(k.Pos()).Line
		var vu PairList
		for _, c := range v {
			tmp := PairInt{
				runner.prog.Fset.Position(c.field[0].ins.Pos()).Line + zero,
				runner.prog.Fset.Position(c.field[1].ins.Pos()).Line + zero,
			}
			vu = append(vu, tmp)
		}
		recv[key+zero] = vu
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

func RunTestCase(t *testing.T, myprog string, except SimpleResult, firstlineno int) {
	prog, pkgs := GetProgAndPkgs(t, myprog)
	r := &CheckerRunner{prog: prog, pkgs: pkgs}
	r.RacePairsAnalyzerRun()

	//r.PrintResult()

	CmpResult(t, r, except, firstlineno-1)

	if t.Failed() {
		r.PrintResult()
	}
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
	}, 1)

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
	RunTestCase(t, myprog, SimpleResult{}, 1)
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
		149: {{154, 156}}, // LineNo of Alloc, [ReadA, WriteA,...]
	}, 139)
}

func TestD(t *testing.T) {
	myprog := `package main
import "os"
func RaceBar(){
	a:=1
	if len(os.Args)==1 {
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
	RunTestCase(t, myprog, SimpleResult{}, 0)
}

func TestE(t *testing.T) {
	myprog := `package main
func ForLoop()  {
	for i:=1;i<=100;i++ {
		go func() {
			println(i)
		}()
	}
}
`
	RunTestCase(t, myprog, SimpleResult{
		190: {{190, 192}}, // LineNo of Alloc, [ReadA, WriteA,...]
	}, 188)
}

func TestF(t *testing.T) {
	myprog := `package main
func ForLoop()  {
	a := 1
	go func() {
		a = 2
	}()
	println(a)
}
`
	RunTestCase(t, myprog, SimpleResult{
		206: {{208, 210}}, // LineNo of Alloc, [ReadA, WriteA,...]
	}, 204)
}

func TestG(t *testing.T) {
	myprog := `package main
import "time"
func main()  {
	ch := make(chan int)
	a:=1
	go func() {
		a=2
		ch <- 1
	}()
	select {
	case <-ch:
		println(a)
	case <-time.After(time.Microsecond):
		return
	}
	a=3
	println(a)
}
`
	RunTestCase(t, myprog, SimpleResult{}, 0)
}

func TestH(t *testing.T) {
	myprog := `package main
import "sync"

type Foo struct {
	sync.RWMutex
	data int
}

func main() {
	foo := &Foo{}
	go func() {
		foo.Lock()
		defer foo.Unlock()
		foo.data = 1
	}()
	foo.RLock()
	println(foo.data)
	foo.RUnlock()
}
`
	RunTestCase(t, myprog, SimpleResult{}, 0)
}

func TestH2(t *testing.T) {
	myprog := `package main
import "sync"

type Foo struct {
	mu sync.RWMutex
	data int
}

func main() {
	foo := &Foo{}
	go func() {
		foo.mu.Lock()
		defer foo.mu.Unlock()
		foo.data = 1
	}()
	foo.mu.RLock()
	println(foo.data)
	foo.mu.RUnlock()
}
`
	RunTestCase(t, myprog, SimpleResult{}, 0)
}

func TestArrayRange(t *testing.T) {
	myprog := `package main
func main(){
	var badCases =[]int{1,2,3,4,5,6,7,8,9}
	for k := range badCases {
		go func() {
			println(k, badCases[k])
		}()
	}

	for _, v := range badCases {
		go func() {
			println(v)
		}()
	}

	for k, v := range badCases {
		go func() {
			println(k, v)
		}()
	}
}
`
	RunTestCase(t, myprog, SimpleResult{
		297: {{297, 299}},
		303: {{303, 305}},
		309: {{309, 311}},
	}, 294)

}
