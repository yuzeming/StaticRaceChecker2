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

func TestH3(t *testing.T) {
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
		foo.mu.Unlock()
		foo.data = 1
	}()
	foo.mu.RLock()
	println(foo.data)
	foo.mu.RUnlock()
}
`
	RunTestCase(t, myprog, SimpleResult{
		303: {{307, 310}},
	}, 294)
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
	
	for k := range badCases {
		k2:=k
		go func() {
			println(k2, badCases[k2])
		}()
	}
	
	for _, v := range badCases {
		v2 := v
		go func() {
			println(v2)
		}()
	}
	
	for k, v := range badCases {
		k2, v2 := k ,v
		go func() {
			println(k2, v2)
		}()
	}
}
`
	RunTestCase(t, myprog, SimpleResult{
		297: {{297, 299}, {297, 299}},
		303: {{303, 305}},
		309: {{309, 311}},
	}, 294)

}

func TestWaitGroup(t *testing.T) {
	myprog := `package main
import "sync"
func main(){
	a := 1
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		a = 2
	}()
	wg.Wait()
	println(a)
}
`
	RunTestCase(t, myprog, SimpleResult{}, 0)

}

func TestWaitGroup2(t *testing.T) {
	myprog := `package main
import (
	"sync"
	"fmt"
)

func main(){
	wg := sync.WaitGroup{}
	for i := 17; i <= 21; i++ { // write
		a := i
		wg.Add(1)
		go func() {
			defer wg.Done()
			apiVersion := fmt.Sprintf("v1.%d", i) // read
			println(apiVersion)
			println(a)
		}()
	}
	wg.Wait()
}
`
	RunTestCase(t, myprog, SimpleResult{
		399: {{399, 404}},
	}, 391)

}

func TestFile(t *testing.T) {
	myprog := `package main
import "os"
func RaceFileClose()  {
	f, _ := os.OpenFile("notes.txt", os.O_RDWR|os.O_CREATE, 0755)
	go func() {
		f.Close()
	}()

	bytes := make([]byte, 10)
	n,_ := f.Read(bytes)
	println(n,bytes)
}
`
	RunTestCase(t, myprog, SimpleResult{
		418: {{420, 424}},
	}, 415)
}

func TestRaceRutrunValue(t *testing.T) {
	myprog := `package main
func aaaaa() (ret int,
		retstr string){
	ret = 2
	retstr ="aaaaa"
	go func() {
		ret = 1
		retstr = "bbbbb"
	}()
	//println(ret,retstr)
	return ret,retstr
}
`
	RunTestCase(t, myprog, SimpleResult{
		435: {{440, 444}, {440, 444}}, //duplicate result
		436: {{441, 444}, {441, 444}},
	}, 434)

}

func TestRaceHttpMux(t *testing.T) {
	myprog := `package main

import (
	"fmt"
	"net/http"
	"net/http/httptest"
)

func main() {
	visitcount := 0
	backendHandler := http.NewServeMux()
	backendHandler.HandleFunc("/", func(w http.ResponseWriter, req *http.Request) {
		visitcount += 1
		fmt.Fprintf(w, "Welcome to the home page! %d\n", visitcount)
	})

	backendServer := httptest.NewUnstartedServer(backendHandler)
	backendServer.Start()

	println(visitcount)
}

`
	RunTestCase(t, myprog, SimpleResult{
		464: {{467, 474}}, //duplicate result
	}, 455)

}

func TestRaceAtomic(t *testing.T) {
	myprog := `package main

import (
	"sync/atomic"
	"time"
)
func main() {
	const waiters = 10
	var waited int32
	for i := 0; i < waiters; i++ {
		go func() {
			atomic.AddInt32(&waited, 1)
		}()
	}

	time.Sleep(100 * time.Millisecond)
	if waited != waiters {
		println("Multiple waiters doesn't work, only %v finished", waited)
	}
}

`
	RunTestCase(t, myprog, SimpleResult{
		493: {{496, 501}, {496, 502}}, //duplicate result
	}, 485)

}

func TestRaceAtomic2(t *testing.T) {
	myprog := `package main

import (
	"sync/atomic"
	"time"
)
func RaceAtomic2() {
	const waiters = 10
	var waited int32
	for i := 0; i < waiters; i++ {
		go func() {
			atomic.AddInt32(&waited, 1)
		}()
	}

	time.Sleep(100 * time.Millisecond)
	waited2 := atomic.LoadInt32(&waited)
	if waited2 != waiters {
		println("Multiple waiters doesn't work, only %v finished", waited2)
	}
}

`
	RunTestCase(t, myprog, SimpleResult{}, 0)
}

func TestRaceArrayAppend(t *testing.T) {
	myprog := `package main
import "sync"
func main() {
	var got []int
	var wg sync.WaitGroup
	for i := 1; i <= 10; i++ {
		wg.Add(1)
		go func(start int) {
			for j := start + 1; j <= start+100; j++ {
				got = append(got, j)
			}
		}(i * 1000)
	}
	println(len(got))
	for i := range got {
		println(got[i])
	}
}

`
	RunTestCase(t, myprog, SimpleResult{
		548: {{554, 560}, {554, 558}},
	}, 545)
}

func TestRaceArrayAppend2(t *testing.T) {
	myprog := `package main
func RaceAppend() {
	a := []int{1,2,3,4,5}

	go func() {
		a = append(a,100)
	}()
	a[0] =1

	for i:=range a {
		println(a[i])
	}
}
`
	RunTestCase(t, myprog, SimpleResult{
		573: {{576, 578}, {576, 581}},
	}, 571)
}

func TestRaceerrGroup(t *testing.T) {
	myprog := `package main
import "golang.org/x/sync/errgroup" 
type Bar struct {
	lst []int
}
func main() {
	bar := Bar{}
	var g errgroup.Group
	g.Go(func() error {
		bar.lst=append(bar.lst, 1)
		return nil
	})
	a := []int{1,2,3,4,5}
	a = append(a,bar.lst...)
	// Wait for all HTTP fetches to complete.
	if err := g.Wait(); err == nil {
		println("Successfully fetched all URLs.")
	}
}
`
	RunTestCase(t, myprog, SimpleResult{
		597: {{604, 600}, {604, 600}},
	}, 591)
}

func TestAppendMutex(t *testing.T) {
	myprog := `package main

import "sync"

func main() {
	var a []int
	var mu sync.Mutex
	ch := make(chan int, 1)
	go func() {
		for i := 1; i <= 1000; i++ {
			mu.Lock()
			a = append(a, i)
			mu.Unlock()
		}
		ch <- 1
	}()

	for i := 1; i <= 1000; i++ {
		mu.Lock()
		a = append(a, -i)
		mu.Unlock()
	}

	<-ch
	println(len(a))
}

`
	RunTestCase(t, myprog, SimpleResult{}, 0)
}

func TestSelectChan(t *testing.T) {
	myprog := `package main
func main() {
	a := 1
	ch := make(chan int)
	go func() {
		a = 2
		ch <- 1
	}()
	select {
	case <-ch:
		println(a)
	default:
		//println(a + 1)
		return
	}
	println(a)

}
`
	RunTestCase(t, myprog, SimpleResult{}, 0)
}

func TestFPfromloop3(t *testing.T) {
	myprog := `package main
func main() {
	a := 1
	go func(){
		a=2
		func() {
			a=3
		}()
		println(a)
	}()
}
`
	RunTestCase(t, myprog, SimpleResult{}, 0)
}
