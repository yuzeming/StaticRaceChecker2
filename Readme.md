This is a static race detecter designed for data race between an anonymous function and its outside function especially sharing data by closure.

This project contributed some commits for several famous open-source softwares.

[cockroach](https://github.com/cockroachdb/cockroach)
* https://github.com/cockroachdb/cockroach/pull/39282

[etcd](https://github.com/etcd-io/etcd)
* https://github.com/etcd-io/etcd/pull/10995
* https://github.com/etcd-io/etcd/pull/10994
* https://github.com/etcd-io/etcd/pull/10993
* https://github.com/etcd-io/etcd/pull/10904
* https://github.com/etcd-io/etcd/pull/10900

[grpc-go](https://github.com/grpc/grpc-go)
* https://github.com/grpc/grpc-go/pull/2935

# Technical Detail about Go SSA

## Alloc, FreeVar and MakeClosure

The Alloc instruction reserves space for a variable of the given type, zero-initializes it, and yields its address. Compiler decided where to reserves space, when this variable is shared between goroutines, it must be alloc in heap.

Declaration of this anonymous function contains `FreeVar`, whose free variables are lexically captured in a closure from its parent function. 

The MakeClosure instruction yields a closure value whose code is Fn and whose free variables' values are supplied by Bindings. Since the MakeClouse is call only once, we can create a map from `FreeVar` to `Alloc` to determine if two values (FreeVar+FreeVar or Value+FreeVar or Value+Value) are pointed to the same variable. 

## Binding Map
```go
func Foo(){
  a:=1 // a
  go func() { // FreeVar Foo$1:a, Binding Foo$1:a -> a
     a = 2 
  }()
  go func() { // FreeVar Foo$2:a, Binding Foo$2:a -> a
     a = 3  
  }()
  println(a) // a
}
```

Figure #1: Binding Map

we can find Foo$1:a, Foo$2:a and a are pointed to the same thing by lookuping binding map.

### Step 1: Read/Write Operation Collection:
My program goes through all functions and methods to collection write/read record about heap allocated `Alloc` and `FreeVar`, include: SSA instruction location in program ,SSA Value(Alloc or FreeVar), FieldID (if access struct fields), isAtomic.
We categorize all record into four kinds: Read/Write about Basic Type, Struct Field,  Array/Slice and Map. 

### Step #2: Collection all MakeClouse to create binding map 

### Step #3: Generation race opreation pair
two opreations (A,B) in the same category may race if:
1. One of A,B is in a anonymous function, and
2. A or B is not atomic, and
3. A or B is write operation, and
4. A and B are not in the same basic block, and
5. A and B are pointed to the same place determined by binding map, and
6. A and B have the same FieldID ( for Struct Field )

### Step #4: Getting Call Graph from package pointer
it address the problem that some functions take anonymous function as a parameter and call it or create a goroutine to call it inside. I also add test function as entry to reach as much as possible functions.

#### Known Limitation
pointer analysis can’t deal with dead function. So all dead functions miss in the call graph. For a workaround, I copy missed function and call-edge from another call graph produced by package cha which is faster and can deal with dead function but less accurate

```go
func Call(fn func()){
  fn()
}

func Go(fn func()){
  go fn()
}

func RaceFoo(){
  a:=1  // ALLOC WRITE#1
  Call( func() { // RaceFoo$1
     a++ // WRITE #2
  })
  println(a) // READ #3
  Go(func() { // RaceFoo$2
     a-- // WRITE #4
  })
  println(a) // READ #5
}

func main() {
  RaceFoo() // There must a main function or Test function to call it.
}
```
Figure #2

### Step #5: Reachable Check
two operations (A and B) could be race if and only if they can be executed at same time. My approach is not right: if there are two call path (path_A and path_B) from named function to operations A and B, and at least one `Go` go in path_A or path_B. For convenience, I add operation as last item.

In Figure #2, for Write #2, Write #4 and READ #5, their paths should be
* Write#2: [Root] =Call=> RaceFoo() =Call=> Call() =Call=> RaceFoo$1 => Write#2
* Write#4: [Root] =Call=> RaceFoo() =Call=> Go() =Go=> RaceFoo$1 =>Write#4
* Read #5: [Root] =Call=> RaceFoo() => Read#5

For Pair Write#2 and Read #5, there is no `Go` in both paths, so it can’t pass reachable check

For Pair Write#4 and Read #5, there is a `Go` in Write#4’s path, so it pass reachable check

For Pair Write#2 and Write #4, there is a `Go` in Write#4’s path, so it pass reachable check but this pair will be removed in the Step 7.

#### Known Limitation
My approach is not right in some case:

```go
func RaceBar(){
  a:=1
  if a==1 {
     go func() {
        a = 2 #WRITE #1
        print(a)
     }()
  } else {
     a = 3 #WRITE #2
     print(a)
  }
}
```

Figure #3: Pair(Write #1, Write #2) passes reachable checker but they can’t be reach at same time.

* Write#1: [Root] =Call=> RaceBar() =Go=> RaceBar$1 => Write#1
* Write#2: [Root] =Call=> RaceBar() => Write#2

#### Todo: Add a new rule:
let `lastOp` be the last instruction in path that was executed without switch goroutine
Write#1: [Root] =Call=> RaceBar() =Go=> RaceBar$1 => Write#1
lastOp_A of Write#1: `GoCall`
Write#2: [Root] =Call=> RaceBar()=> Write#2
lastOp_B of Write#2: Write#2

lastOp_A must reachable to lastOp_B or lastOp_B must reachable to lastOp_A

##Step #6: Collection synchronization operations set from Path_A, Path_B
According to The Go Memory Model, we consider
* Goroutine creation
* Channel send, recv, close
* Locks ( Mutex, RWMutex )
* waitgroup ( Done, Wait )

Normal call are also included in set, see Step #7 for reason.

#### Definition: Must Happens Before Set of a Path (BeforeSet):
For a instruction (target instruction) , Must Happens Before Set contains all synchronization operations that must happen before it. In the basic block this instruction belong to, we include all synchronization operations which is before this instruction. Then we go to this basic block’s parent in dominator tree, include all synchronization operations in this block, until we visit the top basic block of this function.

Then we consider call path from most inner layer to outer layer, for a call edge, we set callsite instruction as the target instruction and collection Must Happens Before Set in caller function, until visit the root node in call graph.

#### Definition: Must Happens After Set of a Path (AfterSet):
For a instruction (target instruction), Must Happens After Set contains all synchronization operations that must happen after it. It’s similar with Must Happens Before Set but we collection all synchronization operations after this instruction in it’s basic block and visit it’s parent in post-dominator tree

Then we consider call path from most inner layer to outer layer, for a call edge, we set callsite instruction as the target instruction and collection Must Happens After Set in caller function, until we visit a go-call-edge or visit the root node  in call graph.

#### Defer Operations: Before we visited a go-call-edge, we can move defer operations from Must Happens Before Set to Must Happens After Set

#### Known Limitation:
It can’t collection synchronization operations in loop and branch

In Case of Write#2 in Fig#2, the this path is:
[Root] =Call=> RaceFoo() =callsite3=> Call() =callsite1=> RaceFoo$1 => Write#2
AfterSet:
First we consider the basic block, add AfterItem1 to set, then move to outer layer of call path, we collection AfterItem2 to set since it after callsite1. Again,we move to outer layer and collection AfterItem3 and a normal call of callsite3

The AfterSet of WRITE#4 only contains AfterItem4, since we can’t move over a go-call-edge to `Go` function for AfterSet
Write#4: [Root] =Call=> RaceFoo() =Call=> Go() =Go callsite4=> RaceFoo$1 =>Write#4

```go
func Call(fn func()){
  fn()  // <= callsite1 of RaceFoo$1
  // AfterItem2
}

func Go(fn func()){
  go fn()  // <= callsite4 of RaceFoo$2 it’s a go call
  // Can’t move here
}

func RaceFoo(){
  a:=1  // ALLOC WRITE#1
  Call( func() { // RaceFoo$1  <= callsite2 of Call
     a++ // WRITE #2
     // AfterItem1
  })
  // AfterItem3
  println(a) // READ #3
  Go(func() { // RaceFoo$2  <= callsite3 of Go
     a-- // WRITE #4
     // AfterItem4
  })
  println(a) // READ #5
}
```
Fig#2

#### Step #7: Check happen-before relationship from Path_A, Path_B, AfterSet_A BeforeSet_A, AfterSet_B, BeforeSet_B

Pair(A,B) is not race if one of follow are true:
* A callsite in Path_A exist on AfterSet_B
* one Channel Ch exist in both AfterSet_A and BeforeSet_B :
* for unbuff channel, the operation of Ch in two set are different or 
	1. for 1 buff channel, the operation is send/close in AfterSet_A and is recv in BeforeSet_B 
	2. one WaitGroup Wg exists in both AfterSet_A and BeforeSet_B : Wg.Done() in AfterSet_A and Wg.Wait() in BeforeSet_B 
* one Mutex / RWMutex exists in BeforeSet_A and BeforeSet_B and Lock() is one more than UnLock() in both BeforeSet_A and BeforeSet_B 

We check two values (Channel, WaitGroup, Mutex) from two sets are the same by lookuping binding map 

Example:
For Write#1 in Fig#2: the AfterSet is {callsite2, callsite3} and Write#4’s path is Write#4: [Root] =Call=> RaceFoo() =callsite3=> Go() =Go=> RaceFoo$1 =>Write#4, callsite3 exist both in AfterSet and Paht, hits Rule #1. It’s not a race

```go
func RaceSample() {
  a := 1 // ALLOC WRITE #1
  ch := make(chan int)
  go func() { //RaceSample$1  <= callsite1
     a = 2 // WRITE #2
     go func() { //RaceSample$1$1 <= callsite2
        a = 3 // WRITE #3
        ch <- 1
     }()
  }()
  println(a) // READ #4
  <-ch
  println(a) // READ #5
}
```
Figure #4

| Op1 \ Op2 | WRITE #2	|WRITE #3	|READ #4	|READ #5	|
|-----------|-----------|-----------|-----------|-----------|
|WRITE #1	|Rule1: callsite1|Rule1: callsite1|unrachable |unrachable |
|WRITE #2	|  -empty-	|Rule1: callsite2 | Race |  FP: #2 <= callsite2 <= ch send <= ch recv <= #5 |
|WRITE #3	|  -empty-	|  -empty-	|Race		|Rule2: ch	|
|READ #4	|  -empty-	|  -empty-	|  -empty-	| unrachable 	|


#### Known Limitation:
1. It can’t deal with channel which buffer size is more than one
2. It assumes the channel is emtpy
3. It can’t understand transitive of happens before

### Incorrect Case#1:
```go
func GoAndWait(fn func()) {
  ch := make(chan int)
  go func() {
     fn()
     ch <- 1
  }()
  <- ch
}

func Foo() {
  a:=1 // Write #1
  GoAndWait(func() {
     a = 2 // Write #2
  })
  a = 3 // Write #3
}
```

Checker don’t step into function `GoAndWait` to get ch recv into BeforeSet of Write#3, I can add `GoAndWait` to a list to treat it as a normal call for now.

### Incorrect Case#2:
```go
func Bar() {
  ch1 := make(chan int)
  ch2 := make(chan int)
  a := 1
  go func() {
     go func() {
        a=2 // incorrect race report
        ch1 <- 1
     }()
     <-ch1
     ch2 <- 1
  }()
  <-ch2
  println(a) // incorrect race report
}
```

It can’t understand transitive of happens before

### Incorrect Case#3:
```go
func Bar2() {
  ch := make(chan int)
  a := 1
  go func() {
     for {
        if a >= 10 {
           close(ch) // it can’t find sync-opreation in branch
        }
        a++
     }
  }()
  <-ch
  print(a)
}
```
