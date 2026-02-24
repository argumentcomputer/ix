module

public import Ix.ShardMap
public import LSpec

open LSpec Ix

namespace Tests.ShardMap

def testInsertAndGet : TestSeq :=
  .individualIO "basic insert and get" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "hello" 42
    let v ← map.get? "hello"
    pure (v == some 42, 0, 0, none)) .done

def testGetNonExistent : TestSeq :=
  .individualIO "get non-existent returns none" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    let v ← map.get? "nonexistent"
    pure (v == none, 0, 0, none)) .done

def testMultipleInserts : TestSeq :=
  .individualIO "multiple inserts" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "foo" 1
    map.insert "bar" 2
    map.insert "baz" 3
    let v1 ← map.get? "foo"
    let v2 ← map.get? "bar"
    let v3 ← map.get? "baz"
    pure (v1 == some 1 && v2 == some 2 && v3 == some 3, 0, 0, none)) .done

def testOverwrite : TestSeq :=
  .individualIO "overwrite existing key" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "key" 1
    map.insert "key" 2
    let v ← map.get? "key"
    pure (v == some 2, 0, 0, none)) .done

def testSize : TestSeq :=
  .individualIO "size" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "a" 1
    map.insert "b" 2
    map.insert "c" 3
    let sz ← map.size
    pure (sz == 3, 0, 0, none)) .done

def testContains : TestSeq :=
  .individualIO "contains" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "exists" 1
    let c1 ← map.contains "exists"
    let c2 ← map.contains "missing"
    pure (c1 && !c2, 0, 0, none)) .done

def testRemove : TestSeq :=
  .individualIO "remove" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "key" 42
    let removed ← map.remove "key"
    let after ← map.get? "key"
    pure (removed == some 42 && after == none, 0, 0, none)) .done

def testModify : TestSeq :=
  .individualIO "modify" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "key" 10
    let modified ← map.modify "key" (· + 5)
    let v ← map.get? "key"
    pure (modified && v == some 15, 0, 0, none)) .done

def testGetOrInsertExisting : TestSeq :=
  .individualIO "getOrInsert existing" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "key" 42
    let v ← map.getOrInsert "key" (fun () => pure 999)
    pure (v == 42, 0, 0, none)) .done

def testGetOrInsertNew : TestSeq :=
  .individualIO "getOrInsert new" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    let v ← map.getOrInsert "key" (fun () => pure 999)
    let check ← map.get? "key"
    pure (v == 999 && check == some 999, 0, 0, none)) .done

def testClear : TestSeq :=
  .individualIO "clear" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "a" 1
    map.insert "b" 2
    map.clear
    let sz ← map.size
    pure (sz == 0, 0, 0, none)) .done

def testToList : TestSeq :=
  .individualIO "toList" none (do
    let map ← ShardMap.new (α := Nat) (β := String) (shardBits := 1)
    map.insert 1 "one"
    map.insert 2 "two"
    let list ← map.toList
    pure (list.length == 2, 0, 0, none)) .done

-- Concurrent tests

/-- Test concurrent reads don't block each other with SharedMutex -/
def testConcurrentReads : TestSeq :=
  .individualIO "concurrent reads" none (do
    let map ← ShardMap.new (α := Nat) (β := Nat) (shardBits := 2)
    -- Insert many values
    for i in [:1000] do
      map.insert i (i * 2)
    -- Spawn many concurrent readers
    let numReaders := 32
    let mut tasks : Array (Task (Except IO.Error Bool)) := #[]
    for _ in [:numReaders] do
      let task ← IO.asTask do
        let mut allOk := true
        for i in [:1000] do
          let v ← map.get? i
          if v != some (i * 2) then allOk := false
        pure allOk
      tasks := tasks.push task
    -- Wait for all readers
    let mut allPassed := true
    for task in tasks do
      match task.get with
      | .ok ok => if !ok then allPassed := false
      | .error _ => allPassed := false
    pure (allPassed, 0, 0, none)) .done

/-- Test concurrent writes to different keys -/
def testConcurrentWritesDifferentKeys : TestSeq :=
  .individualIO "concurrent writes different keys" none (do
    let map ← ShardMap.new (α := Nat) (β := Nat) (shardBits := 4)
    let numWriters := 16
    let keysPerWriter := 100
    let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
    for w in [:numWriters] do
      let task ← IO.asTask do
        for k in [:keysPerWriter] do
          let key := w * keysPerWriter + k
          map.insert key (key * 3)
      tasks := tasks.push task
    -- Wait for all writers and check for errors
    for task in tasks do
      let _ ← IO.ofExcept task.get
    -- Verify all values
    let mut allCorrect := true
    for i in [:(numWriters * keysPerWriter)] do
      let v ← map.get? i
      if v != some (i * 3) then allCorrect := false
    pure (allCorrect, 0, 0, none)) .done

/-- Test concurrent getOrInsert with same keys (race condition test) -/
def testConcurrentGetOrInsert : TestSeq :=
  .individualIO "concurrent getOrInsert consistency" none (do
    let map ← ShardMap.new (α := Nat) (β := Nat) (shardBits := 2)
    let numWorkers := 32
    let numKeys := 100
    -- All workers try to getOrInsert the same keys
    let mut tasks : Array (Task (Except IO.Error (Array Nat))) := #[]
    for w in [:numWorkers] do
      let task ← IO.asTask do
        let mut results : Array Nat := #[]
        for k in [:numKeys] do
          let v ← map.getOrInsert k (fun () => pure (w * 1000 + k))
          results := results.push v
        pure results
      tasks := tasks.push task
    -- Wait for all workers and collect results
    let mut allResults : Array (Array Nat) := #[]
    for task in tasks do
      match task.get with
      | .ok results => allResults := allResults.push results
      | .error _ => pure ()
    -- For each key, all workers should get the same value (whoever inserted first wins)
    let mut consistent := true
    for k in [:numKeys] do
      let firstVal := allResults[0]![k]!
      for results in allResults do
        if results[k]! != firstVal then consistent := false
    pure (consistent, 0, 0, none)) .done

/-- Test getOrInsertLazy works correctly -/
def testGetOrInsertLazy : TestSeq :=
  .individualIO "getOrInsertLazy" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    let v1 ← map.getOrInsertLazy "key" (fun () => 42)
    let v2 ← map.getOrInsertLazy "key" (fun () => 999)  -- Should not be called
    pure (v1 == 42 && v2 == 42, 0, 0, none)) .done

/-- Test getOrInsertIO works correctly -/
def testGetOrInsertIO : TestSeq :=
  .individualIO "getOrInsertIO" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    let counter ← IO.mkRef 0
    let v1 ← map.getOrInsertIO "key" (fun () => do counter.modify (· + 1); pure 42)
    let v2 ← map.getOrInsertIO "key" (fun () => do counter.modify (· + 1); pure 999)
    let calls ← counter.get
    pure (v1 == 42 && v2 == 42 && calls == 1, 0, 0, none)) .done

/-! ## Tests for try operations -/

/-- Test tryGet? returns value when unlocked -/
def testTryGetUnlocked : TestSeq :=
  .individualIO "tryGet? unlocked" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "key" 42
    let v ← map.tryGet? "key"
    pure (v == some (some 42), 0, 0, none)) .done

/-- Test tryGet? returns none for non-existent key -/
def testTryGetNonExistent : TestSeq :=
  .individualIO "tryGet? non-existent" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    let v ← map.tryGet? "missing"
    pure (v == some none, 0, 0, none)) .done

/-- Test tryInsert succeeds when unlocked -/
def testTryInsert : TestSeq :=
  .individualIO "tryInsert" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    let ok ← map.tryInsert "key" 42
    let v ← map.get? "key"
    pure (ok && v == some 42, 0, 0, none)) .done

/-- Test tryGetOrInsertLazy works correctly -/
def testTryGetOrInsertLazy : TestSeq :=
  .individualIO "tryGetOrInsertLazy" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    let v1 ← map.tryGetOrInsertLazy "key" (fun () => 42)
    let v2 ← map.tryGetOrInsertLazy "key" (fun () => 999)  -- Should return existing
    pure (v1 == some 42 && v2 == some 42, 0, 0, none)) .done

/-! ## Tests for insertMany -/

/-- Test insertMany inserts all items correctly -/
def testInsertMany : TestSeq :=
  .individualIO "insertMany" none (do
    let map ← ShardMap.new (α := Nat) (β := String) (shardBits := 2)
    let items := #[(1, "one"), (2, "two"), (3, "three"), (4, "four"), (5, "five")]
    map.insertMany items
    let v1 ← map.get? 1
    let v2 ← map.get? 2
    let v3 ← map.get? 3
    let v4 ← map.get? 4
    let v5 ← map.get? 5
    let sz ← map.size
    pure (v1 == some "one" && v2 == some "two" && v3 == some "three"
      && v4 == some "four" && v5 == some "five" && sz == 5, 0, 0, none)) .done

/-- Test insertMany with empty array -/
def testInsertManyEmpty : TestSeq :=
  .individualIO "insertMany empty" none (do
    let map ← ShardMap.new (α := Nat) (β := Nat) (shardBits := 2)
    map.insertMany #[]
    let sz ← map.size
    pure (sz == 0, 0, 0, none)) .done

/-- Test insertMany overwrites existing keys -/
def testInsertManyOverwrite : TestSeq :=
  .individualIO "insertMany overwrite" none (do
    let map ← ShardMap.new (α := Nat) (β := Nat) (shardBits := 2)
    map.insert 1 100
    map.insertMany #[(1, 200), (2, 300)]
    let v1 ← map.get? 1
    let v2 ← map.get? 2
    pure (v1 == some 200 && v2 == some 300, 0, 0, none)) .done

/-- Test concurrent insertMany operations -/
def testConcurrentInsertMany : TestSeq :=
  .individualIO "concurrent insertMany" none (do
    let map ← ShardMap.new (α := Nat) (β := Nat) (shardBits := 4)
    let numWorkers := 8
    let itemsPerWorker := 100
    let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
    for w in [:numWorkers] do
      let task ← IO.asTask do
        let items : Array (Nat × Nat) := Array.range itemsPerWorker |>.map fun i =>
          let key := w * itemsPerWorker + i
          (key, key * 2)
        map.insertMany items
      tasks := tasks.push task
    -- Wait for all workers
    for task in tasks do
      let _ ← IO.ofExcept task.get
    -- Verify all values
    let mut allCorrect := true
    for i in [:(numWorkers * itemsPerWorker)] do
      let v ← map.get? i
      if v != some (i * 2) then allCorrect := false
    let sz ← map.size
    pure (allCorrect && sz == numWorkers * itemsPerWorker, 0, 0, none)) .done

/-! ## Tests for modifyGet -/

/-- Test modifyGet returns result and updates value -/
def testModifyGet : TestSeq :=
  .individualIO "modifyGet" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "counter" 10
    let result ← map.modifyGet "counter" fun v => (v, v + 1)
    let newVal ← map.get? "counter"
    pure (result == some 10 && newVal == some 11, 0, 0, none)) .done

/-- Test modifyGet returns none for non-existent key -/
def testModifyGetNonExistent : TestSeq :=
  .individualIO "modifyGet non-existent" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    let result ← map.modifyGet "missing" fun v => (v, v + 1)
    pure (result == none, 0, 0, none)) .done

/-- Test modifyGet can return different type than value -/
def testModifyGetDifferentType : TestSeq :=
  .individualIO "modifyGet different type" none (do
    let map ← ShardMap.new (α := String) (β := Nat) (shardBits := 2)
    map.insert "key" 42
    let result ← map.modifyGet "key" fun v => (s!"was {v}", v * 2)
    let newVal ← map.get? "key"
    pure (result == some "was 42" && newVal == some 84, 0, 0, none)) .done

/-- Test concurrent modifyGet operations -/
def testConcurrentModifyGet : TestSeq :=
  .individualIO "concurrent modifyGet" none (do
    let map ← ShardMap.new (α := Nat) (β := Nat) (shardBits := 2)
    -- Initialize counters
    for i in [:10] do
      map.insert i 0
    -- Many workers increment counters
    let numWorkers := 32
    let incrementsPerWorker := 100
    let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
    for _ in [:numWorkers] do
      let task ← IO.asTask do
        for _ in [:incrementsPerWorker] do
          for i in [:10] do
            let _ ← map.modifyGet i fun v => ((), v + 1)
      tasks := tasks.push task
    -- Wait for all workers
    for task in tasks do
      let _ ← IO.ofExcept task.get
    -- Each counter should have been incremented numWorkers * incrementsPerWorker times
    let expected := numWorkers * incrementsPerWorker
    let mut allCorrect := true
    for i in [:10] do
      let v ← map.get? i
      if v != some expected then allCorrect := false
    pure (allCorrect, 0, 0, none)) .done

/-! ## Tests for newWithCapacity -/

/-- Test newWithCapacity creates a working map -/
def testNewWithCapacity : TestSeq :=
  .individualIO "newWithCapacity" none (do
    let map ← ShardMap.newWithCapacity (α := Nat) (β := Nat)
      (shardBits := 4) (capacityPerShard := 1000)
    -- Insert many values
    for i in [:500] do
      map.insert i (i * 2)
    -- Verify values
    let mut allOk := true
    for i in [:500] do
      let v ← map.get? i
      if v != some (i * 2) then allOk := false
    let sz ← map.size
    pure (allOk && sz == 500, 0, 0, none)) .done

/-- Test concurrent tryGet? operations -/
def testConcurrentTryGet : TestSeq :=
  .individualIO "concurrent tryGet?" none (do
    let map ← ShardMap.new (α := Nat) (β := Nat) (shardBits := 2)  -- 4 shards
    for i in [:100] do
      map.insert i i
    -- Many readers trying tryGet?
    let numReaders := 32
    let successCount ← IO.mkRef 0
    let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
    for _ in [:numReaders] do
      let task ← IO.asTask do
        for i in [:100] do
          match ← map.tryGet? i with
          | some _ => successCount.modify (· + 1)
          | none => pure ()  -- Shard was locked (rare with reads)
      tasks := tasks.push task
    for task in tasks do
      match task.get with
      | .ok () => pure ()
      | .error _ => pure ()
    let successes ← successCount.get
    -- Most should succeed (reads don't block each other with SharedMutex)
    -- With 32 readers × 100 keys = 3200 operations, expect at least 100 to succeed
    -- (conservative threshold to avoid flakiness)
    pure (successes > 100, 0, 0, none)) .done

public def suite : List TestSeq := [
  testInsertAndGet,
  testGetNonExistent,
  testMultipleInserts,
  testOverwrite,
  testSize,
  testContains,
  testRemove,
  testModify,
  testGetOrInsertExisting,
  testGetOrInsertNew,
  testClear,
  testToList,
  testConcurrentReads,
  testConcurrentWritesDifferentKeys,
  testConcurrentGetOrInsert,
  testGetOrInsertLazy,
  testGetOrInsertIO,
  testTryGetUnlocked,
  testTryGetNonExistent,
  testTryInsert,
  testTryGetOrInsertLazy,
  testNewWithCapacity,
  testConcurrentTryGet,
  testInsertMany,
  testInsertManyEmpty,
  testInsertManyOverwrite,
  testConcurrentInsertMany,
  testModifyGet,
  testModifyGetNonExistent,
  testModifyGetDifferentType,
  testConcurrentModifyGet,
]

end Tests.ShardMap
