import Ix.ShardMap
import Ix.Benchmark.Bench

open Ix

namespace Benchmarks.ShardMap

/-! ## Helper Functions -/

/-- Insert N sequential keys into a map -/
def insertN (map : ShardMap Nat Nat) (n : Nat) : IO Unit := do
  for i in [:n] do
    map.insert i i

/-- Look up N sequential keys (all hits) -/
def getN (map : ShardMap Nat Nat) (n : Nat) : IO Unit := do
  for i in [:n] do
    let _ ← map.get? i

/-- Look up N keys that don't exist (all misses) -/
def getMissN (map : ShardMap Nat Nat) (n : Nat) (offset : Nat) : IO Unit := do
  for i in [:n] do
    let _ ← map.get? (offset + i)

/-- Remove N sequential keys -/
def removeN (map : ShardMap Nat Nat) (n : Nat) : IO Unit := do
  for i in [:n] do
    let _ ← map.remove i

/-- Insert items one by one in a loop -/
def insertLoop (map : ShardMap Nat Nat) (items : Array (Nat × Nat)) : IO Unit := do
  for (k, v) in items do
    map.insert k v

/-- Generate an array of N key-value pairs -/
def genItems (n : Nat) : Array (Nat × Nat) :=
  Array.range n |>.map fun i => (i, i)

/-- Concurrent workload: each thread inserts and reads its own range of keys -/
def concurrentWorkload (map : ShardMap Nat Nat) (threads : Nat) (opsPerThread : Nat) : IO Unit := do
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for t in [:threads] do
    let task ← IO.asTask do
      for i in [:opsPerThread] do
        let key := t * opsPerThread + i
        map.insert key key
        let _ ← map.get? key
    tasks := tasks.push task
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-- Concurrent reads only: all threads read the same pre-populated keys -/
def concurrentReads (map : ShardMap Nat Nat) (threads : Nat) (keysToRead : Nat) : IO Unit := do
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for _ in [:threads] do
    let task ← IO.asTask do
      for i in [:keysToRead] do
        let _ ← map.get? i
    tasks := tasks.push task
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-- Concurrent writes only: each thread writes to different keys -/
def concurrentWrites (map : ShardMap Nat Nat) (threads : Nat) (keysPerThread : Nat) : IO Unit := do
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for t in [:threads] do
    let task ← IO.asTask do
      for i in [:keysPerThread] do
        let key := t * keysPerThread + i
        map.insert key key
    tasks := tasks.push task
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-- Mixed read/write workload with configurable read ratio -/
def mixedWorkload (map : ShardMap Nat Nat) (threads : Nat) (opsPerThread : Nat)
    (readRatio : Float) : IO Unit := do
  let readOps := (readRatio * opsPerThread.toFloat).toUInt64.toNat
  let writeOps := opsPerThread - readOps
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for t in [:threads] do
    let task ← IO.asTask do
      -- Writes first
      for i in [:writeOps] do
        let key := t * opsPerThread + i
        map.insert key key
      -- Then reads
      for i in [:readOps] do
        let key := t * opsPerThread + (i % writeOps.max 1)
        let _ ← map.get? key
    tasks := tasks.push task
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-- Hot shard workload: all threads access keys that hash to same shard -/
def hotShardWorkload (map : ShardMap Nat Nat) (threads : Nat) (opsPerThread : Nat) : IO Unit := do
  -- All keys will be multiples of 256 to hit the same shard (assuming 256 shards)
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for t in [:threads] do
    let task ← IO.asTask do
      for i in [:opsPerThread] do
        let key := (t * opsPerThread + i) * 256
        map.insert key key
        let _ ← map.get? key
    tasks := tasks.push task
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-- Distributed workload: keys are spread across all shards -/
def distributedWorkload (map : ShardMap Nat Nat) (threads : Nat) (opsPerThread : Nat) : IO Unit := do
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for t in [:threads] do
    let task ← IO.asTask do
      for i in [:opsPerThread] do
        -- Use a prime multiplier to distribute across shards
        let key := (t * opsPerThread + i) * 127
        map.insert key key
        let _ ← map.get? key
    tasks := tasks.push task
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-! ## Benchmark Groups -/

/-- Basic single-threaded operations -/
def basicBench : IO (Array BenchReport) := do
  IO.println "=== Basic Operations (Single-threaded) ===\n"
  bgroup "shardmap-basic" [
    -- Insert throughput
    benchIO "insert 1K" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertN map 1000) (),
    benchIO "insert 10K" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertN map 10000) (),
    benchIO "insert 100K" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertN map 100000) (),

    -- Lookup throughput (pre-populated)
    benchIO "get 10K hits" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertN map 10000
      getN map 10000) (),
    benchIO "get 10K misses" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertN map 10000
      getMissN map 10000 100000) (),

    -- Remove throughput
    benchIO "remove 10K" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertN map 10000
      removeN map 10000) ()
  ]

/-- Compare insertMany vs individual inserts -/
def bulkBench : IO (Array BenchReport) := do
  IO.println "=== Bulk Operations Comparison ===\n"
  let items10K := genItems 10000
  bgroup "shardmap-bulk" [
    benchIO "insertMany 10K" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      map.insertMany items10K) (),
    benchIO "insert loop 10K" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertLoop map items10K) ()
  ]

/-- Concurrent read scaling with SharedMutex -/
def concurrentReadBench : IO (Array BenchReport) := do
  IO.println "=== Concurrent Read Scaling ===\n"
  -- Pre-populate a shared map
  let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
  insertN map 10000
  bgroup "shardmap-concurrent-read" [
    benchIO "read 1 thread" (fun () => concurrentReads map 1 10000) (),
    benchIO "read 2 threads" (fun () => concurrentReads map 2 5000) (),
    benchIO "read 4 threads" (fun () => concurrentReads map 4 2500) (),
    benchIO "read 8 threads" (fun () => concurrentReads map 8 1250) (),
    benchIO "read 16 threads" (fun () => concurrentReads map 16 625) ()
  ]

/-- Concurrent write scaling -/
def concurrentWriteBench : IO (Array BenchReport) := do
  IO.println "=== Concurrent Write Scaling ===\n"
  bgroup "shardmap-concurrent-write" [
    benchIO "write 1 thread 10K" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      concurrentWrites map 1 10000) (),
    benchIO "write 2 threads 5K each" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      concurrentWrites map 2 5000) (),
    benchIO "write 4 threads 2.5K each" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      concurrentWrites map 4 2500) (),
    benchIO "write 8 threads 1.25K each" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      concurrentWrites map 8 1250) ()
  ]

/-- Mixed read/write workload -/
def mixedWorkloadBench : IO (Array BenchReport) := do
  IO.println "=== Mixed Read/Write Workload (8 threads) ===\n"
  bgroup "shardmap-mixed" [
    benchIO "mixed 50/50 8 threads" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      mixedWorkload map 8 1000 0.5) (),
    benchIO "mixed 80/20 read/write 8 threads" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      mixedWorkload map 8 1000 0.8) (),
    benchIO "mixed 95/5 read/write 8 threads" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      mixedWorkload map 8 1000 0.95) ()
  ]

/-- Compare different shard configurations -/
def shardConfigBench : IO (Array BenchReport) := do
  IO.println "=== Shard Configuration Impact (8 threads) ===\n"
  bgroup "shardmap-shards" [
    benchIO "shardBits=2 (4 shards)" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat) (shardBits := 2)
      concurrentWorkload map 8 1000) (),
    benchIO "shardBits=4 (16 shards)" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat) (shardBits := 4)
      concurrentWorkload map 8 1000) (),
    benchIO "shardBits=6 (64 shards)" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat) (shardBits := 6)
      concurrentWorkload map 8 1000) (),
    benchIO "shardBits=8 (256 shards)" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat) (shardBits := 8)
      concurrentWorkload map 8 1000) ()
  ]

/-- Contention patterns: hot shard vs distributed access -/
def contentionBench : IO (Array BenchReport) := do
  IO.println "=== Contention Patterns (8 threads) ===\n"
  bgroup "shardmap-contention" [
    benchIO "hot shard (worst case)" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      hotShardWorkload map 8 500) (),
    benchIO "distributed (best case)" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      distributedWorkload map 8 500) ()
  ]

/-- Pre-allocated capacity impact -/
def capacityBench : IO (Array BenchReport) := do
  IO.println "=== Capacity Pre-allocation Impact ===\n"
  bgroup "shardmap-capacity" [
    benchIO "insert 10K (no prealloc)" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertN map 10000) (),
    benchIO "insert 10K (prealloc 32/shard)" (fun () => do
      let map ← Ix.ShardMap.newWithCapacity (α := Nat) (β := Nat)
        (capacityPerShard := 32)
      insertN map 10000) (),
    benchIO "insert 10K (prealloc 64/shard)" (fun () => do
      let map ← Ix.ShardMap.newWithCapacity (α := Nat) (β := Nat)
        (capacityPerShard := 64)
      insertN map 10000) ()
  ]

/-- Look up N sequential keys using get?Fast (all hits) -/
def getNFast (map : ShardMap Nat Nat) (n : Nat) : IO Unit := do
  for i in [:n] do
    let _ ← map.get?Fast i

/-- Concurrent reads using get?Fast -/
def concurrentReadsFast (map : ShardMap Nat Nat) (threads : Nat) (keysToRead : Nat) : IO Unit := do
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for _ in [:threads] do
    let task ← IO.asTask do
      for i in [:keysToRead] do
        let _ ← map.get?Fast i
    tasks := tasks.push task
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-- Hot shard workload using get?Fast: all threads access keys that hash to same shard -/
def hotShardWorkloadFast (map : ShardMap Nat Nat) (threads : Nat) (opsPerThread : Nat) : IO Unit := do
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for t in [:threads] do
    let task ← IO.asTask do
      for i in [:opsPerThread] do
        let key := (t * opsPerThread + i) * 256
        map.insert key key
        let _ ← map.get?Fast key
    tasks := tasks.push task
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-- Compare get? vs get?Fast under different contention levels -/
def fastPathBench : IO (Array BenchReport) := do
  IO.println "=== get?Fast vs get? Comparison ===\n"
  let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
  insertN map 10000
  bgroup "shardmap-fast-path" [
    -- Single-threaded comparison
    benchIO "get? 10K (single thread)" (fun () => getN map 10000) (),
    benchIO "get?Fast 10K (single thread)" (fun () => getNFast map 10000) (),
    -- Concurrent comparison
    benchIO "get? 8 threads" (fun () => concurrentReads map 8 1250) (),
    benchIO "get?Fast 8 threads" (fun () => concurrentReadsFast map 8 1250) (),
    -- Hot shard comparison (high contention)
    benchIO "hot shard get?" (fun () => do
      let m ← Ix.ShardMap.new (α := Nat) (β := Nat)
      hotShardWorkload m 8 500) (),
    benchIO "hot shard get?Fast" (fun () => do
      let m ← Ix.ShardMap.new (α := Nat) (β := Nat)
      hotShardWorkloadFast m 8 500) ()
  ]

/-- Compare sequential vs parallel insertMany -/
def parallelInsertBench : IO (Array BenchReport) := do
  IO.println "=== Parallel insertMany Performance ===\n"
  let items50K := genItems 50000
  let items100K := genItems 100000
  bgroup "shardmap-parallel-insert" [
    benchIO "insertMany 50K items" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      map.insertMany items50K) (),
    benchIO "insertMany 100K items" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      map.insertMany items100K) (),
    benchIO "insert loop 50K items" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertLoop map items50K) (),
    benchIO "insert loop 100K items" (fun () => do
      let map ← Ix.ShardMap.new (α := Nat) (β := Nat)
      insertLoop map items100K) ()
  ]

end Benchmarks.ShardMap

def main : IO Unit := do
  IO.println "ShardMap Performance Benchmarks\n"
  IO.println "================================\n"

  let _ ← Benchmarks.ShardMap.basicBench
  let _ ← Benchmarks.ShardMap.bulkBench
  let _ ← Benchmarks.ShardMap.concurrentReadBench
  let _ ← Benchmarks.ShardMap.concurrentWriteBench
  let _ ← Benchmarks.ShardMap.mixedWorkloadBench
  let _ ← Benchmarks.ShardMap.shardConfigBench
  let _ ← Benchmarks.ShardMap.contentionBench
  let _ ← Benchmarks.ShardMap.capacityBench
  let _ ← Benchmarks.ShardMap.fastPathBench
  let _ ← Benchmarks.ShardMap.parallelInsertBench

  IO.println "\nBenchmarks complete!"
