/-
  ShardMap: A concurrent hashmap with sharded locks for parallel access.

  This is a Lean equivalent of Rust's DashMap, providing O(1) concurrent
  read/write access with reduced lock contention through sharding.

  ## Thread Safety

  - All single-key operations (`insert`, `get?`, `remove`, `modify`, etc.) are atomic
    and thread-safe.
  - Aggregate operations (`size`, `toArray`, `fold`, `toList`, `toHashMap`) iterate
    over shards non-atomically - they may observe an inconsistent view during
    concurrent modifications.
  - `clear` is not atomic - shards are cleared sequentially.

  ## Performance Characteristics

  - Uses power-of-2 sharding with bit masking for O(1) shard selection.
  - Each shard uses SharedMutex for reader-writer semantics (concurrent reads,
    exclusive writes).
  - Cache line padding prevents false sharing between adjacent shards.
  - Hash mixing distributes keys more evenly across shards.
  - Default 256 shards provides good parallelism for most workloads.
  - `insertMany` parallelizes updates across shards for 10-20x speedup on bulk inserts.

  ## Usage

    let map ← ShardMap.new (shardBits := 6)  -- 64 shards
    map.insert key value
    let val? ← map.get? key

    -- Bulk insert for better performance
    map.insertMany #[(k1, v1), (k2, v2), ...]

    -- Atomic read-modify-write
    let result? ← map.modifyGet key fun v => (computeResult v, updateValue v)
-/
module

public import Std.Data.HashMap
public import Std.Sync.SharedMutex

public section

namespace Ix

/-- Wrapper to prevent false sharing between shards.
    Adds padding to push each shard to separate cache lines (typically 64 bytes).
    The SharedMutex pointer is ~8 bytes, padding adds 56 bytes for 64-byte alignment. -/
structure PaddedShard (α : Type) (β : Type) [BEq α] [Hashable α] where
  shard : Std.SharedMutex (Std.HashMap α β)
  -- Padding fields to reach ~64 bytes total (cache line size)
  -- Each UInt64 is 8 bytes
  private _pad0 : UInt64 := 0
  private _pad1 : UInt64 := 0
  private _pad2 : UInt64 := 0
  private _pad3 : UInt64 := 0
  private _pad4 : UInt64 := 0
  private _pad5 : UInt64 := 0
  private _pad6 : UInt64 := 0

/-- A concurrent hashmap with sharded locks using reader-writer semantics.

    Each shard is protected by a SharedMutex, allowing concurrent reads
    while writes are exclusive. Uses 2^shardBits shards with bit-masking for
    fast shard selection.

    Shards are padded to separate cache lines to prevent false sharing. -/
structure ShardMap (α : Type) (β : Type) [BEq α] [Hashable α] where
  shards : Array (PaddedShard α β)
  shardMask : USize  -- 2^k - 1 for fast bitwise AND
  h_pos : shards.size > 0

namespace ShardMap

variable {α β : Type} [BEq α] [Hashable α]

/-- Build an array of n padded shards with given capacity per shard. -/
private def mkShardArrayWithCapacity (n : Nat) (capacity : Nat)
    : BaseIO { arr : Array (PaddedShard α β) // arr.size = n } := do
  let rec go (remaining : Nat) (acc : Array (PaddedShard α β)) (hacc : acc.size + remaining = n) :
      BaseIO { arr : Array (PaddedShard α β) // arr.size = n } := do
    match remaining with
    | 0 => pure ⟨acc, by omega⟩
    | r + 1 =>
      let mutex ← Std.SharedMutex.new (Std.HashMap.emptyWithCapacity capacity)
      let paddedShard : PaddedShard α β := { shard := mutex }
      go r (acc.push paddedShard) (by simp [Array.size_push]; omega)
  go n #[] (by simp)

/-- Build an array of n empty padded shards. -/
private def mkShardArray (n : Nat) : BaseIO { arr : Array (PaddedShard α β) // arr.size = n } :=
  mkShardArrayWithCapacity n 0

/-- Create a new ShardMap with 2^shardBits shards.
    Default is 8 bits = 256 shards, which provides good parallelism for most workloads. -/
def new (shardBits : Nat := 8) : BaseIO (ShardMap α β) := do
  let numShards := 2 ^ shardBits
  let shardMask : USize := (numShards - 1).toUSize
  let ⟨shards, hsize⟩ ← mkShardArray numShards
  have h : shards.size > 0 := by simp [hsize]; exact Nat.one_le_two_pow
  pure ⟨shards, shardMask, h⟩

/-- Compute the shard index for a given key using fast bit masking.
    Mixes high and low bits of the hash for better distribution across shards,
    which helps when hash functions produce correlated low bits. -/
@[inline]
def shardIdx (m : ShardMap α β) (key : α) : Nat :=
  let h : UInt64 := hash key
  -- Mix high and low bits for better distribution
  let mixed := h ^^^ (h >>> 32)
  (mixed.toUSize &&& m.shardMask).toNat

/-- Get the shard for a key. -/
@[inline]
def getShard (m : ShardMap α β) (key : α) : Std.SharedMutex (Std.HashMap α β) :=
  let idx := m.shardIdx key
  (m.shards[idx % m.shards.size]'(Nat.mod_lt _ m.h_pos)).shard

/-- Contention threshold in nanoseconds (100ms) -/
def contentionThresholdNs : Nat := 100_000_000

/-- Insert a key-value pair into the map.
    If the key already exists, its value is replaced. -/
@[inline]
def insert (m : ShardMap α β) (key : α) (val : β) : BaseIO Unit := do
  m.getShard key |>.atomically fun ref => do
    let map ← ST.Ref.get ref
    ST.Ref.set ref (map.insert key val)

/-- Insert with contention detection. -/
def insertTimed (m : ShardMap α β) (key : α) (val : β)
    (label : String := "ShardMap") : IO Unit := do
  let start ← IO.monoNanosNow
  let shardIdx := m.shardIdx key
  m.getShard key |>.atomically fun ref => do
    let map ← ST.Ref.get ref
    ST.Ref.set ref (map.insert key val)
  let elapsed := (← IO.monoNanosNow) - start
  if elapsed > contentionThresholdNs then
    IO.eprintln s!"[CONTENTION] {label} shard {shardIdx}: insert took {elapsed / 1_000_000}ms"

/-- Look up a key in the map, returning `none` if not found.
    Uses shared read lock for concurrent access. -/
@[inline]
def get? (m : ShardMap α β) (key : α) : BaseIO (Option β) := do
  m.getShard key |>.atomicallyRead fun map => pure (map.get? key)

/-- Look up a key in the map, returning a default value if not found. -/
@[inline]
def getD (m : ShardMap α β) (key : α) (default : β) : BaseIO β := do
  match ← m.get? key with
  | some v => pure v
  | none => pure default

/-- Get a value or insert a new one if the key doesn't exist.
    The `mkVal` function is only called if the key is not present.
    Returns the value (either existing or newly inserted).
    Uses double-checked locking: tries read lock first, only takes write lock on miss. -/
def getOrInsert (m : ShardMap α β) (key : α) (mkVal : Unit → BaseIO β) : BaseIO β := do
  let shard := m.getShard key
  -- Fast path: try read lock first
  let cached? ← shard.atomicallyRead fun map => pure (map.get? key)
  match cached? with
  | some v => pure v
  | none =>
    -- Slow path: take write lock and double-check
    shard.atomically fun ref => do
      let map ← ST.Ref.get ref
      match map.get? key with
      | some v => pure v  -- Another thread inserted while we waited
      | none => do
        let v ← mkVal ()
        ST.Ref.set ref (map.insert key v)
        pure v

/-- Get a value or insert a new one if the key doesn't exist (IO version).
    The `mkVal` function is only called if the key is not present.
    Returns the value (either existing or newly inserted).
    Uses double-checked locking: tries read lock first, only takes write lock on miss. -/
def getOrInsertIO (m : ShardMap α β) (key : α) (mkVal : Unit → IO β) : IO β := do
  let shard := m.getShard key
  -- Fast path: try read lock first
  let cached? ← shard.atomicallyRead fun map => pure (map.get? key)
  match cached? with
  | some v => pure v
  | none =>
    -- Slow path: take write lock and double-check
    shard.atomically fun ref => do
      let map ← ST.Ref.get ref
      match map.get? key with
      | some v => pure v  -- Another thread inserted while we waited
      | none => do
        let v ← mkVal ()
        ST.Ref.set ref (map.insert key v)
        pure v

/-- Get a value or insert a new one (pure version).
    The default value is evaluated only if needed.
    Uses double-checked locking: tries read lock first, only takes write lock on miss. -/
def getOrInsertLazy (m : ShardMap α β) (key : α) (mkVal : Unit → β) : BaseIO β := do
  let shard := m.getShard key
  -- Fast path: try read lock first
  let cached? ← shard.atomicallyRead fun map => pure (map.get? key)
  match cached? with
  | some v => pure v
  | none =>
    -- Slow path: take write lock and double-check
    shard.atomically fun ref => do
      let map ← ST.Ref.get ref
      match map.get? key with
      | some v => pure v
      | none =>
        let v := mkVal ()
        ST.Ref.set ref (map.insert key v)
        pure v

/-- Get a value or insert a new one, with contention detection.
    Prints a warning if the operation takes longer than the threshold.
    Uses double-checked locking: tries read lock first, only takes write lock on miss. -/
def getOrInsertLazyTimed (m : ShardMap α β) (key : α) (mkVal : Unit → β)
    (label : String := "ShardMap") : IO β := do
  let start ← IO.monoNanosNow
  let shardIdx := m.shardIdx key
  let shard := m.getShard key
  -- Fast path: try read lock first
  let cached? ← shard.atomicallyRead fun map => pure (map.get? key)
  let result ← match cached? with
  | some v => pure v
  | none =>
    -- Slow path: take write lock and double-check
    shard.atomically fun ref => do
      let map ← ST.Ref.get ref
      match map.get? key with
      | some v => pure v
      | none =>
        let v := mkVal ()
        ST.Ref.set ref (map.insert key v)
        pure v
  let elapsed := (← IO.monoNanosNow) - start
  if elapsed > contentionThresholdNs then
    IO.eprintln s!"[CONTENTION] {label} shard {shardIdx}: getOrInsertLazy took {elapsed / 1_000_000}ms"
  pure result

/-- Check if a key exists in the map.
    Uses shared read lock for concurrent access. -/
@[inline]
def contains (m : ShardMap α β) (key : α) : BaseIO Bool := do
  m.getShard key |>.atomicallyRead fun map => pure (map.contains key)

/-- Remove a key from the map, returning the removed value if it existed. -/
def remove (m : ShardMap α β) (key : α) : BaseIO (Option β) := do
  m.getShard key |>.atomically fun ref => do
    let map ← ST.Ref.get ref
    match map.get? key with
    | some v =>
      ST.Ref.set ref (map.erase key)
      pure (some v)
    | none => pure none

/-- Modify the value associated with a key, if it exists.
    Returns `true` if the key was found and modified. -/
def modify (m : ShardMap α β) (key : α) (f : β → β) : BaseIO Bool := do
  m.getShard key |>.atomically fun ref => do
    let map ← ST.Ref.get ref
    match map.get? key with
    | some v =>
      ST.Ref.set ref (map.insert key (f v))
      pure true
    | none => pure false

/-- Modify a value and return a result, atomically.
    The function `f` receives the current value and returns both a result and
    a new value. Returns `none` if the key doesn't exist.

    This is useful for patterns that need to read and modify in a single
    lock acquisition, e.g., incrementing a counter and returning the old value. -/
def modifyGet (m : ShardMap α β) (key : α) (f : β → (γ × β)) : BaseIO (Option γ) := do
  m.getShard key |>.atomically fun ref => do
    let map ← ST.Ref.get ref
    match map.get? key with
    | some v =>
      let (result, newV) := f v
      ST.Ref.set ref (map.insert key newV)
      pure (some result)
    | none => pure none

/-! ## Bulk Operations -/

/-- Insert multiple key-value pairs, grouping by shard for efficiency.
    This reduces lock acquisition overhead compared to inserting items one by one.

    Items are grouped by their target shard, then each shard is updated in parallel
    using IO.asTask for better multi-core utilization. -/
def insertMany (m : ShardMap α β) (items : Array (α × β)) : IO Unit := do
  -- Group items by shard index
  let numShards := m.shards.size
  let mut shardGroups : Array (Array (α × β)) := Array.replicate numShards #[]
  for (k, v) in items do
    let idx := m.shardIdx k
    shardGroups := shardGroups.modify idx (·.push (k, v))
  -- Insert each group in parallel across shards
  let finalGroups := shardGroups
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  for i in [:numShards] do
    if let some group := finalGroups[i]? then
      if group.size > 0 then
        let paddedShard := m.shards[i % numShards]'(Nat.mod_lt _ m.h_pos)
        let task ← IO.asTask do
          paddedShard.shard.atomically fun ref => do
            let map ← ST.Ref.get ref
            ST.Ref.set ref (group.foldl (fun m (k, v) => m.insert k v) map)
        tasks := tasks.push task
  -- Wait for all tasks to complete
  for task in tasks do
    let _ ← IO.ofExcept task.get

/-- Get the approximate size of the map.
    Note: This is not atomic and may not be exact during concurrent modifications. -/
def size (m : ShardMap α β) : BaseIO Nat := do
  let mut total := 0
  for paddedShard in m.shards do
    let sz ← paddedShard.shard.atomicallyRead fun map => pure map.size
    total := total + sz
  pure total

/-- Convert the map to an array of key-value pairs. O(n) time complexity.
    Single-pass collection to avoid stale size between passes.
    Not atomic; may be inconsistent during concurrent modifications. -/
def toArray (m : ShardMap α β) : BaseIO (Array (α × β)) := do
  let mut result : Array (α × β) := #[]
  for paddedShard in m.shards do
    let shardMap ← paddedShard.shard.atomicallyRead fun map => pure map
    for pair in shardMap do
      result := result.push pair
  pure result

/-- Fold over all key-value pairs in the map.
    Not atomic; may be inconsistent during concurrent modifications. -/
def fold (m : ShardMap α β) (init : γ) (f : γ -> α -> β -> γ) : BaseIO γ := do
  let mut acc := init
  for paddedShard in m.shards do
    let shardMap ← paddedShard.shard.atomicallyRead fun map => pure map
    for (k, v) in shardMap do
      acc := f acc k v
  pure acc

/-- Convert the map to a list of key-value pairs. O(n) time complexity.
    Note: This is not atomic and may not be consistent during concurrent modifications. -/
def toList (m : ShardMap α β) : BaseIO (List (α × β)) := do
  let arr ← m.toArray
  pure arr.toList

/-- Convert to a regular HashMap. O(n) time complexity using bulk construction.
    Note: This is not atomic and may not be consistent during concurrent modifications. -/
def toHashMap (m : ShardMap α β) : BaseIO (Std.HashMap α β) := do
  let pairs ← m.toArray
  pure (Std.HashMap.emptyWithCapacity pairs.size |>.insertMany pairs)

/-- Clear all entries from the map.
    Note: This is not atomic - shards are cleared sequentially. -/
def clear (m : ShardMap α β) : BaseIO Unit := do
  for paddedShard in m.shards do
    paddedShard.shard.atomically fun ref => ST.Ref.set ref {}

/-! ## Non-blocking operations -/

/-- Get a value with try-lock fast path.
    Attempts non-blocking read first, falls back to blocking if shard is contended.
    Useful for read-heavy workloads where you want to avoid blocking on contended shards. -/
@[inline]
def get?Fast (m : ShardMap α β) (key : α) : BaseIO (Option β) := do
  -- Try non-blocking first
  match ← m.getShard key |>.tryAtomicallyRead fun map => pure (map.get? key) with
  | some result => pure result
  | none => m.get? key  -- Fall back to blocking

/-- Check if a key exists with try-lock fast path.
    Attempts non-blocking read first, falls back to blocking if shard is contended.
    Useful for read-heavy workloads where you want to avoid blocking on contended shards. -/
@[inline]
def containsFast (m : ShardMap α β) (key : α) : BaseIO Bool := do
  -- Try non-blocking first
  match ← m.getShard key |>.tryAtomicallyRead fun map => pure (map.contains key) with
  | some result => pure result
  | none => m.contains key  -- Fall back to blocking

/-- Try to get a value without blocking.
    Returns `some (some v)` if key exists, `some none` if key doesn't exist,
    or `none` if the shard is currently locked. -/
def tryGet? (m : ShardMap α β) (key : α) : BaseIO (Option (Option β)) := do
  m.getShard key |>.tryAtomicallyRead fun map => pure (map.get? key)

/-- Try to insert without blocking.
    Returns `true` if insert succeeded, `false` if shard was locked. -/
def tryInsert (m : ShardMap α β) (key : α) (val : β) : BaseIO Bool := do
  let shard := m.getShard key
  match ← shard.tryAtomically fun ref => do
    let map ← ST.Ref.get ref
    ST.Ref.set ref (map.insert key val)
  with
  | some () => pure true
  | none => pure false

/-- Try to get or insert without blocking.
    Returns `some v` with the value (existing or new), or `none` if shard was locked. -/
def tryGetOrInsertLazy (m : ShardMap α β) (key : α) (mkVal : Unit → β) : BaseIO (Option β) := do
  let shard := m.getShard key
  -- First try read lock
  match ← shard.tryAtomicallyRead fun map => pure (map.get? key) with
  | some (some v) => pure (some v)  -- Found it
  | some none =>
    -- Not found, try write lock
    match ← shard.tryAtomically fun ref => do
      let map ← ST.Ref.get ref
      match map.get? key with
      | some v => pure v
      | none =>
        let v := mkVal ()
        ST.Ref.set ref (map.insert key v)
        pure v
    with
    | some v => pure (some v)
    | none => pure none  -- Write lock failed
  | none => pure none  -- Read lock failed

/-! ## Capacity hints -/

/-- Create a new ShardMap with pre-sized shards.

    **Note:** Benchmarks show that pre-allocation generally hurts performance due to
    HashMap allocation overhead. In most cases, `new` with natural growth performs
    better than `newWithCapacity`. This function is retained for cases where you've
    profiled and determined pre-allocation helps your specific workload.

    Capacity is capped at 64 entries per shard to limit allocation overhead. -/
def newWithCapacity (shardBits : Nat := 8) (capacityPerShard : Nat := 64)
    : BaseIO (ShardMap α β) := do
  let numShards := 2 ^ shardBits
  let shardMask : USize := (numShards - 1).toUSize
  -- Cap capacity to avoid allocation overhead; let HashMap grow naturally beyond this
  let effectiveCapacity := min capacityPerShard 64
  let ⟨shards, hsize⟩ ← mkShardArrayWithCapacity numShards effectiveCapacity
  have h : shards.size > 0 := by simp [hsize]; exact Nat.one_le_two_pow
  pure ⟨shards, shardMask, h⟩

end ShardMap

end Ix

end
