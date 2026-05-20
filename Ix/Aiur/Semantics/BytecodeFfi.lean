module
public import Ix.Aiur.Stages.Bytecode
public import Std.Data.HashMap

/-!
Opaque Rust FFI for bytecode execution. Split out of `Protocol.lean` so the
Lean-native reference evaluator (`Bytecode/Eval.lean`) can stand alone.

The Rust executor is the production backend; our Lean reference is the specification.
A follow-up theorem relates the two under a purity assumption on IO.
-/

public section

namespace Aiur

structure IOKeyInfo where
  idx : Nat
  len : Nat
  deriving DecidableEq

instance : BEq IOKeyInfo where
  beq a b := a.idx == b.idx && a.len == b.len

instance : LawfulBEq IOKeyInfo where
  eq_of_beq {a b} h := by
    simp [BEq.beq, Bool.and_eq_true] at h
    cases a; cases b; simp_all
  rfl {a} := by simp [BEq.beq]

structure IOBuffer where
  data : Array G
  map : Std.HashMap (Array G) IOKeyInfo
  deriving Inhabited

def IOBuffer.extend (ioBuffer : IOBuffer) (key data : Array G) : IOBuffer :=
  let idx := ioBuffer.data.size
  let len := data.size
  { ioBuffer with
    data := ioBuffer.data ++ data
    map := ioBuffer.map.insert key { idx, len } }

instance : BEq IOBuffer where
  beq x y :=
    x.data == y.data && @BEq.beq _ Std.HashMap.instBEq x.map y.map

-- A `LawfulBEq IOBuffer` instance is not provided here. The reflexivity/
-- symmetry/transitivity facts needed downstream (`IOBuffer.equiv_refl`,
-- `_symm`, `_trans`) are proved directly in `Ix/Aiur/Proofs/IOBufferEquiv.lean`
-- via `Std.HashMap.beq_iff_equiv` + `Std.HashMap.Equiv.{refl,symm,trans}`,
-- bypassing the need for `LawfulBEq` on the outer `IOBuffer`.

namespace Bytecode.Toplevel

/-- Per-split execution stats for one return-group of one function.
`groupIdx` keys the corresponding entry in `Function.groupNames`. -/
structure GroupStats where
  groupIdx : Nat
  totalWidth : Nat
  uniqueRows : Nat
  totalHits : Nat
  deriving Inhabited, Repr

/-- Per-memory-size counts. `uniqueRows` is the trace height; `totalHits`
is the sum of multiplicities. `totalHits - uniqueRows` is the cache-hit
count. -/
structure MemoryCount where
  uniqueRows : Nat
  totalHits : Nat
  deriving Inhabited, Repr

/-- Per-function execution stats. Outer index is `FunIdx`; inner index is
the `USize` group index used by `Ctrl.return`. -/
abbrev FunctionStats := Array (Array GroupStats)

/-- Per-memory-size counts, parallel to `Toplevel.memorySizes`. -/
abbrev MemoryCounts := Array MemoryCount

/-- Query counts shipped back from the Rust executor. -/
structure QueryCounts where
  functionStats : FunctionStats
  memoryCounts : MemoryCounts
  deriving Inhabited

/-- Raw FFI tuple shape — kept tuple-flat so the Rust side can build it
without declaring matching Lean structure ctors. `execute` wraps the
result in the structured `QueryCounts` immediately. -/
@[extern "rs_aiur_toplevel_execute"]
private opaque execute' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& Array G → (ioData : @& Array G) →
  (ioMap : @& Array (Array G × IOKeyInfo)) →
    Except String (Array G × (Array G × Array (Array G × IOKeyInfo))
      × (Array (Array (Nat × Nat × Nat × Nat)) × Array (Nat × Nat)))

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
returning the raw output of the function, the updated `IOBuffer`, and a
`QueryCounts`. Returns `Except.error msg` when execution fails (e.g.
`assert_eq!` mismatch from a typechecker rejecting a constant), so callers
can recover instead of crashing. -/
def execute (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Except String (Array G × IOBuffer × QueryCounts) :=
  let ioData := ioBuffer.data
  let ioMap := ioBuffer.map
  match execute' toplevel funIdx args ioData ioMap.toArray with
  | .error e => .error e
  | .ok (output, (ioData, ioMap), rawFn, rawMem) =>
    let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
    let functionStats : FunctionStats := rawFn.map fun perFn =>
      perFn.map fun quad =>
        { groupIdx := quad.1, totalWidth := quad.2.1,
          uniqueRows := quad.2.2.1, totalHits := quad.2.2.2 }
    let memoryCounts : MemoryCounts := rawMem.map fun pair =>
      { uniqueRows := pair.1, totalHits := pair.2 }
    .ok (output, ⟨ioData, ioMap⟩, { functionStats, memoryCounts })

end Bytecode.Toplevel

end Aiur

end
