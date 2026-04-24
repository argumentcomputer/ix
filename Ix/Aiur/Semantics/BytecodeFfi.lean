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

@[extern "rs_aiur_toplevel_execute"]
private opaque execute' : @& Bytecode.Toplevel →
  @& Bytecode.FunIdx → @& Array G → (ioData : @& Array G) →
  (ioMap : @& Array (Array G × IOKeyInfo)) →
    Array G × (Array G × Array (Array G × IOKeyInfo)) × Array Nat

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
returning the raw output of the function, the updated `IOBuffer`, and an array
of query counts (one per function circuit, then one per memory size). -/
def execute (toplevel : @& Bytecode.Toplevel)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × IOBuffer × Array Nat :=
  let ioData := ioBuffer.data
  let ioMap := ioBuffer.map
  let (output, (ioData, ioMap), queryCounts) := execute' toplevel funIdx args
    ioData ioMap.toArray
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (output, ⟨ioData, ioMap⟩, queryCounts)

end Bytecode.Toplevel

end Aiur

end -- public section
