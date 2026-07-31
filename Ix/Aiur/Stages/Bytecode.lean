module
public import Ix.Aiur.Goldilocks

/-!
Stage 5 (Bytecode) IR — flat, post-lowering.

Later passes (`deduplicate`, `needsCircuit`) produce Stage 6 bytecode with the
same datatype.
-/

public section

namespace Aiur

namespace Bytecode

abbrev FunIdx := Nat
abbrev ValIdx := Nat
abbrev SelIdx := Nat

inductive Op
  | const : G → Op
  | add : ValIdx → ValIdx → Op
  | sub : ValIdx → ValIdx → Op
  | mul : ValIdx → ValIdx → Op
  | eqZero : ValIdx → Op
  | call : FunIdx → Array ValIdx → (outputSize : Nat) → (unconstrained : Bool) → Op
  | store : Array ValIdx → Op
  | load : (size : Nat) → ValIdx → Op
  | assertEq : Array ValIdx → Array ValIdx → Option String → Op
  | ioGetInfo : ValIdx → Array ValIdx → Op
  | ioSetInfo : ValIdx → Array ValIdx → ValIdx → ValIdx → Op
  | ioRead : ValIdx → ValIdx → Nat → Op
  | ioWrite : ValIdx → Array ValIdx → Op
  | u8BitDecomposition : ValIdx → Op
  | u8ShiftLeft : ValIdx → Op
  | u8ShiftRight : ValIdx → Op
  | u8Xor : ValIdx → ValIdx → Op
  | u8Add : ValIdx → ValIdx → Op
  | u8Mul : ValIdx → ValIdx → Op
  | u8Sub : ValIdx → ValIdx → Op
  | u8And : ValIdx → ValIdx → Op
  | u8Or : ValIdx → ValIdx → Op
  | u8LessThan : ValIdx → ValIdx → Op
  | u32LessThan : ValIdx → ValIdx → Op
  | u8ChainRotr7 : ValIdx → ValIdx → Op
  | u8ChainRotr4 : ValIdx → ValIdx → Op
  | debug : String → Option (Array ValIdx) → Op
  /-- Range-check the two values into `[0, 256)` via the byte chip. Produces no
  new values: it is a pure side-effect (lookup), and its `u8` results alias the
  two inputs. Kept last so its FFI tag (27) doesn't shift the others. -/
  | u8RangeCheck : ValIdx → ValIdx → Op
  /-- Unconstrained LE byte-list division-modulo hint. Inputs are pointers to
  two `List<U64>` (klimbs) values. Produces 2 fresh pointer values
  `(q_ptr, r_ptr)` to newly-built `List<U64>` values such that `q*b + r = a`
  and `0 ≤ r < b` (when `b > 0`). No constraint relation emitted; caller
  must verify in constrained code. -/
  | unconstrainedBigUintDivMod : ValIdx → ValIdx → Op
  /-- Unconstrained hint: the 8 LE bytes of a field element's canonical `u64`
  value. 8 fresh auxiliary values, no constraint relation, no lookup; the
  caller must range-check, recompose-assert, and canonicality-assert.
  Appended last so the existing FFI tags don't shift (tag 29). -/
  | unconstrainedGToBytes : ValIdx → Op
  /-- Unconstrained hint: the field inverse of a value (`0 ↦ 0`). One fresh
  auxiliary value, no constraint relation; the caller must pin it via
  multiply-and-assert. Appended last (tag 30). -/
  | unconstrainedGInverse : ValIdx → Op
  deriving Repr, BEq, Hashable

mutual
  inductive Ctrl where
    | match : ValIdx → Array (G × Block) → Option Block → Ctrl
    | return : SelIdx → Array ValIdx → Ctrl
    | yield : SelIdx → Array ValIdx → Ctrl
    | matchContinue : ValIdx → Array (G × Block) → Option Block
        → (outputSize : Nat) → (sharedAuxiliaries : Nat) → (sharedLookups : Nat)
        → Block → Ctrl
    deriving Inhabited, Repr

  structure Block where
    ops : Array Op
    ctrl : Ctrl
    deriving Inhabited, Repr
end

deriving instance BEq, Hashable for Ctrl, Block


/-- The circuit layout of a function (non-semantic; the bytecode evaluator ignores it). -/
structure FunctionLayout where
  inputSize : Nat
  selectors : Nat
  auxiliaries : Nat
  lookups : Nat
  deriving Inhabited, Repr, BEq, Hashable, DecidableEq

def FunctionLayout.width (l : FunctionLayout) : Nat :=
  l.inputSize + l.selectors + l.auxiliaries

def FunctionLayout.totalWidth (l : FunctionLayout) : Nat :=
  -- Stage 2 commits max(⌈L/k⌉, 1) chained partial accumulators (no message
  -- inverses); see `multi_stark::lookup::stage2_width`. Mirrors the
  -- synthesis grouping rule (`crates/aiur/src/synthesis.rs`): branchless
  -- functions (one selector) have raw degree-1 lookup arguments, so their
  -- lookups are grouped 2 per accumulator step.
  let slots := if l.selectors == 1 && l.lookups >= 2
    then (l.lookups + 1) / 2
    else max l.lookups 1
  l.width + G.extensionDegree * slots

structure Function where
  body : Block
  layout: FunctionLayout
  entry : Bool
  constrained : Bool
  deriving Inhabited, Repr

/-- A circuit of the proving system, backing one or more functions. By
default every constrained function gets a singleton circuit named after it;
`CompiledToplevel.groupFunctions` can regroup several functions into one
circuit whose branching selects the member function. `layout` is the merged
layout: max `inputSize`, sum of `selectors`, max `auxiliaries` (which
includes the single shared multiplicity column), max `lookups` (slot 0 is
the shared return lookup). -/
structure Circuit where
  name : String
  members : Array FunIdx
  layout : FunctionLayout
  deriving Inhabited, Repr

/-- Merged layout of a group of functions (see `Circuit`). -/
def FunctionLayout.merge (a b : FunctionLayout) : FunctionLayout where
  inputSize := a.inputSize.max b.inputSize
  selectors := a.selectors + b.selectors
  auxiliaries := a.auxiliaries.max b.auxiliaries
  lookups := a.lookups.max b.lookups

structure Toplevel where
  functions : Array Function
  memorySizes : Array Nat
  /-- Circuit partition of the constrained functions, in first-occurrence
  order. Built by `Source.Toplevel.compile` (singletons by default; see
  `CompiledToplevel.groupFunctions`); empty on a freshly lowered toplevel. -/
  circuits : Array Circuit := #[]
  deriving Repr

end Bytecode

end Aiur

end
