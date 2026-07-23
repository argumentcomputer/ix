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
  | assertEq : Array ValIdx → Array ValIdx → Op
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

/-- Number of consecutive lookups covered by each step of multi-stark's
partial-accumulator chain (logup message grouping). Must mirror
`LOOKUP_GROUP_SIZE` in `crates/aiur/src/synthesis.rs`. -/
def lookupGroupSize : Nat := 2

/-- Stage-2 (logup) width in extension-field columns: the accumulator plus
one partial-accumulator column per lookup group after the first, i.e.
`max 1 ⌈lookups / lookupGroupSize⌉`. Mirrors multi-stark's
`LookupAir::stage_2_width`. -/
def stage2ExtensionWidth (lookups : Nat) : Nat :=
  max 1 ((lookups + lookupGroupSize - 1) / lookupGroupSize)

def FunctionLayout.totalWidth (l : FunctionLayout) : Nat :=
  l.width + G.extensionDegree * stage2ExtensionWidth l.lookups

structure Function where
  body : Block
  layout: FunctionLayout
  entry : Bool
  constrained : Bool
  deriving Inhabited, Repr

structure Toplevel where
  functions : Array Function
  memorySizes : Array Nat
  deriving Repr

end Bytecode

end Aiur

end
