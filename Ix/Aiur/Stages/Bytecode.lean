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
  | const : Nat → Op
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
  | u8XorSplit7 : ValIdx → ValIdx → Op
  | u8XorSplit4 : ValIdx → ValIdx → Op
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
  /-- Native wrapping u32 addition. Four result bytes are advice columns; the
  carry is a fifth logical output represented by a compound expression. -/
  | unconstrainedU32Add : Array ValIdx → Array ValIdx → Op
  /-- Native wrapping three-input u32 addition, with virtual carry output. -/
  | unconstrainedU32Add3 : Array ValIdx → Array ValIdx → Array ValIdx → Op
  /-- Virtual LE-byte packing expression; allocates no auxiliary column. -/
  | u32ToField : Array ValIdx → Op
  deriving Repr, BEq, Hashable

mutual
  inductive Ctrl where
    | match : ValIdx → Array (Nat × Block) → Option Block → Ctrl
    | return : SelIdx → Array ValIdx → Ctrl
    | yield : SelIdx → Array ValIdx → Ctrl
    | matchContinue : ValIdx → Array (Nat × Block) → Option Block
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

mutual
  /-- Largest constant in a block (0 if none): `Op.const` values and match
  keys. Consumers specialize constants to a concrete field and must ERROR
  when this exceeds the field size (`maxConstant ≥ p` means the field
  cannot represent the circuit). -/
  partial def Block.maxConstant (b : Block) : Nat :=
    b.ops.foldl (fun acc op => match op with
      | .const c => max acc c
      | _ => acc) (Ctrl.maxConstant b.ctrl)

  partial def Ctrl.maxConstant : Ctrl → Nat
    | .match _ cases def? =>
      let m := cases.foldl (fun acc (c, b) => max acc (max c b.maxConstant)) 0
      match def? with | some b => max m b.maxConstant | none => m
    | .matchContinue _ cases def? _ _ _ cont =>
      let m := cases.foldl (fun acc (c, b) => max acc (max c b.maxConstant)) 0
      let m := match def? with | some b => max m b.maxConstant | none => m
      max m cont.maxConstant
    | .return _ _ | .yield _ _ => 0
end

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

/-- Specialization guard: every constant must fit the target field. Run
by each consumer (interpreter entry, FFI, codegen) before converting
constants; overflow is an ERROR — the field cannot represent the
circuit — never a silent wrap. -/
def Toplevel.checkConstants (t : Toplevel) (fieldSize : Nat) :
    Except String Unit := do
  for f in t.functions do
    let m := f.body.maxConstant
    if m ≥ fieldSize then
      throw s!"constant {m} does not fit the field (size {fieldSize}): the field cannot represent this circuit"

end Bytecode

end Aiur

end
