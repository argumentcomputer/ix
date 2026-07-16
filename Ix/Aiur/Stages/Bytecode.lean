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

abbrev goldilocksExtensionDegree : Nat := 2

def FunctionLayout.totalWidth (l : FunctionLayout) : Nat :=
  l.width + goldilocksExtensionDegree * (1 + l.lookups)

structure Function where
  body : Block
  layout: FunctionLayout
  entry : Bool
  constrained : Bool
  /-- Circuit-group tag from the `#[group=...]` pragma. Functions sharing a
  tag are proven by a single grouped circuit. Non-semantic: the bytecode
  evaluator ignores it, and deduplication keeps differently-tagged functions
  apart. Declared last so the FFI object-field indices of `body`/`layout`
  stay 0/1. -/
  group : Option String := none
  deriving Inhabited, Repr

/-- A circuit of the proving system, backing one or more functions. Ungrouped
functions get a singleton circuit named after the function; functions sharing
a `#[group=...]` tag get one circuit named after the group, whose branching
selects the member function. `layout` is the merged layout: max `inputSize`,
sum of `selectors`, max `auxiliaries` (which includes the single shared
multiplicity column), max `lookups` (slot 0 is the shared return lookup). -/
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
  order. Built by `Source.Toplevel.compile` after deduplication; empty on a
  freshly lowered toplevel. -/
  circuits : Array Circuit := #[]
  deriving Repr

end Bytecode

end Aiur

end
