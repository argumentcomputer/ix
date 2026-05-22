module
public import Ix.Aiur.Goldilocks

/-!
Stage 5 (Bytecode) IR — flat, post-lowering.

Later passes (`deduplicate`, `needsCircuit`) produce Stage 6 bytecode with the
same datatype.
-/

public section
@[expose] section

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
  | ioGetInfo : Array ValIdx → Op
  | ioSetInfo : Array ValIdx → ValIdx → ValIdx → Op
  | ioRead : ValIdx → Nat → Op
  | ioWrite : Array ValIdx → Op
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
  deriving Repr, Hashable, DecidableEq

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

deriving instance Hashable for Ctrl, Block


-- Manual mutual `BEq Block` / `BEq Ctrl` via `Array.attach` for termination
-- through nested `Array (G × Block)`. Each element carries `h : (k, b) ∈ br`,
-- giving `sizeOf b < sizeOf br` via `Array.sizeOf_lt_of_mem`. Derived
-- `deriving BEq` for this mutual-nested shape is opaque (see TACTICS.md §
-- "Nested-inductive deriving BEq is opaque") — the manual version below is
-- reducible in proofs.

mutual
  def Ctrl.beq : Ctrl → Ctrl → Bool
    | .return s₁ v₁, .return s₂ v₂ => s₁ == s₂ && v₁ == v₂
    | .yield s₁ v₁, .yield s₂ v₂ => s₁ == s₂ && v₁ == v₂
    | .match v₁ br₁ none, .match v₂ br₂ none =>
      v₁ == v₂ && Ctrl.beqBranches br₁.toList br₂.toList
    | .match v₁ br₁ (some b₁), .match v₂ br₂ (some b₂) =>
      v₁ == v₂ && Ctrl.beqBranches br₁.toList br₂.toList && Block.beq b₁ b₂
    | .matchContinue v₁ br₁ none o₁ sa₁ sl₁ k₁,
      .matchContinue v₂ br₂ none o₂ sa₂ sl₂ k₂ =>
      v₁ == v₂ && o₁ == o₂ && sa₁ == sa₂ && sl₁ == sl₂ &&
      Ctrl.beqBranches br₁.toList br₂.toList &&
      Block.beq k₁ k₂
    | .matchContinue v₁ br₁ (some b₁) o₁ sa₁ sl₁ k₁,
      .matchContinue v₂ br₂ (some b₂) o₂ sa₂ sl₂ k₂ =>
      v₁ == v₂ && o₁ == o₂ && sa₁ == sa₂ && sl₁ == sl₂ &&
      Ctrl.beqBranches br₁.toList br₂.toList &&
      Block.beq b₁ b₂ &&
      Block.beq k₁ k₂
    | _, _ => false
  def Ctrl.beqBranches : List (G × Block) → List (G × Block) → Bool
    | [], [] => true
    | (k₁, b₁) :: rest₁, (k₂, b₂) :: rest₂ =>
      k₁ == k₂ && Block.beq b₁ b₂ && Ctrl.beqBranches rest₁ rest₂
    | _, _ => false
  def Block.beq : Block → Block → Bool
    | ⟨ops₁, ctrl₁⟩, ⟨ops₂, ctrl₂⟩ => ops₁ == ops₂ && Ctrl.beq ctrl₁ ctrl₂
end

instance : BEq Ctrl := ⟨Ctrl.beq⟩
instance : BEq Block := ⟨Block.beq⟩


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
  deriving Inhabited, Repr

structure Toplevel where
  functions : Array Function
  memorySizes : Array Nat
  deriving Repr

end Bytecode

end Aiur

end -- @[expose] section
end
