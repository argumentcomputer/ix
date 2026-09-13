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
  deriving Repr, BEq, ReflBEq, Hashable

instance : LawfulBEq Op := ⟨by
  deriving_LawfulEq_tactic
  intro h
  exact congrArg Op.const (eq_of_beq h)⟩

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

/-! Total recursive comparison and hashing for deduplication. The ordinary
mutual deriving handlers produce partial opaque logical defaults with
separate native workers. These definitions expose the actual algorithms to
proofs while retaining the native comparison order, hash tags and seeds. -/

private theorem Block.ctrl_lt (block : Block) : sizeOf block.ctrl < sizeOf block := by
  cases block
  simp
  omega

mutual

/-- Compare all control fields, including layout metadata and continuations. -/
def Ctrl.beq : Ctrl → Ctrl → Bool
  | .match idx cases fallback, .match idx' cases' fallback' =>
    idx == idx' && (beqBranches cases cases' && beqFallback fallback fallback')
  | .return sel outs, .return sel' outs' => sel == sel' && outs == outs'
  | .yield sel outs, .yield sel' outs' => sel == sel' && outs == outs'
  | .matchContinue idx cases fallback outputs aux lookups cont,
      .matchContinue idx' cases' fallback' outputs' aux' lookups' cont' =>
    idx == idx' && (beqBranches cases cases' && (beqFallback fallback fallback' &&
      (outputs == outputs' && (aux == aux' && (lookups == lookups' && Block.beq cont cont')))))
  | _, _ => false
termination_by left _ => (sizeOf left, 0)
decreasing_by all_goals decreasing_tactic

def Block.beq (left right : Block) : Bool :=
  left.ops == right.ops && Ctrl.beq left.ctrl right.ctrl
termination_by (sizeOf left, 0)
decreasing_by
  apply Prod.Lex.left
  exact Block.ctrl_lt left

def beqFallback : Option Block → Option Block → Bool
  | none, none => true
  | some left, some right => Block.beq left right
  | _, _ => false
termination_by left _ => (sizeOf left, 0)
decreasing_by all_goals decreasing_tactic

def beqBranches (left right : Array (G × Block)) : Bool :=
  if h : left.size = right.size then beqBranchesAux left right h left.size (Nat.le_refl _)
  else false
termination_by (sizeOf left, left.size + 1)
decreasing_by all_goals decreasing_tactic

/-- Match `Array.isEqvAux`'s reverse traversal without hiding recursive
block comparisons behind an unbounded callback. -/
def beqBranchesAux (left right : Array (G × Block)) (hsz : left.size = right.size) :
    (n : Nat) → n ≤ left.size → Bool
  | 0, _ => true
  | n + 1, h =>
    (left[n].1 == (right[n]'(hsz ▸ h)).1 && Block.beq left[n].2 (right[n]'(hsz ▸ h)).2) &&
      beqBranchesAux left right hsz n (by omega)
termination_by n _ => (sizeOf left, n)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left
       have arrayBound := Array.sizeOf_get left n (by omega)
       have pairBound : sizeOf left[n].2 < sizeOf left[n] := by
         cases left[n]; simp; omega
       omega)

end

instance : BEq Ctrl := ⟨Ctrl.beq⟩
instance : BEq Block := ⟨Block.beq⟩

mutual

/-- Boolean comparison reflects exact syntax equality. -/
theorem Ctrl.beq_eq_true_iff (left right : Ctrl) : Ctrl.beq left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp only [Ctrl.beq, Bool.and_eq_true, beq_iff_eq, reduceCtorEq, Bool.false_eq_true,
      Ctrl.match.injEq, Ctrl.return.injEq, Ctrl.yield.injEq, Ctrl.matchContinue.injEq]
  all_goals rw [beqBranches_eq_true_iff, beqFallback_eq_true_iff]
  all_goals rw [Block.beq_eq_true_iff]
termination_by (sizeOf left, 0)
decreasing_by all_goals decreasing_tactic

theorem Block.beq_eq_true_iff (left right : Block) : Block.beq left right = true ↔ left = right := by
  cases left
  cases right
  simp only [Block.beq, Bool.and_eq_true, beq_iff_eq, Block.mk.injEq]
  rw [Ctrl.beq_eq_true_iff]
termination_by (sizeOf left, 0)
decreasing_by all_goals decreasing_tactic

theorem beqFallback_eq_true_iff (left right : Option Block) :
    beqFallback left right = true ↔ left = right := by
  cases left <;> cases right <;>
    simp only [beqFallback, reduceCtorEq, Bool.false_eq_true, Option.some.injEq]
  rw [Block.beq_eq_true_iff]
termination_by (sizeOf left, 0)
decreasing_by all_goals decreasing_tactic

theorem beqBranches_eq_true_iff (left right : Array (G × Block)) :
    beqBranches left right = true ↔ left = right := by
  unfold beqBranches
  split
  next hsz =>
    rw [beqBranchesAux_eq_true_iff]
    constructor
    · intro h
      exact Array.ext hsz (fun i hi _ => h i hi)
    · intro h
      subst right
      intros
      rfl
  next hsz =>
    simp only [Bool.false_eq_true, false_iff]
    intro h
    exact hsz (congrArg Array.size h)
termination_by (sizeOf left, left.size + 1)
decreasing_by all_goals decreasing_tactic

theorem beqBranchesAux_eq_true_iff (left right : Array (G × Block))
    (hsz : left.size = right.size) (n : Nat) (hn : n ≤ left.size) :
    beqBranchesAux left right hsz n hn = true ↔
      ∀ i (hi : i < n), (left[i]'(by omega)) = (right[i]'(by omega)) := by
  cases n with
  | zero => simp [beqBranchesAux]
  | succ n =>
    rw [beqBranchesAux, Bool.and_eq_true, Bool.and_eq_true,
      beq_iff_eq, Block.beq_eq_true_iff, beqBranchesAux_eq_true_iff]
    constructor
    · rintro ⟨⟨hg, hb⟩, tail⟩ i hi
      by_cases h : i < n
      · exact tail i h
      · have : i = n := by omega
        subst i
        exact Prod.ext hg hb
    · intro h
      refine ⟨⟨congrArg Prod.fst (h n (by omega)), congrArg Prod.snd (h n (by omega))⟩, ?_⟩
      intro i hi
      exact h i (by omega)
termination_by (sizeOf left, n)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.left
       have arrayBound := Array.sizeOf_get left n (by omega)
       have pairBound : sizeOf left[n].2 < sizeOf left[n] := by
         cases left[n]; simp; omega
       omega)

end

instance : LawfulBEq Ctrl where
  eq_of_beq {left right} h := (Ctrl.beq_eq_true_iff left right).mp h
  rfl {value} := (Ctrl.beq_eq_true_iff value value).mpr rfl

instance : LawfulBEq Block where
  eq_of_beq {left right} h := (Block.beq_eq_true_iff left right).mp h
  rfl {value} := (Block.beq_eq_true_iff value value).mpr rfl

mutual

/-- Preserve the derived hash algorithm: constructor tags 0–3, array seed
7, option tags 11/13 and the original left-to-right field mixing. -/
def Ctrl.hash : Ctrl → UInt64
  | .match idx branches fallback =>
    let branchesHash := branches.attach.foldl (fun acc pair =>
      mixHash acc (mixHash (hash pair.val.1) (Block.hash pair.val.2))) 7
    let fallbackHash := match fallback with
      | none => 11
      | some block => mixHash (Block.hash block) 13
    mixHash (mixHash (mixHash 0 (hash idx)) branchesHash) fallbackHash
  | .return sel outs => mixHash (mixHash 1 (hash sel)) (hash outs)
  | .yield sel outs => mixHash (mixHash 2 (hash sel)) (hash outs)
  | .matchContinue idx branches fallback outputs aux lookups cont =>
    let branchesHash := branches.attach.foldl (fun acc pair =>
      mixHash acc (mixHash (hash pair.val.1) (Block.hash pair.val.2))) 7
    let fallbackHash := match fallback with
      | none => 11
      | some block => mixHash (Block.hash block) 13
    mixHash (mixHash (mixHash (mixHash (mixHash (mixHash (mixHash 3 (hash idx))
      branchesHash) fallbackHash) (hash outputs)) (hash aux)) (hash lookups)) (Block.hash cont)
termination_by ctrl => sizeOf ctrl
decreasing_by
  all_goals first
    | decreasing_tactic
    | (have arrayBound := Array.sizeOf_lt_of_mem pair.property
       have pairBound : sizeOf pair.val.2 < sizeOf pair.val := by
         cases pair.val; simp; omega
       simp_all
       omega)

def Block.hash (block : Block) : UInt64 :=
  mixHash (mixHash 0 (hash block.ops)) (Ctrl.hash block.ctrl)
termination_by sizeOf block
decreasing_by exact Block.ctrl_lt block

end

instance : Hashable Ctrl := ⟨Ctrl.hash⟩
instance : Hashable Block := ⟨Block.hash⟩

/-- The circuit layout of a function (non-semantic; the bytecode evaluator ignores it). -/
structure FunctionLayout where
  inputSize : Nat
  selectors : Nat
  auxiliaries : Nat
  lookups : Nat
  deriving Inhabited, Repr, BEq, ReflBEq, LawfulBEq, Hashable, DecidableEq

def FunctionLayout.width (l : FunctionLayout) : Nat :=
  l.inputSize + l.selectors + l.auxiliaries

/-- Layout-only estimate of main and stage-2 width. This lacks the control
tree, compiled lookup degrees and PCS parameters; use the built system's
`circuitShapes` for actual widths after lookup tuning. -/
def FunctionLayout.totalWidth (l : FunctionLayout) : Nat :=
  -- Stage 2 commits max(⌈L/k⌉, 1) chained partial accumulators (no message
  -- inverses); see `multi_stark::lookup::stage2_width`. Retain the original
  -- single-selector heuristic here; synthesis checks control flow and
  -- retunes using compiled degrees and the FFT cost.
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

inductive CallRank where
  | zero
  | bound
  | ordered
  deriving Inhabited, Repr, BEq

/-- A checked static component order. Equal-component calls require both
endpoints to retain dynamic ranks; all other calls increase `order`. -/
structure CallComponent where
  order : Nat
  ranked : Bool
  deriving Inhabited, Repr, BEq

structure Toplevel where
  functions : Array Function
  memorySizes : Array Nat
  /-- Circuit partition of the constrained functions, in first-occurrence
  order. Built by `Source.Toplevel.compile` (singletons by default; see
  `CompiledToplevel.groupFunctions`); empty on a freshly lowered toplevel. -/
  circuits : Array Circuit := #[]
  /-- Empty selects the general dynamic-rank layout. Otherwise there is one
  entry per function, including functions used only as unconstrained hints. -/
  callComponents : Array CallComponent := #[]
  deriving Repr

end Bytecode

end Aiur

end
