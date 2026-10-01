module

public import ConLeche.Kernel.Inductives.StructParts

@[expose] public section

/-!
# The block's shape record and its readers (task #175, kept for the one route)

`InductiveShape` is the shape every block on the fixpoint route is
read into (`nativeShape?`, `ConLeche/Kernel/Inductives/NativeParts.lean`,
extends it with the fields' kinds).  The sum route that named it was
deleted at task #210 Part C; the recognition helpers below are the
one route's.  Historically a **direct sum** was a non-recursive,
non-nested inductive with **any number of constructors other than
one**, or an **indexed family** with any number of constructors:
enumerations (`Bool`, `Ordering`), option- and sum-like types
(`Option`, `Sum`, `Decidable`), propositional disjunctions (`Or`), the
empty inductives (zero constructors), and the index-carrying families
(`Eq`-shaped propositions, `Vector`-like non-recursive families,
`SigmaHom`).  The single-constructor index-free class is the direct
*structure* route (`ConLeche/Kernel/Inductives/StructParts.lean`), which keeps its
projection table, eta and unit-likeness; nothing here has those (the
official kernel's `is_structure_like` needs one constructor AND no
index), so the two routes are disjoint and this recogniser rejects
`n = 1 ∧ nIdx = 0` outright.

The model is the **tagged disjoint union** of one tuple tower per
constructor (`ConLeche/SetModel/TaggedSum.lean`), the family's carrier
at an index tuple being the union of the towers RESTRICTED to the
index equation `e⃗_k f⃗ = ı⃗` (one extra proof-field per constructor,
`ConLeche/Semantics/Tower/SumLeaf.lean`): a value is the pair of a
numeral tag (the constructor's index) and the constructor's tower;
the recursor cases on the tag.  Installation is the direct route's
(`ConLeche/Kernel/Inductives/SumInstall.lean`): the reference checks alone,
no `_model` artifact consumed, the recursor generated and compared
(task #175 S2 — `structRecTyI`/`structRecRhs`).

The checks mirror the reference kernels' inductive-declaration checks
restricted to this class (lean4lean `Lean4Lean/Inductive/Add.lean`,
the official `inductive.cpp`):

* the type former's type is a `∀`-telescope of exactly
  `numParams + numIndices` binders ending in a `Sort`;
* every constructor's type is a `∀`-telescope whose first `numParams`
  binders are the parameters, ending in the type former applied to
  exactly those parameters followed by `numIndices` index expressions
  (`isValidIndAppIdx`); the parameter domains are pinned
  definitionally at install (`checkStructDomsAt`);
* no recursive occurrence: every constructor binder domain resolves
  in the pre-block environment (`sumNonRec`), which subsumes
  positivity for this class and is what the model construction needs;
* the recursor is `T.rec` with `numIndices` indices, one motive, one
  minor per constructor (`rulePrefix = numParams + 1 + n`, `majorIdx =
  rulePrefix + numIndices`), one rule per constructor in constructor
  order whose right-hand side is
  `λ p⃗ motive minor⃗ f⃗_j, minor_j f⃗_j` (`mkRecRules`); the large
  eliminator carries a fresh elimination level parameter in front of
  the block's, the small one the block's own.  The recursor's *type*
  is not pinned here: it is generated and compared at install (S2).
* **the elimination restriction** (official `elim_only_at_universe_zero`):
  an inductive whose result sort is not provably nonzero
  (`Level.isNeverZero`) and which has two or more constructors
  eliminates into `Prop` only — a large eliminator on such a block is
  rejected at install (`checkSum`); with ONE constructor every
  field that is not a proposition must be one of the residual's index
  expressions (`checkStructFieldSortsI`, official's subsingleton-
  elimination criterion — `Eq`'s rule).  This is the rule that keeps
  the model's iota law consistent: at a squash instantiation every
  constructor value is the proof point, and two rules firing to two
  different minors on the same value would contradict each other;
  with one constructor the recursor reads the data fields off the
  index arguments instead of the (squashed) value.
-/

namespace ConLeche

/-- The pieces of a recognised direct sum block. -/
structure InductiveShape where
  /-- the type former -/
  cvT : ConstantVal
  /-- the constructors in declaration order, each with its field count -/
  ctors : List (ConstantVal × Nat)
  /-- parameter count -/
  nP : Nat
  /-- index count (task #175 indexed; `0` at a plain sum) -/
  nIdx : Nat
  /-- the recursor -/
  cvR : ConstantVal
  /-- the recursor's fresh elimination level parameter (`large` only;
  `.anonymous` for a small eliminator) -/
  elim : Name
  /-- the result sort -/
  resSort : Level
  /-- the rules' right-hand sides as exported, in constructor order -/
  rhss : List Expr
  /-- large eliminator (a fresh elimination level parameter in front) -/
  large : Bool
  /-- the result sort is provably `Prop` -/
  isProp : Bool
  deriving Repr

/-- The block's members after the type former: the constructors, then
the closing recursor. -/
def sumSplit : List ConstantInfo →
    Option (List (ConstantVal × Nat × Nat) × ConstantVal × Nat × Nat × List RecRule)
  | [.recInfo cvR mI rP rules] => some ([], cvR, mI, rP, rules)
  | .ctorInfo cvC nP nF :: rest =>
    (sumSplit rest).map fun q => ((cvC, nP, nF) :: q.1, q.2)
  | _ => none

/-- The record completed with the former's result sort (task #195):
the install stage reads the sort off the checked telescope — the
declared one, or official's whnf'd one — and every later stage runs
on this record.  `isProp` is recomputed so that the recogniser's
invariant `isProp = (isEquiv resSort zero == some true)` holds by
definition. -/
def InductiveShape.withSort (p : InductiveShape) (s : Level) : InductiveShape :=
  { p with resSort := s, isProp := Level.isEquiv s .zero == some true }

@[simp] theorem InductiveShape.withSort_cvT (p : InductiveShape) (s : Level) :
    (p.withSort s).cvT = p.cvT := rfl
@[simp] theorem InductiveShape.withSort_ctors (p : InductiveShape) (s : Level) :
    (p.withSort s).ctors = p.ctors := rfl
@[simp] theorem InductiveShape.withSort_nP (p : InductiveShape) (s : Level) :
    (p.withSort s).nP = p.nP := rfl
@[simp] theorem InductiveShape.withSort_nIdx (p : InductiveShape) (s : Level) :
    (p.withSort s).nIdx = p.nIdx := rfl
/-- Completing a record that already carries its own sort (with the
`isProp` flag the recogniser pinned) changes nothing (task #188: the
recursive route's recogniser reads the telescope syntactically). -/
theorem InductiveShape.withSort_self (p : InductiveShape)
    (h : p.isProp = (Level.isEquiv p.resSort .zero == some true)) :
    p.withSort p.resSort = p := by
  cases p with
  | mk cvT ctors nP nIdx cvR elim resSort rhss large isProp =>
    simp only [InductiveShape.withSort]
    simp only at h
    rw [← h]
@[simp] theorem InductiveShape.withSort_cvR (p : InductiveShape) (s : Level) :
    (p.withSort s).cvR = p.cvR := rfl
@[simp] theorem InductiveShape.withSort_elim (p : InductiveShape) (s : Level) :
    (p.withSort s).elim = p.elim := rfl
@[simp] theorem InductiveShape.withSort_resSort (p : InductiveShape) (s : Level) :
    (p.withSort s).resSort = s := rfl
@[simp] theorem InductiveShape.withSort_rhss (p : InductiveShape) (s : Level) :
    (p.withSort s).rhss = p.rhss := rfl
@[simp] theorem InductiveShape.withSort_large (p : InductiveShape) (s : Level) :
    (p.withSort s).large = p.large := rfl
@[simp] theorem InductiveShape.withSort_isProp (p : InductiveShape) (s : Level) :
    (p.withSort s).isProp = (Level.isEquiv s .zero == some true) := rfl

end ConLeche
