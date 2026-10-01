module

public import ConLeche.Verify.Shift

public section

/-!
# The cached representation's field facts (task #163; rewritten at #172
B3a)

This module used to be the *seam floor*: an erasure `eraseC : Expr →
Expr`, its injectivity on the field invariant `WFc`, field exactness
conditioned on `WFc`, and a normal-form characterization of a
hash-checking equality — everything needed to relate a second
expression type to the spec's one.

**There is no seam.**  `Expr` is `ConLeche.Expr` and the four derived
data are its `@[computed_field]`s, so what is left is the three facts
the cached operations actually consume, each now unconditional:

* **field exactness** — `bvarB_eq`, `fvarB_eq`, `hasLP_eq`: the
  computed fields *are* the spec functions `Expr.bvarBound`,
  `Expr.fvarRange`, `Expr.hasLevelParam`.  Same recurrence, one
  written in a `with` block and one as an ordinary definition, so
  every cutoff the cached operations take is the cutoff the spec
  takes;
* **the cutoff consequences** — `bvarB_le`, `fvarB_le`, `hasLP_false`:
  a field at or below the cursor licenses the skip;
* **equality** — `beq` is `decide (· = ·)`, so the `EquivBEq` and
  `LawfulHashable` premises of the `Std.HashMap` lemmas are the
  standard ones, and `beq_iff` is `beq_iff_eq`.

Deleted with the seam: `eraseC` and `eraseC_inj`, `hashSpec` and
`hash_exact`, `zeroC`/`beqSpec_iff_zeroC` and the whole normal-form
apparatus, `MemoErase`/`toExprGo_spec`/`toExpr_eq` (there is no
readback).  847 lines to this.

**Task #172 B3b**: `WFc` itself is gone — the six direct-parse capstone
letters it survived for are restated over `List Declaration` — so the
lemmas below take no invariant argument, the six `WFc.*_inv`
inversions are deleted (a node's children need no certificate), and
what is left is exactly three field equations and their two cutoff
consequences.
-/

namespace ConLeche.Expr

/-! ## Field exactness

The same exactness the arena's `TWF.bvarBoundD_exact2` /
`fvarRangeD_exact2` / `ehasParamD_exact2` provide for the parallel
arrays — without the arrays, and without a hypothesis.

Since task #167 the two range fields are *packed* and **saturate** at
`satRange` (`Kernel/Expr.lean`), so the exactness argument runs in two
steps and lands on the same unconditional equations:

1. `bvarBRaw_exact` / `fvarBRaw_exact` — the stored field is the spec
   function **below saturation** (an induction on the packed word's
   per-constructor equations);
2. `bvarBoundMemo_eq` / `fvarRangeMemo_eq` — the saturated branch's
   memoized recomputation is the spec function *everywhere*.

Their conjunction is `bvarB_eq` / `fvarB_eq` **verbatim as before**:
saturation is a representation decision, so no statement below it
moves and no skip site grows a guard. -/

/-! ### Exactness below saturation -/

/-! ### The saturated branch: the memoized walks are the spec functions

The memo invariant is the usual one — every stored answer is the spec
function of its key — and the walks preserve it. -/

/-! ### The unconditional field equations -/

/-- Cutoff consequence: a bound at or below the cursor certifies
`looseBVarsBounded` (the transposition of `TWF.bvarBoundD_le2`). -/
theorem bvarB_le {e : Expr} {d : Nat} (hle : e.bvarB ≤ d) :
    Expr.looseBVarsBounded d e = true :=
  Expr.looseBVarsBounded_iff.mpr (bvarB_eq e ▸ hle)

/-- Cutoff consequence: a range at or below the base certifies
`Expr.fvarsBelow` — the predicate the abstraction traversals consume
(`abstractRange_eq_self`); the transposition of `TWF.fvarRangeD_le`. -/
theorem fvarB_le {e : Expr} {d : Nat} (hle : e.fvarB ≤ d) :
    Expr.fvarsBelow d e :=
  Expr.fvarsBelow_iff.mpr (fvarB_eq e ▸ hle)

/-! ### Has-level-param -/

/-- The node-level walk is the kernel's `Level.hasParam`. -/
theorem levelHasParam_eq : ∀ u : Level, levelHasParam u = u.hasParam := by
  intro u
  induction u <;> simp_all [levelHasParam, Level.hasParam]

/-- …and its list fold is `List.any`. -/
theorem levelsHaveParam_eq : ∀ us : List Level,
    levelsHaveParam us = us.any Level.hasParam := by
  intro us
  induction us with
  | nil => rfl
  | cons u us ih => simp [levelsHaveParam, List.any_cons, levelHasParam_eq, ih]

/-- The `hasLP` field is `Expr.hasLevelParam`. -/
theorem hasLP_eq : ∀ e : Expr, e.hasLP = Expr.hasLevelParam e := by
  intro e
  induction e <;>
    simp_all [Expr.hasLevelParam, levelHasParam_eq, levelsHaveParam_eq]

/-- Invisibility consequence: level instantiation is the identity on a
node whose flag is off (the `O(1)` shortcut every `instLevelParams`
traversal takes). -/
theorem hasLP_false {e : Expr} {ks : List Name} {us : List Level}
    (h : e.hasLP = false) :
    e.instantiateLevelParams ks us = e :=
  Expr.instantiateLevelParams_eq_self (by rw [← hasLP_eq e, h])

/-! ## Equality

`beq` is `decide (· = ·)` (`ConLeche/Kernel/Expr.lean`): with the hash a
*function* of the node there is nothing for the old `beqSpec`/`zeroC`
normal-form apparatus to say.  It existed only to characterize a
descent that compared *stored* hashes, which could disagree with the
term. -/

/-- `beq` in its unfolded form decides equality. -/
theorem beq_eq {a b : Expr} (h : Expr.beq a b = true) : a = b :=
  of_decide_eq_true h

/-- …and is reflexive there. -/
@[simp] theorem beq_self (a : Expr) : Expr.beq a a = true := by
  simp [Expr.beq]

/-- Soundness of a decided equality — the form the memo proofs
consume (a memo hit's key is only `BEq`-equal to the query). -/
theorem beq_sound {a b : Expr} (h : (a == b) = true) : a = b :=
  eq_of_beq h

/-- Equality is an equivalence — the `Std.HashMap` lemmas' first
premise (an instance, so every memo-preservation proof gets it for
free). -/
instance : EquivBEq Expr where
  symm h := by rw [eq_of_beq h]; exact beq_self_eq_true _
  trans hab hbc := by rw [eq_of_beq hab]; exact hbc
  rfl := beq_self_eq_true _

/-- The `O(1)` `Hashable` instance (the computed field) is lawful for
it — the `Std.HashMap` lemmas' second premise. -/
instance : LawfulHashable Expr where
  hash_eq _ _ h := by rw [eq_of_beq h]

/-- Decided equality **is** equality.  (Before B3a the `←` direction
needed `WFc` on both sides — `eraseC_inj` — because distinct field
blocks could erase alike; B3b deleted the hypotheses with the
invariant.) -/
theorem beq_iff {a b : Expr} : (a == b) = true ↔ a = b := beq_iff_eq

end ConLeche.Expr
