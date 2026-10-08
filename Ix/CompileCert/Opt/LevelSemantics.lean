import Ix.CompileCert.Opt.LevelTransport
import Ix.CompileCert.Translate

/-!
# Semantic level normalization: a proved fragment and an independent check bridge

Every successfully evaluated parameter-free level normalizes to a numeral shape. The actual
smart constructors take their numeric branches before any cached equality in this fragment,
so its semantic result holds with arbitrary cached fields. The fragment is a helper theorem,
not a replacement for the original compiler domain or its polymorphic obligation.

`CheckedIxLevelEq` connects the existing independent structural level export and semantic
checker to `ixLevelEval` under the same source/wire/target valuations. It does not add a check
to the compiler, assume one as a final law, or prove all smart results pass it.
`LevelRefinement` extends the scalar evaluation bridge to polymorphic normalization and
substitution with structural comparisons. Source ingestion, referenced-spine arity, the
general term-conversion bridge, capture avoidance and runtime/core refinements remain open.
-/

namespace Ix.CompileCert.Opt

open Ix (Name Level)
open Ix.Compile.Canon (levelPeelSucc levelExplicitOffset levelMaxSmart levelImaxSmart normalizeLevel
  substLevel)

/-- A numeral-shaped level, with no condition on any cached field. -/
inductive NumericLevel : Level → Nat → Prop where
  | zero (hash : Address) : NumericLevel (.zero hash) 0
  | succ {l : Level} {n : Nat} (hash : Address) : NumericLevel l n →
      NumericLevel (.succ l hash) (n + 1)

theorem NumericLevel.peel {l : Level} {n : Nat} (h : NumericLevel l n) :
    ∃ hash, levelPeelSucc l = (.zero hash, n) := by
  induction h with
  | zero hash => exact ⟨hash, rfl⟩
  | succ hash h ih =>
    obtain ⟨base, hb⟩ := ih
    exact ⟨base, by simp [levelPeelSucc, hb]⟩

theorem NumericLevel.explicit {l : Level} {n : Nat} (h : NumericLevel l n) :
    levelExplicitOffset l = some n := by
  obtain ⟨hash, hp⟩ := h.peel
  simp only [levelExplicitOffset, hp]

theorem NumericLevel.eval (φ : Lean.Name → Nat) {l : Level} {n : Nat}
    (h : NumericLevel l n) : ixLevelEval φ l = some n := by
  induction h with
  | zero hash => rfl
  | succ hash h ih => simp only [ixLevelEval, ih, bind, Option.bind, pure]

/-- Numeral inputs take the explicit-offset branch before every hash comparison. -/
theorem levelMaxSmart_numeric {x y : Level} {a b : Nat}
    (hx : NumericLevel x a) (hy : NumericLevel y b) :
    NumericLevel (levelMaxSmart x y) (max a b) := by
  simp only [levelMaxSmart, hx.explicit, hy.explicit]
  split
  · rename_i h
    simpa only [Nat.max_eq_left h] using hx
  · rename_i h
    simpa only [Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))] using hy

/-- The numeral `imax` branches also avoid hash-based shortcuts. -/
theorem levelImaxSmart_numeric {x y : Level} {a b : Nat}
    (hx : NumericLevel x a) (hy : NumericLevel y b) :
    NumericLevel (levelImaxSmart x y) (if b = 0 then 0 else max a b) := by
  cases hy with
  | zero hash => exact .zero hash
  | succ hash h =>
    simpa only [levelImaxSmart, Nat.add_one_ne_zero, ↓reduceIte] using
      levelMaxSmart_numeric hx (NumericLevel.succ hash h)

/-- A successfully evaluated parameter-free level normalizes to a numeral shape. This proof
uses actual smart-helper branches; it introduces no cached-equality soundness hypothesis. -/
theorem normalizeLevel_numeric (φ : Lean.Name → Nat) :
    ∀ (l : Level) (n : Nat), LevelParamFree l → ixLevelEval φ l = some n →
      NumericLevel (normalizeLevel l) n
  | .zero hash, n, _, h => by
    have : 0 = n := Option.some.inj h
    subst n
    exact .zero hash
  | .param .., _, h, _ => False.elim h
  | .mvar .., _, _, h => by cases h
  | .succ l hash, n, free, h => by
    cases he : ixLevelEval φ l with
    | none => simp [ixLevelEval, he] at h
    | some a =>
      have hn : a + 1 = n := by simpa [ixLevelEval, he] using h
      subst n
      exact NumericLevel.succ _ (normalizeLevel_numeric φ l a free he)
  | .max x y hash, n, free, h => by
    cases hx : ixLevelEval φ x with
    | none => simp [ixLevelEval, hx] at h
    | some a =>
      cases hy : ixLevelEval φ y with
      | none => simp [ixLevelEval, hx, hy] at h
      | some b =>
        have hn : max a b = n := by simpa [ixLevelEval, hx, hy] using h
        subst n
        exact levelMaxSmart_numeric (normalizeLevel_numeric φ x a free.1 hx)
          (normalizeLevel_numeric φ y b free.2 hy)
  | .imax x y hash, n, free, h => by
    cases hx : ixLevelEval φ x with
    | none => simp [ixLevelEval, hx] at h
    | some a =>
      cases hy : ixLevelEval φ y with
      | none => simp [ixLevelEval, hx, hy] at h
      | some b =>
        have hn : (if b = 0 then 0 else max a b) = n := by
          simpa [ixLevelEval, hx, hy] using h
        subst n
        exact levelImaxSmart_numeric (normalizeLevel_numeric φ x a free.1 hx)
          (normalizeLevel_numeric φ y b free.2 hy)

/-- Positive semantic bridge, with the original successful evaluation retained. It does not
turn an evaluator refusal into a value or assert that a polymorphic level is parameter-free. -/
theorem normalizeLevel_paramFree_eval (φ : Lean.Name → Nat) {l : Level} {n : Nat}
    (free : LevelParamFree l) (evaluated : ixLevelEval φ l = some n) :
    ixLevelEval φ (normalizeLevel l) = some n :=
  (normalizeLevel_numeric φ l n free evaluated).eval φ

theorem substLevel_paramFree_eval (φ : Lean.Name → Nat) (ps : Array Name) (us : Array Level)
    {l : Level} {n : Nat} (free : LevelParamFree l) (evaluated : ixLevelEval φ l = some n) :
    ixLevelEval φ (substLevel ps us l) = some n := by
  rw [substLevel_paramFree ps us l free]
  exact normalizeLevel_paramFree_eval φ free evaluated

end Ix.CompileCert.Opt

namespace Ix.CompileCert.Opt

open Ix (Name Level)
open Ix.Compile.Canon (levelMaxSmart levelImaxSmart normalizeLevel substLevel)

/-- Evidence using the existing independent level checker, not cached equality. This is an
intermediate proof relation, not a caller-domain restriction or an assumed compiler law. -/
def CheckedIxLevelEq (ps : List Lean.Name) (a b : Level) : Prop :=
  ∃ av bv ak bk, ixLevel a = .ok av ∧ ixLevel b = .ok bv ∧
    exportSourceLevel ps av = .ok ak ∧ exportSourceLevel ps bv = .ok bk ∧
    checkedLevelImage ak bk = .ok bk

/-- The two sides use the same source, wire and target valuations. No equality of cached hashes
is used, and unresolved levels or unsupported parameter scopes are not fabricated. -/
theorem checkedIxLevelEq_eval {ps : List Lean.Name} {a b : Level}
    (checked : CheckedIxLevelEq ps a b)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat) (ψ : Kernel.Name → Nat)
    (sourceAligned : ∀ n i, ps.idxOf? n = some i → φ n = ρ i.toUInt64)
    (targetAligned : ∀ i n, (ps.map sourceName)[i.toNat]? = some n → ρ i = ψ n) :
    ixLevelEval φ b = ixLevelEval φ a := by
  obtain ⟨av, bv, ak, bk, ha, hb, hka, hkb, hc⟩ := checked
  rw [← ixLevel_eval hb φ, ← ixLevel_eval ha φ,
    exportSourceLevel_eval hkb φ ρ ψ sourceAligned targetAligned,
    exportSourceLevel_eval hka φ ρ ψ sourceAligned targetAligned,
    checkedLevelImage_eval hc ψ]

/-- The existing independent check connects an actual normalization result to `ixLevelEval`.
Universal success of this check on the original source domain is not asserted here. -/
theorem normalizeLevel_eval_of_checked {ps : List Lean.Name} {l : Level}
    (checked : CheckedIxLevelEq ps l (normalizeLevel l))
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat) (ψ : Kernel.Name → Nat)
    (sourceAligned : ∀ n i, ps.idxOf? n = some i → φ n = ρ i.toUInt64)
    (targetAligned : ∀ i n, (ps.map sourceName)[i.toNat]? = some n → ρ i = ψ n) :
    ixLevelEval φ (normalizeLevel l) = ixLevelEval φ l :=
  checkedIxLevelEq_eval checked φ ρ ψ sourceAligned targetAligned

/-- The scalar empty-parameter identity already proved in `LevelTransport` transports the
same accepted normalization certificate without changing the production helper. -/
theorem substLevel_empty_params_eval_of_checked {ps : List Lean.Name} {l : Level}
    (checked : CheckedIxLevelEq ps l (normalizeLevel l)) (us : Array Level)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat) (ψ : Kernel.Name → Nat)
    (sourceAligned : ∀ n i, ps.idxOf? n = some i → φ n = ρ i.toUInt64)
    (targetAligned : ∀ i n, (ps.map sourceName)[i.toNat]? = some n → ρ i = ψ n) :
    ixLevelEval φ (substLevel #[] us l) = ixLevelEval φ l := by
  rw [substLevel_empty_params]
  exact normalizeLevel_eval_of_checked checked φ ρ ψ sourceAligned targetAligned

/-- Each scalar operation on a parameter-free level uses exactly the same checked
normalization fact. Parameter freedom is only this helper lemma's syntax premise. -/
theorem substLevel_paramFree_eval_of_checked {ps : List Lean.Name} {l : Level}
    (checked : CheckedIxLevelEq ps l (normalizeLevel l)) (ks : Array Name) (us : Array Level)
    (free : LevelParamFree l)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat) (ψ : Kernel.Name → Nat)
    (sourceAligned : ∀ n i, ps.idxOf? n = some i → φ n = ρ i.toUInt64)
    (targetAligned : ∀ i n, (ps.map sourceName)[i.toNat]? = some n → ρ i = ψ n) :
    ixLevelEval φ (substLevel ks us l) = ixLevelEval φ l := by
  rw [substLevel_paramFree ks us l free]
  exact normalizeLevel_eval_of_checked checked φ ρ ψ sourceAligned targetAligned

end Ix.CompileCert.Opt
