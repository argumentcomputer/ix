module

public import ConLeche.Model.Inductives.StructRecLam
public section

/-!
# The recursor rule's kit (task #175 W4c, P3 module 6, part 16)

Syntactic and semantic pieces of the recursor rule's law: the
`checkDefEqList` pins indexed, the rule's λ-peel residual as the
body's instantiation sequence and its value (the minor applied to the
fields), a `TeleFitPA` fit's chain memberships as a `SpineFit`, the
constructor's level assignment agreeing with the recursor's on the
block's parameters, and the minor value at a zero elimination level.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The frame values (from the retired `StructRecLawFitsP`, task #175 S2) -/

/-! ## Fits as spines -/

/-- A fit's chain memberships are a `SpineFit` (the values read at the
fit's own frame `ρ`, the domains walked from `σ`). -/
theorem spineFit_of_chain' :
    ∀ {Ds : List AnnotTerm} {ws : List AnnotTerm} {σ ρ : Nat → V},
      ws.length = Ds.length →
      (∀ n, n < Ds.length →
        interp V ρ (ws.getD n default)
          ∈ˢ interp V (consN ((ws.take n).map (interp V ρ)) σ)
            (Ds.reverse.getD (Ds.length - 1 - n) default)) →
      SpineFit σ Ds (ws.map (interp V ρ))
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | D :: Ds, w :: ws, σ, ρ, hlen, hmem => by
    simp only [List.map_cons, SpineFit]
    have h0 := hmem 0 (by simp)
    simp only [List.getD_cons_zero, List.take_zero, List.map_nil, List.length_cons,
      Nat.add_sub_cancel, Nat.sub_zero] at h0
    rw [List.getD_eq_getElem?_getD, List.reverse_cons, List.getElem?_append_right (by simp),
      List.length_reverse, Nat.sub_self] at h0
    refine ⟨h0, ?_⟩
    refine spineFit_of_chain' (by simpa using hlen) ?_
    intro n hn
    have := hmem (n + 1) (by simp; omega)
    simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.length_cons] at this
    rw [List.reverse_cons] at this
    rw [List.getD_eq_getElem?_getD (l := Ds.reverse ++ [D]),
      List.getElem?_append_left (by simp; omega),
      show Ds.length + 1 - 1 - (n + 1) = Ds.length - 1 - n from by omega,
      ← List.getD_eq_getElem?_getD] at this
    exact this

theorem spineFit_of_chain {Ds : List AnnotTerm} {ws : List AnnotTerm} {ρ : Nat → V}
    (hlen : ws.length = Ds.length)
    (hmem : ∀ n, n < Ds.length →
      interp V ρ (ws.getD n default)
        ∈ˢ interp V (chain V ρ (ws.take n)) (Ds.reverse.getD (Ds.length - 1 - n) default)) :
    SpineFit ρ Ds (ws.map (interp V ρ)) :=
  spineFit_of_chain' hlen hmem

/-! ## Level assignments -/

/-- The constructor's level assignment, fixed by the recursor's through
`recFireComparands`, agrees with the recursor's on the block's
parameters. -/
theorem substFn_agree_of_comparand {lps lpsR : List Name} {us usj : List Level}
    (hψ : Level.substFn φ lps usj
      = Level.substFn φ lps (lps.map fun q => Level.subst lpsR us (.param q))) :
    ∀ q ∈ lps, Level.substFn φ lps usj q = Level.substFn φ lpsR us q := by
  intro q hq
  rw [congrFun hψ q]
  have hmap : (lps.map fun q => Level.subst lpsR us (.param q))
      = (lps.map Level.param).map (Level.subst lpsR us) := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, Level.substFn_map_subst (by simp) hq, Level.substFn_map_param]

/-! ## The minor at a zero elimination level -/

end ConLeche.Model
