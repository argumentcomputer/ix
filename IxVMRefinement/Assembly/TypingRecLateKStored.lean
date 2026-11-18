import IxVMRefinement.Assembly.TypingRecLateK

/-! # The stored K bit of a recursor record's rule

The kernel stores a native recursor's rules with the K bit `recRuleKOf`: the rule's constructor
has no field and its family's stored capability record has `ruleK`, which for a family with one
constructor is that constructor's declared field count being zero and the family being
propositional (`Level.isEquiv` of its result sort with zero). The circuit decides K by
`compute_k_target`, whose verdict `1` gives one stored constructor without field and a result
sort that is zero at every assignment (`rec_k_of_arm`).

* `level_simplify_eq_zero_of_eval`, `level_isEquiv_zero_of_eval`: a level that is zero at every
  assignment simplifies to `zero`, so the kernel's equivalence test with `zero` answers `true`
  (completeness of `Level.isEquiv` against zero);
* `recRuleKOf_late`: at a registered family with one stored constructor without field and a
  result sort zero everywhere, the stored K bit of that constructor's rule is set (the declared
  field count is the stored one, `LateFamAt.ctorFields`);
* `rec_k_stored_of_arm`: a record that declares K has, at its tied parent's family, one stored
  constructor whose stored K bit is set.
-/

universe u

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace IxVM.Refinement.Typing

open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

/-! ## Completeness of the equivalence test against zero -/

/-- **A level that is zero at every assignment simplifies to `zero`.** -/
theorem level_simplify_eq_zero_of_eval : ∀ (u : Ix.Kernel.Level),
    (∀ φ, Ix.Kernel.Level.eval φ u = 0) → Ix.Kernel.Level.simplify u = .zero
  | .zero, _ => rfl
  | .succ l, h => by
    have h0 := h (fun _ => 0)
    simp [Ix.Kernel.Level.eval] at h0
  | .param p, h => by
    have h0 := h (fun _ => 1)
    simp [Ix.Kernel.Level.eval] at h0
  | .max l r, h => by
    have hl : ∀ φ, Ix.Kernel.Level.eval φ l = 0 := fun φ => by
      have h0 := h φ
      simp only [Ix.Kernel.Level.eval] at h0
      exact Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq h0))
    have hr : ∀ φ, Ix.Kernel.Level.eval φ r = 0 := fun φ => by
      have h0 := h φ
      simp only [Ix.Kernel.Level.eval] at h0
      exact Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq h0))
    have hsl := level_simplify_eq_zero_of_eval l hl
    have hsr := level_simplify_eq_zero_of_eval r hr
    show Ix.Kernel.Level.combining (Ix.Kernel.Level.simplify l) (Ix.Kernel.Level.simplify r) = _
    rw [hsl, hsr] <;> rfl
  | .imax l r, h => by
    have hr : ∀ φ, Ix.Kernel.Level.eval φ r = 0 := fun φ => by
      have h0 := h φ
      simp only [Ix.Kernel.Level.eval] at h0
      split at h0
      next hz => exact hz
      next hz =>
        exact absurd (Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_of_eq h0))) hz
    have hsr := level_simplify_eq_zero_of_eval r hr
    simp [Ix.Kernel.Level.simplify, hsr]

/-- **The kernel's equivalence test with `zero` is complete**: a level that is zero at every
assignment is `Level.isEquiv`-equivalent to `zero`. -/
theorem level_isEquiv_zero_of_eval {u : Ix.Kernel.Level}
    (h : ∀ φ, Ix.Kernel.Level.eval φ u = 0) :
    Ix.Kernel.Level.isEquiv u .zero = some true := by
  have hs : Ix.Kernel.Level.simplify u = Ix.Kernel.Level.simplify .zero := by
    rw [level_simplify_eq_zero_of_eval u h] <;> rfl
  rw [Ix.Kernel.Level.isEquiv_eq_withoutPtr, ite_eq_left hs] <;> rfl

/-! ## The stored K bit -/

/-- **The stored K bit at a registered family with one constructor without field and a result
sort zero at every assignment**: the constructor is stored with its field count, its type ends in
the family, the family is stored with its capability record, whose `ruleK` reads the declared
constructor's field count (the stored one, `ctorFields`) and the family's `Prop` flag
(`isProp`, decided by `Level.isEquiv` with zero). -/
theorem recRuleKOf_late {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {fam : NativeFam .anon} (hat : LateFamAt t E env fam) {cA : ConstantVal .anon × Nat}
    (hA : fam.ctorsA = [cA]) (h0 : cA.2 = 0)
    (hz : ∀ φ, Ix.Kernel.Level.eval φ fam.p.resSort = 0) :
    Ix.Kernel.recRuleKOf env.find? cA.1.name = true := by
  have hA0 : fam.ctorsA[0]? = some cA := by simp [hA]
  obtain ⟨hfind, -, cbs, es, hres, -⟩ := hat.stored.ctor 0 cA hA0
  have hhead := Ix.Kernel.Model.family_of_residual hres
  have hformer := hat.stored.former
  have h1 : Ix.Kernel.recRuleKOf env.find? cA.1.name =
      ((Ix.Kernel.nativeCaps fam.p).ruleK && cA.2 == 0) := by
    simp only [Ix.Kernel.recRuleKOf, hfind, hhead, hformer]
  have hl : fam.p.ctors.length = 1 := by
    have hlen := hat.stored.lenA
    rw [hA] at hlen
    exact hlen.symm
  obtain ⟨c, hc⟩ : ∃ c, fam.p.ctors = [c] := List.length_eq_one_iff.mp hl
  have hc0 : fam.p.ctors[0]? = some c := by simp [hc]
  have hc2 : cA.2 = c.2 := hat.ctorFields 0 c cA hc0 hA0
  have hprop : fam.p.isProp = true := by
    rw [hat.isProp, level_isEquiv_zero_of_eval hz] <;> rfl
  have hcaps : (Ix.Kernel.nativeCaps fam.p).ruleK = (c.2 == 0 && fam.p.isProp) := by
    unfold Ix.Kernel.nativeCaps Ix.Kernel.nativeCapsAt
    rw [hc] <;> rfl
  rw [h1, hcaps, ← hc2, h0, hprop] <;> rfl

/-- **A record that declares K, at its tied parent's family**: the family has one stored
constructor, and the stored K bit of its rule is set (`rec_k_of_arm` with `recRuleKOf_late`). -/
theorem rec_k_stored_of_arm {calls : List (Aiur.Generic.SourceSemantics.Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} {cm : Ixon.Constant}
    (hcm : Ix.Cert.recordAt E P = some cm) (hcmi : cm.info = .iPrj ip)
    (htie : RecMajorTie t E₀ A c rc P) {fam : NativeFam .anon}
    (hm : MatchedAt t E env P ip fam) :
    rc.k = true → rc.rules.size = 1 ∧
      ∃ cA, fam.ctorsA = [cA] ∧ Ix.Kernel.recRuleKOf env.find? cA.1.name = true := by
  intro hk
  obtain ⟨hsize, hlen, hfields, hz⟩ :=
    rec_k_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hm hk
  obtain ⟨cA, hA⟩ : ∃ cA, fam.ctorsA = [cA] := List.length_eq_one_iff.mp hlen
  have h0 : cA.2 = 0 := hfields cA (by simp [hA])
  exact ⟨hsize, cA, hA, recRuleKOf_late hm.1 hA h0 hz⟩

end IxVM.Refinement.Typing
