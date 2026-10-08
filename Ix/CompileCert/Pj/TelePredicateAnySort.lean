import Ix.CompileCert.Pj.Tele

/-! Truth-valued motives at every universe of the cumulative set model.
The original universe assignment and model laws are preserved. -/

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (InstalledTelescope)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

theorem truthVal_mem_univ_any (Q : Prop) (n : Nat) :
    (truthVal Q : V) ∈ˢ univ n := by
  exact univ_mono (Nat.zero_le n) _
    (by simpa only [univ_zero] using (truthVal_mem_univZero (V := V) Q))

/-- The original-assignment version of `tele_predicate`: no restriction on
the telescope's result level. Its binders retain the original graph-regime
requirement, which `RecRd.Check` supplies for motive telescopes. -/
theorem tele_predicate_any_sort :
    ∀ (bs : List (Kernel.Expr × Kernel.BinderMeta)) {s : Kernel.Level}
      {ρ : Nat → V} {T : V},
    (∀ p ∈ bs, Kernel.regime φ p.2.pw ≠ 0) →
    Kernel.Denotes cval env φ ρ (piJoin bs (.sort s)) T →
    ∀ Q : List V → Prop, ∃ M, M ∈ˢ T ∧ ∀ args finalρ,
      InstalledTelescope cval env φ ρ (piJoin bs (.sort s)) args finalρ (.sort s) →
      args.length = bs.length → args.foldl app M = truthVal (Q args)
  | [], s, ρ, T, _, hT, Q => by
    refine ⟨truthVal (Q []), ?_, ?_⟩
    · rw [Bridge.denotes_sort_inv hT]
      exact truthVal_mem_univ_any (Q []) (Kernel.Level.eval φ s)
    · intro args finalρ _ hl
      cases args with
      | nil => rfl
      | cons _ _ => simp at hl
  | (t, m) :: bs, s, ρ, T, hreg, hT, Q => by
    obtain ⟨A, B, hA, hB, -, rfl⟩ := Bridge.denotes_pi_inv hT
    have hr : Kernel.regime φ m.pw ≠ 0 := hreg (t, m) (List.mem_cons_self ..)
    have hreg' : ∀ p ∈ bs, Kernel.regime φ p.2.pw ≠ 0 :=
      fun p hp => hreg p (List.mem_cons_of_mem _ hp)
    have hex : ∀ x, x ∈ˢ A → ∃ M, M ∈ˢ B x ∧ ∀ args finalρ,
        InstalledTelescope cval env φ (Kernel.push x ρ)
          (piJoin bs (.sort s)) args finalρ (.sort s) →
        args.length = bs.length → args.foldl app M = truthVal (Q (x :: args)) :=
      fun x hx => tele_predicate_any_sort bs hreg' (hB x hx) (fun as => Q (x :: as))
    classical
    let F : V → V := fun x => if hx : x ∈ˢ A then Classical.choose (hex x hx) else empty
    have hF : ∀ x (hx : x ∈ˢ A), F x = Classical.choose (hex x hx) := fun x hx => by
      simp only [F, hx, ↓reduceDIte]
    refine ⟨lamR (Kernel.regime φ m.pw) A F, lamR_mem fun x hx => ?_, ?_⟩
    · rw [hF x hx]; exact (Classical.choose_spec (hex x hx)).1
    · intro args finalρ typed hl
      cases typed with
      | @cons _ _ _ _ x A' args' _ _ hA' hx rest =>
        obtain rfl := Kernel.Denotes_functional hA' hA
        simp only [List.foldl_cons]
        rw [app_lamR_pos hr hx, hF x hx]
        exact (Classical.choose_spec (hex x hx)).2 args' finalρ rest (by simpa using hl)

end Ix.CompileCert.Pj
