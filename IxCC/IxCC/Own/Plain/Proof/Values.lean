import IxCC.Own.Proof.Heap
import IxCC.Own.Semantics

/-! Policy-independent value lemmas copied mechanically from Own.Proof.Immortal for scratch RC refinement. No immortal-heap premise is used. Production files and fences remain unchanged. -/

set_option autoImplicit false
namespace IxCC.Own.Plain.Values
open IxCC.Sem (Forall2)
open IxCC.Own.Proof
variable {H : Heap}

theorem den_lit_inv {v : RVal} {l : Lam.Lit} (h : Den H v (.lit l)) : v = .lit l := by
  cases v with
  | lit l' => simp only [Den, Heap.value?, toFir, Option.some.injEq, Fir.Val.lit.injEq] at h; rw [h]
  | ctor0 c => simp [Den, Heap.value?, toFir] at h
  | erased => simp [Den, Heap.value?, toFir] at h
  | loc ℓ =>
    obtain ⟨_, _, _, _, _, hw, _⟩ := den_loc h
    cases hw

theorem den_erased_inv {v : RVal} (h : Den H v .erased) : v = .erased := by
  cases v with
  | lit l' => simp [Den, Heap.value?, toFir] at h
  | ctor0 c => simp [Den, Heap.value?, toFir] at h
  | erased => rfl
  | loc ℓ =>
    obtain ⟨_, _, _, _, _, hw, _⟩ := den_loc h
    cases hw

theorem dens_of_toFirList {fuel : Nat} (hf : fuel ≤ H.size + 1) :
    ∀ {vs : List RVal} {ws : List Fir.Val}, toFirList H fuel vs = some ws → Forall2 (Den H) vs ws
  | [], ws, h => by simp only [toFirList, Option.some.injEq] at h; subst h; exact .nil
  | v :: vs, ws, h => by
    simp only [toFirList] at h
    cases hv : toFir H fuel v with
    | none => rw [hv] at h; cases h
    | some w =>
      cases hvs : toFirList H fuel vs with
      | none => rw [hv, hvs] at h; cases h
      | some ws' =>
        rw [hv, hvs] at h
        simp only [Option.some.injEq] at h
        subst h
        exact .cons (toFir_ext (Ext.refl H) hf hv) (dens_of_toFirList hf hvs)

theorem asCtor_den (K : Lam.Known) {v : RVal} {w : Fir.Val} (h : Den H v w) :
    (∀ key fs, w.asCtor K = some (key, fs) → ∃ vs, v.asCtor K H = some (key, vs) ∧ Forall2 (Den H) vs fs) ∧
      (w.asCtor K = none → v.asCtor K H = none) := by
  cases v with
  | lit l =>
    have : w = .lit l := by simp only [Den, Heap.value?, toFir, Option.some.injEq] at h; exact h.symm
    subst this
    rcases l with (_ | n) | s
    · refine ⟨fun key fs hk => ?_, fun hk => ?_⟩
      · simp only [Fir.Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hk
        obtain ⟨c, hc, rfl, rfl⟩ := hk
        exact ⟨[], by simp [RVal.asCtor, hc], .nil⟩
      · simp only [Fir.Val.asCtor, Option.map_eq_none_iff] at hk
        simp [RVal.asCtor, hk]
    · refine ⟨fun key fs hk => ?_, fun hk => ?_⟩
      · simp only [Fir.Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hk
        obtain ⟨c, hc, rfl, rfl⟩ := hk
        exact ⟨[.lit (.nat n)], by simp [RVal.asCtor, hc], .cons (den_lit H _) .nil⟩
      · simp only [Fir.Val.asCtor, Option.map_eq_none_iff] at hk
        simp [RVal.asCtor, hk]
    · exact ⟨fun _ _ hk => by simp [Fir.Val.asCtor] at hk, fun _ => rfl⟩
  | ctor0 c =>
    have : w = .ctor c [] := by simp only [Den, Heap.value?, toFir, Option.some.injEq] at h; exact h.symm
    subst this
    exact ⟨fun key fs hk => by
      simp only [Fir.Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      exact ⟨[], rfl, .nil⟩, fun hk => by simp [Fir.Val.asCtor] at hk⟩
  | erased =>
    have : w = .erased := by simp only [Den, Heap.value?, toFir, Option.some.injEq] at h; exact h.symm
    subst this
    exact ⟨fun _ _ hk => by simp [Fir.Val.asCtor] at hk, fun _ => rfl⟩
  | loc ℓ =>
    obtain ⟨r, m, b, ws, hc, rfl, hws⟩ := den_loc h
    refine ⟨fun key fs hk => ?_, fun hk => by simp [Fir.Val.asCtor] at hk⟩
    simp only [Fir.Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨b.fields, by simp [RVal.asCtor, hc], dens_of_toFirList (by omega) hws⟩

theorem natArgs_den : ∀ {vs : List RVal} {ws : List Fir.Val}, Forall2 (Den H) vs ws →
    Own.natArgs vs = Fir.natArgs ws
  | _, _, .nil => rfl
  | v :: _, w :: _, .cons hd hvs => by
    cases w with
    | lit l =>
      rw [den_lit_inv hd]
      rcases l with n | s
      · simp [Own.natArgs, Fir.natArgs, natArgs_den hvs]
      · rfl
    | ctor c fs =>
      cases v with
      | lit l => simp [Den, Heap.value?, toFir] at hd
      | _ => rfl
    | erased => rw [den_erased_inv hd]; rfl


end IxCC.Own.Plain.Values
