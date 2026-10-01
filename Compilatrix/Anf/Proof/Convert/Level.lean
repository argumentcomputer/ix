import Compilatrix.Anf.Proof.Convert.Term

/-! # ANF conversion: the simulation at every clock

By strong induction on the clock bound `n`: application at `n` needs bodies
below `n` (`app_sim`), and every conversion function at `n` needs
application at `n`, bodies below `n` and itself at lower fuel (`convAt`, by
induction on fuel). So every converted body simulates its Lam body at every
clock (`bodySim`), and applying related closures does (`appSim`). Runs from
a root (`run_sim`): a root's global is applied to value arguments; a run
with arguments simulates with the identity clock map, and every run with
clock map `k + 1` (a function root applied to nothing is a closure at clock
0 in Anf, one δ later in Lam) (P1, M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo Sim later later_succ later_zero)
open Compilatrix.Lam (Kind Mode argSlot applyArgs)
open Compilatrix.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName expected covered KindsSpec sigsOf)
open Compilatrix.Ixon

namespace Setting

variable (S : Setting)

theorem convAt_zero (n : Nat) : S.ConvAt n 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ _ h; rw [conv] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; rw [caseOn] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; rw [caseBody] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ h; rw [convAlts] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ h; rw [convList] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ h; rw [convArgs] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; rw [groups] at h; cases h
  · intro _ _ _ _ _ _ _ _ _ _ _ h; rw [spine] at h; cases h

variable {S}

theorem convAt_succ {n fuel : Nat} (ih : S.ConvAt n fuel) (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m) :
    S.ConvAt n (fuel + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ _ h henv hd hdj hk ht; exact conv_step ih hb h henv hd hdj hk ht
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ h henv hd hdj hk ho hv ha hdf
    exact caseOn_step ih h henv hd hdj hk ho hv ha hdf
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ h henv hd hdj hk ho hv ha hdf
    exact caseBody_step ih h henv hd hdj hk ho hv ha hdf
  · intro _ _ _ _ _ _ _ _ _ h henv hd hdj hk ha _ _ _ _ _ hfs hdf
    exact convAlts_step ih h henv hd hdj hk ha hfs hdf
  · intro _ _ _ _ _ _ _ _ _ h henv hd hdj hf hts; exact convList_step ih h henv hd hdj hf hts
  · intro _ _ _ _ _ _ _ _ _ _ _ _ h henv hd hdj hf ha; exact convArgs_step ih h henv hd hdj hf ha
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h henv hd hdj hk hfo hh ha hc
    exact groups_step ih hb h henv hd hdj hk hfo hh ha hc
  · intro _ _ _ _ _ _ _ _ _ _ _ h henv hd hdj hk ht; exact spine_step ih hb h henv hd hdj hk ht

theorem convAt {n : Nat} (hb : ∀ m < n, BodySim S.L S.Q S.A S.G m) : ∀ fuel, S.ConvAt n fuel
  | 0 => S.convAt_zero n
  | fuel + 1 => convAt_succ (convAt hb fuel) hb

variable (S)

/-- Every converted body simulates its Lam body at every clock bound. -/
theorem bodySim : ∀ n, BodySim S.L S.Q S.A S.G n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro fuel vars d body bt ρ ρt ks h hd henv ht
  exact ((convAt ih fuel).conv (SK := fun x _ => .ok x) h henv hd rfl
    (fun x w hxw => SimUpTo.ok hxw) ht).congr (fun k => (Result.bind_pure _).symm) (fun _ => rfl)

/-- Applying related values at every clock bound. -/
theorem appSim (n : Nat) {fv : Lam.Val} {w : Val} {ss : List Lam.Slot} {ws : List Val}
    (hv : S.V fv w) (hargs : ArgsR S.A S.G [] 0 ss ws) (hne : ss ≠ []) :
    SimUpTo S.V n (fun k => Lam.applyAll S.L k fv ss) (fun k => applyN S.Q k w ws) :=
  (app_sim n (fun m _ => S.bodySim m) ss.length).2 (Nat.le_refl _) hv hargs hne

/-! ## Runs from a root -/

theorem _root_.Compilatrix.Sem.Sim.succ_of_id {α β : Type} {R : α → β → Prop}
    {c₁ : Nat → Result α} {c₂ : Nat → Result β} (h₁ : ClockMono c₁) (h : Sim R id c₁ c₂) :
    Sim R (fun k => k + 1) c₁ c₂ where
  forward := h.forward
  timeout k ht := h.timeout k (h₁.timeout_of_le (Nat.le_succ k) ht)

theorem _root_.Compilatrix.Sem.Sim.congr {α β : Type} {R : α → β → Prop} {f : Nat → Nat}
    {c₁ c₁' : Nat → Result α} {c₂ c₂' : Nat → Result β} (h : Sim R f c₁ c₂)
    (h₁ : ∀ k, c₁' k = c₁ k) (h₂ : ∀ k, c₂' k = c₂ k) : Sim R f c₁' c₂' where
  forward k hk := by
    rw [h₁] at hk ⊢
    obtain ⟨k', h'⟩ := h.forward k hk
    exact ⟨k', by rw [h₂]; exact h'⟩
  timeout k ht := by rw [h₂]; exact h.timeout k (by rw [← h₁]; exact ht)

/-- A root that is no global of the conversion is no global of `L`. -/
theorem root_global {r : Lam.GlobalId} (hr : r ∈ S.L.roots) (hA : S.A.get? r = none) :
    S.L.global? r = none := by
  cases hg : S.L.global? r with
  | none => rfl
  | some gl =>
    exfalso
    have hs := List.all_eq_true.1 S.rootsStrict r hr
    simp only [rootStrict, hg, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [arities_of hg hs.1] at hA
    cases hA

/-- A function root's telescope has no `name` binder. -/
theorem root_value {r : Lam.GlobalId} (hr : r ∈ S.L.roots) {nA : Nat} (hA : S.A.get? r = some nA) :
    hasName (((S.G.get? r).map (·.tele)).getD []) = false := by
  obtain ⟨gl, gd, gi, kinds, hgl, hgd, hgi, hn, hps, hconv, htele, hsigs, hma, htm⟩ := S.glob hA
  have hs := List.all_eq_true.1 S.rootsStrict r hr
  simp only [rootStrict, hgl, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hs
  rw [hgi]
  simp only [Option.map_some, Option.getD_some, htele]
  rw [lam_telescope_eq] at hs
  exact hs.2

/-- A CAF's value: one clock down, its body. -/
theorem caf_value {g : Lam.GlobalId} (hA : S.A.get? g = some 0) (n : Nat) (ρ : Lam.Env)
    (ρ' : List Val) :
    SimUpTo S.V n (fun k => Lam.eval S.L k ρ (.glob g)) (fun k => evalBind S.Q k ρ' (.glob g)) := by
  obtain ⟨gl, gd, gi, kinds, hgl, hgd, hgi, hn, hps, hconv, htele, hsigs, hma, htm⟩ := S.glob hA
  have hbody : gl.body = lamsWith (telescope gl.body).1 (telescope gl.body).2 :=
    (lamsWith_telescope gl.body).symm
  generalize (telescope gl.body).1 = ps at hn hconv htele hma hbody
  generalize (telescope gl.body).2 = body at hconv htm hbody
  have hps0 : ps = [] := List.length_eq_zero_iff.1 hn.symm
  subst hps0
  have hk0 : kinds = [] := List.length_eq_zero_iff.1 hma.1.symm
  subst hk0
  have hgd0 : gd.ps = [] := List.length_eq_zero_iff.1 hps
  exact (SimUpTo.later fun m' hm' => S.bodySim m' (ρt := []) hconv rfl .nil
    (by simpa [lamsWith, ← hbody] using htm)).congr
    (fun k => by rw [lam_eval_glob S.L hgl, hbody]; rfl)
    (fun k => by rw [evalBind_glob, hgd]; simp [Result.ofOption, globVal, hgd0])

theorem argsR_vals : ∀ {xs : List Lam.Val} {ws : List Val}, VRs S.A S.G xs ws →
    ∀ (tk : List Kind) (i : Nat), (∀ p, i ≤ p → tk.getD p .strict = .strict) →
    ArgsR S.A S.G tk i (xs.map .val) ws
  | [], [], .nil, _, _, _ => .nil
  | _ :: _, _ :: _, .cons hv h, tk, i, hst =>
    .cons (by rw [hst i (Nat.le_refl i)]; exact .val hv)
      (argsR_vals h tk (i + 1) fun p hp => hst p (by omega))

/-- A run from a root with arguments: the identity clock map. -/
theorem run_simUpTo {r : Lam.GlobalId} (hr : r ∈ S.L.roots) {xs : List Lam.Val} {ws : List Val}
    (hxs : VRs S.A S.G xs ws) (hne : xs ≠ []) (n : Nat) :
    SimUpTo S.V n (fun k => Lam.run S.L k r xs) (fun k => Anf.run S.Q k r ws) := by
  have hrun : ∀ k, Lam.run S.L k r xs =
      (Lam.eval S.L k [] (.glob r)).bind fun f => Lam.applyAll S.L k f (xs.map .val) := fun k => by
    unfold Lam.run; cases Lam.eval S.L k [] (.glob r) <;> rfl
  have hwne : ws ≠ [] := by
    intro hw; rw [hw] at hxs; cases hxs; exact hne rfl
  have hanf : ∀ k, Anf.run S.Q k r ws =
      (evalBind S.Q k [] (.glob r)).bind fun f => applyN S.Q k f ws := fun k => run_eq S.Q k r ws
  cases hA : S.A.get? r with
  | none =>
    -- not a global: Lam is stuck
    have hg := S.root_global hr hA
    exact (SimUpTo.stuck _).congr (fun k => by rw [hrun, Lam.eval_glob, hg]; rfl) (fun _ => rfl)
  | some nA =>
  cases nA with
  | zero =>
    -- a CAF root: its value one clock down, then the arguments
    exact (SimUpTo.bind (evalBind_mono S.Q [] _) (fun f => applyN_mono S.Q f ws) (S.caf_value hA n [] [])
      fun v w hvw => S.appSim n hvw (argsR_vals S hxs [] 0 (fun _ _ => by simp))
        (by intro e; apply hne; simpa using e)).congr hrun hanf
  | succ nn =>
    -- a function root: its closure (free in Anf), then one application
    obtain ⟨body, ps', hL, w, hQ, hv⟩ := glob_value hA (S.root_value hr hA)
    obtain ⟨s, ss, hss⟩ : ∃ s ss, xs.map Lam.Slot.val = s :: ss := by
      cases xs with
      | nil => exact absurd rfl hne
      | cons x xs => exact ⟨_, _, rfl⟩
    refine (S.appSim n hv (argsR_vals S hxs [] 0 (fun _ _ => by simp))
      (by rw [hss]; simp)).congr (fun k => ?_) (fun k => by rw [hanf, hQ]; rfl)
    rw [hrun, hL]
    cases k with
    | zero => rw [hss, later_zero, Lam.applyAll_cons, apply_clos_later, later_zero]; rfl
    | succ k => rw [later_succ, Result.bind_ok]

/-- A run of a root on related arguments simulates with clock map `k + 1`;
with arguments, `run_simUpTo` gives the identity map. -/
theorem run_sim {r : Lam.GlobalId} (hr : r ∈ S.L.roots) {xs : List Lam.Val} {ws : List Val}
    (hxs : VRs S.A S.G xs ws) :
    Sim S.V (fun k => k + 1) (fun k => Lam.run S.L k r xs) (fun k => Anf.run S.Q k r ws) := by
  by_cases hne : xs = []
  · subst hne
    cases hxs
    have hrun : ∀ k, Lam.run S.L k r [] = Lam.eval S.L k [] (.glob r) := fun k => by
      unfold Lam.run; cases Lam.eval S.L k [] (.glob r) <;> rfl
    have hanf : ∀ k, Anf.run S.Q k r [] = evalBind S.Q k [] (.glob r) := fun k => by
      rw [run_eq]
      cases evalBind S.Q k [] (.glob r) with
      | ok v => rw [Result.bind_ok, applyN_nil']
      | _ => rfl
    cases hA : S.A.get? r with
    | none =>
      have hg := S.root_global hr hA
      exact ⟨fun k _ => ⟨0, by rw [hrun, Lam.eval_glob, hg]; exact .stuck⟩,
        fun k ht => by rw [hrun, Lam.eval_glob, hg] at ht; cases ht⟩
    | some nA =>
    cases nA with
    | zero =>
      exact Sim.succ_of_id (Lam.run_mono S.L r [])
        ((SimUpTo.sim fun n => S.caf_value hA n [] []).congr hrun hanf)
    | succ nn =>
      obtain ⟨body, ps', hL, w, hQ, hv⟩ := glob_value hA (S.root_value hr hA)
      refine ⟨fun k hk => ⟨0, ?_⟩, fun k ht => ?_⟩
      · rw [hrun, hL] at hk ⊢
        cases k with
        | zero => exact absurd rfl hk
        | succ k => rw [later_succ, hanf, hQ]; exact .ok hv
      · rw [hrun, hL, later_succ] at ht; cases ht
  · exact Sim.succ_of_id (Lam.run_mono S.L r xs) (SimUpTo.sim fun n => S.run_simUpTo hr hxs hne n)

end Setting

end Compilatrix.Anf.Convert.Proof
