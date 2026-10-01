import Compilatrix.Anf.Proof.Pass.Ren
import Compilatrix.Anf.Proof.Lang

/-! # Pruning: renamed code at every bound, and adequacy

Applying related closures enters the source body and its renaming one clock
down (`app_at`); calls and global values of `S` simulate their renamed ids
(`call_at`, `glob_at`); with the fundamental lemma for renamed code, the
interface holds at every bound (`levels`), and a program whose roots are the
renamed roots refines its source (`refines`) (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Prune.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo Sim later later_succ later_zero)
open Compilatrix.Anf.Rel (Pw)

variable {X : Setting} {n : Nat}

theorem app_at (hlow : ∀ m < n, FundRen X m) : Rel.AppSim X.P X.Q (RV X) n := by
  suffices H : ∀ len, ∀ ⦃f g : Val⦄ ⦃vs ws : List Val⦄, vs.length ≤ len → RV X f g →
      Pw (RV X) vs ws → SimUpTo (RV X) n (fun k => applyN X.P k f vs) (fun k => applyN X.Q k g ws) by
    intro f g vs ws hfg hvs; exact H _ (Nat.le_refl _) hfg hvs
  intro len
  induction len using Nat.strongRecOn with
  | _ len ih =>
  intro f g vs ws hlen hfg hvs
  have hnc : ∀ ⦃f g : Val⦄, (∀ ρ n b got, f ≠ .clos ρ n b got) → (∀ ρ n b got, g ≠ .clos ρ n b got) →
      RV X f g → SimUpTo (RV X) n (fun k => applyN X.P k f vs) (fun k => applyN X.Q k g ws) := by
    intro f g hf hg hfg
    cases vs with
    | nil =>
      cases hvs
      exact (SimUpTo.ok hfg).congr (fun k => applyN_nil' X.P k f) (fun k => applyN_nil' X.Q k g)
    | cons v vs' =>
      cases hvs with
      | cons _ _ =>
        exact (SimUpTo.stuck _).congr (fun k => applyN_not_clos X.P k f v vs' hf)
          (fun k => applyN_not_clos X.Q k g _ _ hg)
  cases hfg with
  | lit => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) .lit
  | box => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) .box
  | con h => exact hnc (fun _ _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h) (.con h)
  | clos hρ hgot hb =>
    rename_i ρ ρ' got got' m b
    have hρ' := pw_of hρ
    have hgot' := pw_of hgot
    have hgl := hgot'.length
    have hvl := hvs.length
    cases vs with
    | nil =>
      cases hvs
      exact (SimUpTo.ok (.clos hρ hgot hb)).congr (fun k => applyN_nil' X.P k _) (fun k => applyN_nil' X.Q k _)
    | cons v vs' =>
      obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by
        cases ws with
        | nil => cases hvs
        | cons w ws' => exact ⟨w, ws', rfl⟩
      by_cases hg : got.length < m
      · by_cases hu : got.length + (v :: vs').length < m
        · have hu' : got'.length + (w :: ws').length < m := by simp at hvl hu ⊢; omega
          refine (SimUpTo.later fun _ _ => SimUpTo.ok (RV.clos (n := m) hρ (of_pw (hgot'.append hvs)) hb)).congr
            (fun k => ?_) (fun k => ?_)
          · rw [applyN_clos]; simp only [hg, hu, if_true]
          · rw [applyN_clos]; simp only [show got'.length < m by omega, hu', if_true]
        · have hall := hgot'.append hvs
          refine (SimUpTo.bind (d := fun r k => applyN X.P k r ((got ++ v :: vs').drop m))
            (d' := fun r k => applyN X.Q k r ((got' ++ w :: ws').drop m))
            (ClockMono.later (eval_mono X.Q _ [] _)) (fun r => applyN_mono X.Q r _)
            (SimUpTo.later fun i hi => hlow i (by omega) ((hall.take m).reverse.append hρ') .nil b hb)
            fun r r' hr => ?_).congr (fun k => ?_) (fun k => ?_)
          · by_cases hnil : ((got ++ v :: vs').drop m) = []
            · have : ((got' ++ w :: ws').drop m) = [] := by
                rw [List.drop_eq_nil_iff] at hnil ⊢; simp at hnil hvl ⊢; omega
              rw [hnil, this]
              exact (SimUpTo.ok hr).congr (fun k => applyN_nil' X.P k r) (fun k => applyN_nil' X.Q k r')
            · exact ih _ (by simp at hnil hlen ⊢; omega) (Nat.le_refl _) hr (hall.drop m)
          · rw [applyN_clos]
            simp only [hg, hu, if_true, if_false]
            cases k with
            | zero => rfl
            | succ k => simp only [later_succ, enter]
          · rw [applyN_clos]
            simp only [show got'.length < m by omega, if_true,
              show ¬ (got'.length + (w :: ws').length < m) by simp at hvl hu ⊢; omega, if_false]
            cases k with
            | zero => rfl
            | succ k => simp only [later_succ, enter]
      · refine (SimUpTo.later (c₁ := fun _ => (.stuck : Result Val)) (c₂ := fun _ => .stuck)
          fun _ _ => SimUpTo.stuck _).congr (fun k => ?_) (fun k => ?_)
        · rw [applyN_clos]; simp only [hg, if_false]
        · rw [applyN_clos]; simp only [show ¬ got'.length < m by omega, if_false]

theorem call_at (hlow : ∀ m < n, FundRen X m) : CallRen X n := by
  intro g hgS vs ws hvs
  cases hP : X.P.global? g with
  | none => exact (SimUpTo.stuck _).congr (fun k => rfl) (fun _ => rfl)
  | some gd =>
    rw [X.glob g gd hgS hP]
    simp only [Result.ofOption, Result.bind_ok]
    have hvl := hvs.length
    by_cases hl : vs.length = gd.ps.length
    · have hl' : ws.length = gd.ps.length := by rw [hvl, hl]
      refine (SimUpTo.later fun i hi => hlow i (by omega) hvs.reverse .nil gd.body
        (X.closed g gd hgS hP)).congr (fun k => ?_) (fun k => ?_)
      · simp only [callVal, hl, if_true]
      · simp only [callVal, hl', if_true]
    · have hl' : ¬ ws.length = gd.ps.length := by rw [hvl]; exact hl
      refine (SimUpTo.stuck _).congr (fun k => ?_) (fun _ => rfl)
      simp only [callVal, hl, if_false]

theorem glob_at (hlow : ∀ m < n, FundRen X m) : GlobRen X n := by
  intro g hgS
  cases hP : X.P.global? g with
  | none => exact (SimUpTo.stuck _).congr (fun k => rfl) (fun _ => rfl)
  | some gd =>
    rw [X.glob g gd hgS hP]
    simp only [Result.ofOption, Result.bind_ok]
    unfold globVal
    cases gd.ps with
    | nil => exact SimUpTo.later fun i hi => hlow i (by omega) .nil .nil gd.body (X.closed g gd hgS hP)
    | cons p ps => exact SimUpTo.ok (.clos .nil .nil (X.closed g gd hgS hP))

theorem levels : ∀ n, FundRen X n ∧ Rel.AppSim X.P X.Q (RV X) n ∧ CallRen X n ∧ GlobRen X n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  have hlow : ∀ m < n, FundRen X m := fun m hm => (ih m hm).1
  have ha := app_at hlow
  have hc := call_at hlow
  have hg := glob_at hlow
  exact ⟨fund_step hlow ha hc hg, ha, hc, hg⟩

/-- **Adequacy** for renamed code: with the source's roots in `S` and the
target's roots their renamings, the target refines the source. -/
theorem refines (hroots : X.Q.roots = X.P.roots.map fun r => X.m.getD r r)
    (hS : ∀ r ∈ X.P.roots, X.S.contains r = true) : Sem.Refines X.P X.Q := by
  refine Sem.Refines.of_sim (R := RV X) (fun _ _ h => obs h) fun i => ⟨id, ?_⟩
  show Sim (RV X) id (anfRun X.P i) (anfRun X.Q i)
  unfold anfRun
  rw [hroots, List.getElem?_map]
  cases hr : X.P.roots[i.1]? with
  | none => exact ⟨fun _ _ => ⟨0, .stuck⟩, fun _ h => nomatch h⟩
  | some r =>
    have hrS := hS r (List.mem_of_getElem? hr)
    have hxs : Pw (RV X) (i.2.map fun n => Val.lit (.nat n)) (i.2.map fun n => Val.lit (.nat n)) := by
      induction i.2 with
      | nil => exact .nil
      | cons n ns ih => exact .cons .lit ih
    refine SimUpTo.sim fun n => ?_
    obtain ⟨-, ha, -, hg⟩ := levels (X := X) n
    exact (SimUpTo.bind (evalBind_mono X.Q [] _) (fun g => applyN_mono X.Q g _)
      ((hg r hrS).congr (fun k => evalBind_glob X.P k [] r) (fun k => evalBind_glob X.Q k [] _))
      fun _ _ hfg => ha hfg hxs).congr (fun k => run_eq X.P k r _) (fun k => run_eq X.Q k _ _)

end Compilatrix.Anf.Prune.Proof
