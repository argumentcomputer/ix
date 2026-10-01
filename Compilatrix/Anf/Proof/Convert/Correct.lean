import Compilatrix.Anf.Proof.Convert.Level
import Compilatrix.Anf.Proof.Lang
import Compilatrix.Lam.Erase.Proof.Correct

/-! # ANF conversion is correct

`convert_correct` (P1, M2.3): every root of a converted program simulates
its Lam root from related arguments, with the clock map `k + 1` (the identity
map when there are arguments): a Lam value is matched by a related Anf value
at some clock, a trap by a trap, and a Lam timeout at `k + 1` by an Anf
timeout at `k` (tick dominance: Anf charges at least as deep); a stuck Lam
run imposes nothing. Related values observe the same (`vr_obs`), so the
converted program refines the Lam program (`convert_refines`, through
`Sem.Refines.of_sim`), and P1 is a `Sem.Transform` without a certificate
(`convertPass`). The traced restatements (decision D-1) are `TSim.ofPure`
and `Transform.lift` of these. -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo Sim Lang TSim TRefines Traced)
open Compilatrix.Lam (Kind Mode)
open Compilatrix.Lam.Erase.Proof (Forall2 RunInput)

variable {A : Arities} {G : Src.NatMap Lam.ModesOk.GInfo}

mutual

/-- Related values observe the same. -/
theorem vr_obs : ∀ {v : Lam.Val} {w : Val}, VR A G v w → Lam.Erase.Proof.obsV v = obsV w
  | _, _, .lit => by
    rename_i l
    cases l <;> rfl
  | _, _, .box => rfl
  | _, _, .con hfs => by
    rename_i c _ _
    cases c with
    | src c => simp only [Lam.Erase.Proof.obsV, obsV, vrs_obs hfs]
    | clo f j => rfl
  | _, _, .clo hc _ => by
    cases hc with
    | mk _ _ _ _ _ _ _ _ hv hw => subst hv hw; rfl

theorem vrs_obs : ∀ {vs : List Lam.Val} {ws : List Val}, VRs A G vs ws →
    Lam.Erase.Proof.obsList vs = obsList ws
  | _, _, .nil => rfl
  | _, _, .cons hv hvs => by
    rename_i w ws
    simp only [Lam.Erase.Proof.obsList, obsList, vr_obs hv, vrs_obs hvs]
    cases obsV w <;> cases obsList ws <;> rfl

end

theorem vrs_of_forall2 : ∀ {vs : List Lam.Val} {ws : List Val}, Forall2 (VR A G) vs ws →
    VRs A G vs ws
  | _, _, .nil => .nil
  | _, _, .cons hv h => .cons hv (vrs_of_forall2 h)

/-- **ANF conversion is correct**: every root of a converted program
simulates its Lam root from related arguments; values are related by a
relation that keeps observations and relates equal `Nat` literals. -/
theorem convert_correct {L : Lam.Program} {Q : Program} (h : convert L = .ok Q) :
    ∃ R : Lam.Val → Val → Prop, (∀ v w, R v w → Lam.Erase.Proof.obsV v = obsV w) ∧
      (∀ n, R (.lit (.nat n)) (.lit (.nat n))) ∧
      ∀ r ∈ L.roots, ∀ (xs : List Lam.Val) (ws : List Val), Forall2 R xs ws →
        Sim R (fun k => k + 1) (fun k => Lam.run L k r xs) (fun k => run Q k r ws) ∧
        (xs ≠ [] → Sim R id (fun k => Lam.run L k r xs) (fun k => run Q k r ws)) := by
  obtain ⟨S, rfl, rfl⟩ := Setting.exists h
  refine ⟨S.V, fun v w hvw => vr_obs hvw, fun n => .lit, fun r hr xs ws hxs => ?_⟩
  have hvs := vrs_of_forall2 hxs
  exact ⟨S.run_sim hr hvs, fun hne => SimUpTo.sim fun n => S.run_simUpTo hr hvs hne n⟩

theorem sim_stuck {α β : Type} {R : α → β → Prop} {f : Nat → Nat} (c₂ : Nat → Result β) :
    Sim R f (fun _ => (.stuck : Result α)) c₂ where
  forward _ _ := ⟨0, .stuck⟩
  timeout _ h := nomatch h

/-- **ANF conversion refines the Lam program**: on every root and `Nat`
arguments, the converted program's behaviour refines Lam's up to equal
first-order observations. -/
theorem convert_refines {L : Lam.Program} {Q : Program} (h : convert L = .ok Q) :
    Sem.Refines L Q := by
  obtain ⟨S, rfl, rfl⟩ := Setting.exists h
  refine Sem.Refines.of_sim (R := S.V) (fun v w hvw => vr_obs hvw) fun i => ⟨fun k => k + 1, ?_⟩
  show Sim S.V (fun k => k + 1) (Lam.Erase.Proof.lamRun S.L i) (anfRun S.Q i)
  unfold Lam.Erase.Proof.lamRun anfRun
  rw [S.roots]
  cases hr : S.L.roots[i.1]? with
  | none => exact sim_stuck _
  | some g =>
    have hvs : VRs S.A S.G (i.2.map fun n => Lam.Val.lit (.nat n)) (i.2.map fun n => Val.lit (.nat n)) := by
      induction i.2 with
      | nil => exact .nil
      | cons n ns ih => exact .cons .lit ih
    exact S.run_sim (List.mem_of_getElem? hr) hvs

/-- P1 as a pass: no certificate, no precondition (conversion checks
`ModesOk` and the roots itself). -/
def convertPass : Sem.Transform Lam.Program Program where
  name := "P1 convert"
  pre _ := True
  run L _ := convert L
  post _ := True
  correct _ _ _ _ h := ⟨trivial, convert_refines h⟩

/-! ## The traced shape (decision D-1) -/

/-- `convert_correct` as traced simulations of the lifted runs. -/
theorem convert_correct_traced {L : Lam.Program} {Q : Program} (h : convert L = .ok Q) :
    ∃ R : Lam.Val → Val → Prop, (∀ v w, R v w → Lam.Erase.Proof.obsV v = obsV w) ∧
      (∀ n, R (.lit (.nat n)) (.lit (.nat n))) ∧
      ∀ r ∈ L.roots, ∀ (xs : List Lam.Val) (ws : List Val), Forall2 R xs ws →
        TSim (Env := Unit) (E := Empty) R (fun k => k + 1)
          (fun _ k => Traced.lift (Lam.run L k r xs)) (fun _ k => Traced.lift (run Q k r ws)) := by
  obtain ⟨R, hobs, hlit, hroots⟩ := convert_correct h
  exact ⟨R, hobs, hlit, fun r hr xs ws hxs => TSim.ofPure (hroots r hr xs ws hxs).1⟩

/-- `convert_refines` as traced refinement of the lifted languages. -/
theorem convert_refines_traced {L : Lam.Program} {Q : Program} (h : convert L = .ok Q) :
    TRefines L Q :=
  Sem.Refines.ofPure (convert_refines h)

/-- P1 as a traced pass. -/
def convertTPass : Sem.TTransform Lam.Program Program := convertPass.lift

theorem convertTPass_run (L : Lam.Program) (c : Unit) : convertTPass.run L c = convert L := rfl

end Compilatrix.Anf.Convert.Proof
