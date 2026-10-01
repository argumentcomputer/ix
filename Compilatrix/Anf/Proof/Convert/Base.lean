import Compilatrix.Anf.Proof.Convert.Rel

/-! # ANF conversion: basic facts

Telescopes and spines on the Lam side, environments and parameters on both
sides, and the shape of Anf application on a closure, for the P1
simulation (M2.3). -/

set_option autoImplicit false

namespace Compilatrix.Anf.Convert.Proof

open Compilatrix.Sem (Result ClockMono SimUpTo later later_succ later_zero)
open Compilatrix.Lam (Kind Mode)
open Compilatrix.Lam.ModesOk (TermOk NameArgOk ArgsOk GInfo hasName)
open Compilatrix.Ixon

/-! ## Telescopes -/

theorem telescope_lamsWith : ∀ (ps : List (Mode × V3.BinderContract)) {body : Lam.Term},
    NotLam body → telescope (lamsWith ps body) = (ps, body)
  | [], body, h => by
    cases body <;> first | rfl | exact absurd h id
  | (m, c) :: ps, body, h => by
    simp only [lamsWith, telescope, telescope_lamsWith ps h]

theorem lamsWith_telescope : ∀ t : Lam.Term, lamsWith (telescope t).1 (telescope t).2 = t
  | .lam m c b => by simp only [telescope, lamsWith, lamsWith_telescope b]
  | .var _ | .glob _ | .app .. | .letE .. | .con .. | .case .. | .proj .. | .lit _ | .prim .. | .tick _
  | .box | .trap => rfl

theorem notLam_telescope : ∀ t : Lam.Term, NotLam (telescope t).2
  | .lam m c b => by simp only [telescope]; exact notLam_telescope b
  | .var _ | .glob _ | .app .. | .letE .. | .con .. | .case .. | .proj .. | .lit _ | .prim .. | .tick _
  | .box | .trap => trivial

theorem lam_telescope_lamsWith : ∀ (ps : List (Mode × V3.BinderContract)) {body : Lam.Term},
    NotLam body → Lam.Term.telescope (lamsWith ps body) = (ps.map (·.1), body)
  | [], body, h => by
    cases body <;> first | rfl | exact absurd h id
  | (m, c) :: ps, body, h => by
    simp only [lamsWith, Lam.Term.telescope, lam_telescope_lamsWith ps h, List.map_cons]

theorem lamsWith_append : ∀ (ps qs : List (Mode × V3.BinderContract)) (b : Lam.Term),
    lamsWith (ps ++ qs) b = lamsWith ps (lamsWith qs b)
  | [], _, _ => rfl
  | (m, c) :: ps, qs, b => by simp only [List.cons_append, lamsWith, lamsWith_append ps qs b]

/-! ## Lam on telescopes -/

variable (L : Lam.Program)

theorem eval_lamsWith_cons (k : Nat) (ρ : Lam.Env) (p : Mode × V3.BinderContract)
    (ps : List (Mode × V3.BinderContract)) (body : Lam.Term) :
    Lam.eval L k ρ (lamsWith (p :: ps) body) = .ok (.clos ρ (lamsWith ps body)) := by
  obtain ⟨m, c⟩ := p
  simp only [lamsWith]
  exact Lam.eval_lam L k ρ _ _ _

/-- Applying a closure whose term is a λ: a charge, then the next closure. -/
theorem apply_lamsWith_cons (k : Nat) (ρ : Lam.Env) (p : Mode × V3.BinderContract)
    (ps : List (Mode × V3.BinderContract)) (body : Lam.Term) (s : Lam.Slot) :
    Lam.apply L k (.clos ρ (lamsWith (p :: ps) body)) s =
      later k fun _ => .ok (.clos (s :: ρ) (lamsWith ps body)) := by
  rw [Lam.apply_clos]
  cases k with
  | zero => rfl
  | succ k => exact eval_lamsWith_cons L k (s :: ρ) p ps body

theorem apply_clos_later (k : Nat) (ρ : Lam.Env) (b : Lam.Term) (s : Lam.Slot) :
    Lam.apply L k (.clos ρ b) s = later k fun k => Lam.eval L k (s :: ρ) b := by
  rw [Lam.apply_clos]; cases k <;> rfl

/-- Applying a telescope closure with `j` slots to the rest of its `n`
slots: the body one clock down. -/
theorem applyAll_tele (k : Nat) (body : Lam.Term) :
    ∀ (ps : List (Mode × V3.BinderContract)) (ρ : Lam.Env) (ss : List Lam.Slot),
      ss.length = ps.length + 1 →
      Lam.applyAll L k (.clos ρ (lamsWith ps body)) ss =
        later k fun k => Lam.eval L k (ss.reverse ++ ρ) body
  | [], ρ, [s], _ => by
    rw [Lam.applyAll_cons, apply_clos_later]
    simp only [lamsWith, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ]
      cases Lam.eval L k (s :: ρ) body <;> rfl
  | p :: ps, ρ, s :: ss, h => by
    rw [Lam.applyAll_cons, apply_lamsWith_cons]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ, Result.bind_ok]
      rw [applyAll_tele (k + 1) body ps (s :: ρ) ss (by simp at h ⊢; omega)]
      simp [List.reverse_cons, List.append_assoc]
  | [], _, [], h => by simp at h
  | [], _, _ :: _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h

/-- Applying a telescope closure to fewer slots than it lacks: a charge,
then the extended closure. -/
theorem applyAll_tele_partial (k : Nat) (body : Lam.Term) :
    ∀ (ps : List (Mode × V3.BinderContract)) (ρ : Lam.Env) (ss : List Lam.Slot),
      ss ≠ [] → ss.length ≤ ps.length →
      Lam.applyAll L k (.clos ρ (lamsWith ps body)) ss =
        later k fun _ => .ok (.clos (ss.reverse ++ ρ) (lamsWith (ps.drop ss.length) body))
  | p :: ps, ρ, [s], _, _ => by
    rw [Lam.applyAll_cons, apply_lamsWith_cons]
    cases k with
    | zero => rfl
    | succ k => simp [Lam.applyAll_nil]
  | p :: ps, ρ, s :: s' :: ss, _, h => by
    rw [Lam.applyAll_cons, apply_lamsWith_cons]
    cases k with
    | zero => rfl
    | succ k =>
      simp only [later_succ, Result.bind_ok]
      rw [applyAll_tele_partial (k + 1) body ps (s :: ρ) (s' :: ss) (by simp) (by simp at h ⊢; omega)]
      simp [List.reverse_cons, List.append_assoc]
  | [], _, _ :: _, _, h => by simp at h
  | _, _, [], h, _ => absurd rfl h


end Compilatrix.Anf.Convert.Proof
