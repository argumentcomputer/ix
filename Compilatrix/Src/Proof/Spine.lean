import Compilatrix.Src.Proof.Unfold

/-! # SrcEval on application spines

E7 builds one slot per argument (`slotOf`: `irr` where the argument is
irrelevant at the levels, else strict or by name) and applies the head to
it, left to right; `eval_mkApps` evaluates a whole spine that way
(`applySpine`). A special head accumulates its slots for free and fires at
its arity, so a saturated spine is "build every slot, then fire"
(`applySpine_pap_sat`). M2.2's erasure simulation reads spines through these
equations. -/

namespace Compilatrix.Src

open Compilatrix.Sem (Result)

variable (p : Program) (k : Nat) (ls : Levels) (ρ : Env)

/-- E7's slot for one argument. -/
def slotOf : Term.Arg → Result Slot
  | (a, m, r) =>
    if r.irrAt ls then .ok (.val (.irr (some a) ρ ls))
    else match m with
      | .strict => (eval p k ls ρ a).bind fun x => .ok (.val x)
      | .byName => .ok (.name a ρ ls)

/-- The slots of several arguments, left to right. -/
def slotsOf : List Term.Arg → Result (List Slot)
  | [] => .ok []
  | a :: as => (slotOf p k ls ρ a).bind fun s => (slotsOf as).bind fun ss => .ok (s :: ss)

/-- Apply a value to the slots of a spine's arguments, left to right. -/
def applySpine : Value → List Term.Arg → Result Value
  | f, [] => .ok f
  | f, a :: as => (slotOf p k ls ρ a).bind fun s => (apply p k f s).bind fun v => applySpine v as

theorem eval_app_slot (f a : Term) (m : Mode) (r : Rel) :
    eval p k ls ρ (.app f a m r) =
      (eval p k ls ρ f).bind fun fv => (slotOf p k ls ρ (a, m, r)).bind (apply p k fv) := by
  rw [eval_app]
  apply Result.bind_congr
  intro fv
  simp only [slotOf]
  split
  · rfl
  · cases m with
    | strict => rw [Sem.Result.bind_assoc]; rfl
    | byName => rfl

theorem eval_mkApps : ∀ (h : Term) (args : List Term.Arg),
    eval p k ls ρ (Term.mkApps h args) = (eval p k ls ρ h).bind (applySpine p k ls ρ · args)
  | h, [] => by simp [Term.mkApps, applySpine, Sem.Result.bind_pure]
  | h, (a, m, r) :: args => by
    have e : Term.mkApps h ((a, m, r) :: args) = Term.mkApps (.app h a m r) args := rfl
    rw [e, eval_mkApps, eval_app_slot, Sem.Result.bind_assoc]
    apply Result.bind_congr
    intro fv
    rw [Sem.Result.bind_assoc]
    rfl

theorem applySpine_append (f : Value) :
    ∀ (as bs : List Term.Arg),
      applySpine p k ls ρ f (as ++ bs) = (applySpine p k ls ρ f as).bind (applySpine p k ls ρ · bs)
  | [], bs => by simp [applySpine]
  | a :: as, bs => by
    simp only [List.cons_append, applySpine, Sem.Result.bind_assoc]
    apply Result.bind_congr
    intro s
    apply Result.bind_congr
    intro v
    exact applySpine_append v as bs

theorem slotsOf_length :
    ∀ (as : List Term.Arg) (ss : List Slot), slotsOf p k ls ρ as = .ok ss → ss.length = as.length
  | [], ss, h => by simp [slotsOf] at h; subst h; rfl
  | a :: as, ss, h => by
    simp only [slotsOf] at h
    cases hs : slotOf p k ls ρ a with
    | ok s =>
      rw [hs] at h
      simp only [Result.bind] at h
      cases hr : slotsOf p k ls ρ as with
      | ok ss' =>
        rw [hr] at h
        simp only [Result.ok.injEq] at h
        subst h
        simp [slotsOf_length as ss' hr]
      | _ => rw [hr] at h; simp at h
    | _ => rw [hs] at h; simp [Result.bind] at h

/-- Accumulating a special head's slots below its arity is free. -/
theorem applySpine_pap_lt (h : Head) (ls' : Levels) :
    ∀ (acc : List Slot) (as : List Term.Arg), acc.length + as.length < p.headArity h →
      applySpine p k ls ρ (.pap h ls' acc) as =
        (slotsOf p k ls ρ as).bind fun ss => .ok (.pap h ls' (acc ++ ss))
  | acc, [], _ => by simp [applySpine, slotsOf]
  | acc, a :: as, hlt => by
    simp only [applySpine, slotsOf, Sem.Result.bind_assoc]
    apply Result.bind_congr
    intro s
    have hl : (acc ++ [s]).length < p.headArity h := by simp at hlt ⊢; omega
    rw [apply_pap]
    simp only [show ((acc ++ [s]).length == p.headArity h) = false by
      simp at hl ⊢; omega, hl, ite_true, Bool.false_eq_true, ite_false, Sem.Result.bind_ok]
    rw [applySpine_pap_lt h ls' (acc ++ [s]) as (by simp at hlt ⊢; omega)]
    apply Result.bind_congr
    intro ss
    simp

/-- A special head fires once its arity of slots is built. -/
theorem applySpine_pap_sat (h : Head) (ls' : Levels) :
    ∀ (acc : List Slot) (as : List Term.Arg), as ≠ [] → acc.length + as.length = p.headArity h →
      applySpine p k ls ρ (.pap h ls' acc) as =
        (slotsOf p k ls ρ as).bind fun ss => fire p k h ls' (acc ++ ss)
  | _, [], hne, _ => absurd rfl hne
  | acc, [a], _, heq => by
    simp only [applySpine, slotsOf, Sem.Result.bind_assoc]
    apply Result.bind_congr
    intro s
    rw [apply_pap]
    simp only [show ((acc ++ [s]).length == p.headArity h) = true by simp at heq ⊢; omega,
      ite_true, Result.bind]
    cases fire p k h ls' (acc ++ [s]) <;> rfl
  | acc, a :: b :: as, _, heq => by
    simp only [applySpine, slotsOf, Sem.Result.bind_assoc]
    apply Result.bind_congr
    intro s
    have hl : (acc ++ [s]).length < p.headArity h := by simp at heq ⊢; omega
    rw [apply_pap]
    simp only [show ((acc ++ [s]).length == p.headArity h) = false by
      simp at hl ⊢; omega, hl, ite_true, Bool.false_eq_true, ite_false, Sem.Result.bind_ok]
    have e := applySpine_pap_sat h ls' (acc ++ [s]) (b :: as) (by simp)
      (by simp at heq ⊢; omega)
    simp only [applySpine, slotsOf] at e
    rw [e]
    simp only [Sem.Result.bind_assoc]
    apply Result.bind_congr
    intro s'
    apply Result.bind_congr
    intro ss
    simp

end Compilatrix.Src
