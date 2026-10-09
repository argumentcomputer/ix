import Compilatrix.Cfg.Rc.Proof.Physical.FusedLexical
import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Tokens
import Compilatrix.Own.Plain.Proof.CaptureRoots

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Own Compilatrix.Own.Rc

theorem Tokens.present {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots) :
    ∀ x ∈ live, ∃ value, ρo.get? x = some value := by
  intro x member
  obtain ⟨value, _, lookup, _⟩ := before.den x member
  exact ⟨value, lookup⟩

theorem env_absent_sub {lexical actual : Own.Env} (sub : EnvSub lexical actual)
    {x : Fir.Var} (absent : actual.get? x = none) : lexical.get? x = none := by
  cases lookup : lexical.get? x with
  | none => rfl
  | some value =>
    have found := sub x value lookup
    rw [absent] at found
    cases found

theorem envBounded_sub {lexical actual : Own.Env} {size : Nat}
    (sub : EnvSub lexical actual) (bounded : Own.Plain.EnvBounded size actual) :
    Own.Plain.EnvBounded size lexical := fun x value lookup => bounded x value (sub x value lookup)

theorem env_agree_live {lexical actual : Own.Env} {live : List Fir.Var}
    (sub : EnvSub lexical actual)
    (present : ∀ x ∈ live, ∃ value, lexical.get? x = some value) :
    ∀ x ∈ live, lexical.get? x = actual.get? x := by
  intro x member
  obtain ⟨value, lookup⟩ := present x member
  exact lookup.trans (sub x value lookup).symm

/-- The physical prefix may track the entire Cfg map. Additional populated
bindings acquire no root tokens; the live lexical roots are identical. -/
theorem Tokens.extend {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {lexical actual : Own.Env}
    (before : Tokens H external held live ρf lexical roots) (sub : EnvSub lexical actual) :
    Tokens H external held live ρf actual roots := by
  refine ⟨?_, Cfg.Proof.evalArgs_sub sub before.exactRoots, before.balance, before.distinct⟩
  intro x member
  obtain ⟨value, logical, lookup, source, den⟩ := before.den x member
  exact ⟨value, logical, sub x value lookup, source, den⟩

/-- Recover the lexical token view after the physical prefix. Original live
lookup receipts establish map agreement; no old-heap denotation is reused. -/
theorem Tokens.restrict {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {lexical actual : Own.Env}
    (before : Tokens H external held live ρf actual roots) (sub : EnvSub lexical actual)
    (present : ∀ x ∈ live, ∃ value, lexical.get? x = some value) :
    Tokens H external held live ρf lexical roots := by
  have agree := env_agree_live sub present
  refine ⟨?_, ?_, before.balance, before.distinct⟩
  · intro x member
    obtain ⟨value, logical, lookup, source, den⟩ := before.den x member
    exact ⟨value, logical, (agree x member).trans lookup, source, den⟩
  · change Own.evalArgs lexical (live.map Fir.Arg.var) = some roots
    rw [Own.Plain.evalVars_congr lexical actual live agree]
    exact before.exactRoots

def actionVariable : Action → Fir.Var
  | .inc x _ | .dec x => x

theorem evalActions_agree (lexical actual : Own.Env) (actions : List Action)
    (agree : ∀ action ∈ actions,
      lexical.get? (actionVariable action) = actual.get? (actionVariable action)) (H : Heap) :
    Own.Plain.evalActions lexical H actions = Own.Plain.evalActions actual H actions := by
  induction actions generalizing H with
  | nil => rfl
  | cons action actions ih =>
    have same : Own.Plain.evalAction lexical H action = Own.Plain.evalAction actual H action := by
      have lookup := agree action (by simp)
      cases action <;> simp only [actionVariable] at lookup <;>
        simp only [Own.Plain.evalAction, lookup]
    simp only [Own.Plain.evalActions, same]
    cases Own.Plain.evalAction actual H action <;>
      simp only [Sem.Result.bind] <;>
      exact ih (fun a ha => agree a (by simp [ha])) _

theorem copies_variables {live : List Fir.Var} (args : List Fir.Arg)
    (scope : args.all (Own.Plain.argIn live) = true) :
    ∀ action ∈ Own.Plain.copies args, actionVariable action ∈ live := by
  induction args with
  | nil => simp [Own.Plain.copies]
  | cons arg args ih =>
    have parts : Own.Plain.argIn live arg = true ∧ args.all (Own.Plain.argIn live) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using scope
    cases arg with
    | var x =>
      intro action member
      rcases List.mem_cons.mp member with rfl | member
      · simpa [actionVariable, Own.Plain.argIn] using parts.1
      · exact ih parts.2 action member
    | lit literal => exact ih parts.2
    | erased => exact ih parts.2

theorem drops_variables (captured live : List Fir.Var) :
    ∀ action ∈ Own.Plain.drops captured live, actionVariable action ∈ live := by
  induction live with
  | nil => simp [Own.Plain.drops]
  | cons x live ih =>
    intro action member
    by_cases retained : captured.contains x = true
    · have member' : action ∈ Own.Plain.drops captured live := by
        simpa only [Own.Plain.drops, retained, Bool.false_eq_true, ↓reduceIte] using member
      exact List.mem_cons_of_mem _ (ih action member')
    · have member' : action ∈ .dec x :: Own.Plain.drops captured live := by
        simpa only [Own.Plain.drops, retained, Bool.false_eq_true, ↓reduceIte] using member
      rcases List.mem_cons.mp member' with rfl | member'
      · simp [actionVariable]
      · exact List.mem_cons_of_mem _ (ih action member')

theorem copies_eval_sub {lexical actual : Own.Env} {live : List Fir.Var}
    (sub : EnvSub lexical actual)
    (present : ∀ x ∈ live, ∃ value, lexical.get? x = some value)
    (args : List Fir.Arg) (scope : args.all (Own.Plain.argIn live) = true) (H : Heap) :
    Own.Plain.evalActions lexical H (Own.Plain.copies args) =
      Own.Plain.evalActions actual H (Own.Plain.copies args) :=
  evalActions_agree lexical actual _
    (fun action member => env_agree_live sub present _ (copies_variables args scope action member)) H

theorem drops_eval_sub {lexical actual : Own.Env} (captured live : List Fir.Var)
    (sub : EnvSub lexical actual)
    (present : ∀ x ∈ live, ∃ value, lexical.get? x = some value) (H : Heap) :
    Own.Plain.evalActions lexical H (Own.Plain.drops captured live) =
      Own.Plain.evalActions actual H (Own.Plain.drops captured live) :=
  evalActions_agree lexical actual _
    (fun action member => env_agree_live sub present _ (drops_variables captured live action member)) H

theorem transfer_eval_sub {lexical actual : Own.Env} (captured live : List Fir.Var)
    (sub : EnvSub lexical actual)
    (present : ∀ x ∈ live, ∃ value, lexical.get? x = some value)
    (args : List Fir.Arg) (scope : args.all (Own.Plain.argIn live) = true) (H : Heap) :
    Own.Plain.evalActions lexical H (Own.Plain.copies args ++ Own.Plain.drops captured live) =
      Own.Plain.evalActions actual H (Own.Plain.copies args ++ Own.Plain.drops captured live) := by
  apply evalActions_agree
  intro action member
  apply env_agree_live sub present
  rcases List.mem_append.mp member with member | member
  · exact copies_variables args scope action member
  · exact drops_variables captured live action member






end Compilatrix.Cfg.Rc.Native
