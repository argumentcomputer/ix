import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Tokens
import Compilatrix.Own.Plain.Proof.Actions
import Compilatrix.Own.Plain.Proof.Bindings
import Compilatrix.Own.Plain.Proof.Scope

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge

/-- Constructor argument occurrences are held independently of the live
lexical roots. Turning them into heap edges preserves repeated aliases and
the suspended callers' token counts exactly. -/
theorem allocation_field_balance {H : Heap} {external : Nat → Nat}
    {fields held roots : List RVal} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external (fields ++ held) live ρf ρo roots) :
    Balance H (holdRoots external (roots ++ held)) fields := by
  intro location
  have count := before.balance location
  simp only [holdRoots, refsIn_append] at count ⊢
  omega

theorem allocation_tokens {H : Heap} {external : Nat → Nat}
    {fields held roots : List RVal} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external (fields ++ held) live ρf ρo roots)
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    (fresh : x ∉ live) (scope : args.all (Own.Plain.argIn live) = true)
    (arguments : Own.evalArgs ρo args = some fields) (arity : fields.length = ctor.arity)
    (positive : 0 < ctor.arity) :
    ∃ values,
      Fir.evalArgs ρf args = some values ∧
      let allocated := H.alloc .rc {ctor, fields}
      Own.Plain.evalRhs tables ρo H (.ctor ctor args) = .ok allocated ∧
      Tokens allocated.2 external held (live ++ [x])
        (ρf.insert x (.ctor ctor values)) (ρo.insert x allocated.1) (roots ++ [allocated.1]) ∧
      (∀ v w, Own.Proof.Den H v w → Own.Proof.Den allocated.2 v w) := by
  obtain ⟨actual, values, actualArgs, sourceArgs, den⟩ := Own.Plain.args_den before.den args scope
  have same : actual = fields := Option.some.inj (actualArgs.symm.trans arguments)
  subst actual
  obtain ⟨effect, counts, result, preserve⟩ :=
    Own.Plain.evalRhs_alloc_owned (T := tables) arguments arity positive (allocation_field_balance before) den
  refine ⟨values, sourceArgs, effect, ?_, preserve⟩
  have oldDen : Own.Plain.EnvDen (H.alloc .rc {ctor, fields}).2 live ρf ρo := by
    intro y member
    obtain ⟨v, w, lookup, source, represented⟩ := before.den y member
    exact ⟨v, w, lookup, source, preserve v w represented⟩
  refine {
    den := oldDen.insert x result
    exactRoots := before.exactRoots.insert x _ fresh
    balance := ?_
    distinct := ?_ }
  · intro location
    have count := counts location
    simp only [holdRoots, refsIn_append] at count ⊢
    omega
  · exact Own.Plain.fresh_nodup_append before.distinct (by simp [Own.Plain.fresh, fresh])



end Compilatrix.Cfg.Rc.Native
