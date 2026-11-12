import IxCC.Own.Plain.Proof.Prefixes
import IxCC.Own.Plain.Proof.Environment

/-! `retained captured live`, the live variables a join captures, in scope order; and the
inversion of `EnvRoots` at a cons. The Cfg layer's token bookkeeping uses both. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

def retained (captured live : List Fir.Var) : List Fir.Var :=
  live.filter captured.contains

theorem envRoots_cons {ρ : Own.Env} {x : Fir.Var} {xs : List Fir.Var} {roots : List RVal}
    (h : EnvRoots ρ (x :: xs) roots) :
    ∃ v vs, ρ.get? x = some v ∧ EnvRoots ρ xs vs ∧ roots = v :: vs := by
  cases hx : ρ.get? x with
  | none => simp [EnvRoots, Own.evalArgs, Own.evalArg, hx] at h
  | some v =>
    cases ht : Own.evalArgs ρ (xs.map Fir.Arg.var) with
    | none => simp [EnvRoots, Own.evalArgs, Own.evalArg, hx, ht] at h
    | some vs =>
      exact ⟨v, vs, rfl, ht, by simpa [EnvRoots, Own.evalArgs, Own.evalArg, hx, ht] using h.symm⟩


end IxCC.Own.Plain
