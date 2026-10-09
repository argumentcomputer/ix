import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Tokens

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs

/-- The actual accepted Cfg decrement effect is derived, not supplied. Both
the stale source environment and all suspended frames remain present; exactly
one live ownership occurrence disappears. This does not yet connect the
successor's Lir cursor to the actual consumed native instruction. -/
theorem decrement_cfg {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Cfg.Rc.Program} (accepted : Cfg.Rc.checkScopedProgram F bodies P = true)
    {addresses : AddressMap} {saved : List (SavedCaller addresses)}
    {H : Heap} {external : Nat → Nat} {x : Fir.Var} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {roots : List RVal} {fr : Cfg.Frame}
    {target : Lir.Frame} {bound : Nat} {joins : List Own.Plain.JEntry} {code : Own.Plain.Code}
    (before : Boundary F P addresses saved H external (x :: live) ρf ρo roots
      fr target bound joins (.act (.dec x) code)) :
    ∃ value remaining H' next,
      ρo.get? x = some value ∧ roots = value :: remaining ∧
      Own.Plain.evalAction ρo H (.dec x) = .ok H' ∧
      Cfg.Rc.step P (.run fr (savedStack saved) H) =
        .next (.run next (savedStack saved) H') false ∧
      Boundary F P addresses saved H' external live ρf ρo remaining
        next target bound joins code ∧
      (∀ root ∈ remaining, H.value? root = H'.value? root) ∧
      (∀ root ∈ savedRoots saved, H.value? root = H'.value? root) := by
  obtain ⟨value, remaining, H', lookup, equal, action, tokens, retained, held⟩ :=
    before.tokens.decrement
  obtain ⟨next, step, cursor⟩ := Cfg.Rc.At.action accepted before.cursor
    (stk := savedStack saved) action
  refine ⟨value, remaining, H', next, lookup, equal, action, step,
    ⟨tokens, cursor, before.registers, ?_⟩, retained, held⟩
  intro y member
  exact before.liveBound y (by simp [member])

end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
