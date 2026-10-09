import Compilatrix.Cfg.Rc.Proof.Physical.TokenEnvironments
import Compilatrix.Own.Plain.Proof.State

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Own Compilatrix.Own.Rc

/-- Extend the active lexical view to the actual Cfg map, retaining exactly
the same owned roots and saved join environments. Extra stale entries are
represented by the frame invariant and acquire no ownership. -/
theorem state_extend {functions : Own.Plain.Signatures} {H : Heap} {external : Nat → Nat}
    {held roots : List RVal} {live : List Fir.Var} {ρf : Fir.Env} {lexical actual : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    (before : Own.Plain.State functions H (holdRoots external held) live ρf lexical roots joins Jf Jo)
    (sub : EnvSub lexical actual) :
    Own.Plain.State functions H (holdRoots external held) live ρf actual roots joins Jf Jo := by
  have tokens := Tokens.extend (Tokens.ofState before) sub
  have agree := env_agree_live sub (Tokens.present (Tokens.ofState before))
  refine ⟨tokens.den, tokens.exactRoots, tokens.balance, tokens.distinct, before.stack, ?_, before.scope⟩
  cases before.views with
  | nil => exact .nil _ _
  | cons view tail =>
    exact .cons ⟨view.order, view.distinct,
      fun x member => (view.agree x member).trans (agree x (view.order.subset member))⟩ tail


end Compilatrix.Cfg.Rc.Native
