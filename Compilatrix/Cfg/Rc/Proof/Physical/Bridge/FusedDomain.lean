import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedWords

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt.Rc.Procs

/-- A return-marker write preserves all represented source variables when
its destination is absent from the actual source map. This does not identify
the real source-name bound with the larger lowering temporary supply. -/
theorem FusedWords.marker_fresh
    {addresses : AddressMap} {D : Nat → Prop} {bound dummy : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses D bound source target)
    (absent : source.get? dummy = none) (word : Lir.Word) :
    FusedWords addresses D bound source (target.insert dummy word) := by
  apply related.agree
  intro x value lookup _
  have different : dummy ≠ x := by
    intro equal
    subst x
    rw [absent] at lookup
    cases lookup
  exact Lir.env_insert_ne _ _ different

/-- Source-name bounds establish actual absence even when the target's
lowering supply also contains the reserved marker registers. -/
theorem FusedWords.reserved_absent
    {addresses : AddressMap} {D : Nat → Prop} {bound dummy : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses D bound source target) (reserved : bound ≤ dummy) :
    source.get? dummy = none := by
  cases lookup : source.get? dummy with
  | none => rfl
  | some value => have real := related.dom lookup; omega



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
