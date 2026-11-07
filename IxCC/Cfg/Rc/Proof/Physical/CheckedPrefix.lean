import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Cfg.Rc.Proof.Physical.ActionPrefixCursor
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedDomain

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open Spec IxCC.Cfg.Rc.Proof.Physical.Bridge
open Cfg.Proof (Impl spine)
open IxCC.Rt.Rc.Procs

/-- The original checker bounds every actually emitted marker. An empty
prefix may choose the original real-name bound because it emits no slots.
Thus the physical prefix's freshness is derived even when the syntactic
marker supply is unconstrained by a marker-free continuation. -/
theorem checked_prefix_cursor
    {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {source : Cfg.Frame} {ρ : Own.Env} {saved : List Own.Plain.JEntry}
    {actions : List Action} {code : Own.Plain.Code}
    (layout : At F P source ρ saved (Own.Plain.actionPrefix actions code))
    {sourceFunction : Fir.Fun} (sourceLookup : F.fun? source.fn = some sourceFunction)
    {addresses : AddressMap} {D : Nat → Prop} {target : Lir.Env}
    (words : FusedWords addresses D sourceFunction.vars source.env target) :
    ∃ first tail,
      source.rest = encodePrefix P.base.size first actions ++ tail ∧
      At F P {source with rest := tail} ρ saved code ∧
      (∀ dummy, first ≤ dummy → source.env.get? dummy = none) := by
  obtain ⟨emitted, head, after⟩ := layout.action_prefix_cursor
  cases actions with
  | nil =>
    refine ⟨sourceFunction.vars, _, ?_, after, fun dummy bound => words.reserved_absent bound⟩
    simpa only [encodePrefix, List.nil_append] using head
  | cons action actions =>
    obtain ⟨fd, scope, params, acc, next, supply, lower, lookup, range, codeLayout, cursor,
      sub, bounded, names, joins⟩ := layout
    obtain ⟨terminal, blockLookup⟩ := Cfg.Proof.impl_head codeLayout
    have member : marker P.base.size emitted action ∈
        (acc.reverse ++ spine (skeleton P.base.size supply
          (Own.Plain.actionPrefix (action :: actions) code))) := by
      rw [← cursor, head]
      simp [encodePrefix]
    have markerBound := (checked_marker_bounds checked range sourceLookup lookup blockLookup
      member (reserved_marker P.base.size emitted action) (decode_marker P.base.size emitted action)).1
    exact ⟨emitted, _, head, after,
      fun dummy bound => words.reserved_absent (Nat.le_trans markerBound bound)⟩


end IxCC.Cfg.Rc.Native
