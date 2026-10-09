import Compilatrix.Own.Rc.Proof.ReleaseValue
import Compilatrix.Own.Proof.Heap

/-! The source-to-counted-heap result relation. Successful returns carry one
owned result token and preserve every suspended external root's full value.
The source-stuck branch matches the existing Own refinement convention. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

open Rc
open Compilatrix.Sem (Result)

/-- Preserve complete values of valid external roots. Allocation may change
the interpretation of an arbitrary previously non-denoting location, so this
interface deliberately speaks about actual denotations rather than None. -/
def ExternalPreserved (before after : Heap) (external : Nat → Nat) : Prop :=
  ∀ root w, ExternalRoot external root → Proof.Den before root w → Proof.Den after root w

inductive ResultRel (before : Heap) (external : Nat → Nat) :
    Result Fir.Val → Result (RVal × Heap) → Prop
  | ok {w : Fir.Val} {v : RVal} {after : Heap}
      (den : Proof.Den after v w)
      (balance : Balance after external [v])
      (preserve : ExternalPreserved before after external) :
      ResultRel before external (.ok w) (.ok (v, after))
  | timeout : ResultRel before external .timeout .timeout
  | trap : ResultRel before external .trap .trap
  | resource (r : Sem.Resource) : ResultRel before external (.resource r) (.resource r)
  | stuck {target : Result (RVal × Heap)} : ResultRel before external .stuck target

theorem ResultRel.preheap {H₀ H₁ : Heap} {external : Nat → Nat}
    {source : Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ResultRel H₁ external source target)
    (hv : ExternalPreserved H₀ H₁ external) :
    ResultRel H₀ external source target := by
  cases h with
  | ok hd hb hp => exact .ok hd hb (fun root w hr hd => hp root w hr (hv root w hr hd))
  | timeout => exact .timeout
  | trap => exact .trap
  | resource r => exact .resource r
  | stuck => exact .stuck

/-- Every successful simulated call exposes its actual owned returned root
and preserves roots held by its caller; there is no assumed readback law. -/
theorem ResultRel.success {before : Heap} {external : Nat → Nat} {w : Fir.Val}
    {target : Result (RVal × Heap)} (h : ResultRel before external (.ok w) target) :
    ∃ v after, target = .ok (v, after) ∧ Proof.Den after v w ∧ Balance after external [v] ∧
      ExternalPreserved before after external := by
  cases h with
  | ok hd hb hp => exact ⟨_, _, rfl, hd, hb, hp⟩

end Compilatrix.Own.Plain
