import IxCC.Own.Plain.Proof.Owned.Reach

/-! The source-to-counted-heap result relation. Successful returns carry one
owned result token and preserve every suspended external root's full value
and every live cell reachable from external roots (`ReachablePreserved`).
The source-stuck branch matches the existing Own refinement convention. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)

/-- Preserve complete values of valid external roots. Allocation may change
the interpretation of an arbitrary previously non-denoting location, so this
interface deliberately speaks about actual denotations rather than None. -/
def ExternalPreserved (before after : Heap) (external : Nat → Nat) : Prop :=
  ∀ root w, ExternalRoot external root → Proof.Den before root w → Proof.Den after root w

theorem ReachablePreserved.externalPreserved {before after : Heap} {external : Nat → Nat}
    (hp : ReachablePreserved before after external) : ExternalPreserved before after external :=
  fun root _ hr hd => hp.den (ReachableFrom.of_externalRoot hr) hd

inductive ResultRel (before : Heap) (external : Nat → Nat) :
    Result Fir.Val → Result (RVal × Heap) → Prop
  | ok {w : Fir.Val} {v : RVal} {after : Heap}
      (den : Proof.Den after v w)
      (balance : Balance after external [v])
      (preserve : ExternalPreserved before after external)
      (reach : ReachablePreserved before after external) :
      ResultRel before external (.ok w) (.ok (v, after))
  | timeout : ResultRel before external .timeout .timeout
  | trap : ResultRel before external .trap .trap
  | resource (r : Sem.Resource) : ResultRel before external (.resource r) (.resource r)
  | stuck {target : Result (RVal × Heap)} : ResultRel before external .stuck target

theorem ResultRel.preheap {H₀ H₁ : Heap} {external : Nat → Nat}
    {source : Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ResultRel H₁ external source target)
    (hr : ReachablePreserved H₀ H₁ external) :
    ResultRel H₀ external source target := by
  cases h with
  | ok hd hb hp hreach =>
    exact .ok hd hb (fun root w he hd' => hp root w he (hr.externalPreserved root w he hd'))
      (hr.trans hreach)
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
  | ok hd hb hp _ => exact ⟨_, _, rfl, hd, hb, hp⟩

/-- Strengthened result relation used internally by `Owned.Simulation`: additionally tracks
private-frame preservation (`PrivPreserved`), non-aliasing of the returned value against private
locations (`retNoPriv`), and `@unique` return guarantees (`UniqVal`). Projects directly to
`ResultRel`. -/
inductive ResultRelFull (before : Heap) (external : Nat → Nat) (priv : Nat → Prop)
    (ctors : List Lam.CtorInfo) (retUniq : Bool) :
    Result Fir.Val → Result (RVal × Heap) → Prop
  | ok {w : Fir.Val} {v : RVal} {after : Heap}
      (den : Proof.Den after v w)
      (balance : Balance after external [v])
      (preserve : ExternalPreserved before after external)
      (reach : ReachablePreserved before after external)
      (privPres : PrivPreserved before after priv)
      (retNoPriv : ∀ l, priv l → v ≠ .loc l)
      (retU : retUniq = true → UniqVal ctors after external [v] v) :
      ResultRelFull before external priv ctors retUniq (.ok w) (.ok (v, after))
  | timeout : ResultRelFull before external priv ctors retUniq .timeout .timeout
  | trap : ResultRelFull before external priv ctors retUniq .trap .trap
  | resource (r : Sem.Resource) :
      ResultRelFull before external priv ctors retUniq (.resource r) (.resource r)
  | stuck {target : Result (RVal × Heap)} :
      ResultRelFull before external priv ctors retUniq .stuck target

theorem ResultRelFull.toResultRel {before : Heap} {external : Nat → Nat} {priv : Nat → Prop}
    {ctors : List Lam.CtorInfo} {retUniq : Bool}
    {source : Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ResultRelFull before external priv ctors retUniq source target) :
    ResultRel before external source target := by
  cases h with
  | ok hd hb hp hr _ _ _ => exact .ok hd hb hp hr
  | timeout => exact .timeout
  | trap => exact .trap
  | resource r => exact .resource r
  | stuck => exact .stuck

theorem ResultRelFull.preheap {H₀ H₁ : Heap} {external : Nat → Nat} {priv : Nat → Prop}
    {ctors : List Lam.CtorInfo} {retUniq : Bool}
    {source : Result Fir.Val} {target : Result (RVal × Heap)}
    (h : ResultRelFull H₁ external priv ctors retUniq source target)
    (hr : ReachablePreserved H₀ H₁ external) (hpv : PrivPreserved H₀ H₁ priv) :
    ResultRelFull H₀ external priv ctors retUniq source target := by
  cases h with
  | ok hd hb hp hreach hpriv hret hru =>
    exact .ok hd hb (fun root w he hd' => hp root w he (hr.externalPreserved root w he hd'))
      (hr.trans hreach) (hpv.trans hpriv) hret hru
  | timeout => exact .timeout
  | trap => exact .trap
  | resource r => exact .resource r
  | stuck => exact .stuck

end IxCC.Own.Plain
