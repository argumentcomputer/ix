import IxCC.Cfg.Rc.Proof.Physical.Placement
import IxCC.Src.Proof.NatMap

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc.Procs

theorem EnvWordsBelow.bind {addresses : AddressMap} {bound destination : Nat}
    {source : Own.Env} {target : Lir.Env} {value : Own.RVal} {word : Lir.Word}
    (related : EnvWordsBelow addresses bound source target)
    (represented : valueWord addresses value = some word) :
    EnvWordsBelow addresses bound (source.insert destination value) (target.insert destination word) := by
  intro x other real lookup
  by_cases same : x = destination
  · subst x
    rw [Src.NatMap.get?_insert_self] at lookup
    have equal := Option.some.inj lookup
    subst other
    exact ⟨word, represented, Lir.env_insert_self _ _ _⟩
  · rw [Src.NatMap.get?_insert_ne _ _ same] at lookup
    obtain ⟨actual, representation, register⟩ := related x other real lookup
    refine ⟨actual, representation, ?_⟩
    rw [Lir.env_insert_ne _ _ (Ne.symm same)]
    exact register

/-- After publication, the actual returned pointer represents the fresh
logical result; all previous real registers retain their meanings, including
inactive registers that still refer to older dead logical locations. -/
theorem EnvWordsBelow.publish {addresses : AddressMap} {fresh bound destination : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : EnvWordsBelow addresses bound source target)
    (bounded : Own.Plain.EnvBounded fresh source) (address : Lir.Word) :
    EnvWordsBelow (IxCC.Cfg.Rc.Native.placeFresh addresses fresh address) bound
      (source.insert destination (.loc fresh)) (target.insert destination address) :=
  (related.placeFresh bounded address).bind (placeFresh_new addresses fresh address)



end IxCC.Cfg.Rc.Native
