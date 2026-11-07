import IxCC.Rt.Rc.Proof.Readback.Capacity
import IxCC.Rt.Rc.Proof.Readback.Structural

set_option autoImplicit false
namespace IxCC.Rt.Rc.Procs.Readback
open IxCC.Lir (Word)
open IxCC.Own
open IxCC.Rt.Proof (Typed)

/-- The actual driver fuel, region bytes divided by eight, suffices for the
complete represented constructor tree even after physical address reuse. -/
theorem readback_region {H : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {base bump limit : Word} {slots : List Slot} {regionBytes : Nat}
    (heap : HeapLive H addresses mem)
    (partition : ArenaPartition H addresses base bump limit slots)
    (ordered : Own.Rc.HeapOk H)
    (region : limit.toNat-base.toNat ≤ regionBytes)
    {v : RVal} {logical : Fir.Val} {word : Word} {sig : Sig} {ty : FoTy}
    (den : Own.Proof.Den H v logical) (typed : Typed sig H ty v)
    (represented : valueWord addresses v = some word) :
    Rt.readback sig (regionBytes/8) mem ty word = Fir.readback logical := by
  rw [readback_toFir heap _ typed represented]
  have small := liveBefore_capacity heap partition region
  have exactValue := Own.Proof.toFir_ext (Own.Proof.Ext.refl H) small
    (toFir_totalLive ordered den)
  rw [exactValue]
  rfl


end IxCC.Rt.Rc.Procs.Readback
