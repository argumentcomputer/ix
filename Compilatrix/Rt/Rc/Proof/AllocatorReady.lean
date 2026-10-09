import Compilatrix.Rt.Rc.Proof.ReleaseInvariant
import Compilatrix.Rt.Rc.Proof.AllocBump

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

/-- Physical allocator control words and arena permissions augment the idle
ownership invariant. These are actual memory facts, not promises that the
allocator succeeds. The same external field tokens remain owned throughout
reservation; publication consumes them in the next interface. -/
structure AllocatorReady (heap : Own.Heap) (addresses : AddressMap) (mem : X86.Memory)
    (external : Nat → Nat) (context base bump limit : Word) (slots : List Slot)
    (lists : Nat → List Word) : Prop where
  idle : ReleaseInvariant heap addresses mem external none [] context base bump limit slots lists
  context_lower : 40 ≤ context.toNat
  context_before : context.toNat+8*33 ≤ base.toNat
  bump_aligned : bump.toNat % 8 = 0
  bump_word : WordAt mem (bumpAddress context) bump
  limit_word : WordAt mem (limitAddress context) limit
  bump_writable : ∀ j < 8, mem.writable (bumpAddress context+UInt64.ofNat j) = true
  arena_access : ∀ address : Word, base.toNat ≤ address.toNat → address.toNat < limit.toNat →
    mem.readable address = true ∧ mem.writable address = true

end Compilatrix.Rt.Rc.Procs
