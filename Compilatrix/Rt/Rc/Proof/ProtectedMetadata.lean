import Compilatrix.Rt.Rc.Proof.ProtectedFrame

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

/-- A control word strictly below the context lies outside the class-head
write table; the explicit context/base ordering also places it outside all
object writes. -/
theorem ProtectedFrame.word_before_context
    {before after : X86.Memory} {context base bump address value : Word}
    (h : ProtectedFrame before after context base bump) (hw : WordAt before address value)
    (hfit : context.toNat < 2^63) (hword : address.toNat+8 ≤ context.toNat)
    (hbase : context.toNat ≤ base.toNat) : WordAt after address value := by
  apply h.word hw
  · intro j hj
    have hj' : (address+UInt64.ofNat j).toNat = address.toNat+j := addr_toNat (by omega)
    left; rw [hj']; omega
  · intro j hj
    have hj' : (address+UInt64.ofNat j).toNat = address.toNat+j := addr_toNat (by omega)
    left; rw [hj']; omega

/-- General negative-offset allocator metadata, including ctx−40 bump and
ctx−32 limit. No modular-address or separation assumption is implicit. -/
theorem ProtectedFrame.context_word
    {before after : X86.Memory} {context base bump value : Word} (offset : Nat)
    (h : ProtectedFrame before after context base bump)
    (hw : WordAt before (context-UInt64.ofNat offset) value)
    (hfit : context.toNat < 2^63) (hoff : 8 ≤ offset) (hunder : offset ≤ context.toNat)
    (hbase : context.toNat ≤ base.toNat) :
    WordAt after (context-UInt64.ofNat offset) value := by
  apply h.word_before_context hw hfit _ hbase
  have hn : (UInt64.ofNat offset).toNat = offset := toNat_ofNat_lt (by omega)
  rw [sub_toNat_of_le (by rw [hn]; exact hunder), hn]
  omega



end Compilatrix.Rt.Rc.Procs
