import IxCC.Cfg.Rc.Proof.Physical.PublishMemory
import IxCC.Rt.Rc.Gen.Proof.ObjectFrame

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt.Rc
open IxCC.Lir
open IxCC.Rt.Proof
open IxCC.Rt.Rc.Procs

theorem publishFields_objectFrame (indices : List Nat) (address : Word) (words : Nat → Word)
    {target : Word} {bytes : Nat} (targetFit : target.toNat + bytes ≤ 2^64)
    (fits : ∀ i ∈ indices, (fieldAddress address i).toNat + 8 ≤ 2^64)
    (separate : ∀ i ∈ indices,
      target.toNat + bytes ≤ (fieldAddress address i).toNat ∨
        (fieldAddress address i).toNat + 8 ≤ target.toNat)
    (mem : X86.Memory) :
    ObjectFrame mem (publishFields mem address words indices) target bytes := by
  induction indices generalizing mem with
  | nil => exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons i indices ih =>
    have first := objectFrame_write mem target (fieldAddress address i) (words i) bytes .w64
      targetFit (fits i (by simp)) (separate i (by simp))
    exact first.trans (ih (fun j hj => fits j (by simp [hj]))
      (fun j hj => separate j (by simp [hj])) _)

theorem publishFields_headerFrame {address : Word} {count : Nat}
    (fit : address.toNat + 8 * (count + 1) < 2^63)
    (words : Nat → Word) (mem : X86.Memory) :
    ObjectFrame mem (publishFields mem address words (List.range count)) address 8 := by
  apply publishFields_objectFrame (List.range count) address words (by omega)
    (fun i hi => fieldAddress_fit fit (List.mem_range.mp hi)) (fun i hi => ?_) mem
  left
  rw [fieldAddress_nat fit (List.mem_range.mp hi)]
  omega

theorem fieldAddress_byte (address : Word) (i byte : Nat) :
    fieldAddress address i + UInt64.ofNat byte = address + UInt64.ofNat (8 * (i + 1) + byte) := by
  simp only [fieldAddress, UInt64.ofNat_add, UInt64.add_assoc]



end IxCC.Cfg.Rc.Native
