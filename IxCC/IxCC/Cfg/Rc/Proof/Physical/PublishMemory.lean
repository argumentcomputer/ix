import IxCC.Cfg.Rc.Proof.Physical.Publish

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt.Proof

theorem fieldAddress_nat {address : Word} {i count : Nat}
    (fit : address.toNat + 8 * (count + 1) < 2^63) (bound : i < count) :
    (fieldAddress address i).toNat = address.toNat + 8 * (i + 1) := by
  unfold fieldAddress
  apply addr_toNat
  omega

theorem fieldAddress_fit {address : Word} {i count : Nat}
    (fit : address.toNat + 8 * (count + 1) < 2^63) (bound : i < count) :
    (fieldAddress address i).toNat + 8 ≤ 2^64 := by
  rw [fieldAddress_nat fit bound]
  omega

theorem fieldAddress_disjoint {address : Word} {i j count : Nat}
    (fit : address.toNat + 8 * (count + 1) < 2^63)
    (ib : i < count) (jb : j < count) (different : i ≠ j) :
    (fieldAddress address i).toNat + 8 ≤ (fieldAddress address j).toNat ∨
      (fieldAddress address j).toNat + 8 ≤ (fieldAddress address i).toNat := by
  rw [fieldAddress_nat fit ib, fieldAddress_nat fit jb]
  omega

/-- Publication frames every word disjoint from its actual payload stores. -/
theorem publishFields_frame (indices : List Nat) (address : Word) (words : Nat → Word)
    {target word : Word} (targetFit : target.toNat + 8 ≤ 2^64)
    (fits : ∀ i ∈ indices, (fieldAddress address i).toNat + 8 ≤ 2^64)
    (separate : ∀ i ∈ indices,
      target.toNat + 8 ≤ (fieldAddress address i).toNat ∨
        (fieldAddress address i).toNat + 8 ≤ target.toNat)
    {mem : X86.Memory} (before : WordAt mem target word) :
    WordAt (publishFields mem address words indices) target word := by
  induction indices generalizing mem with
  | nil => exact before
  | cons i indices ih =>
    apply ih (fun j hj => fits j (by simp [hj]))
      (fun j hj => separate j (by simp [hj]))
    exact before.write_disjoint (fits i (by simp)) targetFit (separate i (by simp))

/-- Every published field contains its exact input word, through any later
stores in the wrapper. This uses concrete disjoint word intervals. -/
theorem publishFields_word (indices : List Nat) (address : Word) (words : Nat → Word)
    {count index : Nat} (fit : address.toNat + 8 * (count + 1) < 2^63)
    (bounds : ∀ i ∈ indices, i < count) (distinct : indices.Nodup)
    (member : index ∈ indices) {mem : X86.Memory}
    (readable : ∀ byte < 8, mem.readable (fieldAddress address index + UInt64.ofNat byte) = true) :
    WordAt (publishFields mem address words indices) (fieldAddress address index) (words index) := by
  induction indices generalizing mem with
  | nil => simp at member
  | cons i indices ih =>
    have tailBounds : ∀ j ∈ indices, j < count := fun j hj => bounds j (by simp [hj])
    have tailDistinct := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with rfl | member
    · apply publishFields_frame indices address words
        (fieldAddress_fit fit (bounds index (by simp)))
        (fun j hj => fieldAddress_fit fit (tailBounds j hj))
        (fun j hj => fieldAddress_disjoint fit (bounds index (by simp)) (tailBounds j hj) (by
          intro same
          subst j
          exact tailDistinct.1 hj))
      exact wordAt_write64 readable
    · apply ih tailBounds tailDistinct.2 member
      intro byte hb
      simpa [X86.Memory.write] using readable byte hb

theorem publishFields_header {address header : Word} {count : Nat}
    (fit : address.toNat + 8 * (count + 1) < 2^63)
    (words : Nat → Word) {mem : X86.Memory} (before : WordAt mem address header) :
    WordAt (publishFields mem address words (List.range count)) address header := by
  apply publishFields_frame (List.range count) address words (by omega)
    (fun i hi => fieldAddress_fit fit (List.mem_range.mp hi))
    (fun i hi => ?_) before
  left
  rw [fieldAddress_nat fit (List.mem_range.mp hi)]
  omega



end IxCC.Cfg.Rc.Native
