import Compilatrix.Ixby.Runtime.Representation

/-! Source scalar operations agree with the pinned reference primitives.
Variable-size scalar limits remain premises of successful evaluation; field
and extension operations require no Nat or byte capacity assumption. -/

namespace Compilatrix.Ixby.Runtime.Representation

open Ix.Ixby

theorem eval_natToWord32 (limits : Limits) (n : Nat)
    (valid : (Scalar.nat n).validate limits = .ok ()) :
    Primitive.natToWord32.eval limits [.scalar (.nat n)] =
      .ok (.scalar (.word32 n.toUInt32)) := by
  simp [Primitive.eval, Primitive.arity, valid] <;> rfl

theorem eval_word32ToNat (limits : Limits) (word : UInt32)
    (valid : (Scalar.nat word.toNat).validate limits = .ok ()) :
    Primitive.word32ToNat.eval limits [.scalar (.word32 word)] =
      .ok (.scalar (.nat word.toNat)) := by
  simp [Primitive.eval, Primitive.arity, valid] <;> rfl

theorem eval_natAdd (limits : Limits) (a b : Nat)
    (left : (Scalar.nat a).validate limits = .ok ())
    (right : (Scalar.nat b).validate limits = .ok ())
    (result : (Scalar.nat (a + b)).validate limits = .ok ()) :
    Primitive.natAdd.eval limits [.scalar (.nat a), .scalar (.nat b)] =
      .ok (.scalar (.nat (a + b))) := by
  simp [Primitive.eval, Primitive.arity, left, right, result] <;> rfl

theorem eval_natSub (limits : Limits) (a b : Nat)
    (left : (Scalar.nat a).validate limits = .ok ())
    (right : (Scalar.nat b).validate limits = .ok ())
    (result : (Scalar.nat (a - b)).validate limits = .ok ()) :
    Primitive.natSub.eval limits [.scalar (.nat a), .scalar (.nat b)] =
      .ok (.scalar (.nat (a - b))) := by
  simp [Primitive.eval, Primitive.arity, left, right, result] <;> rfl

theorem eval_natMul (limits : Limits) (a b : Nat)
    (left : (Scalar.nat a).validate limits = .ok ())
    (right : (Scalar.nat b).validate limits = .ok ())
    (result : (Scalar.nat (a * b)).validate limits = .ok ()) :
    Primitive.natMul.eval limits [.scalar (.nat a), .scalar (.nat b)] =
      .ok (.scalar (.nat (a * b))) := by
  simp [Primitive.eval, Primitive.arity, left, right, result] <;> rfl

theorem eval_natDiv (limits : Limits) (a b : Nat)
    (left : (Scalar.nat a).validate limits = .ok ())
    (right : (Scalar.nat b).validate limits = .ok ())
    (result : (Scalar.nat (a / b)).validate limits = .ok ()) :
    Primitive.natDiv.eval limits [.scalar (.nat a), .scalar (.nat b)] =
      .ok (.scalar (.nat (a / b))) := by
  simp [Primitive.eval, Primitive.arity, left, right, result] <;> rfl

theorem eval_natMod (limits : Limits) (a b : Nat)
    (left : (Scalar.nat a).validate limits = .ok ())
    (right : (Scalar.nat b).validate limits = .ok ())
    (result : (Scalar.nat (a % b)).validate limits = .ok ()) :
    Primitive.natMod.eval limits [.scalar (.nat a), .scalar (.nat b)] =
      .ok (.scalar (.nat (a % b))) := by
  simp [Primitive.eval, Primitive.arity, left, right, result] <;> rfl

theorem eval_natEq (limits : Limits) (a b : Nat)
    (left : (Scalar.nat a).validate limits = .ok ())
    (right : (Scalar.nat b).validate limits = .ok ()) :
    Primitive.natEq.eval limits [.scalar (.nat a), .scalar (.nat b)] =
      .ok (.scalar (.bool (a == b))) := by
  simp [Primitive.eval, Primitive.arity, left, right] <;> rfl

private theorem eval_field_binary (limits : Limits) (a b : Goldilocks) :
    Primitive.fieldAdd.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.field (a.add b))) ∧
    Primitive.fieldSub.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.field (a.sub b))) ∧
    Primitive.fieldMul.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.field (a.mul b))) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate]
  exact ⟨rfl, rfl, rfl⟩

theorem eval_fieldAdd (limits : Limits) (a b : Goldilocks) :
    Primitive.fieldAdd.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.field (a.add b))) := (eval_field_binary limits a b).1

theorem eval_fieldSub (limits : Limits) (a b : Goldilocks) :
    Primitive.fieldSub.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.field (a.sub b))) := (eval_field_binary limits a b).2.1

theorem eval_fieldMul (limits : Limits) (a b : Goldilocks) :
    Primitive.fieldMul.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.field (a.mul b))) := (eval_field_binary limits a b).2.2

theorem eval_fieldInverse (limits : Limits) (a : Goldilocks) :
    Primitive.fieldInverse.eval limits [.scalar (.field a)] =
      .ok (.scalar (.field a.inverse)) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_fieldEq (limits : Limits) (a b : Goldilocks) :
    Primitive.fieldEq.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.bool (a.val == b.val))) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate,
    field_comparison_exact] <;> rfl

theorem eval_extAdd (limits : Limits) (a b : ExtGoldilocks) :
    Primitive.extAdd.eval limits [.scalar (.extField a), .scalar (.extField b)] =
      .ok (.scalar (.extField (a.add b))) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_extSub (limits : Limits) (a b : ExtGoldilocks) :
    Primitive.extSub.eval limits [.scalar (.extField a), .scalar (.extField b)] =
      .ok (.scalar (.extField (a.sub b))) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_extMul (limits : Limits) (a b : ExtGoldilocks) :
    Primitive.extMul.eval limits [.scalar (.extField a), .scalar (.extField b)] =
      .ok (.scalar (.extField (a.mul b))) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_extInverse (limits : Limits) (a : ExtGoldilocks) :
    Primitive.extInverse.eval limits [.scalar (.extField a)] =
      .ok (.scalar (.extField a.inverse)) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_extEq (limits : Limits) (a b : ExtGoldilocks) :
    Primitive.extEq.eval limits [.scalar (.extField a), .scalar (.extField b)] =
      .ok (.scalar (.bool (a == b))) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_extPack (limits : Limits) (a b : Goldilocks) :
    Primitive.extPack.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.extField ⟨a, b⟩)) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_extFst (limits : Limits) (a : ExtGoldilocks) :
    Primitive.extFst.eval limits [.scalar (.extField a)] = .ok (.scalar (.field a.c0)) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_extSnd (limits : Limits) (a : ExtGoldilocks) :
    Primitive.extSnd.eval limits [.scalar (.extField a)] = .ok (.scalar (.field a.c1)) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_word32ToField (limits : Limits) (word : UInt32) :
    Primitive.word32ToField.eval limits [.scalar (.word32 word)] =
      .ok (.scalar (.field (Goldilocks.reduce word.toNat))) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate] <;> rfl

theorem eval_fieldToBytes (limits : Limits) (field : Goldilocks)
    (capacity : 8 ≤ limits.byteArrayBytes) :
    Primitive.fieldToBytes.eval limits [.scalar (.field field)] =
      .ok (.scalar (.bytes (bytesLE 8 field.val))) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate,
    Nat.not_lt.mpr capacity] <;> rfl

theorem eval_bytesToField (limits : Limits) (field : Goldilocks)
    (capacity : 8 ≤ limits.byteArrayBytes) :
    Primitive.bytesToField.eval limits [.scalar (.bytes (bytesLE 8 field.val))] =
      .ok (.scalar (.field field)) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate,
    Nat.not_lt.mpr capacity, field_bytes_roundtrip, field.isLt] <;> rfl

/-- The evaluator rejects a noncanonical field encoding instead of reducing
it modulo p. Both the input capacity and the eight-byte width are explicit. -/
theorem eval_bytesToField_noncanonical (limits : Limits) (bytes : Array UInt8)
    (capacity : 8 ≤ limits.byteArrayBytes) (width : bytes.size = 8)
    (noncanonical : goldilocksModulus ≤ natOfBytesLE bytes) :
    Primitive.bytesToField.eval limits [.scalar (.bytes bytes)] =
      .error (.primitiveValue .bytesToField) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate,
    width, Nat.not_lt.mpr capacity, Nat.not_lt.mpr noncanonical] <;> rfl

theorem eval_bytesToWord32 (limits : Limits) (word : UInt32)
    (capacity : 4 ≤ limits.byteArrayBytes) :
    Primitive.bytesToWord32.eval limits [.scalar (.bytes (bytesLE 4 word.toNat))] =
      .ok (.scalar (.word32 word)) := by
  simp [Primitive.eval, Primitive.arity, Scalar.validate,
    Nat.not_lt.mpr capacity, word_bytes_roundtrip, Nat.toUInt32] <;> rfl

/-- The four native primitive invocations in the reconstruction suffix of
`fieldFromNatural`, for its mathematically specified low/high words. The
conversion loops that produce those words have separate machine obligations. -/
theorem eval_field_from_natural_words (limits : Limits) (n : Nat) :
    (do
      let low ← Primitive.word32ToField.eval limits
        [.scalar (.word32 (n % goldilocksModulus).toUInt32)]
      let high ← Primitive.word32ToField.eval limits
        [.scalar (.word32 ((n % goldilocksModulus) / 2 ^ 32).toUInt32)]
      let weighted ← Primitive.fieldMul.eval limits
        [high, .scalar (.field (Goldilocks.reduce (2 ^ 32)))]
      Primitive.fieldAdd.eval limits [low, weighted]) =
      .ok (.scalar (.field (Goldilocks.reduce n))) := by
  simp only [eval_word32ToField, eval_fieldMul, eval_fieldAdd, field_from_natural_words,
    bind, Except.bind]

/-- Native field byte roundtrip through both reference primitives. -/
theorem eval_field_bytes_roundtrip (limits : Limits) (field : Goldilocks)
    (capacity : 8 ≤ limits.byteArrayBytes) :
    ((Primitive.fieldToBytes.eval limits [.scalar (.field field)]).bind fun bytes =>
      Primitive.bytesToField.eval limits [bytes]) = .ok (.scalar (.field field)) := by
  rw [eval_fieldToBytes limits field capacity]
  exact eval_bytesToField limits field capacity

end Compilatrix.Ixby.Runtime.Representation
