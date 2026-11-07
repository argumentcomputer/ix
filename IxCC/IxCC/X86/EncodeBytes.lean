import IxCC.X86.Encode
import IxCC.X86.Decode
import IxCC.X86.Memory

/-! Kernel-checked byte-field laws for the table encoder and the independent
parser: little-endian fields, canonical immediates and displacements, and
the parser's evaluation rules. -/

namespace IxCC.X86.Encode

@[simp] theorem bytes_list (values : List UInt8) : (bytes values).data.toList = values := by
  simp [bytes]

@[simp] theorem bytes_size (values : List UInt8) : (bytes values).size = values.length := by
  simp [bytes, ByteArray.size]

@[simp] theorem byte_size (value : UInt8) : (byte value).size = 1 := by simp [byte]

/-! ## Running the parser -/

@[simp] theorem parse_bind (parser : Decode.Parser α) (next : α → Decode.Parser β) (input : List UInt8) :
    (parser >>= next) input = (parser input).bind fun result => next result.1 result.2 := rfl

@[simp] theorem parse_pure (value : α) (input : List UInt8) :
    (pure value : Decode.Parser α) input = some (value, input) := rfl

@[simp] theorem byte_cons (head : UInt8) (tail : List UInt8) :
    Decode.byte (head :: tail) = some (head, tail) := rfl

@[simp] theorem byte_nil : Decode.byte [] = none := rfl

@[simp] theorem fail_apply (input : List UInt8) : (Decode.fail : Decode.Parser α) input = none := rfl

@[simp] theorem lift_some (value : α) (input : List UInt8) :
    Decode.lift (some value) input = some (value, input) := rfl

@[simp] theorem lift_none (input : List UInt8) : Decode.lift (none : Option α) input = none := rfl

@[simp] theorem parse_map (f : α → β) (parser : Decode.Parser α) (input : List UInt8) :
    (f <$> parser) input = (parser input).bind fun result => some (f result.1, result.2) := rfl

/-! ## Little-endian fields -/

@[simp] theorem leNat_length (count value : Nat) : (leNat count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [leNat, ih]

@[simp] theorem le_length (count : Nat) (value : Word) : (le count value).length = count := by
  simp [le]

theorem readLE_leNat (count value : Nat) (rest : List UInt8) :
    Decode.readLE count (leNat count value ++ rest) = some (value % 256 ^ count, rest) := by
  induction count generalizing value with
  | zero => simp [leNat, Decode.readLE, Nat.mod_one]
  | succ count ih =>
      simp only [leNat, List.cons_append, Decode.readLE, parse_bind, byte_cons, Option.bind_some, ih,
        parse_pure, Option.some.injEq, Prod.mk.injEq, and_true]
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ count) 256, Nat.mod_mul]
      simp [UInt8.toNat_ofNat']

theorem readLE_le (count : Nat) (value : Word) (rest : List UInt8) :
    Decode.readLE count (le count value ++ rest) = some (value.toNat % 256 ^ count, rest) :=
  readLE_leNat count value.toNat rest

/-! ## Canonical immediates and displacements -/

@[simp] theorem uint8_ofNat_mod32 (value : UInt32) : UInt8.ofNat (value.toNat % 256) = value.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_ofNat', UInt32.toNat_toUInt8]

@[simp] theorem uint8_ofNat_mod64 (value : UInt64) : UInt8.ofNat (value.toNat % 256) = value.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_ofNat', UInt64.toNat_toUInt8]

@[simp] theorem uint16_ofNat_mod64 (value : UInt64) :
    UInt16.ofNat (value.toNat % 65536) = value.toUInt16 := by
  apply UInt16.toNat_inj.mp
  simp [UInt16.toNat_ofNat', UInt64.toNat_toUInt16]

@[simp] theorem uint32_ofNat_mod64 (value : UInt64) :
    UInt32.ofNat (value.toNat % 4294967296) = value.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_ofNat', UInt64.toNat_toUInt32]

theorem imm_decode (kind : ImmKind) (value : Word) (present : kind ≠ .none) :
    kind.norm (UInt64.ofNat (value.toNat % 256 ^ kind.bytes)) = kind.norm value := by
  cases kind <;> simp_all [ImmKind.norm, ImmKind.bytes]

theorem disp32_decode (displacement : Imm32) :
    UInt32.ofNat (displacement.toUInt64.toNat % 256 ^ 4) = displacement := by
  simp

theorem disp8_decode (displacement : Imm32) (fits : fitsDisp8 displacement = true) :
    (signExtend8 (UInt8.ofNat (displacement.toUInt64.toNat % 256 ^ 1))).toUInt32 = displacement := by
  simpa [fitsDisp8] using fits

theorem imm32_zero_list : le 4 0 = [0, 0, 0, 0] := rfl

theorem imm32_zero_bytes : imm32Bytes 0 = bytes [0, 0, 0, 0] := rfl

end IxCC.X86.Encode
