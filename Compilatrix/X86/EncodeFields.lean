import Compilatrix.X86.EncodeBytes

/-! Register, prefix, ModRM and SIB field inverses. -/

namespace Compilatrix.X86.Encode

@[simp] theorem register_decode (register : GPR) :
    Decode.register (registerExtended (gprCode register)) (registerLow (gprCode register)) =
      some register := by
  cases register <;> rfl

@[simp] theorem index_decode (register : IndexReg) :
    Decode.index (registerExtended (indexRegCode register)) (registerLow (indexRegCode register)) =
      some (some register) := by
  cases register <;> rfl

@[simp] theorem index_none : Decode.index false 4 = some none := rfl

@[simp] theorem scale_decode (scale : Scale) : Decode.scale (scaleBits scale) = some scale := by
  cases scale <;> rfl

theorem low_lt (code : UInt8) : registerLow code < 8 := Nat.mod_lt _ (by decide)

@[simp] theorem modRM_mode (mode register rm : Nat) (bound : mode < 4) :
    Decode.modMode (modRM mode register rm) = mode := by
  have := Nat.mod_lt register (by decide : 0 < 8)
  have := Nat.mod_lt rm (by decide : 0 < 8)
  simp only [Decode.modMode, modRM, UInt8.toNat_ofNat']
  omega

@[simp] theorem modRM_register (mode register rm : Nat) :
    Decode.modReg (modRM mode register rm) = register % 8 := by
  have := Nat.mod_lt register (by decide : 0 < 8)
  have := Nat.mod_lt rm (by decide : 0 < 8)
  simp only [Decode.modReg, modRM, UInt8.toNat_ofNat']
  omega

@[simp] theorem modRM_rm (mode register rm : Nat) :
    Decode.modRM (modRM mode register rm) = rm % 8 := by
  have := Nat.mod_lt register (by decide : 0 < 8)
  have := Nat.mod_lt rm (by decide : 0 < 8)
  simp only [Decode.modRM, modRM, UInt8.toNat_ofNat']
  omega

@[simp] theorem sib_scale (scale index base : Nat) :
    Decode.modMode (sib scale index base) = scale % 4 := by
  exact modRM_mode _ _ _ (Nat.mod_lt _ (by decide))

@[simp] theorem sib_index (scale index base : Nat) :
    Decode.modReg (sib scale index base) = index % 8 := by
  exact modRM_register _ _ _

@[simp] theorem sib_base (scale index base : Nat) :
    Decode.modRM (sib scale index base) = base % 8 := by
  exact modRM_rm _ _ _

@[simp] theorem low_mod (code : UInt8) : registerLow code % 8 = registerLow code := by
  simp [registerLow]

@[simp] theorem scale_mod (scale : Scale) : scaleBits scale % 4 = scaleBits scale := by
  cases scale <;> rfl

@[simp] theorem rex_rexByte (w r x b : Bool) : Decode.rex? (rexByte w r x b) = some ⟨w, r, x, b⟩ := by
  cases w <;> cases r <;> cases x <;> cases b <;> rfl

@[simp] theorem rexByte_ne_escape (w r x b : Bool) : (rexByte w r x b == 0x66) = false := by
  cases w <;> cases r <;> cases x <;> cases b <;> rfl

@[simp] theorem rex_escape : Decode.rex? 0x0f = none := rfl

@[simp] theorem rex_rexByte_eta (rex : Decode.Rex) :
    Decode.rex? (rexByte rex.w rex.r rex.x rex.b) = some rex := by
  cases rex with
  | mk w r x b => exact rex_rexByte w r x b

@[simp] theorem rexByte_not_escape (w r x b : Bool) : rexByte w r x b ≠ 0x66 := by
  cases w <;> cases r <;> cases x <;> cases b <;> decide

theorem registerLow_gpr (register : GPR) : registerLow (gprCode register) = (gprCode register).toNat % 8 := rfl

theorem highByte_code (register : GPR) (extended : registerExtended (gprCode register) = false) :
    register.highByteCode = decide (4 ≤ registerLow (gprCode register)) := by
  cases register <;> simp_all [registerExtended, gprCode, registerLow, GPR.highByteCode]

end Compilatrix.X86.Encode
