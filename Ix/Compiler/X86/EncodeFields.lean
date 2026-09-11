import Ix.Compiler.X86.EncodeBytes

/-! Register, prefix, ModRM and SIB field inverses. -/

namespace Ix.Compiler.X86.Encode

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

theorem registers_decode (operand16 w : Bool) (reg rm : GPR) :
    Decode.registers
      ⟨operand16, w, registerExtended (gprCode reg), false, registerExtended (gprCode rm)⟩
      (modRM 3 (registerLow (gprCode reg)) (registerLow (gprCode rm))) = some (reg, rm) := by
  simp [Decode.registers]

theorem one_prefixes (operand16 w r x b : Bool) (opcode : UInt8) (rest : List UInt8)
    (notStack : (0x50 ≤ opcode.toNat && opcode.toNat < 0x60) = false) :
    Decode.one ((prefixes operand16 w r x b).data.toList ++ opcode :: rest) =
      Decode.prefixed ⟨operand16, w, r, x, b⟩ (opcode :: rest) := by
  cases operand16 <;> cases w <;> cases r <;> cases x <;> cases b <;>
    simp [prefixes, byte, Decode.one, Decode.rex, notStack]

end Ix.Compiler.X86.Encode
