import IxCC.X86.EncodeMemory

/-! The decoder's stages on encoder output: the optional operand-size and
REX prefixes, the opcode map, the row lookup, and the operand fields of
each ModRM use (none, a register, or an opcode extension). -/

namespace IxCC.X86.Encode

/-! ## Prefixes and opcode -/

/-- Whether the encoder emits a REX prefix. -/
def rexPresent (enc : EncDesc) (f : Fields) : Bool :=
  enc.rexW || rexR enc f || (tail enc f).rexX || (tail enc f).rexB || byteForce enc f

def rexBits (enc : EncDesc) (f : Fields) : Decode.Rex :=
  ⟨enc.rexW, rexR enc f, (tail enc f).rexX, (tail enc f).rexB⟩

/-- The REX prefix as the decoder sees it. -/
def rexView (enc : EncDesc) (f : Fields) : Option Decode.Rex :=
  if rexPresent enc f then some (rexBits enc f) else none

theorem rexPrefix_view (enc : EncDesc) (f : Fields) :
    rexPrefix enc f = match rexView enc f with
      | some rex => [rexByte rex.w rex.r rex.x rex.b]
      | none => [] := by
  unfold rexPrefix rexView rexPresent rexBits
  by_cases present : (enc.rexW || rexR enc f || (tail enc f).rexX || (tail enc f).rexB ||
      byteForce enc f) = true
  · simp only [present, ite_true]
  · simp only [present, ite_false, Bool.false_eq_true]

theorem rexView_bits (enc : EncDesc) (f : Fields) : Decode.Rex.bits (rexView enc f) = rexBits enc f := by
  unfold rexView Decode.Rex.bits rexBits
  split
  · rfl
  · rename_i absent
    simp only [rexPresent, Bool.or_eq_true, not_or, Bool.not_eq_true] at absent
    simp [absent]

/-- The opcode byte, with an embedded register's low bits. -/
def opcodeByte (enc : EncDesc) (f : Fields) : UInt8 :=
  match enc.emb with
  | .regLow3 => enc.opcode + UInt8.ofNat (match f.reg with
      | some register => registerLow (gprCode register)
      | none => 0)
  | .none => enc.opcode

theorem opcodeBytes_split (enc : EncDesc) (f : Fields) :
    opcodeBytes enc f = (if enc.map == .x0F then [0x0f] else []) ++ [opcodeByte enc f] := rfl

theorem stages_decode (enc : EncDesc) (f : Fields) (after : List UInt8)
    (clear : Table.opcodeClear enc.map (opcodeByte enc f) = true) :
    Decode.one ((if enc.p66 then [0x66] else []) ++ rexPrefix enc f ++ opcodeBytes enc f ++ after) =
      Decode.body enc.p66 (rexView enc f) enc.map (opcodeByte enc f) after := by
  rw [rexPrefix_view, opcodeBytes_split]
  cases hmap : enc.map with
  | x0F =>
      cases hview : rexView enc f with
      | some rex =>
          cases hp : enc.p66 <;>
            simp [Decode.one, Decode.rexStage, Decode.opcodeStage]
      | none =>
          cases hp : enc.p66 <;>
            simp [Decode.one, Decode.rexStage, Decode.opcodeStage]
  | legacy =>
      simp only [Table.opcodeClear, hmap, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
        Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt] at clear
      obtain ⟨⟨notEscape, notMap⟩, notRex⟩ := clear
      have noRex : Decode.rex? (opcodeByte enc f) = none := by
        unfold Decode.rex?
        split
        · rename_i inside
          simp only [Bool.and_eq_true, decide_eq_true_eq] at inside
          omega
        · rfl
      have notEscape' : (opcodeByte enc f == 0x66) = false := by simpa using notEscape
      have notMap' : (opcodeByte enc f == 0x0f) = false := by simpa using notMap
      cases hview : rexView enc f with
      | some rex =>
          cases hp : enc.p66 <;>
            simp [Decode.one, Decode.rexStage, Decode.opcodeStage, notMap]
      | none =>
          cases hp : enc.p66 <;>
            simp [Decode.one, Decode.rexStage, Decode.opcodeStage, noRex, notEscape, notMap]

theorem body_plain {o : Op} (row : o ∈ Op.rows) (f : Fields) {opcode : UInt8}
    (member : opcode ∈ (desc o).enc.opcodes) (plain : ∀ digit, (desc o).enc.modrm ≠ .digit digit)
    (after : List UInt8) :
    Decode.body (desc o).enc.p66 (rexView (desc o).enc f) (desc o).enc.map opcode after =
      Decode.operands o (rexView (desc o).enc f) opcode none after := by
  have reach := List.all_eq_true.mp (Op.reachable_of_row row) opcode member
  have found : Table.lookup (Table.key (desc o).enc.p66 (desc o).enc.rexW (desc o).enc.map opcode 8) = some o := by
    cases hmodrm : (desc o).enc.modrm with
    | digit digit => exact absurd hmodrm (plain digit)
    | none | reg => simpa [hmodrm] using reach
  simp [Decode.body, rexView_bits, rexBits, found]

theorem body_group {o : Op} (row : o ∈ Op.rows) (f : Fields) {opcode : UInt8}
    (member : opcode ∈ (desc o).enc.opcodes) {digit : Nat} (group : (desc o).enc.modrm = .digit digit)
    (modrm : UInt8) (hdigit : Decode.modReg modrm = digit) (after : List UInt8) :
    Decode.body (desc o).enc.p66 (rexView (desc o).enc f) (desc o).enc.map opcode (modrm :: after) =
      Decode.operands o (rexView (desc o).enc f) opcode (some modrm) after := by
  have reach := List.all_eq_true.mp (Op.reachable_of_row row) opcode member
  simp only [group, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at reach
  obtain ⟨⟨_, absent⟩, found⟩ := reach
  simp [Decode.body, rexView_bits, rexBits, absent, found, hdigit]

theorem opcode_member (enc : EncDesc) : enc.opcode ∈ enc.opcodes := by
  unfold EncDesc.opcodes
  split
  · exact List.mem_map.mpr ⟨0, by simp, by simp⟩
  · simp

theorem digit_lt {o : Op} (row : o ∈ Op.rows) {digit : Nat} (group : (desc o).enc.modrm = .digit digit) :
    digit < 8 := by
  have entry := List.all_eq_true.mp (Op.reachable_of_row row) _ (opcode_member (desc o).enc)
  simp only [group, Bool.and_eq_true, decide_eq_true_eq] at entry
  exact entry.1.1

/-! ## Operand fields -/

/-- An r/m operand: a register or a canonical memory address. -/
def RMArg : Arg → Prop
  | .reg _ => True
  | .mem address => address.canonical = true
  | .imm _ => False

theorem rmOperand_decode (rex : Decode.Rex) (regField : Nat) (arg : Arg) (ok : RMArg arg)
    (hx : rex.x = (rmTail regField arg).rexX) (hb : rex.b = (rmTail regField arg).rexB)
    (rest : List UInt8) :
    ∃ modrm more, (rmTail regField arg).bytes = modrm :: more ∧ Decode.modReg modrm = regField % 8 ∧
      Decode.rmOperand rex modrm (more ++ rest) = some (arg, rest) := by
  cases arg with
  | reg register =>
      simp only [rmTail] at hx hb
      refine ⟨modRM 3 regField (registerLow (gprCode register)), [], rfl, by simp, ?_⟩
      simp [Decode.rmOperand, hx, hb]
  | mem address =>
      obtain ⟨modrm, more, shape, notReg, field, parsed⟩ :=
        memoryTail_decode rex regField address ok hx hb rest
      refine ⟨modrm, more, shape, field, ?_⟩
      simp [Decode.rmOperand, notReg, parsed]
  | imm value => exact False.elim ok

theorem byteRegistersOk_view (enc : EncDesc) (f : Fields) :
    Decode.byteRegistersOk enc (rexView enc f).isSome f.reg f.rm = true := by
  unfold Decode.byteRegistersOk rexView
  split
  · simp
  · rename_i absent
    simp only [rexPresent, Bool.or_eq_true, not_or, Bool.not_eq_true] at absent
    have force := absent.2
    simp only [byteForce, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at force
    simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rcases force.1 with byteReg | high
      · exact Or.inl byteReg
      · exact Or.inr high
    · rcases force.2 with byteRM | high
      · exact Or.inl byteRM
      · right
        cases hrm : f.rm with
        | none => rfl
        | some arg =>
            rw [hrm] at high
            cases arg <;> simp_all

end IxCC.X86.Encode
