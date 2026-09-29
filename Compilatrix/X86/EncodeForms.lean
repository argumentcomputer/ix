import Compilatrix.X86.EncodeRegisters

/-! E1 decoding per encoding class. `fieldsOk` reads, from a row's slot
kinds and its encoding class, where its operands go; the three operand laws
cover the ModRM uses (none, register, opcode extension); `row_decode`
combines them with the prefix and lookup stages. No law names an
instruction form: a new row is covered by the table facts alone. -/

namespace Compilatrix.X86.Encode

/-- What well-kinded operands put in each encoding field. -/
structure FieldsOk (o : Op) (args : List Arg) : Prop where
  assembled : Decode.assemble o.form (fields o.form args).reg (fields o.form args).rm
    (fields o.form args).imm = some args
  rm : ∀ arg, (fields o.form args).rm = some arg → RMArg arg
  uses : match (desc o).enc.modrm with
    | .none => (fields o.form args).rm = none ∧
        match (desc o).enc.emb with
        | .regLow3 => (fields o.form args).reg.isSome
        | .none => (fields o.form args).reg = none
    | .reg => (fields o.form args).reg.isSome ∧ (fields o.form args).rm.isSome
    | .digit _ => (fields o.form args).reg = none ∧ (fields o.form args).rm.isSome
  imm : ∀ rest, Decode.immediate (desc o).enc.imm
    (immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) = some ((fields o.form args).imm, rest)

theorem accepts_reg {slot : Slot} {arg : Arg} (kinds : Table.regKinds slot = true)
    (accepts : slot.kinds.any (·.accepts arg) = true) : ∃ register, arg = .reg register := by
  simp only [Table.regKinds, beq_iff_eq] at kinds
  rw [kinds] at accepts
  cases arg <;> simp_all [ArgKind.accepts]

theorem accepts_rm {slot : Slot} {arg : Arg} (kinds : Table.rmKinds slot = true)
    (accepts : slot.kinds.any (·.accepts arg) = true) : RMArg arg := by
  simp only [Table.rmKinds, Bool.or_eq_true, beq_iff_eq] at kinds
  rcases kinds with kinds | kinds <;> rw [kinds] at accepts <;>
    cases arg <;> simp_all [ArgKind.accepts, RMArg]

theorem accepts_imm {slot : Slot} {arg : Arg} {kind : ImmKind} (kinds : Table.immKinds kind slot = true)
    (accepts : slot.kinds.any (·.accepts arg) = true) :
    ∃ value, arg = .imm value ∧ kind.norm value = value ∧ kind ≠ .none := by
  cases kind <;> simp only [Table.immKinds, Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true] at kinds
  all_goals
    first
    | (rcases kinds with kinds | kinds <;> rw [kinds] at accepts <;>
        cases arg <;> simp_all [ArgKind.accepts, ImmKind.norm])
    | (rw [kinds] at accepts; cases arg <;> simp_all [ArgKind.accepts, ImmKind.norm])

theorem immediate_some (kind : ImmKind) (value : Word) (canonical : kind.norm value = value)
    (present : kind ≠ .none) (rest : List UInt8) :
    Decode.immediate kind (immBytes kind (some value) ++ rest) = some (some value, rest) := by
  have decoded := imm_decode kind value present
  rw [canonical] at decoded
  cases kind <;> simp_all [Decode.immediate, immBytes, readLE_le]

theorem immediate_none (rest : List UInt8) :
    Decode.immediate .none (immBytes .none none ++ rest) = some (none, rest) := rfl

theorem slotsAccept_two {slots : List Slot} {args : List Arg} {first second : Slot}
    (shape : slots = [first, second]) (accepted : slotsAccept slots args = true) :
    ∃ a b, args = [a, b] ∧ first.kinds.any (·.accepts a) = true ∧ second.kinds.any (·.accepts b) = true := by
  subst shape
  match args with
  | [] => simp [slotsAccept] at accepted
  | [_] => simp [slotsAccept] at accepted
  | [a, b] =>
      simp only [slotsAccept, Bool.and_eq_true, Bool.and_true] at accepted
      exact ⟨a, b, rfl, accepted.1, accepted.2⟩
  | _ :: _ :: _ :: _ => simp [slotsAccept] at accepted

theorem slotsAccept_three {slots : List Slot} {args : List Arg} {first second third : Slot}
    (shape : slots = [first, second, third]) (accepted : slotsAccept slots args = true) :
    ∃ a b c, args = [a, b, c] ∧ first.kinds.any (·.accepts a) = true ∧
      second.kinds.any (·.accepts b) = true ∧ third.kinds.any (·.accepts c) = true := by
  subst shape
  match args with
  | [] => simp [slotsAccept] at accepted
  | [_] => simp [slotsAccept] at accepted
  | [_, _] => simp [slotsAccept] at accepted
  | [a, b, c] =>
      simp only [slotsAccept, Bool.and_eq_true, Bool.and_true] at accepted
      exact ⟨a, b, c, rfl, accepted.1, accepted.2.1, accepted.2.2⟩
  | _ :: _ :: _ :: _ :: _ => simp [slotsAccept] at accepted

theorem slotsAccept_one {slots : List Slot} {args : List Arg} {first : Slot}
    (shape : slots = [first]) (accepted : slotsAccept slots args = true) :
    ∃ a, args = [a] ∧ first.kinds.any (·.accepts a) = true := by
  subst shape
  match args with
  | [] => simp [slotsAccept] at accepted
  | [a] =>
      simp only [slotsAccept, Bool.and_true] at accepted
      exact ⟨a, rfl, accepted⟩
  | _ :: _ :: _ => simp [slotsAccept] at accepted

theorem slotsAccept_zero {slots : List Slot} {args : List Arg} (shape : slots = [])
    (accepted : slotsAccept slots args = true) : args = [] := by
  subst shape
  match args with
  | [] => rfl
  | _ :: _ => simp [slotsAccept] at accepted

/-- The table facts and slot kinds determine each class's field layout. -/
theorem fieldsOk {o : Op} {args : List Arg} (row : o ∈ Op.rows) (ok : o.argsOk args = true) :
    FieldsOk o args := by
  have shape := Op.shaped_of_row row
  unfold Table.shaped at shape
  simp only [Bool.and_eq_true] at shape
  obtain ⟨⟨_, _⟩, shape⟩ := shape
  unfold Op.argsOk at ok
  generalize hslots : (desc o).slots = slots at shape ok
  cases hform : o.form <;> rw [hform] at shape
  case MR =>
    match slots, shape with
    | [first, second], shape =>
      simp only [Bool.and_eq_true, beq_iff_eq] at shape
      obtain ⟨⟨⟨⟨hmodrm, hemb⟩, himm⟩, rmOk⟩, regOk⟩ := shape
      obtain ⟨a, b, rfl, accA, accB⟩ := slotsAccept_two rfl ok
      obtain ⟨register, rfl⟩ := accepts_reg regOk accB
      have rm := accepts_rm rmOk accA
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [fields, Decode.assemble, hform]
      · intro arg found
        simp only [fields, hform, Option.some.injEq] at found
        exact found ▸ rm
      · simp [hmodrm, fields, hform]
      · intro rest
        simp [himm, fields, hform, immediate_none]
    | [], shape => simp at shape
    | [_], shape => simp at shape
    | _ :: _ :: _ :: _, shape => simp at shape
  case RM =>
    match slots, shape with
    | [first, second], shape =>
      simp only [Bool.and_eq_true, beq_iff_eq] at shape
      obtain ⟨⟨⟨⟨hmodrm, hemb⟩, himm⟩, regOk⟩, rmOk⟩ := shape
      obtain ⟨a, b, rfl, accA, accB⟩ := slotsAccept_two rfl ok
      obtain ⟨register, rfl⟩ := accepts_reg regOk accA
      have rm := accepts_rm rmOk accB
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [fields, Decode.assemble, hform]
      · intro arg found
        simp only [fields, hform, Option.some.injEq] at found
        exact found ▸ rm
      · simp [hmodrm, fields, hform]
      · intro rest
        simp [himm, fields, hform, immediate_none]
    | [], shape => simp at shape
    | [_], shape => simp at shape
    | _ :: _ :: _ :: _, shape => simp at shape
  case MI | MI8 =>
    match slots, shape with
    | [first, second], shape =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at shape
      obtain ⟨⟨⟨⟨notNone, notReg⟩, hemb⟩, rmOk⟩, immOk⟩ := shape
      obtain ⟨a, b, rfl, accA, accB⟩ := slotsAccept_two rfl ok
      obtain ⟨value, rfl, canonical, present⟩ := accepts_imm immOk accB
      have rm := accepts_rm rmOk accA
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [fields, Decode.assemble, hform]
      · intro arg found
        simp only [fields, hform, Option.some.injEq] at found
        exact found ▸ rm
      · cases hmodrm : (desc o).enc.modrm with
        | none => exact absurd hmodrm notNone
        | reg => exact absurd hmodrm notReg
        | digit digit => simp [fields, hform]
      · intro rest
        simpa [fields, hform] using immediate_some _ value canonical present rest
    | [], shape => simp at shape
    | [_], shape => simp at shape
    | _ :: _ :: _ :: _, shape => simp at shape
  case OI =>
    match slots, shape with
    | [first, second], shape =>
      simp only [Bool.and_eq_true, beq_iff_eq] at shape
      obtain ⟨⟨⟨hmodrm, hemb⟩, regOk⟩, immOk⟩ := shape
      obtain ⟨a, b, rfl, accA, accB⟩ := slotsAccept_two rfl ok
      obtain ⟨register, rfl⟩ := accepts_reg regOk accA
      obtain ⟨value, rfl, canonical, present⟩ := accepts_imm immOk accB
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [fields, Decode.assemble, hform]
      · intro arg found
        simp [fields, hform] at found
      · simp [hmodrm, hemb, fields, hform]
      · intro rest
        simpa [fields, hform] using immediate_some _ value canonical present rest
    | [], shape => simp at shape
    | [_], shape => simp at shape
    | _ :: _ :: _ :: _, shape => simp at shape
  case O =>
    match slots, shape with
    | [first], shape =>
      simp only [Bool.and_eq_true, beq_iff_eq] at shape
      obtain ⟨⟨⟨hmodrm, hemb⟩, himm⟩, regOk⟩ := shape
      obtain ⟨a, rfl, accA⟩ := slotsAccept_one rfl ok
      obtain ⟨register, rfl⟩ := accepts_reg regOk accA
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [fields, Decode.assemble, hform]
      · intro arg found
        simp [fields, hform] at found
      · simp [hmodrm, hemb, fields, hform]
      · intro rest
        simp [himm, fields, hform, immediate_none]
    | [], shape => simp at shape
    | _ :: _ :: _, shape => simp at shape
  case RMI | RMI8 =>
    match slots, shape with
    | [first, second, third], shape =>
      simp only [Bool.and_eq_true, beq_iff_eq] at shape
      obtain ⟨⟨⟨⟨hmodrm, hemb⟩, regOk⟩, rmOk⟩, immOk⟩ := shape
      obtain ⟨a, b, c, rfl, accA, accB, accC⟩ := slotsAccept_three rfl ok
      obtain ⟨register, rfl⟩ := accepts_reg regOk accA
      obtain ⟨value, rfl, canonical, present⟩ := accepts_imm immOk accC
      have rm := accepts_rm rmOk accB
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [fields, Decode.assemble, hform]
      · intro arg found
        simp only [fields, hform, Option.some.injEq] at found
        exact found ▸ rm
      · simp [hmodrm, fields, hform]
      · intro rest
        simpa [fields, hform] using immediate_some _ value canonical present rest
    | [], shape => simp at shape
    | [_], shape => simp at shape
    | [_, _], shape => simp at shape
    | _ :: _ :: _ :: _ :: _, shape => simp at shape
  case D32 =>
    match slots, shape with
    | [first], shape =>
      simp only [Bool.and_eq_true, beq_iff_eq] at shape
      obtain ⟨⟨⟨hmodrm, hemb⟩, himm⟩, relKinds⟩ := shape
      obtain ⟨a, rfl, accA⟩ := slotsAccept_one rfl ok
      have immOk : Table.immKinds .imm32 first = true := by simp [Table.immKinds, relKinds]
      obtain ⟨value, rfl, canonical, present⟩ := accepts_imm immOk accA
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [fields, Decode.assemble, hform]
      · intro arg found
        simp [fields, hform] at found
      · simp [hmodrm, hemb, fields, hform]
      · intro rest
        simpa [himm, fields, hform] using immediate_some _ value canonical present rest
    | [], shape => simp at shape
    | _ :: _ :: _, shape => simp at shape
  case ZO =>
    match slots, shape with
    | [], shape =>
      simp only [Bool.and_eq_true, beq_iff_eq] at shape
      obtain ⟨⟨hmodrm, hemb⟩, himm⟩ := shape
      have empty := slotsAccept_zero rfl ok
      subst empty
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [fields, Decode.assemble, hform]
      · intro arg found
        simp [fields, hform] at found
      · simp [hmodrm, hemb, fields, hform]
      · intro rest
        simp [himm, fields, hform, immediate_none]
    | _ :: _, shape => simp at shape

/-! ## Operands per ModRM use -/

theorem operands_opcode {o : Op} {args : List Arg} (row : o ∈ Op.rows) (ok : o.argsOk args = true)
    (use : (desc o).enc.modrm = .none) (rest : List UInt8) :
    Decode.operands o (rexView (desc o).enc (fields o.form args)) (opcodeByte (desc o).enc (fields o.form args))
      none (immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) = some (.op o args, rest) := by
  have fok := fieldsOk row ok
  have uses := fok.uses
  rw [use] at uses
  obtain ⟨noRm, regUse⟩ := uses
  have shape := Op.shaped_of_row row
  unfold Table.shaped at shape
  simp only [Bool.and_eq_true] at shape
  have lowFact := shape.1.2
  have bits : Decode.Rex.bits (rexView (desc o).enc (fields o.form args)) =
      ⟨(desc o).enc.rexW, false, false, (tail (desc o).enc (fields o.form args)).rexB⟩ := by
    rw [rexView_bits]
    simp [rexBits, rexR, tail, use]
  have parsed : Decode.opcodeFields (desc o).enc.emb (Decode.Rex.bits (rexView (desc o).enc (fields o.form args)))
      (opcodeByte (desc o).enc (fields o.form args)) (immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) =
      some (((fields o.form args).reg, (fields o.form args).rm), immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) := by
    rw [bits, noRm]
    cases hemb : (desc o).enc.emb with
    | regLow3 =>
        rw [hemb] at regUse
        obtain ⟨register, hreg⟩ := Option.isSome_iff_exists.mp regUse
        simp only [hemb, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at lowFact
        have low : ((desc o).enc.opcode.toNat + registerLow (gprCode register)) % 8 =
            registerLow (gprCode register) := by
          have := low_lt (gprCode register)
          omega
        simp [Decode.opcodeFields, opcodeByte, hemb, hreg, low, tail, use]
    | none =>
        rw [hemb] at regUse
        simp [Decode.opcodeFields, regUse, tail, use, hemb]
  simp only [Decode.operands, use, parse_bind, parsed, Option.bind_some, fok.imm, fok.assembled, lift_some,
    ok, byteRegistersOk_view, Bool.and_self, ite_true, parse_pure]

theorem operands_modrm {o : Op} {args : List Arg} (row : o ∈ Op.rows) (ok : o.argsOk args = true)
    (use : (desc o).enc.modrm = .reg) (rest : List UInt8) :
    Decode.operands o (rexView (desc o).enc (fields o.form args)) (opcodeByte (desc o).enc (fields o.form args))
      none ((tail (desc o).enc (fields o.form args)).bytes ++ immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) =
      some (.op o args, rest) := by
  have fok := fieldsOk row ok
  have uses := fok.uses
  rw [use] at uses
  obtain ⟨regSome, rmSome⟩ := uses
  obtain ⟨register, hreg⟩ := Option.isSome_iff_exists.mp regSome
  obtain ⟨arg, hrm⟩ := Option.isSome_iff_exists.mp rmSome
  have rmOk := fok.rm arg hrm
  have tailEq : tail (desc o).enc (fields o.form args) = rmTail (registerLow (gprCode register)) arg := by
    simp [tail, use, hrm, regField, hreg]
  have bits : Decode.Rex.bits (rexView (desc o).enc (fields o.form args)) =
      ⟨(desc o).enc.rexW, registerExtended (gprCode register), (rmTail (registerLow (gprCode register)) arg).rexX,
        (rmTail (registerLow (gprCode register)) arg).rexB⟩ := by
    rw [rexView_bits, rexBits, tailEq]
    simp [rexR, use, hreg]
  obtain ⟨modrm, more, shape, field, parsedRm⟩ := rmOperand_decode
    (Decode.Rex.bits (rexView (desc o).enc (fields o.form args))) (registerLow (gprCode register)) arg rmOk
    (by rw [bits]) (by rw [bits]) (immBytes (desc o).enc.imm (fields o.form args).imm ++ rest)
  rw [tailEq, shape]
  have fieldsParsed : Decode.modrmFields .reg (Decode.Rex.bits (rexView (desc o).enc (fields o.form args))) modrm
      (more ++ immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) =
      some ((some register, some arg), immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) := by
    rw [List.append_assoc]
    simp only [Decode.modrmFields, parse_bind, field, low_mod, bits] at parsedRm ⊢
    simp [parsedRm]
  simp only [Decode.operands, use, parse_bind, List.cons_append, byte_cons, Option.bind_some, fieldsParsed,
    fok.imm, ← hreg, ← hrm, fok.assembled, lift_some, ok, byteRegistersOk_view, Bool.and_self, ite_true,
    parse_pure]

theorem operands_digit {o : Op} {args : List Arg} (row : o ∈ Op.rows) (ok : o.argsOk args = true)
    {digit : Nat} (use : (desc o).enc.modrm = .digit digit) (rest : List UInt8) :
    ∃ modrm more, (tail (desc o).enc (fields o.form args)).bytes = modrm :: more ∧ Decode.modReg modrm = digit ∧
      Decode.operands o (rexView (desc o).enc (fields o.form args)) (opcodeByte (desc o).enc (fields o.form args))
        (some modrm) (more ++ immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) = some (.op o args, rest) := by
  have fok := fieldsOk row ok
  have uses := fok.uses
  rw [use] at uses
  obtain ⟨regNone, rmSome⟩ := uses
  obtain ⟨arg, hrm⟩ := Option.isSome_iff_exists.mp rmSome
  have rmOk := fok.rm arg hrm
  have small := digit_lt row use
  have tailEq : tail (desc o).enc (fields o.form args) = rmTail digit arg := by
    simp [tail, use, hrm, regField]
  have bits : Decode.Rex.bits (rexView (desc o).enc (fields o.form args)) =
      ⟨(desc o).enc.rexW, false, (rmTail digit arg).rexX, (rmTail digit arg).rexB⟩ := by
    rw [rexView_bits, rexBits, tailEq]
    simp [rexR, use]
  obtain ⟨modrm, more, shape, field, parsedRm⟩ := rmOperand_decode
    (Decode.Rex.bits (rexView (desc o).enc (fields o.form args))) digit arg rmOk
    (by rw [bits]) (by rw [bits]) (immBytes (desc o).enc.imm (fields o.form args).imm ++ rest)
  refine ⟨modrm, more, by rw [tailEq, shape], by rw [field]; exact Nat.mod_eq_of_lt small, ?_⟩
  have fieldsParsed : Decode.modrmFields (.digit digit) (Decode.Rex.bits (rexView (desc o).enc (fields o.form args)))
      modrm (more ++ immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) =
      some ((none, some arg), immBytes (desc o).enc.imm (fields o.form args).imm ++ rest) := by
    rw [List.append_assoc]
    simp only [Decode.modrmFields, bits] at parsedRm ⊢
    simp [parsedRm]
  simp only [Decode.operands, use, parse_bind, parse_pure, Option.bind_some, fieldsParsed,
    fok.imm, ← regNone, ← hrm, fok.assembled, lift_some, ok, byteRegistersOk_view, Bool.and_self, ite_true]

/-! ## Rows -/

theorem opcodeByte_member (o : Op) (args : List Arg) :
    opcodeByte (desc o).enc (fields o.form args) ∈ (desc o).enc.opcodes := by
  unfold opcodeByte EncDesc.opcodes
  cases hemb : (desc o).enc.emb with
  | none => simp
  | regLow3 =>
      simp only [List.mem_map, List.mem_range]
      cases hreg : (fields o.form args).reg with
      | none => exact ⟨0, by decide, rfl⟩
      | some register => exact ⟨_, low_lt _, rfl⟩

theorem opcodeByte_clear {o : Op} (row : o ∈ Op.rows) (args : List Arg) :
    Table.opcodeClear (desc o).enc.map (opcodeByte (desc o).enc (fields o.form args)) = true := by
  have shape := Op.shaped_of_row row
  unfold Table.shaped at shape
  simp only [Bool.and_eq_true] at shape
  exact List.all_eq_true.mp shape.1.1 _ (opcodeByte_member o args)

/-- E1 round trip, for every row of every encoding class: the independent
decoder recovers the row and its operands from the encoder's bytes, and
consumes exactly them. -/
theorem row_decode (o : Op) (args : List Arg) (row : o ∈ Op.rows) (ok : o.argsOk args = true)
    (rest : List UInt8) :
    Decode.one (encodeList o args ++ rest) = some (.op o args, rest) := by
  unfold encodeList
  simp only [List.append_assoc]
  have stages := stages_decode (desc o).enc (fields o.form args)
    ((tail (desc o).enc (fields o.form args)).bytes ++ immBytes (desc o).enc.imm (fields o.form args).imm ++ rest)
    (opcodeByte_clear row args)
  simp only [List.append_assoc] at stages
  rw [stages]
  cases hmodrm : (desc o).enc.modrm with
  | none =>
      have empty : (tail (desc o).enc (fields o.form args)).bytes = [] := by simp [tail, hmodrm]
      rw [body_plain row _ (opcodeByte_member o args) (by simp [hmodrm]), empty, List.nil_append]
      exact operands_opcode row ok hmodrm rest
  | reg =>
      rw [body_plain row _ (opcodeByte_member o args) (by simp [hmodrm]), ← List.append_assoc]
      exact operands_modrm row ok hmodrm rest
  | digit digit =>
      obtain ⟨modrm, more, shape, field, parsed⟩ := operands_digit row ok hmodrm rest
      rw [shape, List.cons_append, body_group row _ (opcodeByte_member o args) hmodrm modrm field,
        ← List.append_assoc]
      exact parsed

theorem encodeOp_decode (o : Op) (args : List Arg) (row : o ∈ Op.rows) (ok : o.argsOk args = true)
    (rest : List UInt8) :
    Decode.one ((encodeOp o args).data.toList ++ rest) = some (.op o args, rest) := by
  simpa [encodeOp] using row_decode o args row ok rest

end Compilatrix.X86.Encode
