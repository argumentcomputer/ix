import Compilatrix.X86.Decode

/-! Bounded decoding with the same independent parser and exact acceptance
as `Decode.decodeAt`. The parser consumes a prefix without inspecting its
suffix; only a fifteen-byte window is materialized at runtime. -/

namespace Compilatrix.X86.Decode

private def PrefixResult (parser : List UInt8 → Option (α × List UInt8))
    (input : List UInt8) (value : α) (rest : List UInt8) : Prop :=
  ∃ consumed, input = consumed ++ rest ∧
    ∀ suffix, parser (consumed ++ suffix) = some (value, suffix)

private theorem readLE_prefix {count input value rest}
    (accepted : readLE count input = some (value, rest)) :
    PrefixResult (readLE count) input value rest := by
  induction count generalizing input value rest with
  | zero =>
    simp only [readLE, Option.some.injEq, Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    exact ⟨[], rfl, fun _ => rfl⟩
  | succ count ih =>
    cases input with
    | nil => simp [readLE] at accepted
    | cons head tail =>
      rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, equal⟩
      simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨consumed, same, extension⟩ := ih parsed
      refine ⟨head :: consumed, by simp [same], ?_⟩
      intro suffix
      simp [readLE, extension suffix]

private theorem memory_prefix {pref modrm input value rest}
    (accepted : memory pref modrm input = some (value, rest)) :
    PrefixResult (memory pref modrm) input value rest := by
  by_cases path : (modRM modrm == 4) = true
  · cases input with
    | nil => simp [memory, path] at accepted
    | cons sib tail =>
      simp only [memory, path, if_true] at accepted
      rcases Option.bind_eq_some_iff.mp accepted with ⟨idx, indexAt, accepted⟩
      rcases Option.bind_eq_some_iff.mp accepted with ⟨scale, scaleAt, accepted⟩
      by_cases absent : (modMode modrm == 0 && modRM sib == 5 && !pref.b) = true
      · simp only [absent, if_true, bind, Option.bind] at accepted
        rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, equal⟩
        simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
        rcases equal with ⟨rfl, rfl⟩
        obtain ⟨consumed, same, extension⟩ := readLE_prefix parsed
        refine ⟨sib :: consumed, by simp [same], ?_⟩
        intro suffix
        simp [memory, path, absent, indexAt, scaleAt, extension suffix]
      · by_cases based : (modMode modrm == 2) = true
        · simp only [absent, based, if_true] at accepted
          rcases Option.bind_eq_some_iff.mp accepted with ⟨base, baseAt, accepted⟩
          rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, equal⟩
          simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
          rcases equal with ⟨rfl, rfl⟩
          obtain ⟨consumed, same, extension⟩ := readLE_prefix parsed
          refine ⟨sib :: consumed, by simp [same], ?_⟩
          intro suffix
          simp [memory, path, absent, based, indexAt, scaleAt, baseAt, extension suffix]
        · simp [absent, based] at accepted
  · by_cases invalid : (modMode modrm != 2 || pref.x) = true
    · cases input <;> simp [memory, path, invalid] at accepted
    · have parsedBody : (do
        let base ← register pref.b (modRM modrm)
        let (displacement, rest) ← readLE 4 input
        pure ({ base := some base, displacement := displacement.toUInt32 : MemAddr }, rest)) =
          some (value, rest) := by
        cases input <;> simpa [memory, path, invalid] using accepted
      rcases Option.bind_eq_some_iff.mp parsedBody with ⟨base, baseAt, accepted⟩
      rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, equal⟩
      simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, rfl⟩
      obtain ⟨consumed, same, extension⟩ := readLE_prefix parsed
      refine ⟨consumed, same, ?_⟩
      intro suffix
      cases joined : consumed ++ suffix <;>
        have decoded := extension suffix <;>
        rw [joined] at decoded <;>
        simp [memory, path, invalid, baseAt, decoded]

private theorem memoryOperation_prefix {pref make modrm input value rest}
    (accepted : memoryOperation pref make (modrm :: input) = some (value, rest)) :
    PrefixResult (fun tail => memoryOperation pref make (modrm :: tail)) input value rest := by
  rcases Option.bind_eq_some_iff.mp accepted with ⟨register, registerAt, accepted⟩
  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨address, remaining⟩, parsed, equal⟩
  simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
  rcases equal with ⟨rfl, rfl⟩
  obtain ⟨consumed, same, extension⟩ := memory_prefix parsed
  refine ⟨consumed, same, ?_⟩
  intro suffix
  simp [memoryOperation, registerAt, extension suffix]

private theorem groupImmediate_prefix {width input value rest}
    (accepted : groupImmediate width input = some (value, rest)) :
    PrefixResult (groupImmediate width) input value rest := by
  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, equal⟩
  simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
  rcases equal with ⟨rfl, rfl⟩
  obtain ⟨consumed, same, extension⟩ := readLE_prefix parsed
  refine ⟨consumed, same, ?_⟩
  intro suffix
  simp only [groupImmediate, extension suffix, bind, Option.bind, pure, Pure.pure]

private theorem prefixed_prefix {pref input value rest}
    (accepted : prefixed pref input = some (value, rest)) :
    PrefixResult (prefixed pref) input value rest := by
  cases input with
  | nil => simp [prefixed] at accepted
  | cons opcode input =>
    by_cases immediate : (0xb0 ≤ opcode.toNat && opcode.toNat < 0xc0) = true
    · by_cases invalid : (pref.r || pref.x) = true
      · cases input <;> simp [prefixed, immediate, invalid] at accepted
      · have body : (do
          let width ← pref.width (opcode.toNat < 0xb8)
          let destination ← register pref.b (opcode.toNat % 8)
          let (number, remaining) ← readLE (immediateBytes width) input
          pure (Operation.mov width destination (.imm number), remaining)) = some (value, rest) := by
          cases input <;> simpa [prefixed, immediate, invalid] using accepted
        rcases Option.bind_eq_some_iff.mp body with ⟨width, widthAt, body⟩
        rcases Option.bind_eq_some_iff.mp body with ⟨destination, destinationAt, body⟩
        rcases Option.bind_eq_some_iff.mp body with ⟨⟨number, remaining⟩, parsed, equal⟩
        simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
        rcases equal with ⟨rfl, rfl⟩
        obtain ⟨consumed, same, extension⟩ := readLE_prefix parsed
        refine ⟨opcode :: consumed, by simp [same], ?_⟩
        intro suffix
        cases joined : consumed ++ suffix <;>
          have decoded := extension suffix <;>
          rw [joined] at decoded <;>
          simp [prefixed, joined, immediate, invalid, widthAt, destinationAt, decoded]
    · cases input with
      | nil => simp [prefixed, immediate] at accepted
      | cons opcode2 input =>
        by_cases twoByte : (opcode == 0x0f) = true
        · cases input with
          | nil => simp [prefixed, immediate, twoByte] at accepted
          | cons modrm input =>
            by_cases multiply : (opcode2 == 0xaf) = true
            · simp only [prefixed, immediate, twoByte, multiply, if_true] at accepted
              rcases Option.bind_eq_some_iff.mp accepted with ⟨width, widthAt, accepted⟩
              rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨destination, source⟩, registersAt, equal⟩
              simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
              rcases equal with ⟨rfl, rfl⟩
              refine ⟨[opcode, opcode2, modrm], rfl, ?_⟩
              intro suffix
              simp [prefixed, immediate, twoByte, multiply, widthAt, registersAt]
            · by_cases load : ((opcode2 == 0xb6 || opcode2 == 0xb7) && pref.w && !pref.operand16) = true
              · simp only [prefixed, immediate, twoByte, multiply, load, if_true] at accepted
                simp at accepted
                obtain ⟨consumed, same, extension⟩ := memoryOperation_prefix accepted
                refine ⟨opcode :: opcode2 :: modrm :: consumed, by simp [same], ?_⟩
                intro suffix
                simpa [prefixed, immediate, twoByte, multiply, load] using extension suffix
              · simp [prefixed, immediate, twoByte, multiply, load] at accepted
        · by_cases move : (opcode == 0x88 || opcode == 0x89) = true
          · simp only [prefixed, immediate, twoByte, move, if_true] at accepted
            rcases Option.bind_eq_some_iff.mp accepted with ⟨width, widthAt, accepted⟩
            by_cases direct : (modMode opcode2 == 3) = true
            · simp only [direct, if_true] at accepted
              rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨source, destination⟩, registersAt, equal⟩
              simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
              rcases equal with ⟨rfl, rfl⟩
              refine ⟨[opcode, opcode2], rfl, ?_⟩
              intro suffix
              simp [prefixed, immediate, twoByte, move, direct, widthAt, registersAt]
            · simp only [direct] at accepted
              simp at accepted
              obtain ⟨consumed, same, extension⟩ := memoryOperation_prefix accepted
              refine ⟨opcode :: opcode2 :: consumed, by simp [same], ?_⟩
              intro suffix
              simp [prefixed, immediate, twoByte, move, direct, widthAt, extension suffix]
          · by_cases memoryCode : (opcode == 0x8b || opcode == 0x8d) = true
            · by_cases narrow : pref.operand16 = true
              · simp [prefixed, immediate, twoByte, move, memoryCode, narrow] at accepted
              · by_cases address : (opcode == 0x8d) = true
                · by_cases wide : pref.w = true
                  · simp only [prefixed, immediate, twoByte, move, narrow, address, wide,
                      if_true] at accepted
                    simp at accepted
                    obtain ⟨consumed, same, extension⟩ := memoryOperation_prefix accepted
                    refine ⟨opcode :: opcode2 :: consumed, by simp [same], ?_⟩
                    intro suffix
                    simp [prefixed, immediate, twoByte, move, narrow, address, wide, extension suffix]
                  · simp [prefixed, immediate, twoByte, move, narrow, address, wide] at accepted
                · simp only [prefixed, immediate, twoByte, move, narrow, address] at accepted
                  have loadCode : opcode = 0x8b := by simpa [address] using memoryCode
                  simp [loadCode] at accepted
                  obtain ⟨consumed, same, extension⟩ := memoryOperation_prefix accepted
                  refine ⟨opcode :: opcode2 :: consumed, by simp [same], ?_⟩
                  intro suffix
                  simp [prefixed, loadCode, narrow, extension suffix]
            · by_cases immediateCode : (opcode == 0x80 || opcode == 0x81) = true
              · by_cases invalid : pref.r = true
                · simp [prefixed, immediate, twoByte, move, memoryCode, immediateCode, invalid] at accepted
                · simp only [prefixed, immediate, twoByte, move, memoryCode, immediateCode, invalid,
                    if_true] at accepted
                  rcases Option.bind_eq_some_iff.mp accepted with ⟨width, widthAt, accepted⟩
                  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨unused, destination⟩, registersAt, accepted⟩
                  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, accepted⟩
                  by_cases comparison : (modReg opcode2 == 7) = true
                  · simp only [comparison, if_true, Option.some.injEq, Prod.mk.injEq] at accepted
                    rcases accepted with ⟨rfl, rfl⟩
                    obtain ⟨consumed, same, extension⟩ := groupImmediate_prefix parsed
                    refine ⟨opcode :: opcode2 :: consumed, by simp [same], ?_⟩
                    intro suffix
                    simp [prefixed, immediate, twoByte, move, memoryCode, immediateCode, invalid,
                      widthAt, registersAt, comparison, extension suffix]
                  · simp only [comparison] at accepted
                    rcases Option.bind_eq_some_iff.mp accepted with ⟨operation, operationAt, equal⟩
                    simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
                    rcases equal with ⟨rfl, rfl⟩
                    obtain ⟨consumed, same, extension⟩ := groupImmediate_prefix parsed
                    refine ⟨opcode :: opcode2 :: consumed, by simp [same], ?_⟩
                    intro suffix
                    simp [prefixed, immediate, twoByte, move, memoryCode, immediateCode, invalid,
                      widthAt, registersAt, comparison, operationAt, extension suffix]
              · by_cases compareCode : (opcode == 0x38 || opcode == 0x39) = true
                · simp only [prefixed, immediate, twoByte, move, memoryCode, immediateCode, compareCode,
                    if_true] at accepted
                  rcases Option.bind_eq_some_iff.mp accepted with ⟨width, widthAt, accepted⟩
                  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨right, left⟩, registersAt, equal⟩
                  simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
                  rcases equal with ⟨rfl, rfl⟩
                  refine ⟨[opcode, opcode2], rfl, ?_⟩
                  intro suffix
                  simp [prefixed, immediate, twoByte, move, memoryCode, immediateCode, compareCode,
                    widthAt, registersAt]
                · simp only [prefixed, immediate, twoByte, move, memoryCode, immediateCode, compareCode
                    ] at accepted
                  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨operation, narrow⟩, operationAt, accepted⟩
                  rcases Option.bind_eq_some_iff.mp accepted with ⟨width, widthAt, accepted⟩
                  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨source, destination⟩, registersAt, equal⟩
                  simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
                  rcases equal with ⟨rfl, rfl⟩
                  refine ⟨[opcode, opcode2], rfl, ?_⟩
                  intro suffix
                  simp [prefixed, immediate, twoByte, move, memoryCode, immediateCode, compareCode,
                    operationAt, widthAt, registersAt]

private theorem stack_suffix {extended opcode input value rest}
    (accepted : stack extended opcode input = some (value, rest)) :
    input = rest ∧ ∀ suffix, stack extended opcode suffix = some (value, suffix) := by
  rcases Option.bind_eq_some_iff.mp accepted with ⟨register, registerAt, accepted⟩
  by_cases push : (0x50 ≤ opcode.toNat && opcode.toNat < 0x58) = true
  · simp only [push, if_true, Option.some.injEq, Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    exact ⟨rfl, fun suffix => by simp [stack, registerAt, push]⟩
  · by_cases pop : (0x58 ≤ opcode.toNat && opcode.toNat < 0x60) = true
    · simp [push, pop] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact ⟨rfl, fun suffix => by simp [stack, registerAt, push, pop]⟩
    · simp [push, pop] at accepted

private theorem one_prefix {input value rest}
    (accepted : one input = some (value, rest)) : PrefixResult one input value rest := by
  fun_cases one input
  case case1 => simp [one] at accepted
  case case2 input =>
    simp only [one, Option.some.injEq, Prod.mk.injEq] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    exact ⟨[0xc3], rfl, fun _ => rfl⟩
  case case3 input =>
    rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, equal⟩
    simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
    rcases equal with ⟨rfl, rfl⟩
    obtain ⟨consumed, same, extension⟩ := readLE_prefix parsed
    refine ⟨0xe8 :: consumed, by simp [same], ?_⟩
    intro suffix
    simp [one, extension suffix]
  case case4 input =>
    rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, equal⟩
    simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
    rcases equal with ⟨rfl, rfl⟩
    obtain ⟨consumed, same, extension⟩ := readLE_prefix parsed
    refine ⟨0xe9 :: consumed, by simp [same], ?_⟩
    intro suffix
    simp [one, extension suffix]
  case case5 opcode input =>
    rcases Option.bind_eq_some_iff.mp accepted with ⟨condition, conditionAt, accepted⟩
    rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨number, remaining⟩, parsed, equal⟩
    simp only [pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at equal
    rcases equal with ⟨rfl, rfl⟩
    obtain ⟨consumed, same, extension⟩ := readLE_prefix parsed
    refine ⟨0x0f :: opcode :: consumed, by simp [same], ?_⟩
    intro suffix
    simp [one, conditionAt, extension suffix]
  case case6 header input =>
    rcases Option.bind_eq_some_iff.mp accepted with ⟨pref, prefAt, parsed⟩
    obtain ⟨consumed, same, extension⟩ := prefixed_prefix parsed
    refine ⟨0x66 :: header :: consumed, by simp [same], ?_⟩
    intro suffix
    simp [one, prefAt, extension suffix]
  case case7 head notReturn notCall notJump extended opcode input allowed notBranch notLegacy =>
    have sameHead : head = 0x41 := beq_iff_eq.mp extended
    subst head
    have parsed : stack true opcode input = some (value, rest) := by simpa [one, allowed] using accepted
    obtain ⟨rfl, extension⟩ := stack_suffix parsed
    refine ⟨[0x41, opcode], rfl, ?_⟩
    intro suffix
    simp [one, allowed, extension suffix]
  case case8 head notReturn notCall notJump extended opcode input allowed notBranch notLegacy =>
    have sameHead : head = 0x41 := beq_iff_eq.mp extended
    subst head
    have parsedBody : (do let pref ← rex false 0x41; prefixed pref (opcode :: input)) = some (value, rest) := by
      simpa [one, allowed] using accepted
    rcases Option.bind_eq_some_iff.mp parsedBody with ⟨pref, prefAt, parsed⟩
    obtain ⟨consumed, same, extension⟩ := prefixed_prefix parsed
    cases consumed with
    | nil => have impossible := extension []; simp [prefixed] at impossible
    | cons actual consumed =>
      simp only [List.cons_append, List.cons.injEq] at same
      rcases same with ⟨rfl, same⟩
      refine ⟨0x41 :: opcode :: consumed, by simp [same], ?_⟩
      intro suffix
      simpa [one, allowed, prefAt] using extension suffix
  case case9 head notReturn notCall notJump extended notBranch notLegacy =>
    have sameHead : head = 0x41 := beq_iff_eq.mp extended
    subst head
    simp [one] at accepted
  case case10 head input notReturn notCall notJump notBranch notLegacy notExtended allowed =>
    have notNear : head ≠ 0x0f := by intro equal; subst head; simp at allowed
    have notOperand : head ≠ 0x66 := by intro equal; subst head; simp at allowed
    have parsed : stack false head input = some (value, rest) := by
      cases input <;> simpa [one, notReturn, notCall, notJump, notNear, notOperand, notExtended, allowed] using accepted
    obtain ⟨rfl, extension⟩ := stack_suffix parsed
    refine ⟨[head], rfl, ?_⟩
    intro suffix
    cases suffix <;>
      simp [one, notNear, notOperand, notExtended, allowed, extension]
  case case11 head input notReturn notCall notJump notBranch notLegacy notExtended notStack =>
    have parsedBody : (do let pref ← rex false head; prefixed pref input) = some (value, rest) := by
      simpa only [one, notReturn, notCall, notJump, notBranch, notLegacy, notExtended, notStack,
        Bool.false_eq_true, if_false] using accepted
    rcases Option.bind_eq_some_iff.mp parsedBody with ⟨pref, prefAt, parsed⟩
    have notNear : head ≠ 0x0f := by intro equal; subst head; simp [rex] at prefAt
    have notOperand : head ≠ 0x66 := by intro equal; subst head; simp [rex] at prefAt
    obtain ⟨consumed, same, extension⟩ := prefixed_prefix parsed
    refine ⟨head :: consumed, by simp [same], ?_⟩
    intro suffix
    cases joined : consumed ++ suffix <;>
      have decoded := extension suffix <;>
      rw [joined] at decoded <;>
      simp [one, notNear, notOperand, notExtended, notStack, prefAt, joined, decoded]

private def decodedList (input : List UInt8) : Option Decoded := do
  let (operation, rest) ← one input
  let length := input.length - rest.length
  if 0 < length && length ≤ 15 then some ⟨operation, length⟩ else none

private theorem decodedList_prefix {input decoded}
    (accepted : decodedList input = some decoded) :
    ∃ consumed remaining, input = consumed ++ remaining ∧ consumed.length = decoded.length ∧
      0 < decoded.length ∧ decoded.length ≤ 15 ∧
      ∀ suffix, one (consumed ++ suffix) = some (decoded.operation, suffix) := by
  rcases Option.bind_eq_some_iff.mp accepted with ⟨⟨operation, rest⟩, parsed, accepted⟩
  change (if 0 < input.length - rest.length && input.length - rest.length ≤ 15 then
    some ⟨operation, input.length - rest.length⟩ else none) = some decoded at accepted
  split at accepted
  · rename_i bounds
    cases accepted
    obtain ⟨consumed, same, extension⟩ := one_prefix parsed
    have length : input.length - rest.length = consumed.length := by simp [same]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at bounds
    exact ⟨consumed, rest, same, length.symm, bounds.1, bounds.2, extension⟩
  · contradiction

private theorem decodedList_of_prefix {consumed : List UInt8} {decoded : Decoded}
    (length : consumed.length = decoded.length) (positive : 0 < decoded.length) (short : decoded.length ≤ 15)
    (parsed : ∀ suffix, one (consumed ++ suffix) = some (decoded.operation, suffix)) (suffix : List UInt8) :
    decodedList (consumed ++ suffix) = some decoded := by
  cases decoded
  simp [decodedList, parsed suffix, length, positive, short]

private theorem decodedList_take (input : List UInt8) : decodedList (input.take 15) = decodedList input := by
  apply Option.ext
  intro decoded
  constructor
  · intro accepted
    obtain ⟨consumed, remaining, same, length, positive, short, parsed⟩ := decodedList_prefix accepted
    have full : input = consumed ++ (remaining ++ input.drop 15) := by
      rw [← List.append_assoc, ← same, List.take_append_drop]
    rw [full]
    exact decodedList_of_prefix length positive short parsed _
  · intro accepted
    obtain ⟨consumed, remaining, same, length, positive, short, parsed⟩ := decodedList_prefix accepted
    have fits : consumed.length ≤ 15 := by omega
    rw [same, List.take_append, List.take_of_length_le fits]
    exact decodedList_of_prefix length positive short parsed _

/-- Decode at most fifteen bytes, without converting or traversing the rest
of the text. The independent parser and rejection behavior are unchanged. -/
def decodeWindowAt (text : ByteArray) (offset : Nat) : Option Decoded :=
  if offset ≥ text.size then none
  else decodedList (text.extract offset (offset + 15)).data.toList

/-- Exact agreement includes malformed encodings, truncation, and arbitrary
offsets. This theorem does not assume the bytes came from the encoder. -/
theorem decodeWindowAt_eq (text : ByteArray) (offset : Nat) :
    decodeWindowAt text offset = decodeAt text offset := by
  unfold decodeWindowAt decodeAt
  by_cases outside : offset ≥ text.size
  · simp [outside]
  · simp only [outside, if_false]
    have window : (text.extract offset (offset + 15)).data.toList =
        (text.data.toList.drop offset).take 15 := by
      simp [List.extract_eq_take_drop]
    rw [window, decodedList_take]
    rfl

end Compilatrix.X86.Decode
