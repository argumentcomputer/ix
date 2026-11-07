import IxCC.X86.Decode

/-! Bounded decoding with the same independent parser and exact acceptance
as `Decode.decodeAt`. Every parser choice depends only on consumed bytes, so
a successful parse is a prefix independent of its suffix; only a
fifteen-byte window is materialized at runtime. -/

namespace IxCC.X86.Decode

/-- A successful parse consumed a prefix and succeeds on any suffix. -/
def PrefixResult (parser : List UInt8 → Option (α × List UInt8))
    (input : List UInt8) (value : α) (rest : List UInt8) : Prop :=
  ∃ consumed, input = consumed ++ rest ∧
    ∀ suffix, parser (consumed ++ suffix) = some (value, suffix)

/-- Every successful parse is a suffix-independent prefix. -/
structure Stable (parser : Parser α) : Prop where
  holds : ∀ {input value rest}, parser input = some (value, rest) → PrefixResult parser input value rest

theorem Stable.pure (value : α) : Stable (Pure.pure value : Parser α) := by
  constructor
  intro input result rest parsed
  simp only [Pure.pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at parsed
  obtain ⟨rfl, rfl⟩ := parsed
  exact ⟨[], rfl, fun _ => rfl⟩

theorem Stable.fail : Stable (fail : Parser α) := by
  constructor
  intro input value rest parsed
  simp [Decode.fail] at parsed

theorem Stable.byte : Stable byte := by
  constructor
  intro input value rest parsed
  cases input with
  | nil => simp [Decode.byte] at parsed
  | cons head tail =>
      simp only [Decode.byte, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      exact ⟨[head], rfl, fun _ => rfl⟩

theorem Stable.lift (option : Option α) : Stable (lift option) := by
  cases option with
  | none => exact Stable.fail
  | some value => exact Stable.pure value

theorem Stable.bind {parser : Parser α} {next : α → Parser β} (first : Stable parser)
    (rest : ∀ value, Stable (next value)) : Stable (parser >>= next) := by
  constructor
  intro input value remaining parsed
  change (parser input).bind (fun result => next result.1 result.2) = some (value, remaining) at parsed
  rcases Option.bind_eq_some_iff.mp parsed with ⟨⟨middle, after⟩, parsedFirst, parsedNext⟩
  simp only at parsedNext
  obtain ⟨consumed, same, extension⟩ := first.holds parsedFirst
  obtain ⟨consumedNext, sameNext, extensionNext⟩ := (rest middle).holds parsedNext
  refine ⟨consumed ++ consumedNext, by rw [same, sameNext, List.append_assoc], ?_⟩
  intro suffix
  change (parser (consumed ++ consumedNext ++ suffix)).bind (fun result => next result.1 result.2) = _
  rw [List.append_assoc, extension, Option.bind_some]
  exact extensionNext suffix

theorem Stable.map {parser : Parser α} (f : α → β) (first : Stable parser) : Stable (f <$> parser) := by
  constructor
  intro input value remaining parsed
  change (parser input).bind (fun result => some (f result.1, result.2)) = some (value, remaining) at parsed
  rcases Option.bind_eq_some_iff.mp parsed with ⟨⟨middle, after⟩, parsedFirst, equal⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  obtain ⟨consumed, same, extension⟩ := first.holds parsedFirst
  refine ⟨consumed, same, fun suffix => ?_⟩
  change (parser (consumed ++ suffix)).bind (fun result => some (f result.1, result.2)) = _
  rw [extension]
  rfl

theorem Stable.ite {condition : Prop} [Decidable condition] {left right : Parser α}
    (yes : Stable left) (no : Stable right) : Stable (if condition then left else right) := by
  split
  · exact yes
  · exact no

/-- Apply the stability combinators through a parser's structure. -/
macro "stable" : tactic => `(tactic|
  repeat' (first
    | (intro)
    | apply Stable.bind
    | apply Stable.map
    | apply Stable.pure
    | apply Stable.fail
    | apply Stable.byte
    | apply Stable.lift
    | apply Stable.ite
    | split
    | (dsimp only)))

theorem readLE_stable (count : Nat) : Stable (readLE count) := by
  induction count with
  | zero => exact Stable.pure 0
  | succ count ih =>
      unfold readLE
      stable
      exact ih

theorem displacement_stable (mode : Nat) : Stable (displacement mode) := by
  unfold displacement
  stable
  all_goals exact readLE_stable _

theorem memory_stable (rex : Rex) (modrm : UInt8) : Stable (memory rex modrm) := by
  unfold memory
  stable
  all_goals first | exact readLE_stable _ | exact displacement_stable _

theorem immediate_stable (kind : ImmKind) : Stable (immediate kind) := by
  unfold immediate
  stable
  all_goals exact readLE_stable _

theorem rmOperand_stable (rex : Rex) (modrm : UInt8) : Stable (rmOperand rex modrm) := by
  unfold rmOperand
  stable
  all_goals exact memory_stable _ _

theorem modrmFields_stable (use : ModRMUse) (rex : Rex) (modrm : UInt8) : Stable (modrmFields use rex modrm) := by
  unfold modrmFields
  stable
  all_goals exact rmOperand_stable _ _

theorem opcodeFields_stable (emb : Emb) (rex : Rex) (opcode : UInt8) : Stable (opcodeFields emb rex opcode) := by
  unfold opcodeFields
  stable

theorem operands_stable (o : Op) (rexByte : Option Rex) (opcode : UInt8) (preread : Option UInt8) :
    Stable (operands o rexByte opcode preread) := by
  unfold operands
  stable
  all_goals first
    | exact opcodeFields_stable _ _ _
    | exact modrmFields_stable _ _ _
    | exact immediate_stable _

theorem body_stable (p66 : Bool) (rexByte : Option Rex) (map : OpMap) (opcode : UInt8) :
    Stable (body p66 rexByte map opcode) := by
  unfold body
  stable
  all_goals exact operands_stable _ _ _ _

theorem opcodeStage_stable (p66 : Bool) (rexByte : Option Rex) (first : UInt8) :
    Stable (opcodeStage p66 rexByte first) := by
  unfold opcodeStage
  stable
  all_goals exact body_stable _ _ _ _

theorem rexStage_stable (p66 : Bool) (first : UInt8) : Stable (rexStage p66 first) := by
  unfold rexStage
  stable
  all_goals first | exact opcodeStage_stable _ _ _ | exact body_stable _ _ _ _

theorem one_stable : Stable one := by
  unfold one
  stable
  all_goals first | exact rexStage_stable _ _ | exact opcodeStage_stable _ _ _ | exact body_stable _ _ _ _

private theorem one_prefix {input value rest}
    (accepted : one input = some (value, rest)) : PrefixResult one input value rest :=
  one_stable.holds accepted


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

end IxCC.X86.Decode
