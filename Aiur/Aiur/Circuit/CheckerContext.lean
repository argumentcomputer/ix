import Aiur.Circuit.CheckerCompleteness
import Aiur.Circuit.CompileFacts

namespace Aiur.Circuit

variable {F : Type}

/-- Global layout and namespace checks, including unused chips. -/
def System.WellFormed (system : System F) : Prop :=
  (system.chips.map Chip.name).Nodup ∧ ∀ chip ∈ system.chips, chip.wellFormed = true

theorem checkChips_iff {seen : List String} {chips : List (Chip F)} :
    checkChips seen chips = .ok () ↔
      (chips.map Chip.name).Nodup ∧
        (∀ chip ∈ chips, chip.wellFormed = true) ∧
        (∀ chip ∈ chips, chip.name ∉ seen) := by
  induction chips generalizing seen with
  | nil => simp [checkChips]
  | cons chip chips ih =>
      by_cases fresh : chip.name ∈ seen
      · simp [checkChips, fresh, bind, Except.bind]
      · by_cases formed : chip.wellFormed = true
        · simp [checkChips, fresh, formed, bind, Except.bind, pure, Except.pure, ih,
            List.nodup_cons, List.mem_map, and_assoc, and_left_comm, and_comm]
          grind
        · simp [checkChips, fresh, formed, bind, Except.bind, pure, Except.pure]

variable [Field F] [DecidableEq F]

theorem compile_wellFormed {program : Program F} {system : System F}
    (compiled : compile program = .ok system) : system.WellFormed := by
  have checked := checkChips_iff.mp (compile_checkChips compiled)
  exact ⟨checked.1, checked.2.1⟩

theorem System.checkContext_iff {system : System F} {rom : WireROM F} {root : Message F} :
    system.checkContext rom root = .ok () ↔
      root.WellFormed system.enums ∧ root.PublicArguments system.enums ∧
        rom.Valid ∧ system.WellFormed := by
  simp only [System.checkContext, except_bind_ok]
  simp [mapM_unit_succeeds, Message.WellFormed, Message.PublicArguments,
    checkChips_iff, System.WellFormed, pure, Except.pure, bind, Except.bind,
    ite_eq_iff, forall_and, and_assoc, and_left_comm, and_comm, Option.ne_none_iff_exists]
  simp only [eq_comm]
  simp

theorem System.check_entry_sound {system : System F} {rom : WireROM F}
    {root : Message F} {rows : List (Row F)}
    (checked : system.check rom root rows = .ok ()) : EntryDerives system root := by
  obtain ⟨formed, free, valid, _⟩ := System.checkContext_iff.mp (System.check_iff.mp checked).1
  exact ⟨formed, free, rom, valid, system.check_sound checked⟩

theorem System.checkMemo_entry_sound {system : System F} {rom : WireROM F}
    {root : Message F} {rows : List (WeightedRow F)}
    (checked : system.checkMemo rom root rows = .ok ()) : MemoEntryDerives system root := by
  obtain ⟨formed, free, valid, _⟩ := System.checkContext_iff.mp (System.checkMemo_iff.mp checked).1
  exact ⟨formed, free, rom, valid, system.checkMemo_sound checked⟩

theorem System.check_entry_iff {system : System F} (wellFormed : system.WellFormed)
    {root : Message F} :
    (∃ rom rows, system.check rom root rows = .ok ()) ↔ EntryDerives system root := by
  constructor
  · rintro ⟨rom, rows, checked⟩; exact system.check_entry_sound checked
  · rintro ⟨formed, free, rom, valid, tree⟩
    obtain ⟨rows, checked⟩ := (system.check_derives_iff
      (System.checkContext_iff.mpr ⟨formed, free, valid, wellFormed⟩)).mpr tree
    exact ⟨rom, rows, checked⟩

theorem System.checkMemo_entry_iff {system : System F} (wellFormed : system.WellFormed)
    {root : Message F} :
    (∃ rom rows, system.checkMemo rom root rows = .ok ()) ↔ MemoEntryDerives system root := by
  constructor
  · rintro ⟨rom, rows, checked⟩; exact system.checkMemo_entry_sound checked
  · rintro ⟨formed, free, rom, valid, graph⟩
    obtain ⟨rows, checked⟩ := (system.checkMemo_derives_iff
      (System.checkContext_iff.mpr ⟨formed, free, valid, wellFormed⟩)).mpr graph
    exact ⟨rom, rows, checked⟩

end Aiur.Circuit
