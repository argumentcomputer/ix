import Aiur.Circuit.MemoDerivation

namespace Aiur.Circuit

/-- An admissible root encodes actual values. This does not assert its truth. -/
def Message.WellFormed [Field F] [DecidableEq F] (decls : Declarations)
    (message : Message F) : Prop :=
  (∀ argument ∈ message.args, ∃ value, argument.decode decls = some value) ∧
    ∃ value, message.result.decode decls = some value

/-- The entire type of every public argument is pointer-free, across all constructors. -/
def Message.PublicArguments (decls : Declarations)
    (message : Message F) : Prop :=
  ∀ argument ∈ message.args, argument.type.pointerFree decls = true

/-- Public acceptance uses a well-formed root and one prover-chosen functional table. -/
def EntryDerives [Field F] [DecidableEq F] (system : System F) (message : Message F) : Prop :=
  message.WellFormed system.enums ∧ message.PublicArguments system.enums ∧
    ∃ rom : WireROM F, rom.Valid ∧ Derives system rom message

/-- Public memoized acceptance permits shared and cyclic call references. -/
def MemoEntryDerives [Field F] [DecidableEq F] (system : System F) (message : Message F) : Prop :=
  message.WellFormed system.enums ∧ message.PublicArguments system.enums ∧
    ∃ rom : WireROM F, rom.Valid ∧ MemoDerives system rom message

theorem EntryDerives.memo [Field F] [DecidableEq F] {system : System F} {message : Message F}
    (accepted : EntryDerives system message) : MemoEntryDerives system message := by
  obtain ⟨formed, free, rom, valid, tree⟩ := accepted
  exact ⟨formed, free, rom, valid, tree.memo⟩

end Aiur.Circuit
