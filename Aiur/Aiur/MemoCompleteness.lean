import Aiur.Completeness
import Aiur.Circuit.MemoDerivation

namespace Aiur

variable {F : Type} {rom : WireROM F}

/-- Successful ROM evaluation admits a finite memoized graph of its canonical encodings. -/
theorem memo_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F}
    (evaluated : ROMEvalCall (rom.decode program.enums) program name args result) :
    ∃ wires output, DecodesValues program.enums wires args ∧ output.decode program.enums = some result ∧
      Circuit.MemoAccepts system rom name wires output := by
  obtain ⟨wires, output, arguments, decoded, tree⟩ := evaluation_complete compiled evaluated
  exact ⟨wires, output, arguments, decoded, tree.memo⟩

end Aiur
