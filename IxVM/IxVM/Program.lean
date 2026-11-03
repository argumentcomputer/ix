import Aiur.Modules.Frontend
import Aiur.Library.Blake3.Goldilocks
import Aiur.Library.List.Word
import Aiur.Library.Option

/-! The stage-one IxVM application explicitly selects Goldilocks word and hash
implementations. The compiler, its proofs, and the runtime remain generic. -/
namespace IxVM
open Aiur

abbrev modulus := Library.U32.Goldilocks.modulus
abbrev F := Library.U32.Goldilocks.F

/-- Parse and type-check the IxVM source, then attach its shared word/hash library.
Callers choose entrypoints with `Aiur.Modules.prepare` and may export bytecode,
certified circuits, or population plans from that prepared program. -/
def parse (env : Lean.Environment) (text : String) : Except String (Modules.Program F) := do
  let source ← Modules.Frontend.parse env text
  Modules.checkTemplates (Library.Blake3.templates.append Library.List.Word.declarations
    |>.append Library.Option.declarations |>.append source)
  return Library.Blake3.Goldilocks.program.append (Library.List.Word.declarations.toField F)
    |>.append (Library.Option.declarations.toField F)
    |>.append (source.toField F)

end IxVM
