import Aiur.Modules.Frontend
import Aiur.Library.Blake3.Goldilocks

/-! Recursive multi-stark verification as an ordinary Aiur program. This package
selects Goldilocks explicitly, including its degree-two extension and Blake3
transcript. It introduces no compiler or semantic primitives. -/
namespace MultiStark
open Aiur

abbrev modulus := Library.U32.Goldilocks.modulus
abbrev F := Library.U32.Goldilocks.F

def parse (env : Lean.Environment) (text : String) : Except String (Modules.Program F) := do
  let source ← Modules.Frontend.parse env text
  Modules.checkTemplates (Library.Blake3.templates.append source)
  return Library.Blake3.Goldilocks.program.append (source.toField F)

end MultiStark
