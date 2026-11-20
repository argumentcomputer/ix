import IxAIRefine.Elab

/-! The `Fixed` program, elaborated once into named definitions (`#ixai_fixed_program`):
the definitions used by `IxAIStep.Fixed.source` and by the refinement proofs. -/

set_option maxRecDepth 100000

#ixai_fixed_program

namespace IxAIStep.Fixed

/-- The emitted functions, in program order. -/
def functionNames : List String := functions.map (·.name)

end IxAIStep.Fixed
