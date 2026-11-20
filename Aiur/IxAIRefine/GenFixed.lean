import IxAIRefine.ObsGen
import IxAIRefine.Source

/-! The generator target of the `Fixed` program: the emitted `IxAIStep.Fixed.program`, its
checked source `IxAIStep.Fixed.source`, and the generated modules `IxAIRefine.Fixed.Lookup`
and `IxAIRefine.Fixed.Obs.*`. `Tools/IxAIRefineGen.lean` writes them. -/

namespace IxAIRefine.GenFixed

def target : ProofGen.Target where
  program := IxAIStep.Fixed.program
  source := IxAIStep.Fixed.source
  ns := "IxAIStep.Fixed"
  fieldName := "IxAIStep.Fixed.F"
  functionName := fun symbol => ".".intercalate (symbol.splitOn "::")
  sourceModule := "IxAIRefine.Source"
  modulePrefix := "IxAIRefine.Fixed"
  dir := "IxAIRefine/Fixed"
  command := "`lake env lean Tools/IxAIRefineGen.lean` (in `Aiur/`)"
  -- Most functions have at most 40 facts on a path (`hidden`, `update_row16` and
  -- `update_bias16`, with 32 calls each; `train` has 30 `train_block` calls). The transposes
  -- bind the rows of their matrix and project every entry, one fact per entry (up to 320), so
  -- they need a larger `maxFacts`. An array pattern on a parameter is one fact but binds every
  -- element, and each variable lookup is weighted by the environment's length, so functions
  -- that take whole matrices or thread the model through many calls need a larger
  -- `maxLookups`.
  caps :=
    let wide : ProofGen.Limits := { maxChars := 1000000, maxLookups := 200000, maxFacts := 400 }
    let medium : ProofGen.Limits := { maxChars := 400000, maxLookups := 50000 }
    [("Fixed::transpose11x16", wide), ("Fixed::transpose20x16", wide),
     ("Fixed::transpose20x8", wide), ("Fixed::transpose20x11", wide),
     ("Fixed::deltas", medium), ("Fixed::train_block", medium), ("Fixed::train", medium),
     ("Fixed::hidden", medium), ("Fixed::outputs", medium), ("Fixed::delta", medium),
     ("Fixed::update_w1", medium), ("Fixed::update_w2", medium),
     ("Fixed::update_bias16", medium), ("Fixed::update_bias11", medium),
     ("Fixed::update_row8", medium), ("Fixed::update_row16", medium), ("Fixed::sub11", medium)]

end IxAIRefine.GenFixed
