import IxAIRefine.GenFixed

/-! Writes the generated lookup facts and path lemmas of the `Fixed` program
(`IxAIRefine.GenFixed.target`) under `IxAIRefine/Fixed/`. Run from the `Aiur/` package
root: `lake env lean Tools/IxAIRefineGen.lean`. -/

#eval do
  discard <| IxAIRefine.ObsGen.writeIO IxAIRefine.GenFixed.target
