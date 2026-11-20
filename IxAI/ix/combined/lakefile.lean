import Lake
open Lake DSL

/- The environment of the combined training certificate. Its imports (`IxAIRefine`, `IxAICore`,
Mathlib, Aiur) come from `~/repos/ix.ixai-aiur/Aiur`, whose `LEAN_PATH` the caller supplies. -/
package combined

lean_lib IxAICombined
