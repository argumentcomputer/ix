import Lean

open Lean

/-- Print the name of every axiom in the environment imported by the given
modules, one per line. -/
def main (modules : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let imports := modules.toArray.map fun m => { module := m.toName : Import }
  let env ← importModules imports {}
  env.constants.forM fun name info => do
    if info matches .axiomInfo _ then
      IO.println name
