import CompilatrixTests.Ixby.Fri.Execution

namespace CompilatrixTests.Ixby.Fri

def run : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `CompilatrixTests.Ixby.Fri.Examples }] {}
  checking env
  execution env

end CompilatrixTests.Ixby.Fri
