import Ix.CompileM
import Ix.Meta

def compile (name : String) : IO Unit := do
  println! "Compiling {name} environment"

  let leanEnv ← get_env!

  let start ← IO.monoMsNow
  let phases ← Ix.CompileM.rsCompilePhases leanEnv
  let elapsed := (← IO.monoMsNow) - start

  IO.println s!"{phases.rawEnv.consts.size} consts, {phases.condensed.blocks.size} blocks, {phases.compileEnv.constCount} compiled in {elapsed}ms"
