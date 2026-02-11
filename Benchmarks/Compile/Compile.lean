import Ix.CompileM
import Ix.Meta

/-- Format a byte count with appropriate unit suffix (B, kB, MB, GB). -/
def fmtBytes (n : Nat) : String :=
  if n < 1024 then s!"{n} B"
  else if n < 1024 * 1024 then
    let kb := n * 10 / 1024
    s!"{kb / 10}.{kb % 10} kB"
  else if n < 1024 * 1024 * 1024 then
    let mb := n * 10 / (1024 * 1024)
    s!"{mb / 10}.{mb % 10} MB"
  else
    let gb := n * 10 / (1024 * 1024 * 1024)
    s!"{gb / 10}.{gb % 10} GB"

def compile (name : String) : IO Unit := do
  println! "Compiling {name} environment"

  let path := s!"Compile{name}.lean"
  let leanEnv ← getFileEnv path

  let totalConsts := leanEnv.constants.toList.length
  println! "{totalConsts} consts"

  let start ← IO.monoMsNow
  let bytes ← Ix.CompileM.rsCompileEnvBytes leanEnv
  let elapsed := (← IO.monoMsNow) - start

  IO.println s!"Compiled {fmtBytes bytes.size} env in {elapsed}ms"
