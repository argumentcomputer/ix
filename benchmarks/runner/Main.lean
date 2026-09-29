import Runner.Report

open Runner System

def usage : String :=
  "usage: runner (build | check | measure [--cpu N] [--blocks B] [--fixtures a,b] | report) OUT\n\
   Run from benchmarks/runner; fixtures come from ../fixtures/manifest.json."

def main (args : List String) : IO UInt32 := do
  let root : FilePath := "../fixtures"
  try
    let manifest ← Manifest.load (root / "manifest.json")
    match args with
    | ["build", out] => build manifest root out
    | ["check", out] => check manifest root out
    | "measure" :: rest =>
      let rec options (cpu blocks : Nat) (only : Option (List String)) :
          List String → IO (Nat × Nat × Option (List String) × FilePath)
        | "--cpu" :: n :: more => options n.toNat! blocks only more
        | "--blocks" :: n :: more => options cpu n.toNat! only more
        | "--fixtures" :: names :: more => options cpu blocks (some (names.splitOn ",")) more
        | [out] => pure (cpu, blocks, only, out)
        | _ => throw (IO.userError usage)
      let (cpu, blocks, only, out) ← options 2 10 none rest
      measure manifest out cpu blocks only
    | ["report", out] => report manifest out
    | _ => throw (IO.userError usage)
    return 0
  catch error =>
    IO.eprintln s!"runner: {error}"
    return 1
