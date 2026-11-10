import IxVM.ProofGen

/-! `lake exe ixvm/ixvm-proof-gen [--check]`: write or check the derived lookup
certificates and refinement mirrors. The function definitions themselves are
elaborated from the DSL during compilation. -/

open IxVM.ProofGen

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let files := render
  let mut ok := true
  for (path, text) in files do
    if check then
      let existing ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
      if existing == some text then
        IO.println s!"[ixvm-proof-gen --check] {path} up to date"
      else
        IO.eprintln s!"[ixvm-proof-gen --check] {path} STALE: run `lake exe ixvm/ixvm-proof-gen` and commit the result"
        ok := false
    else
      if let some dir := path.parent then IO.FS.createDirAll dir
      IO.FS.writeFile path text
      IO.println s!"[ixvm-proof-gen] wrote {path}"
  return if ok then 0 else 1
