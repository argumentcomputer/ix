import IxVM.ProofGen
import IxVM.ObsGen

/-! `lake exe ixvm/ixvm-proof-gen [--check] [--out DIR]`: write or check the
derived lookup certificates, refinement mirrors and path lemmas (`--out` writes
them under `DIR` instead of the working directory). The function definitions
themselves are elaborated from the DSL during compilation. -/

open IxVM.ProofGen

def outDir : List String → Option System.FilePath
  | "--out" :: dir :: _ => some dir
  | _ :: rest => outDir rest
  | [] => none

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let root := outDir args
  let files := render ++ (← IxVM.ObsGen.renderIO)
  let mut ok := true
  for (path, text) in files do
    let path := match root with
      | some dir => dir / path
      | none => path
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
  -- a path-lemma module the generator no longer writes (its chunks moved) would still be
  -- built by the `IxVMRefinement` glob: report it (and fail `--check`); it is not deleted here
  let obsDir : System.FilePath := match root with
    | some dir => dir / "IxVMRefinement" / "Obs"
    | none => ⟨"IxVMRefinement/Obs"⟩
  if ← obsDir.isDir then
    let written := files.map fun (path, _) => match root with
      | some dir => dir / path
      | none => path
    for entry in ← obsDir.readDir do
      if entry.path.extension == some "lean" && !written.contains entry.path then
        IO.eprintln s!"[ixvm-proof-gen] {entry.path} is not generated any more: delete it"
        if check then ok := false
  return if ok then 0 else 1
