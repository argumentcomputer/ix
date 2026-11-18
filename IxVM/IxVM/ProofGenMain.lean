import IxVM.ProofGen
import IxVM.ObsGen

/-! `lake exe ixvm/ixvm-proof-gen [--check] [--out DIR]`: write or check the
derived lookup certificates, refinement mirrors and path lemmas (`--out` writes
them under `DIR` instead of the working directory). The function definitions
themselves are elaborated from the DSL during compilation.

The path lemmas' names (`IxVM.ObsGen`) are read from the table
`IxVM/IxVM/ObsNames.txt` (`--names FILE` for another). The table must match the hash
in its header, in every mode. `--explain FILE` writes every shown name with its
position in words.

`--counter-names` ignores the table and numbers every name by the function's counter;
`--emit-names FILE` does the same and writes the table of those names to `FILE`. Both
need `--out DIR`: the counter's names never replace the tracked files.

Exit status: 0; 1 a file is stale (`--check`) or no longer generated; 2 the arguments
or the table are wrong; 3 a name could not be assigned (nothing is written). -/

open IxVM.ProofGen

def outDir : List String → Option System.FilePath
  | "--out" :: dir :: _ => some dir
  | _ :: rest => outDir rest
  | [] => none

def argOf (flag : String) : List String → Option String
  | f :: rest => if f == flag then rest.head? else argOf flag rest
  | [] => none

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let root := outDir args
  let emit := argOf "--emit-names" args
  let explain := argOf "--explain" args
  let counter := args.contains "--counter-names" || emit.isSome
  if counter && root.isNone then
    IO.eprintln ("[ixvm-proof-gen] --counter-names and --emit-names need --out DIR: " ++
      "the counter's names never replace the tracked files")
    return 2
  let namesPath : System.FilePath := ⟨(argOf "--names" args).getD "IxVM/IxVM/ObsNames.txt"⟩
  let mut table : Option IxVM.ObsGen.Table := none
  if !counter then
    let text ← try pure (some (← IO.FS.readFile namesPath)) catch _ => pure none
    match text.map IxVM.ObsGen.readTable with
    | none =>
      IO.eprintln s!"[ixvm-proof-gen] no table of names at {namesPath}"
      return 2
    | some (.error e) =>
      IO.eprintln s!"[ixvm-proof-gen] the table of names {namesPath} is not a table: {e}"
      return 2
    | some (.ok t) =>
      if t.declared != some t.computed then
        IO.eprintln (s!"[ixvm-proof-gen] the table of names {namesPath} does not match its hash " ++
          s!"(declared {t.declared.getD "none"}, computed {t.computed}): it was changed")
        return 2
      -- a function that was renamed keeps its names when its `@` line is renamed
      let known := IxVM.functions.map (·.name)
      let unknown := t.order.filter fun name => !known.contains name
      unless unknown.isEmpty do
        IO.eprintln (s!"[ixvm-proof-gen] {unknown.size} functions of the table are not in the " ++
          s!"program: {", ".intercalate unknown.toList}")
      table := some t
  let obs ← IxVM.ObsGen.renderIO { table := table.map (·.sections), explain := explain.isSome }
  unless obs.failures.isEmpty do
    for m in obs.failures do IO.eprintln s!"[ixvm-proof-gen] names: {m}"
    IO.eprintln "[ixvm-proof-gen] a name could not be assigned: nothing is written or checked"
    return 3
  if let some path := emit then IO.FS.writeFile ⟨path⟩ obs.table
  if let some path := explain then IO.FS.writeFile ⟨path⟩ obs.explain
  let files := render ++ obs.files
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
