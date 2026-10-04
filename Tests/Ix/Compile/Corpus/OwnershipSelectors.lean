import Tests.Ix.Compile.Corpus.Run

open Lean Tests.Ix.Compile.Corpus

/-- Run after the private ownership oracle fixture, passing its retained off-mode
run directory. Exercise actual CLI selection, including mixed valid/missing input,
through the same strict command wrapper as production corpus runs. -/
def main (args : List String) : IO UInt32 := do
  let [runPath] := args | throw <| IO.userError "expected private fixture run directory"
  let runDir : System.FilePath := runPath
  let manifest : Json ← readJson (runDir / "compile-ownership.json")
  let records ← IO.ofExcept (manifest.getObjValAs? (Array Json) "records")
  let mut names : Array String := #[]
  let mut addresses : Array String := #[]
  for row in records do
    if ← IO.ofExcept (row.getObjValAs? Bool "private") then
      names := names.push (← IO.ofExcept (row.getObjValAs? String "display"))
      addresses := addresses.push (← IO.ofExcept (row.getObjValAs? String "address"))
  unless names.size == 2 && addresses.size == 2 do
    throw <| IO.userError "private control must select exactly its helper and theorem"
  let dir := runDir / "selector-controls"
  IO.FS.createDirAll dir
  let namesFile := dir / "private-names.txt"
  let addressesFile := dir / "private-addresses.txt"
  let missingFile := dir / "mixed-missing.txt"
  let missingAddressFile := dir / "mixed-missing-address.txt"
  let write (path : System.FilePath) (xs : Array String) :=
    IO.FS.writeFile path (String.intercalate "\n" xs.toList ++ "\n")
  write namesFile names
  write addressesFile addresses
  write missingFile (names.push "CorpusOwnership.absent")
  write missingAddressFile (addresses.push (String.ofList (List.replicate 64 '0')))
  let cfg : RunConfig := { dir, workers := 2 }
  let envPath := (runDir / "lean.ixe").toString
  for (label, checker, anon, file) in #[
      ("rust-meta", "check-rs", false, namesFile),
      ("rust-anon", "check-rs", true, namesFile),
      ("lean-meta", "check-lean", false, namesFile),
      ("lean-anon", "check-lean", true, addressesFile)] do
    let extra := if anon then #["--anon"] else #[]
    let out ← command cfg dir label cfg.ix.toString
      (#[checker, envPath, "--consts-file", file.toString] ++ extra)
    unless out.exitCode == 0 do throw <| IO.userError s!"private selector {label} failed"
  for (label, checker, anon, file) in #[
      ("rust-missing", "check-rs", false, missingFile),
      ("lean-missing", "check-lean", false, missingFile),
      ("lean-anon-missing", "check-lean", true, missingAddressFile)] do
    let extra := if anon then #["--anon"] else #[]
    let rejected ← try
        let out ← command cfg dir label cfg.ix.toString
          (#[checker, envPath, "--consts-file", file.toString] ++ extra)
        -- Rust's exact-only fast path checks the absent request explicitly:
        -- it reports 2/3, exits rejected, and names the missing Named entry.
        -- Lean instead emits an unmatched-selection diagnostic, caught below.
        pure (checker == "check-rs" && out.exitCode != 0 &&
          (out.stdout.splitOn "CorpusOwnership.absent: kernel: CorpusOwnership.absent: missing Named entry").length > 1)
      catch e =>
        -- Do not mistake an unrelated process failure for the selection guard.
        pure ((e.toString.splitOn "unmatched").length > 1)
    unless rejected do throw <| IO.userError s!"{label}: mixed valid/missing selector was not rejected explicitly"
  IO.println "[ownership-selectors] 2 private identities; 4 positive checker selections; 3 mixed-missing guards PASS"
  return 0
