/-
  Emit the list of arena fixture names that should NOT be driven through
  `dbg_check_const` in the IxVM kernel binary:

    - Constants registered under a `.bad` test-case outcome (intentional
      kernel rejections).
    - Constants in `Tests.Ix.Kernel.Arena.knownIncompatible` (cases the
      Aiur kernel structurally cannot adjudicate — see comments there).
    - Constants whose test case carries a non-empty `renamings` field
      (collision tests, not single-constant typechecks).

  Output: one fully-qualified Lean name per line, suitable for feeding to
  `ix compile --exclude-file`.

  With `--out <path>` the list is written to that file (one name per line,
  trailing newline) instead of stdout, so callers don't need a shell
  redirect. The build log on stderr stays out of the way either way.
-/
import Ix.Meta
import Tests.Ix.Kernel.TutorialMeta
import Tests.Ix.Kernel.Arena

open Tests.Ix.Kernel.TutorialMeta
open Tests.Ix.Kernel.Arena (knownIncompatible)

/-- Parse `--out <path>` / `--out=<path>` from the arg list. Last one wins. -/
private def outPath? : List String → Option String
  | [] => none
  | "--out" :: path :: rest => (outPath? rest).orElse (fun _ => some path)
  | arg :: rest =>
    if arg.startsWith "--out=" then
      (outPath? rest).orElse (fun _ => some (arg.drop "--out=".length).toString)
    else outPath? rest

def main (args : List String) : IO UInt32 := do
  let env ← get_env!
  let mut excludes : Std.HashSet Lean.Name :=
    knownIncompatible.foldl (init := {}) (fun s (n, _) => s.insert n)
  for tc in getTestCases env do
    let bad := tc.outcome == .bad
    let renamingTest := tc.renamings.size > 0
    if bad || renamingTest then
      for n in tc.decls do
        excludes := excludes.insert n
  let sorted := excludes.toArray.qsort (fun a b => toString a < toString b)
  match outPath? args with
  | some path =>
    let body := String.intercalate "\n" (sorted.map toString).toList
    IO.FS.writeFile path (body ++ "\n")
    IO.eprintln s!"[arena-exclude] wrote {sorted.size} excluded names to {path}"
  | none =>
    for n in sorted do
      IO.println (toString n)
  pure 0
