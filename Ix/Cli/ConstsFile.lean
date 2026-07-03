/-
  Shared parsing for constant-name inputs (`--consts` comma-lists and
  `--consts-file` files) across every CLI that takes them: `ix check-rs`,
  `ix compile --exclude-file`, and `bench-typecheck`.

  One grammar everywhere: one name per line, everything from a `#` to end of
  line is a comment (whole-line or inline), blank lines dropped. `#` never
  appears in a Lean name, so splitting on it is safe. The zkVM hosts'
  `--consts-file` (Rust `collect_consts`) parses the same grammar, so a single
  names file drives all backends identically.

  Names stay RAW strings here — resolution differs per caller (`toName` for
  meta-mode seeds, string-match against the env's `named` map for the anon /
  zkVM-style paths, where a `toName` round-trip could mangle numeric or
  private components).
-/
module
public import Cli

public section

namespace Ix.Cli.ConstsFile

/-- Parse names-file contents: one name per line, `#`-to-EOL comments,
    blank lines dropped. -/
def parseLines (contents : String) : Array String :=
  (contents.splitOn "\n").filterMap (fun line =>
    let s := ((line.splitOn "#").head?.getD "").trimAscii
    if s.isEmpty then none else some s.toString) |>.toArray

/-- Read and parse a names file. -/
def read (path : String) : IO (Array String) :=
  parseLines <$> IO.FS.readFile path

/-- Split a `--consts`-style comma-list into trimmed, non-empty names. -/
def parseCommaList (arg : String) : Array String :=
  (arg.splitOn ",").filterMap (fun s =>
    let t := s.trimAscii
    if t.isEmpty then none else some t.toString) |>.toArray

/-- Union of a parsed `--consts` comma-list flag and a `--consts-file` file
    (both optional), deduped in first-seen order. -/
def gather (p : Cli.Parsed)
    (constsFlag : String := "consts") (fileFlag : String := "consts-file") :
    IO (Array String) := do
  let fromFlag : Array String :=
    match p.flag? constsFlag with
    | some f => parseCommaList (f.as! String)
    | none => #[]
  let fromFile : Array String ←
    match p.flag? fileFlag with
    | some f => read (f.as! String)
    | none => pure #[]
  -- Linear-scan dedupe: name lists are tens of entries, not thousands.
  let mut acc : Array String := #[]
  for n in fromFlag ++ fromFile do
    if !acc.contains n then
      acc := acc.push n
  return acc

end Ix.Cli.ConstsFile
