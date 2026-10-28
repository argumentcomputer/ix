/-
  The namespace filter of the CLI commands that select constants by name
  prefix (`--ns`, `--prefix`): `parsePrefixes`.
-/
module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.Meta
public import Ix.EnvScope

public section

/-- Strip ASCII whitespace from both ends of `s`. We roll our own because
`String.trim` was deprecated in favor of slice-returning variants, and we
need a `String → String` shape for `.toName`. -/
private def asciiTrim (s : String) : String :=
  let cs := s.toList.dropWhile Char.isWhitespace
  String.ofList (cs.reverse.dropWhile Char.isWhitespace).reverse

/-- Parse a comma-separated namespace filter like `"Aesop,SetTheory.PGame"` into
a list of `Lean.Name` prefixes. Empty entries are dropped. -/
def parsePrefixes (s : String) : List Lean.Name :=
  (s.splitOn ",").filterMap fun raw =>
    let trimmed := asciiTrim raw
    if trimmed.isEmpty then none else some trimmed.toName

end
