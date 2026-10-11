/-
  The long flags of `ix` commands parse under the names their commands read
  (`Cli.Parsed.hasFlag`). The `[Cli| …]` DSL names a flag written as an
  identifier by `Name.toString`, which escapes a component that is not an
  identifier (`«full-oracle»`) or is a keyword (`«meta»`): such a flag could
  only be passed as `--«full-oracle»`, and the command's
  `hasFlag "full-oracle"` never saw it. Those flags are registered as string
  literals; each is parsed here, with the escaped spelling refused and a
  neighbouring flag of the same command parsed.
-/
module
public import LSpec
public import Ix.Cli.ValidateLeanCmd
public import Ix.Cli.DiffCmd

public section

open LSpec

namespace Tests.Ix.CliFlags

/-- `args` parse for `cmd` and the parse has `flag`. -/
def parsesWith (cmd : Cli.Cmd) (args : List String) (flag : String) : Bool :=
  match cmd.process args with
  | .ok (_, p) => p.hasFlag flag
  | .error _ => false

/-- `args` do not parse for `cmd`. -/
def refused (cmd : Cli.Cmd) (args : List String) : Bool :=
  match cmd.process args with
  | .ok _ => false
  | .error _ => true

def suite : List TestSeq := [
  test "validate-lean --full-oracle parses as `full-oracle`"
    (parsesWith validateLeanCmd ["--full-oracle", "--ns", "Nat", "f.lean"] "full-oracle"),
  test "validate-lean --«full-oracle» (the escaped spelling) is refused"
    (refused validateLeanCmd ["--«full-oracle»", "f.lean"]),
  test "validate-lean --local parses (neighbour)"
    (parsesWith validateLeanCmd ["--local", "f.lean"] "local"),
  test "validate-lean without --full-oracle has no `full-oracle` flag"
    (!parsesWith validateLeanCmd ["--local", "f.lean"] "full-oracle"),
  test "diff --meta parses as `meta`"
    (parsesWith diffCmd ["--meta", "a.ixe", "b.ixe"] "meta"),
  test "diff --«meta» (the escaped spelling) is refused"
    (refused diffCmd ["--«meta»", "a.ixe", "b.ixe"]),
  test "diff --verbose parses (neighbour)"
    (parsesWith diffCmd ["--verbose", "a.ixe", "b.ixe"] "verbose")]

end Tests.Ix.CliFlags

end
