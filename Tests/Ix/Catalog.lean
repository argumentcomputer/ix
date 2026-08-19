/-
  `Ix.Catalog` smoke test: build a qualified union of two real workspace
  packages (LSpec and Cli), and assert the catalog contract — owned
  constants appear under `<prefix>.<qualifier>.<source name>` (lossless,
  so `LSpec.TestSeq` becomes `TestCatalog.LSpec.LSpec.TestSeq`), the
  kernel regenerates recursors under the qualified names, source names
  do not leak, and the toolchain base stays unqualified.
-/
module

public import LSpec
public import Ix.Catalog

public section

open LSpec

namespace Tests.Ix.Catalog

def spec : Ix.Catalog.CatalogSpec := {
  catalogPrefix := `TestCatalog
  libs := #[
    { qualifier := `LSpec, roots := #[`LSpec] },
    { qualifier := `Cli, roots := #[`Cli] } ] }

def buildTest : TestSeq :=
  .individualIO "catalog: LSpec+Cli qualified union kernel-replays" none (do
    -- `buildCatalog` documents search-path init as caller responsibility;
    -- with no cwd this honors the inherited LEAN_PATH or queries lake in
    -- the working directory (the workspace root under `lake test`).
    initLeanSearchPath
    let result ← Ix.Catalog.buildCatalog spec
    let names : Std.HashSet Lean.Name :=
      result.consts.foldl (fun s (n, _) => s.insert n) {}
    let checks : List (String × Bool) := [
      ("replayed something", result.replayed > 0),
      ("qualified LSpec.TestSeq present",
        names.contains `TestCatalog.LSpec.LSpec.TestSeq),
      ("qualified Cli.Cmd present",
        names.contains `TestCatalog.Cli.Cli.Cmd),
      ("kernel regenerated the recursor",
        names.contains `TestCatalog.LSpec.LSpec.TestSeq.rec),
      ("no unqualified LSpec constants", !names.contains `LSpec.TestSeq),
      ("no unqualified Cli constants", !names.contains `Cli.Cmd),
      ("toolchain base is unqualified", names.contains `Nat),
      ("perLib counts populated", result.perLib.all (·.2 > 0)) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, 0, 0, none)) .done

def suite : List TestSeq := [buildTest]

end Tests.Ix.Catalog
