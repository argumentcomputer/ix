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
    -- LSpec depends on plausible since the v4.33 workspace pins; every
    -- non-toolchain package in the import closure needs an entry, and
    -- dependencies replay before their dependents.
    { qualifier := `Plausible, roots := #[`Plausible] },
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
    -- I4 loader-level gate, base leg: at `OLeanLevel.private` the
    -- toolchain base keeps theorem proofs and `_private.*` constants.
    -- At exported level `Nat.add_comm` is a body-less axiom and the
    -- privates are absent — and kernel replay still succeeds, so only
    -- this check notices (see the `Ix.Catalog` module header).
    let baseThmKeepsProof :=
      match result.consts.find? (·.1 == `Nat.add_comm) with
      | some (_, .thmInfo _) => true
      | _ => false
    let basePrivatesPresent :=
      result.consts.any fun (n, _) => (`_private).isPrefixOf n
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
      ("base theorem keeps its proof (private-level import)",
        baseThmKeepsProof),
      ("base `_private.*` constants present", basePrivatesPresent),
      ("perLib counts populated", result.perLib.all (·.2 > 0)) ]
    match checks.find? (!·.2) with
    | some (what, _) => return (false, 0, 0, some s!"failed: {what}")
    | none => return (true, 0, 0, none)) .done

def suite : List TestSeq := [buildTest]

end Tests.Ix.Catalog
