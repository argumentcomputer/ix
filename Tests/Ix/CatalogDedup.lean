/-
  Cross-process anonymous dedup gate (`--ignored catalog-dedup`) — the
  re-homed C2/C5 invariant from the retired union-loader suites.

  The RelocFixture collision pair (packages A and B, both declaring
  `Collision.Tree` with DIFFERENT definitions, sharing the toolchain
  base) is compiled from its two minimal local Lake workspaces as two
  SEPARATE pieces in two separate `ix compile` processes — no
  qualification, no relocation, no shared frontend — and assembled
  into a `.ixc`. The gates:

  - Assembly succeeds: colliding source NAMES are no conflict at all
    in anon space (names play no part in catalog identity).
  - Shared content dedups: the union is strictly smaller than the sum
    of the pieces — the shared base's constants got IDENTICAL
    addresses in both processes (the old C5 audit's invariant, now
    structural: content addressing is name-independent).
  - Genuine difference survives: the union is strictly larger than
    either piece — the two `Collision.Tree`s are distinct content at
    distinct addresses, coexisting without any namespace work.

  `IxTests` depends on the `ix` executable target. The fixture pieces
  are otherwise self-contained (fixture packages + Init-class closure),
  so this is the merge-queue-scale leg (`catalog-fixtures`'s replacement)
  without materializing the full TruthMines dependency graph.
-/
module

public import LSpec
public import Ix.Cli.CatalogCmd

public section

open LSpec

namespace Tests.Ix.CatalogDedup

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

private def fixtureA : System.FilePath :=
  "Benchmarks" / "Catalog" / "RelocFixtureA" / "FixtureA.lean"

private def fixtureB : System.FilePath :=
  "Benchmarks" / "Catalog" / "RelocFixtureB" / "FixtureB.lean"

private def compilePiece (exe : System.FilePath) (driver out : String) :
    IO (Except String Unit) := do
  let r ← IO.Process.output {
    cmd := exe.toString, args := #["compile", driver, "--out", out] }
  if r.exitCode != 0 then
    return .error s!"ix compile {driver} failed ({r.exitCode}): \
{r.stderr.take 300} … {(r.stdout.takeEnd 300).toString}"
  return .ok ()

private def dedupTest : IO (Bool × Nat × Nat × Option String) := do
  unless (← ixExe.pathExists) do
    return (false, 0, 0, some s!"{ixExe} missing — run `lake build ix` first")
  for fixture in [fixtureA, fixtureB] do
    unless (← fixture.pathExists) do
      return (false, 0, 0, some s!"fixture source missing: {fixture}")
  let exe ← IO.FS.realPath ixExe
  let dir ← IO.FS.createTempDir
  try
    let pieceA := (dir / "A.ixe").toString
    let pieceB := (dir / "B.ixe").toString
    -- Two separate processes: nothing shared but the source tree.
    if let .error e ← compilePiece exe fixtureA.toString pieceA then
      return (false, 0, 0, some e)
    if let .error e ← compilePiece exe fixtureB.toString pieceB then
      return (false, 0, 0, some e)
    -- Assemble the self-contained .ixc dir via the CLI, then gate on
    -- the manifest through the in-process core (info/verify FFI) — no
    -- report artifacts anywhere in this flow.
    let ixc := (dir / "cat.ixc").toString
    let r ← IO.Process.output {
      cmd := exe.toString
      args := #["catalog", "assemble", ixc, pieceA, pieceB,
        "--labels", "A,B"] }
    if r.exitCode != 0 then
      return (false, 0, 0, some s!"assemble failed ({r.exitCode}): \
{r.stderr.take 300}")
    let infoContent ← Ix.Cli.CatalogCmd.rsCatalogInfoFFI ixc
    let verifyContent ← Ix.Cli.CatalogCmd.rsCatalogVerifyFFI ixc false
    let checks : Except String (Nat × Nat) := do
      let info ← Lean.Json.parse infoContent
      let verifyJson ← Lean.Json.parse verifyContent
      let members ← (← info.getObjVal? "members").getArr?
      let countOf (i : Nat) : Except String Nat := do
        (← (members[i]!).getObjVal? "constCount").getNat?
      let a ← countOf 0
      let b ← countOf 1
      let union ← (← verifyJson.getObjVal? "unionConsts").getNat?
      unless union < a + b do
        throw s!"no dedup: union {union} = |A| {a} + |B| {b} — shared \
content got different addresses across processes"
      unless union > a && union > b do
        throw s!"union {union} not larger than both pieces ({a}, {b}) — \
the collision pair's distinct content collapsed"
      return (union, a + b)
    match checks with
    | .ok (union, sum) => return (true, union, sum, none)
    | .error m => return (false, 0, 0, some m)
  finally
    IO.FS.removeDirAll dir

def suite : List TestSeq := [
  .individualIO
    "catalog-dedup: cross-process pieces share addresses, collisions coexist"
    none dedupTest .done ]

end Tests.Ix.CatalogDedup
