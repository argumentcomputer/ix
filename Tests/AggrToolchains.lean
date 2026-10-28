module

public import LSpec
public import Ix.ClaimContext
public import Ix.Ixon
public import IxC.Kernel.Ixon.RoleTable

/-!
# Libraries from several Lean toolchains in one aggregate

End to end through the `ix` binary, over the toolchain fixtures
(`Tests/Fixtures/toolchains/lean-<version>.ndjson.zst`, exports of the roles,
the certificate theorems and a few library theorems from Lean 4.29.0, 4.33.1,
4.34.1 and 4.35.0):

1. each export is compiled (`ix compile-export`) into a piece with its own
   toolchain's role binding, and the role tables are compared with 4.34.1's:
   4.33.1 binds `Nat.land`, `Nat.lor` and `Nat.xor` to other constants but has
   4.34.1's literal class; 4.29.0 and 4.35.0 each have a class of their own;
2. each piece's binding is proven (`ix prove-binding`), its shards are proven
   assuming the binding (`ix prove --assume-binding`) and aggregated with the
   binding proof (`ix aggregate --binding-proof`), and the root verifies;
3. the pieces are assembled into a catalog (`ix catalog assemble`), the roots
   are joined (`ix aggregate --ixc`: 4.33.1 and 4.34.1 under their class, then
   the three classes into a `Catalog` claim), and the root verifies against
   the catalog (`ix verify --aggregate --ixc`), printing every member's
   context;
4. a catalog that drops a member does not verify the root, and the join
   refuses a missing member root.

Every node of every aggregate verifies its children under one identity, the
IxVM and `ix_aggr` keys, so each library is proven with the same IxVM key.

Tens of minutes of proving, so a manual runner. It needs `.lake/build/bin/ix`
(`lake build ix`) and `zstd`, and keeps the store and caches in a temporary
`HOME`. Proving steps run within `IX_TOOLCHAINS_MAX_RAM` GiB (default 140).
-/

public section

namespace Tests.Aggr.Toolchains

private def isAddressHex (s : String) : Bool :=
  s.length == 64 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

private def lines (s : String) : List String :=
  (s.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)

/-- Run `ix` with `HOME` set to `home`, logging the command, its exit code
    and time, and on failure the end of its output. -/
private def ix (exe : String) (home : System.FilePath) (args : Array String) :
    IO IO.Process.Output := do
  IO.eprintln s!"[toolchains] ix {" ".intercalate args.toList}"
  let started ← IO.monoMsNow
  let out ← IO.Process.output { cmd := "env", args := #[s!"HOME={home}", exe] ++ args }
  IO.eprintln s!"[toolchains]   exit {out.exitCode} in {(← IO.monoMsNow) - started} ms"
  if out.exitCode != 0 then
    IO.eprintln s!"{(out.stdout.takeEnd 2000).toString}\n{(out.stderr.takeEnd 2000).toString}"
  pure out

/-- The fixture toolchains, 4.34.1 (ix's own) first. -/
def versions : List String := ["4.34.1", "4.33.1", "4.29.0", "4.35.0"]

/-- A compiled piece's role table and binding hash. -/
private def tableOf (piece : System.FilePath) : IO (Ix.Kernel.RoleTable × Address × ByteArray) := do
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile piece))
  let some binding := env.roleBinding
    | throw (IO.userError s!"{piece} carries no role binding")
  let some table := Ix.Kernel.RoleTable.ofBytes binding.bytes
    | throw (IO.userError s!"{piece}: not a role binding section")
  pure (table, binding.address, binding.bytes)

/-- The roles two tables bind to different constants. -/
private def boundDiff (a b : Ix.Kernel.RoleTable) : List Ix.Kernel.Role :=
  Ix.Kernel.Role.all.filter fun r =>
    (a.bound.find? (·.1 == r)).map (·.2) != (b.bound.find? (·.1 == r)).map (·.2)

/-- One member: its piece proven and aggregated. Returns its root's address. -/
private def member (exe : String) (home dir : System.FilePath) (maxRam : Nat) (v : String) :
    IO (Except String String) := do
  let piece := dir / s!"lean-{v}.ixe"
  let ixes := dir / s!"lean-{v}.ixes"
  let bindingProof := dir / s!"binding-{v}.proof"
  let proved ← ix exe home #["prove-binding", piece.toString, "--out", bindingProof.toString]
  if proved.exitCode != 0 then return .error s!"{v}: ix prove-binding"
  let sharded ← ix exe home #["shard", piece.toString, "--max-ram", "64", "--out", ixes.toString]
  if sharded.exitCode != 0 then return .error s!"{v}: ix shard"
  let envArgs := #["--ixe", piece.toString, "--ixes", ixes.toString]
  let shards ← ix exe home (#["prove"] ++ envArgs ++
    #["--assume-binding", "--max-ram", "64"])
  let proofs := (lines shards.stdout).filter isAddressHex
  if shards.exitCode != 0 || proofs.isEmpty then return .error s!"{v}: ix prove --assume-binding"
  let aggregated ← ix exe home (#["aggregate"] ++ envArgs ++ proofs.toArray ++
    #["--binding-proof", bindingProof.toString, "--max-ram", toString maxRam, "--jobs", "1",
      "--trace-shards"])
  let some root := (lines aggregated.stdout).getLast? | return .error s!"{v}: no root"
  if aggregated.exitCode != 0 || !isAddressHex root then return .error s!"{v}: ix aggregate"
  let verified ← ix exe home (#["verify", "--aggregate", root] ++ envArgs)
  if verified.exitCode != 0 then return .error s!"{v}: ix verify --aggregate"
  return .ok root

def run : IO UInt32 := do
  let ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"
  unless (← ixExe.pathExists) do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  let exe := (← IO.FS.realPath ixExe).toString
  let maxRam := ((← IO.getEnv "IX_TOOLCHAINS_MAX_RAM").bind String.toNat?).getD 140
  let home ← IO.FS.createTempDir
  let dir ← IO.FS.createTempDir
  try
    -- 1. The pieces, and their role tables against 4.34.1's.
    let mut tables : Array (String × Ix.Kernel.RoleTable × Address × Address) := #[]
    for v in versions do
      let export_ := dir / s!"{v}.ndjson"
      let out ← IO.Process.output { cmd := "zstd", args := #["-dc", "-q", "-o", export_.toString,
        s!"Tests/Fixtures/toolchains/lean-{v}.ndjson.zst"] }
      if out.exitCode != 0 then
        IO.eprintln s!"zstd: {out.stderr}"
        return 1
      let piece := dir / s!"lean-{v}.ixe"
      let compiled ← ix exe home #["compile-export", export_.toString, "--out", piece.toString]
      if compiled.exitCode != 0 then return 1
      IO.FS.removeFile export_
      let (table, binding, bytes) ← tableOf piece
      let klass ← IO.ofExcept (Ix.ClaimContext.literalClassOfBytes bytes)
      tables := tables.push (v, table, binding, klass)
    let some (_, base, baseBinding, baseClass) := tables[0]? | return 1
    let mut checks : Array (String × Bool) := #[]
    for (v, table, binding, klass) in tables do
      IO.println s!"[toolchains] {v}: binding {binding}, literal class {klass}"
      unless v == "4.34.1" do
        let moved := boundDiff table base
        let same := if klass == baseClass then "equal" else "differs"
        IO.println s!"[toolchains] {v} against 4.34.1: {moved.length} roles bound elsewhere: \
          {moved.map (·.leanName)}; literal class {same}"
    let some (_, t331, b331, k331) := tables.find? (·.1 == "4.33.1") | return 1
    let classOf (v : String) : Option Address := (tables.find? (·.1 == v)).map (·.2.2.2)
    checks := checks.push ("4.33.1 binds exactly Nat.land, Nat.lor and Nat.xor elsewhere",
      boundDiff t331 base == [.natLand, .natLor, .natXor])
    checks := checks.push ("4.33.1 and 4.34.1 have different bindings", b331 != baseBinding)
    checks := checks.push ("4.33.1 and 4.34.1 have one literal class", k331 == baseClass)
    for v in ["4.29.0", "4.35.0"] do
      checks := checks.push (s!"{v} has another literal class",
        (classOf v).isSome && classOf v != some baseClass)
    -- 2. Each member proven and aggregated with its own binding proof.
    let mut roots : Array String := #[]
    for v in versions do
      match ← member exe home dir maxRam v with
      | .ok root =>
        roots := roots.push root
        checks := checks.push (s!"{v}: its binding, shards and aggregate are proven, and the \
          root verifies", true)
      | .error e =>
        checks := checks.push (s!"{v}: {e}", false)
    -- 3. The catalog of the four, the join and its verification.
    let labels := versions.map fun v => s!"lean-{v}"
    let pieces := labels.map fun l => (dir / s!"{l}.ixe").toString
    let ixc := dir / "toolchains.ixc"
    let assembled ← ix exe home (#["catalog", "assemble", ixc.toString] ++ pieces.toArray ++
      #["--labels", ",".intercalate labels, "--toolchains", ",".intercalate versions])
    checks := checks.push ("the four pieces assemble into a catalog", assembled.exitCode == 0)
    for l in labels do
      IO.FS.writeBinFile (ixc / s!"{l}.ixes") (← IO.FS.readBinFile (dir / s!"{l}.ixes"))
    let joined ← ix exe home (#["aggregate", "--ixc", ixc.toString] ++ roots ++
      #["--max-ram", toString maxRam])
    let root := (lines joined.stdout).getLast?.getD ""
    checks := checks.push ("the member roots join into one root",
      joined.exitCode == 0 && isAddressHex root)
    IO.println s!"{joined.stderr}"
    let verified ← ix exe home #["verify", "--aggregate", root, "--ixc", ixc.toString]
    IO.println verified.stdout
    checks := checks.push ("the root verifies against the catalog", verified.exitCode == 0)
    checks := checks.push ("verification prints every member's context",
      labels.all fun l => (verified.stdout.splitOn s!"member {l} ").length > 1)
    -- 4. Refusals: a catalog without 4.29.0 does not verify the root, and the
    -- join refuses to run without a member's root.
    let partialCatalog := dir / "partial.ixc"
    let partialLabels := labels.filter (· != "lean-4.29.0")
    let assembledPartial ← ix exe home (#["catalog", "assemble", partialCatalog.toString] ++
      (partialLabels.map fun l => (dir / s!"{l}.ixe").toString).toArray ++
      #["--labels", ",".intercalate partialLabels])
    let refusedVerify ← ix exe home
      #["verify", "--aggregate", root, "--ixc", partialCatalog.toString]
    checks := checks.push ("a catalog without a member does not verify the root",
      assembledPartial.exitCode == 0 && refusedVerify.exitCode != 0)
    let refusedJoin ← ix exe home (#["aggregate", "--ixc", ixc.toString] ++ roots.pop ++
      #["--max-ram", toString maxRam])
    checks := checks.push ("the join refuses a catalog with a member root missing",
      refusedJoin.exitCode != 0)
    LSpec.lspecIO (.ofList [("aggregate-toolchains",
      checks.toList.map fun (label, ok) => LSpec.test label ok)]) []
  finally
    IO.FS.removeDirAll home
    IO.FS.removeDirAll dir

end Tests.Aggr.Toolchains

end
