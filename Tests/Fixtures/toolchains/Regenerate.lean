/-!
# Regenerating the toolchain fixtures

```
lean --run Tests/Fixtures/toolchains/Regenerate.lean <work dir> [<version>…]
```

Run it from the repository root, on Linux x86-64 with `curl`, `tar`, `zstd` and
`git`; any Lean can run it. It regenerates `Tests/Fixtures/toolchains/lean-<version>.ndjson.zst`
for each toolchain in `toolchains`, or for the versions given. For each one it:

1. fetches the official release `lean-<version>-linux.tar.zst` into the work directory;
2. builds `lean4export` at the commit pinned below, with that toolchain's `lake`,
   after two small changes (`exporterPatches`);
3. compiles the certificate theorems (`IxC/Kernel/PinGen/Certs.lean`, or the
   variant named below) and `Primitives.lean` with that toolchain's `lean`, under
   the module names ix compiles them under;
4. exports the closure of `roots` with `lean4export --export-mdata
   --export-unsafe`, and fails if the exporter exits nonzero or prints `PANIC`
   (it panics, and still exits 0, on a missing root);
5. compresses the export with `zstd -19`.

ix is never built on these toolchains: `ix compile-export` reads the exports on
ix's own toolchain. A `.ixe` compiled from an export matches the native compile
of the same declarations in content, not in metadata: `lean4export` writes
syntax-valued `mdata` in a form that cannot be read back, and an unpatched one
also keeps only one set of binder names and binder info per α-equivalence class
of subterms (see `Ix/LeanExport.lean`).

The script also checks that the 4.35.0 certificate variant is still
`Certs.lean` under the substitution `certificateVariant` describes, so the two
cannot drift apart.
-/

/-- A fixture toolchain: its release version, the `lean4export` commit that
builds on it (the exporter's release tag for that Lean), and the certificate
source it compiles. -/
structure Toolchain where
  version : String
  exporterTag : String
  exporterCommit : String
  certificates : System.FilePath := "IxC/Kernel/PinGen/Certs.lean"

def fixtureDir : System.FilePath := "Tests/Fixtures/toolchains"

def toolchains : List Toolchain := [
  { version := "4.29.0", exporterTag := "v4.29.0"
    exporterCommit := "5a53b634f6a3e21e55b4852337c4fcf0781ad1aa" },
  { version := "4.33.1", exporterTag := "v4.33.0"
    exporterCommit := "15f6055e299ad5b89345e533cc2192f4cc00f659" },
  { version := "4.34.1", exporterTag := "v4.34.0"
    exporterCommit := "076e8e57707e813375e8f9da8bf989799ace9680" },
  -- `Decidable` became a structure: the certificate proofs case on it differently.
  { version := "4.35.0", exporterTag := "v4.35.0"
    exporterCommit := "5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe"
    certificates := fixtureDir / "Certs-4.35.0.lean" }]

/-- The roles' constants (`Ix.Kernel.Role.all`). -/
def roleNames : List String :=
  ["Nat", "Nat.zero", "Nat.succ", "Nat.rec", "Bool", "Bool.false", "Bool.true", "Bool.rec",
   "Eq", "Eq.refl", "Eq.rec", "PUnit", "PUnit.unit", "PUnit.rec", "Empty", "Empty.rec",
   "False", "False.rec", "True", "True.intro", "And", "And.intro", "And.rec",
   "Iff", "Iff.intro", "Iff.rec", "Nonempty", "Nonempty.intro", "Nonempty.rec",
   "List", "List.nil", "List.cons", "Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound",
   "String", "String.ofList", "Char", "Char.ofNat", "Nat.pred", "Nat.add", "Nat.sub",
   "Nat.mul", "Nat.pow", "Nat.beq", "Nat.ble", "Nat.div", "Nat.mod", "Nat.gcd", "Nat.land",
   "Nat.lor", "Nat.xor", "Nat.shiftLeft", "Nat.shiftRight", "propext", "Classical.choice",
   "sorryAx", "Decidable", "Decidable.isTrue", "Decidable.isFalse", "Not",
   "of_decide_eq_true", "of_decide_eq_false", "Decidable.decide", "Nat.le", "Nat.decEq",
   "Nat.decLe", "Nat.decLt", "Int", "Int.ofNat", "Int.negSucc", "Int.negOfNat",
   "Int.subNatNat", "Int.neg", "Int.add", "Int.sub", "Int.mul", "Int.natAbs", "Int.ediv",
   "Int.emod", "Int.pow", "BitVec", "BitVec.ofNat", "BitVec.toNat", "BitVec.ult",
   "String.decEq", "ByteArray", "ByteArray.empty", "String.toByteArray", "List.append",
   "String.append", "ite", "Int.le", "Int.decEq", "Int.decLe", "Int.decLt", "Int.bmod",
   "Int.bdiv", "Char.utf8Size", "String.utf8ByteSize", "String.back"]

/-- The certificate theorems (`Ix.RoleEvidence.allCertTheorems`). -/
def certificateNames : List String :=
  ["divBaseZeroCert", "divBaseGtCert", "divRecCert", "modBaseZeroCert", "modBaseGtCert",
   "modRecCert", "gcdBaseCert", "gcdRecCert", "landBaseCert", "landRecCert", "lorBaseCert",
   "lorRecCert", "xorBaseCert", "xorRecCert", "shiftLeftBaseCert", "shiftLeftRecCert",
   "shiftRightBaseCert", "shiftRightRecCert", "decideExtCert", "natDecEqCert", "natDecLeCert",
   "intSubNatNatGeCert", "intSubNatNatLtCert", "intPowEvenCert", "intPowOddCert",
   "bitVecUltCert", "stringDecEqCert", "stringAppendCert", "intDecEqOfNatCert",
   "intDecEqNegSuccCert", "intDecLeOfNatCert", "intDecLeOfNatNegSuccCert",
   "intDecLeNegSuccCert", "charUtf8Size1Cert", "charUtf8Size2Cert", "charUtf8Size3Cert",
   "charUtf8Size3HighCert", "charUtf8Size4Cert", "stringUtf8ByteSizeConsCert",
   "stringBackOneCert", "stringBackConsCert"].map ("Ix.Kernel.PinGen." ++ ·)

/-- The library theorems: present in every fixture toolchain. -/
def libraryNames : List String :=
  ["Nat.add_comm", "Nat.mul_comm", "List.length_append"]

/-- The literal facts (`Primitives.lean`). -/
def literalFactNames : List String :=
  ["natLand", "natLor", "natXor", "natDiv", "natMod", "natGcd", "natMul", "charLiteral",
   "stringLiteral"].map ("ToolchainFixture." ++ ·)

def roots : List String := roleNames ++ certificateNames ++ libraryNames ++ literalFactNames

/-- The changes made to each pinned `lean4export` before it is built, as
(file, text, replacement); each text must occur exactly once.

- **Every constant without roots.** Upstream's `Main.lean` drops, from the
  default root set (every constant of the environment), each name with a
  component starting with `_`: private and auxiliary constants such as
  `_private…`, `_unsafe_rec` and `_cstage`. ix compiles them, so an export of
  whole modules must carry them. The fixtures name their roots, so this does
  not change them; it matters for an export of a whole library.
- **Binder names and binder info.** Upstream hash-conses expressions under
  Lean's `BEq Expr`, which is α-equivalence and ignores binder annotations, so
  every α-equivalent subterm is written with its first occurrence's binder
  names and binder info. Keying the table by `ExprStructEq` (`Expr.equal`)
  keeps them. -/
def exporterPatches : List (System.FilePath × String × String) := [
  ("Main.lean", "env.constants.toList.map Prod.fst |>.filter (!·.isInternal)",
    "env.constants.toList.map Prod.fst"),
  ("Export.lean", "visitedExprs : HashMap Expr Nat", "visitedExprs : HashMap ExprStructEq Nat"),
  ("Export.lean", "getIdx e \"ie\"", "getIdx (ExprStructEq.mk e) \"ie\"")]

/-- Apply `exporterPatches` to a checkout. -/
def patchExporter (dir : System.FilePath) : IO Unit := do
  for (file, text, replacement) in exporterPatches do
    let source ← IO.FS.readFile (dir / file)
    unless (source.splitOn text).length == 2 do
      throw (IO.userError s!"{dir / file}: expected `{text}` exactly once")
    IO.FS.writeFile (dir / file) (source.replace text replacement)

/-- Run a command, failing with its output unless it exits 0. -/
def run (cmd : String) (args : Array String) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let out ← IO.Process.output { cmd, args, cwd, env }
  unless out.exitCode == 0 do
    throw (IO.userError s!"{cmd} {args.toList} exited {out.exitCode}\n{out.stdout}\n{out.stderr}")
  return out

/-- The helper the 4.35.0 variant adds before `dpos`. -/
def certificateHelper : String :=
  "/-- Case analysis on a `Decidable` instance, false case first: the argument
order of `Decidable.casesOn` when `Decidable` was an inductive with the two
constructors `isFalse` and `isTrue`. It cases on the instance's fields, as
`dite` does, so that a closed proof reaches `Decidable` only through its
projections and constructor (structure eta), never through its recursor, which
is outside the operations' dependency closures. -/
private abbrev decCases {c : Prop} {motive : Decidable c → Sort u} (d : Decidable c)
    (isFalse : ∀ h, motive (Decidable.isFalse h)) (isTrue : ∀ h, motive (Decidable.isTrue h)) :
    motive d :=
  Bool.casesOn (motive := fun b => ∀ r : b.Reflects c, motive ⟨b, r⟩) d.decide isFalse isTrue
    d.reflects_decide

"

/-- The 4.35.0 certificate variant, from `Certs.lean`: in 4.35.0 `Decidable` is
a structure (`decide : Bool` with a proof that it reflects the proposition), so
`Decidable.casesOn` takes one case, not two. The variant adds `decCases`, a
two-case eliminator in the old argument order, and uses it wherever `Certs.lean`
uses `Decidable.casesOn`. `decCases` cases on the instance's `decide` field with
`Bool.casesOn`, as 4.35.0's `dite` does, rather than through `Decidable`'s
recursor (`Decidable.falseTrueCases`): the role binding closes each certificate
over its operation's dependency closure, which holds `Decidable`'s projections
and constructor but not its recursor. The theorems' statements are unchanged. -/
def certificateVariant (certs : String) : String :=
  let anchor := "/-- `dite` at a true condition. -/"
  let withHelper := certs.replace anchor (certificateHelper ++ anchor)
  withHelper.replace "Decidable.casesOn (motive" "decCases (motive"

def regenerate (work : System.FilePath) (t : Toolchain) : IO Unit := do
  let repo ← IO.currentDir
  let v := t.version
  let sysroot := work / s!"lean-{v}-linux"
  let bin := sysroot / "bin"
  unless ← (bin / "lean").pathExists do
    let tarball := work / s!"lean-{v}-linux.tar.zst"
    IO.println s!"[{v}] fetching the release"
    let _ ← run "curl" #["-sSfL", "-o", tarball.toString,
      s!"https://github.com/leanprover/lean4/releases/download/v{v}/lean-{v}-linux.tar.zst"]
    let _ ← run "tar" #["--use-compress-program=zstd", "-xf", tarball.toString, "-C", work.toString]
  let path := s!"{bin}:{(← IO.getEnv "PATH").getD ""}"
  -- The exporter, at its pinned commit, built with this toolchain.
  let exporter := work / s!"lean4export-{v}"
  unless ← exporter.pathExists do
    let _ ← run "git" #["clone", "--quiet", "https://github.com/leanprover/lean4export",
      exporter.toString]
  let _ ← run "git" #["-C", exporter.toString, "checkout", "--quiet", "--force", t.exporterCommit]
  patchExporter exporter
  IO.FS.writeFile (exporter / "lean-toolchain") s!"leanprover/lean4:v{v}\n"
  IO.println s!"[{v}] building lean4export {t.exporterTag}"
  let _ ← run "lake" #["build", "--wfail", "lean4export"] (cwd := exporter) (env := #[("PATH", some path)])
  -- The certificate theorems and the literal facts, under ix's module names.
  let src := work / s!"src-{v}"
  let olean := work / s!"olean-{v}"
  let modules : List (System.FilePath × System.FilePath) := [
    (t.certificates, "IxC/Kernel/PinGen/Certs.lean"),
    (fixtureDir / "Primitives.lean", "Tests/Fixtures/toolchains/Primitives.lean")]
  for (from_, to) in modules do
    IO.FS.createDirAll ((src / to).parent.get!)
    IO.FS.createDirAll ((olean / to).parent.get!)
    IO.FS.writeFile (src / to) (← IO.FS.readFile (repo / from_))
    IO.println s!"[{v}] compiling {from_}"
    let _ ← run (bin / "lean").toString #["-E", "warning", "--root=.", "-o", (olean / to.withExtension "olean").toString,
      to.toString] (cwd := src)
  -- The export.
  IO.println s!"[{v}] exporting {roots.length} roots"
  let out ← IO.Process.output {
    cmd := (exporter / ".lake" / "build" / "bin" / "lean4export").toString
    args := #["--export-mdata", "--export-unsafe", "Init", "IxC.Kernel.PinGen.Certs",
      "Tests.Fixtures.toolchains.Primitives", "--"] ++ roots.toArray
    env := #[("LEAN_PATH", some s!"{olean}:{sysroot}/lib/lean")] }
  if out.exitCode != 0 || (out.stderr.splitOn "PANIC").length > 1 then
    throw (IO.userError s!"[{v}] lean4export exited {out.exitCode}:\n{out.stderr}")
  let raw := work / s!"lean-{v}.ndjson"
  IO.FS.writeFile raw out.stdout
  let fixture := repo / fixtureDir / s!"lean-{v}.ndjson.zst"
  let _ ← run "zstd" #["-19", "-q", "-f", raw.toString, "-o", fixture.toString]
  IO.println s!"[{v}] wrote {fixture}: {out.stdout.utf8ByteSize} bytes before compression"

def main (args : List String) : IO UInt32 := do
  let some work := args.head? | do
    IO.eprintln "usage: lean --run Tests/Fixtures/toolchains/Regenerate.lean <work dir> [<version>…]"
    return 2
  let variant := certificateVariant (← IO.FS.readFile "IxC/Kernel/PinGen/Certs.lean")
  unless variant == (← IO.FS.readFile (fixtureDir / "Certs-4.35.0.lean")) do
    IO.eprintln "Certs-4.35.0.lean is not Certs.lean under `certificateVariant`: rewrite it from Certs.lean"
    return 1
  let work ← do IO.FS.createDirAll work; IO.FS.realPath work
  let wanted := args.tail
  for t in toolchains do
    if wanted.isEmpty || wanted.contains t.version then regenerate work t
  return 0
