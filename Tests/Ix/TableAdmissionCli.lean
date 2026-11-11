import Tests.Ix.RoleGeneration
import Ix.Cli.TableAdmissionKernel
import Ix.Claim
import Ix.Store

/-! # The kernel's admission of a claim's role table, at the consumer

Two runners.

`table-admission-cli` (`cli`): `ix verify` through the `ix` binary, in a
temporary `HOME`, on a claim under a role table other than the default one: the
table of a generated artifact (`Tests.Ix.RoleGeneration.completeArtifact`),
which the kernel admits over the artifact's own records. The claim's wrapper
carries no proof, and the artifact path names no file: the admission runs before
verification, so each case is decided by whether the claim was refused, and an
admitted one then fails at verification only.
* with no environment supplied, the claim is refused, naming `--binding-env`;
* with an environment that lacks one of the table's evidence theorems, refused,
  naming the record;
* with the artifact as `--binding-env`, admitted by the kernel;
* then with no environment, admitted from the record the previous run wrote;
* a table that also binds `String`, without the rest of a string literal's
  support, refused at that stage.

`table-admission-fixtures` (`fixtures`, manual): every role-bound `.ixe` under
`$IX_TABLE_FIXTURES`, each table checked over its own artifact's records, with
the time of each check, the stage that refuses one, the records the table's
seeds name that the artifact lacks, and whether the table is a restriction of
the default table (each bound role at the address the default table binds). -/

namespace Tests.Ix.TableAdmissionCli

open Ix.Kernel (Role RoleTable)

/-- `bytes` stored at their address in the store under `home`, as `Store.write`
stores them there. -/
def storeUnder (home : System.FilePath) (bytes : ByteArray) : IO Address := do
  let addr := Address.admissionHash bytes
  let s := (hexOfBytes addr.hash).toSlice
  let dir := home / ".ix" / "store" / (s.take 2).toString / (s.drop 2 |>.take 2).toString /
    (s.drop 4 |>.take 2).toString
  IO.FS.createDirAll dir
  IO.FS.writeBinFile (dir / (s.drop 6).toString) bytes
  return addr

/-- Whether `text` occurs in `s`. -/
def mentions (s text : String) : Bool := (s.splitOn text).length > 1

/-- The theorems a table's evidence names. -/
def proofsOf (t : RoleTable) : List Address :=
  t.evidence.toList.flatMap fun (_, es) => es.toList.filterMap fun
    | .proof a => some a
    | .defeq => none

def cli : IO UInt32 := do
  let ix ← IO.FS.realPath ".lake/build/bin/ix"
  let (artifact, _) ← IO.ofExcept (Tests.Ix.RoleGeneration.completeArtifact .natDiv)
  let some rb := artifact.roleBinding | throw (IO.userError "the artifact carries no role table")
  let some t := RoleTable.ofBytes rb.bytes | throw (IO.userError "the artifact's table does not decode")
  let defaultTable ← IO.ofExcept Ix.Kernel.Reader.defaultTableAddress
  let failures ← IO.mkRef (#[] : Array String)
  if rb.address == defaultTable then failures.modify (·.push "the artifact's table is the default one")
  let b : Ix.Kernel.Admission.Binding := ⟨rb.address, rb.bytes⟩
  -- the kernel admits the table over the artifact's records, in this process
  let t0 ← IO.monoMsNow
  let admitted ← IO.lazyPure fun _ => Ix.Cert.TableAdmission.check b artifact
  IO.println s!"[table-admission-cli] the kernel's admission of {rb.address}: {admitted} \
    ({(← IO.monoMsNow) - t0} ms)"
  unless admitted do
    failures.modify (·.push s!"the kernel refuses the artifact's table: \
      {Ix.Cli.TableAdmissionKernel.explain b artifact}")
  let some thm := (proofsOf t).head? | throw (IO.userError "the table's evidence names no theorem")
  let stripped := { artifact with consts := artifact.consts.erase thm }
  let dir ← IO.FS.createTempDir
  try
    let home := dir / "home"
    let full := dir / "artifact.ixe"
    let lacking := dir / "lacking.ixe"
    IO.FS.writeBinFile full (← IO.ofExcept (Ixon.serEnv artifact))
    IO.FS.writeBinFile lacking (← IO.ofExcept (Ixon.serEnv stripped))
    let spec ← IO.ofExcept Ix.SpecDigest.specDigest
    let some (_, target) := t.bound[0]? | throw (IO.userError "the table binds nothing")
    -- a stored wrapper with no proof, for a check claim under the table `table`
    let claimUnder (table : Address) : IO Address := do
      let claim : Ix.Claim := .check { spec, binding := table, axioms := none } target none
      storeUnder home (Ixon.Proof.ser { claim, proof := "no proof".toUTF8 })
    let addr ← claimUnder rb.address
    -- the artifact's table with String bound too, and nothing else of a literal's support
    let some lone := artifact.consts.toList.findSome? fun (a, _) =>
        if t.bound.any (·.2 == a) then none else some a
      | throw (IO.userError "every record of the artifact is bound")
    let loneTable := RoleTable.ofEntries t.version (t.bound.toList ++ [(Role.string, lone)])
      t.evidence.toList
    let loneBytes := loneTable.toBytes
    let loneAddr := Address.admissionHash loneBytes
    let loneEnv := dir / "lone-string.ixe"
    IO.FS.writeBinFile loneEnv (← IO.ofExcept (Ixon.serEnv
      { artifact with roleBinding := some ⟨loneAddr, loneBytes⟩ }))
    let loneClaim ← claimUnder loneAddr
    let verifyAt (proof : Address) (extra : Array String) : IO String := do
      let out ← IO.Process.output {
        cmd := ix.toString
        args := #["verify", toString proof, "--aiur-artifact", (dir / "absent.ixa").toString] ++ extra
        env := #[("HOME", some home.toString)] }
      return out.stdout ++ out.stderr
    let verify := verifyAt addr
    let check (label : String) (ok : Bool) (out : String) : IO Unit := do
      IO.println s!"[table-admission-cli] {if ok then "ok" else "FAILED"}: {label}"
      unless ok do
        IO.eprintln out
        failures.modify (·.push label)
    let o1 ← verify #[]
    check "no environment supplied: refused, naming --binding-env"
      (mentions o1 "refused:" && mentions o1 "--binding-env") o1
    let o2 ← verify #["--binding-env", lacking.toString]
    check "an environment lacking an evidence theorem: refused, naming it"
      (mentions o2 "refused:" && mentions o2 (toString thm)) o2
    let o3 ← verify #["--binding-env", full.toString]
    check "the artifact's own records: admitted by the kernel"
      (!mentions o3 "refused:" && mentions o3 "admitted by the kernel") o3
    let o4 ← verify #[]
    check "then with no environment: admitted from the record"
      (!mentions o4 "refused:" && mentions o4 "recorded by an earlier run") o4
    let o5 ← verifyAt loneClaim #["--binding-env", loneEnv.toString]
    check "a table binding String without a literal's support: refused, saying so"
      (mentions o5 "refused:" && mentions o5 "binds String without") o5
  finally
    IO.FS.removeDirAll dir
  let failed ← failures.get
  for f in failed do IO.eprintln s!"[table-admission-cli] {f}"
  return if failed.isEmpty then 0 else 1

/-- Every `.ixe` under `dir`, in path order. -/
partial def ixeFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← ixeFiles e.path)
    else if e.path.extension == some "ixe" then out := out.push e.path
  return out.qsort (·.toString < ·.toString)

/-- One role-bound artifact of the survey: its file, records, original table address,
the decoded table, and the binding it is checked under. -/
structure Entry where
  file : String
  env : Ixon.Env
  table : Address
  decoded : RoleTable
  binding : Ix.Kernel.Admission.Binding

/-- The survey's line for `e`: the check's verdict over the artifact's own records, its
time, and, for a refusal, the refusing stage. -/
def survey (defaultTable : RoleTable) (e : Entry) : IO (Bool × String) := do
  let t := e.decoded
  let restriction := t.bound.all fun (r, a) => defaultTable.addressOf? r == some a
  let missing := (Ix.Cert.TableAdmission.seedList t).filter (!e.env.consts.contains ·)
  let t0 ← IO.monoMsNow
  let admitted ← IO.lazyPure fun _ => Ix.Cert.TableAdmission.check e.binding e.env
  let ms := (← IO.monoMsNow) - t0
  let why := if admitted then "" else Ix.Cli.TableAdmissionKernel.explain e.binding e.env
  return (admitted, s!"FIXTURE {e.file}: table {e.table} checked-as {e.binding.address} \
    version={t.version} roles={t.bound.size} evidence={(proofsOf t).length} \
    records={e.env.consts.size} restriction={restriction} admitted={admitted} ms={ms} \
    missing-seeds={missing.length}{if missing.isEmpty then "" else s!" {missing.take 8}"}\
    {if admitted then "" else s!" why: {why}"}")

/-- The survey. With `IX_TABLE_FIXTURES_REVERSION` set, each table is checked
re-encoded at this build's specification version, the same bindings and evidence
(a diagnostic: another table, at another address), so that a table made for an
earlier version shows what the rest of the admission makes of its artifact's records.
The first artifact of each table is checked alone and timed; the others in parallel. -/
def fixtures : IO UInt32 := do
  let some root ← IO.getEnv "IX_TABLE_FIXTURES"
    | IO.eprintln "[table-admission-fixtures] set IX_TABLE_FIXTURES to a directory of .ixe files"
      return 2
  let reversion := (← IO.getEnv "IX_TABLE_FIXTURES_REVERSION").isSome
  let defaultTable ← IO.ofExcept Ix.Kernel.Reader.defaultTable
  let files ← ixeFiles root
  let mut entries : Array Entry := #[]
  let mut unbound := 0
  for f in files do
    let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile f) with
      | .ok env => pure env
      | .error e => IO.println s!"FIXTURE {f}: does not decode: {e}"; continue
    if env.roleBinding.isNone then
      unbound := unbound + 1
      IO.println s!"FIXTURE {f}: no role table"
      continue
    let some rb := env.roleBinding | continue
    let some t := RoleTable.ofBytes rb.bytes
      | IO.println s!"FIXTURE {f}: table {rb.address} does not decode"; continue
    let (binding, env) :=
      if reversion then
        let bytes := ({ t with version := Ix.Kernel.specVersion } : RoleTable).toBytes
        let a := Address.admissionHash bytes
        ((⟨a, bytes⟩ : Ix.Kernel.Admission.Binding), { env with roleBinding := some ⟨a, bytes⟩ })
      else ((⟨rb.address, rb.bytes⟩ : Ix.Kernel.Admission.Binding), env)
    entries := entries.push { file := f.toString, env, table := rb.address, decoded := t, binding }
  let mut seen : Std.HashSet Address := {}
  let mut firsts : Array Entry := #[]
  let mut rest : Array Entry := #[]
  for e in entries do
    if seen.contains e.table then rest := rest.push e
    else
      seen := seen.insert e.table
      firsts := firsts.push e
  let mut refused := 0
  let t0 ← IO.monoMsNow
  for e in firsts do
    let (ok, line) ← survey defaultTable e
    unless ok do refused := refused + 1
    IO.println line
  let sequential := (← IO.monoMsNow) - t0
  let tasks ← rest.mapM fun e => IO.asTask (prio := .dedicated) (survey defaultTable e)
  for task in tasks do
    let (ok, line) ← IO.ofExcept (← IO.wait task)
    unless ok do refused := refused + 1
    IO.println line
  IO.println s!"[table-admission-fixtures] {files.size} files, {seen.size} tables, \
    {unbound} without a table, {refused} refused; the first artifact of each table checked \
    alone in {sequential} ms{if reversion then " (tables re-encoded at this specification version)" else ""}"
  return 0

end Tests.Ix.TableAdmissionCli
