/-
  The kernel's admission of a claim's role table, run by the consumer.

  `IxVM.consistent` covers a typing claim under the default role table, or under
  a role table the kernel admits (`TableAdmitted`): its section is
  authenticated, canonical and well formed, its prelude roles are the committed
  records, and the kernel's strict check accepts the closure of the constants it
  binds (all but the compiler-trust roles) and the theorems its evidence names,
  each constant meeting its role's specification. The circuit does not
  establish that premise for a table other than the default one; `ix verify` and
  `ix compress` do, before they accept a claim under it
  (`Ix.Cli.ClaimPolicy.admit`), by running the kernel's executable admission
  (`Ix.Cert.TableAdmission.check`, whose `true` establishes `TableAdmitted` for
  a view holding the records) over records the user supplies:

  * the `.ixe` named by `--ixe`, when its role binding is the claim's table;
  * the `.ixe` named by `--binding-env`: an environment whose role binding is
    the claim's table, holding the records the table binds, the theorems its
    evidence names and their closures (an `ix compile` output carries them);
  * for a catalog, each member's own piece (`<label>.ixe`).

  The environment must hold every record the closure reads, the recursor
  records of its inductive blocks included: the admission reads only the
  supplied records (and the committed prelude), and draws in nothing.

  The check lives outside the module system (`Ix.Cert.TableAdmission` imports
  the refinement's statement), so the command line receives it at startup
  (`install`, called by the `ix` executable's `Main` through
  `Ix.Cli.TableAdmissionKernel`); a program that installs none admits no table
  other than the default one.

  A table the kernel admits is recorded under
  `~/.ix/cache/table-admission/<spec digest>/<table address>`, so the kernel
  runs once per table and specification set. The entry is the local user's own
  record, read as the shard-proof index is read: a record this user's earlier
  run wrote, not evidence a proof carries.

  The admission is not established, and `Ix.Cli.ClaimPolicy` refuses the claim
  unless `--allow-custom-binding` accepts it, when the claim is relative to a
  literal class rather than a table, names another specification set than this
  build's, no supplied environment carries its table, this build has no
  executable admission, or the kernel does not admit the table.
-/
module
public import Cli
public import Ix.Claim
public import Ix.Ixon
public import Ix.Store
public import Ix.SpecDigest
public import IxC.Kernel.Admission

public section

namespace Ix.Cli.TableAdmission

/-- **The kernel's executable admission of a role table** over the records of an
environment: `check`, whose `true` establishes the statement's premise
(`TableAdmitted`) for that table, and `explain`, the first stage that refuses
(read only when `check` refused; it reruns the stages). -/
structure Checker where
  check : Ix.Kernel.Admission.Binding → Ixon.Env → Bool
  explain : Ix.Kernel.Admission.Binding → Ixon.Env → String

/-- The checker this program runs, installed at startup (`install`); `none` until
then, when every table other than the default one is refused. -/
initialize checkerRef : IO.Ref (Option Checker) ← IO.mkRef none

/-- Install the checker this program runs. -/
def install (c : Checker) : IO Unit := checkerRef.set (some c)

/-- The admission run whose answers the cache holds. Change it whenever the
checker's answers may change, so that older entries are no longer read. -/
def checkerVersion : String := "table-admission/1"

/-- The flag naming an `.ixe` that supplies a table and its records. -/
def envFlag : String := "binding-env"

/-! ## The cache -/

/-- The cache's root: `~/.ix/cache/table-admission`, or a hermetic root for
tests. Nothing is created here. -/
def cacheRoot (root? : Option System.FilePath := none) : IO System.FilePath := do
  match root? with
  | some root => pure root
  | none => return (← StoreIO.toIO Store.getHomeDir) / ".ix" / "cache" / "table-admission"

/-- Whether the table `binding` is recorded as admitted under `spec` by this
checker version. A missing or unreadable entry is a miss; reading creates
nothing. -/
def cached (root : System.FilePath) (spec binding : Address) : IO Bool := do
  let path := root / toString spec / toString binding
  if !(← path.pathExists) then return false
  try
    return (← IO.FS.readFile path).trimAscii.toString == checkerVersion
  catch _ => return false

/-- Record the table `binding` as admitted under `spec`. The temporary name
carries the pid, so concurrent writers never share it. -/
def record (root : System.FilePath) (spec binding : Address) : IO Unit := do
  let dir := root / toString spec
  IO.FS.createDirAll dir
  let pid ← IO.Process.getPID
  let tmp := dir / s!"{binding}.tmp.{pid}"
  IO.FS.writeFile tmp s!"{checkerVersion}\n"
  IO.FS.rename tmp (dir / toString binding)

/-! ## The standing of a claim's table -/

/-- An environment read from an `.ixe` file, as it was compiled. -/
def readEnv (path : String) : IO Ixon.Env := do
  match Ixon.deEnvAnon (← IO.FS.readBinFile path) with
  | .ok env => pure env
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- `envs`, then the environment `--binding-env` names, if any. -/
def withSupplied (p : Cli.Parsed) (envs : IO (List Ixon.Env)) : IO (List Ixon.Env) := do
  let supplied ← match p.flag? envFlag with
    | some flag => pure [← readEnv (flag.as! String)]
    | none => pure []
  return (← envs) ++ supplied

/-- How a typing claim's table stands: the default table; admitted by the
kernel, now or by an earlier run (`recorded`); or not established, with the
reason. -/
inductive Standing where
  | default
  | admitted (recorded : Bool)
  | unestablished (why : String)

/-- The standing of the table in context `ctx`. `envs` are the environments
that may carry it (the first whose role binding is the claim's table is used);
they are read only when the table is neither the default one nor recorded. The
kernel runs at most once per table and specification set. `checker` is the
admission run (`checkerRef`'s, or a test's) and `root?` the cache's root
(`cacheRoot`). -/
def standing (ctx : Ix.ClaimContext) (envs : IO (List Ixon.Env)) (checker : Option Checker)
    (root? : Option System.FilePath := none) : IO Standing := do
  if ctx.literalClass then
    return .unestablished "a literal class names no role table the kernel could admit"
  let defaultTable ← IO.ofExcept Ix.Kernel.Reader.defaultTableAddress
  if ctx.binding == defaultTable then return .default
  let spec ← IO.ofExcept Ix.SpecDigest.specDigest
  unless ctx.spec == spec do
    return .unestablished s!"the claim names the specification set {ctx.spec}, and this build \
      admits role tables under {spec}"
  let root ← cacheRoot root?
  if (← cached root spec ctx.binding) then return .admitted true
  let some (env, rb) := (← envs).findSome? fun env =>
      env.roleBinding.bind fun rb => if rb.address == ctx.binding then some (env, rb) else none
    | return .unestablished s!"no supplied environment carries the role table; pass \
        --{envFlag} FILE.ixe (an environment whose role binding is the table, with the records it \
        binds, its evidence theorems and their closures, recursor records included) or the \
        claim's own --ixe"
  let some c := checker
    | return .unestablished "this program cannot run the kernel's admission of a role table"
  let b : Ix.Kernel.Admission.Binding := ⟨rb.address, rb.bytes⟩
  unless c.check b env do
    return .unestablished s!"the kernel does not admit the role table over the supplied \
      records: {c.explain b env}"
  record root spec ctx.binding
  return .admitted false

end Ix.Cli.TableAdmission

end
