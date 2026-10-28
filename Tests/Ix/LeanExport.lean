/-
  The `lean4export` bridge (`Ix.LeanExport`, `ix compile-export`).

  - **The reader** accepts a well-formed export and refuses malformed ones:
    another format version, a missing or misplaced `meta` record, an index out
    of sequence or not yet defined, missing or extra fields, a name declared
    twice, a metadata value or numeral that does not read back.
  - **Fidelity on ix's own toolchain.** The committed 4.34.1 fixture
    (`Tests/Fixtures/toolchains/lean-4.34.1.ndjson.zst`) is the export of the
    roles, the certificate theorems, a few library theorems and the literal
    facts (`Tests/Fixtures/toolchains/Primitives.lean`). Its declarations equal
    the native ones of this toolchain up to binder names, binder info and
    `mdata`, which an export does not keep. Compiling the export, role binding
    included, gives exactly the content of the native compile of the same
    declarations: every name, address, constant and the binding. Metadata
    differences are reported.

  The fixture is decompressed with the `zstd` command.
-/
module

public import LSpec
public import Ix.LeanExport
public import Ix.LeanExport.Compare
public import Ix.RoleBinding.Compile
public import Ix.Meta
public import Tests.Fixtures.toolchains.Primitives

public section

namespace Tests.Ix.LeanExport

open _root_.Ix.LeanExport (importString environment)

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-! ## The reader -/

private def metaLine (format := "3.1.0") : String :=
  "{\"meta\":{\"exporter\":{\"name\":\"lean4export\",\"version\":\"3.1.0\"},\"format\":{\"version\":\"" ++
    format ++ "\"},\"lean\":{\"githash\":\"0\",\"version\":\"4.34.1\"}}}"

/-- `axiom T : Sort 1`, with whatever lines are spliced in before the declaration. -/
private def export_ (extra : List String := []) (decl : String :=
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}") : String :=
  "\n".intercalate ([metaLine, "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"T\"}}",
    "{\"il\":1,\"succ\":0}", "{\"ie\":0,\"sort\":1}"] ++ extra ++ [decl])

private def accepts (text : String) : Bool := (importString text).isOk
private def refuses (text : String) : Bool := !(importString text).isOk

/-- An `mdata` around expression 0 with the given data object, as expression 1,
and an axiom of that type. -/
private def withMData (data : String) : String :=
  export_ ["{\"ie\":1,\"mdata\":{\"data\":" ++ data ++ ",\"expr\":0}}"]
    "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}"

def readerTests : LSpec.TestSeq :=
  let dropped (text : String) : Option Nat := (importString text).toOption.map (·.droppedSyntaxMData)
  LSpec.test "a well-formed export is read" ((importString (export_ [])).toOption.any fun im =>
    im.constants.size == 1 && im.exportMeta.leanVersion == "4.34.1") ++
  LSpec.test "another format version is refused" (refuses ((export_ []).replace metaLine (metaLine "3.0.0"))) ++
  LSpec.test "an export without its meta record is refused"
    (refuses ("\n".intercalate ((export_ []).splitOn "\n" |>.drop 1))) ++
  LSpec.test "a second meta record is refused" (refuses (export_ [metaLine])) ++
  LSpec.test "a name index out of sequence is refused"
    (refuses (export_ ["{\"in\":3,\"str\":{\"pre\":0,\"str\":\"U\"}}"])) ++
  LSpec.test "a reference to an expression not yet defined is refused"
    (refuses (export_ [] "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":7}}")) ++
  LSpec.test "an extra field is refused"
    (refuses (export_ [] "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0,\"x\":1}}")) ++
  LSpec.test "a missing field is refused"
    (refuses (export_ [] "{\"axiom\":{\"levelParams\":[],\"name\":1,\"type\":0}}")) ++
  LSpec.test "a name declared twice is refused"
    (refuses (export_ ["{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"])) ++
  LSpec.test "an unknown record is refused" (refuses (export_ ["{\"universe\":0}"])) ++
  LSpec.test "an unknown binder info is refused"
    (refuses (export_ ["{\"ie\":1,\"lam\":{\"binderInfo\":\"auto\",\"body\":0,\"name\":1,\"type\":0}}"])) ++
  LSpec.test "a canonical numeral is read"
    (accepts (export_ ["{\"ie\":1,\"natVal\":\"120\"}"])) ++
  LSpec.test "a numeral that is not canonical is refused"
    (refuses (export_ ["{\"ie\":1,\"natVal\":\"0120\"}"])) ++
  LSpec.test "a metadata value that reads back is kept"
    (dropped (withMData "{\"noImplicitLambda\":\"Lean.DataValue.ofBool true\"}") == some 0) ++
  LSpec.test "a name-valued metadata entry is kept"
    (dropped (withMData "{\"k\":\"Lean.DataValue.ofName `Nat.add\"}") == some 0) ++
  LSpec.test "a name written in constructor form is kept"
    (dropped (withMData ("{\"k\":" ++ (Lean.Json.str (reprStr (Lean.DataValue.ofName
      (.num (.str (.num `h 4) "_hyg") 17)))).compress ++ "}")) == some 0) ++
  LSpec.test "a syntax-valued metadata entry is dropped and counted"
    (dropped (withMData "{\"_recApp\":\"Lean.DataValue.ofSyntax\\n  (Lean.Syntax.missing)\"}") == some 1) ++
  LSpec.test "a metadata value that does not read back is refused"
    (refuses (withMData "{\"k\":\"Lean.DataValue.ofBool maybe\"}")) ++
  LSpec.test "a metadata value in another form is refused"
    (refuses (withMData "{\"k\":\"Lean.DataValue.ofNat  3\"}"))

/-! ## Fidelity on ix's own toolchain -/

def fixtureDir : System.FilePath := "Tests/Fixtures/toolchains"

/-- A committed fixture, decompressed. -/
def readFixture (version : String) : IO String := do
  let path := fixtureDir / s!"lean-{version}.ndjson.zst"
  let out ← IO.Process.output { cmd := "zstd", args := #["-dc", "-q", path.toString] }
  unless out.exitCode == 0 do throw (IO.userError s!"zstd -dc {path}: {out.stderr}")
  return out.stdout

/-- Remove every `mdata` node. -/
partial def stripMData (e : Lean.Expr) : Lean.Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

/-- The declaration with its expressions' `mdata` removed. -/
def stripDeclaration : Lean.ConstantInfo → Lean.ConstantInfo
  | .axiomInfo v => .axiomInfo { v with type := stripMData v.type }
  | .defnInfo v => .defnInfo { v with type := stripMData v.type, value := stripMData v.value }
  | .thmInfo v => .thmInfo { v with type := stripMData v.type, value := stripMData v.value }
  | .opaqueInfo v => .opaqueInfo { v with type := stripMData v.type, value := stripMData v.value }
  | .quotInfo v => .quotInfo { v with type := stripMData v.type }
  | .inductInfo v => .inductInfo { v with type := stripMData v.type }
  | .ctorInfo v => .ctorInfo { v with type := stripMData v.type }
  | .recInfo v => .recInfo { v with
      type := stripMData v.type
      rules := v.rules.map fun r => { r with rhs := stripMData r.rhs } }

/-- Equal as declarations up to binder names, binder info (Lean's `BEq Expr`)
and `mdata`. -/
def sameDeclaration (a b : Lean.ConstantInfo) : Bool :=
  match stripDeclaration a, stripDeclaration b with
  | .axiomInfo x, .axiomInfo y => x == y
  | .defnInfo x, .defnInfo y => x == y
  | .thmInfo x, .thmInfo y => x == y
  | .opaqueInfo x, .opaqueInfo y => x == y
  | .quotInfo x, .quotInfo y => x == y
  | .inductInfo x, .inductInfo y => x == y
  | .ctorInfo x, .ctorInfo y => x == y
  | .recInfo x, .recInfo y => x == y
  | _, _ => false

/-- Whether two declarations' expressions are equal with their binder names and
binder info (`Expr.equal`), `mdata` removed. -/
def sameBinders (a b : Lean.ConstantInfo) : Bool :=
  let exprs (c : Lean.ConstantInfo) : List Lean.Expr :=
    let c := stripDeclaration c
    [c.type] ++ (c.value? (allowOpaque := true)).toList ++
      (match c with | .recInfo v => v.rules.map (·.rhs) | _ => [])
  (exprs a).length == (exprs b).length && ((exprs a).zip (exprs b)).all fun (x, y) => x.equal y

/-- Compile an environment's declarations and add the role binding, with the
certificate theorems from the same environment. -/
def compileBound (env : Lean.Environment) : IO Ixon.Env := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env env.constants.toList).mapError toString)
  let out ← IO.ofExcept (← Ix.CompileM.compileLeanInputValidated input (numWorkers := 8))
  require out.cenv.ungrounded.isEmpty
    s!"{out.cenv.ungrounded.size} constants failed to compile"
  Ix.RoleBinding.Compile.finalize (Ix.RoleBinding.Compile.leanBackend 8 {}) env (pure env) input
    out.env Ix.Resource.typingLimits

def fidelity : IO (Bool × Nat × Nat × Option String) := do
  let exported ← IO.ofExcept (importString (← readFixture Lean.versionString))
  require (exported.exportMeta.leanVersion == Lean.versionString)
    s!"the fixture comes from Lean {exported.exportMeta.leanVersion}, the test runs on {Lean.versionString}"
  let native ← getCompileEnv #[`IxC.Kernel.PinGen.Certs, `Tests.Fixtures.toolchains.Primitives]
  let mut nativeDecls : Array (Lean.Name × Lean.ConstantInfo) := #[]
  let mut binderDiffs := 0
  for (name, ci) in exported.constants do
    let some nci := native.find? name
      | throw (IO.userError s!"{name} is exported but not in the native environment")
    require (sameDeclaration ci nci) s!"{name}: the exported declaration differs from the native one"
    unless sameBinders ci nci do binderDiffs := binderDiffs + 1
    nativeDecls := nativeDecls.push (name, nci)
  let fromNative ← compileBound (← environment nativeDecls)
  let fromExport ← compileBound (← environment exported.constants)
  let c := _root_.Ix.LeanExport.compare fromNative fromExport
  let report := c.report fromNative fromExport
  IO.println s!"[lean-export] {exported.constants.size} declarations; {binderDiffs} differ from the \
native ones in binder names or info; {exported.droppedSyntaxMData} syntax-valued metadata entries dropped"
  for line in report do IO.println s!"[lean-export]   {line}"
  require fromNative.roleBinding.isSome "the native compile has no role binding"
  require c.contentExact s!"the export's compile differs in content: {report}"
  return (true, 0, 0, none)

def suite : List LSpec.TestSeq := [
  readerTests,
  .individualIO "a 4.34.1 export compiles to exactly the native content, role binding included" none
    fidelity .done]

end Tests.Ix.LeanExport

end
