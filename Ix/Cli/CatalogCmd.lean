/-
  `ix catalog`: build a qualified multi-library union environment (an
  `Ix.Catalog` catalog) and compile it to one `.ixe` through the
  ordinary fail-closed pipeline. Member libraries are given as
  positional `Qualifier=Root[,Root...]` specs in dependency order;
  every constant owned by member `X` lands as `<prefix>.<X>.<name>`.
-/
module

public import Cli
public import Ix.Common
public import Ix.Meta
public import Ix.CompileM
public import Ix.Catalog

public section

open System (FilePath)

namespace Ix.Cli.CatalogCmd

private def parseLibSpec (raw : String) : Except String Ix.Catalog.LibSpec := do
  match raw.splitOn "=" with
  | [qualifier, roots] =>
    if qualifier.isEmpty then throw s!"empty qualifier in `{raw}`"
    let rootNames := (roots.splitOn ",").filterMap fun r =>
      let r := r.trimAscii.toString
      if r.isEmpty then none else some r.toName
    if rootNames.isEmpty then throw s!"no root modules in `{raw}`"
    return { qualifier := qualifier.toName, roots := rootNames.toArray }
  | _ => throw s!"expected `Qualifier=Root[,Root...]`, got `{raw}`"

def runCatalogCmd (p : Cli.Parsed) : IO UInt32 := do
  let some prefixFlag := p.flag? "prefix"
    | p.printError "error: --prefix is required (the catalog namespace, e.g. `MyCatalog`)"
      return 1
  let catalogPrefix := (prefixFlag.as! String).toName
  let rawLibs := (p.variableArgsAs! String).toList
  if rawLibs.isEmpty then
    p.printError "error: at least one `Qualifier=Root[,Root...]` library spec is required"
    return 1
  let mut libs : Array Ix.Catalog.LibSpec := #[]
  for raw in rawLibs do
    match parseLibSpec raw with
    | .ok lib => libs := libs.push lib
    | .error e =>
      p.printError s!"error: {e}"
      return 1
  let spec : Ix.Catalog.CatalogSpec := { catalogPrefix, libs }
  let outPath := (p.flag? "out").map (·.as! String)
    |>.getD (s!"{catalogPrefix}".toLower ++ ".ixe")

  -- Resolve modules through the current directory's Lake workspace.
  initLeanSearchPath (some (← IO.currentDir))

  println! "Building catalog {catalogPrefix} from {libs.size} librar(ies)..."
  let buildStart ← IO.monoMsNow
  let result ← Ix.Catalog.buildCatalog spec
  let buildElapsed := (← IO.monoMsNow) - buildStart
  for (qualifier, count) in result.perLib do
    println! "[catalog] {qualifier}: {count} owned constants"
  println! "[catalog] replayed {result.replayed} declarations; \
{result.consts.size} constants total in {buildElapsed}ms"

  if p.hasFlag "audit" then
    let auditStart ← IO.monoMsNow
    let audit ← Ix.Catalog.auditCatalog spec result.consts
    let auditElapsed := (← IO.monoMsNow) - auditStart
    if audit.violations.isEmpty then
      println! "[audit] anon-address preservation: {audit.checked} owned \
constants verified in {auditElapsed}ms"
    else
      let stderr ← IO.getStderr
      stderr.putStrLn s!"error: catalog audit found \
{audit.violations.size} anon-address violation(s) \
({audit.checked} checked); nothing written to {outPath}"
      for v in audit.violations.toList.take 20 do
        stderr.putStrLn s!"  [audit] {v}"
      if audit.violations.size > 20 then
        stderr.putStrLn s!"  … and {audit.violations.size - 20} more"
      return 1

  let allowPartial := p.hasFlag "allow-partial"
  let start ← IO.monoMsNow
  let status ← Ix.CompileM.rsCompileEnvBytesFFI result.consts.toList outPath
    allowPartial
  let size := status.bytes.toNat
  let elapsed := (← IO.monoMsNow) - start

  let ungroundedCount := status.ungrounded.size
  let failClosed := !allowPartial && ungroundedCount > 0

  if let some flag := p.flag? "report" then
    let report := Lean.Json.mkObj
      [ ("schemaVersion", Lean.toJson (1 : Nat))
      , ("ixVersion", Lean.Json.str Ix.versionString)
      , ("leanToolchain", Lean.Json.str Lean.versionString)
      , ("ixeFormatVersion", Lean.toJson Ixon.Env.VERSION.toNat)
      , ("catalogPrefix", Lean.Json.str s!"{catalogPrefix}")
      , ("libs", Lean.Json.arr <| libs.map fun lib => Lean.Json.mkObj
          [ ("qualifier", Lean.Json.str s!"{lib.qualifier}")
          , ("roots", Lean.Json.arr <|
              lib.roots.map (Lean.Json.str s!"{·}")) ])
      , ("output", Lean.Json.str outPath)
      , ("requested", Lean.toJson result.consts.size)
      , ("replayed", Lean.toJson result.replayed)
      , ("named", Lean.toJson status.named.toNat)
      , ("uniqueAnon", Lean.toJson status.uniqueAnon.toNat)
      , ("ungroundedCount", Lean.toJson ungroundedCount)
      , ("ungrounded", Lean.Json.arr <| status.ungrounded.map fun (n, r) =>
          Lean.Json.mkObj
            [("name", Lean.Json.str n), ("reason", Lean.Json.str r)])
      , ("root", Lean.Json.str status.root)
      , ("allowPartial", Lean.toJson allowPartial)
      , ("written", Lean.toJson (!failClosed))
      , ("bytes", Lean.toJson size)
      , ("buildMs", Lean.toJson buildElapsed)
      , ("compileMs", Lean.toJson elapsed) ]
    IO.FS.writeFile (flag.as! String) (report.pretty ++ "\n")

  if ungroundedCount > 0 then
    let stream ← if failClosed then IO.getStderr else IO.getStdout
    let verdict := if failClosed then
      s!"error: {ungroundedCount} catalog constant(s) failed to compile; \
nothing written to {outPath} (use --allow-partial to serialize the \
grounded subset)"
    else
      s!"PARTIAL: {ungroundedCount} catalog constant(s) failed to compile; \
serialized the grounded subset ({status.named} named, \
{status.uniqueAnon} unique constants)"
    stream.putStrLn verdict
    for (n, r) in status.ungrounded.toList.take 10 do
      stream.putStrLn s!"  [ungrounded] {n}: {(r.replace "\n" " ").take 200}"
    if ungroundedCount > 10 then
      stream.putStrLn s!"  … and {ungroundedCount - 10} more (see --report for the full list)"
    if failClosed then
      return 1

  println! "Compiled and wrote {size} bytes to {outPath} in {elapsed}ms \
(root {status.root.take 12}…)"
  return 0

end Ix.Cli.CatalogCmd

open Ix.Cli.CatalogCmd in
def catalogCmd : Cli.Cmd := `[Cli|
  catalog VIA runCatalogCmd;
  "Build a qualified multi-library union environment (a catalog) and compile it to one .ixe. Member constants land under <prefix>.<qualifier>.<source name>; the toolchain base stays unqualified. Kernel-level: instances, attributes, and native code do not transfer."

  FLAGS:
    "prefix"        : String; "The catalog namespace, e.g. `MyCatalog` (required)."
    out             : String; "Output path for the serialized .ixe; defaults to the lowercased prefix with `.ixe`."
    "allow-partial" ;         "Serialize the grounded subset and exit 0 even when some catalog constants fail to compile. Default is fail-closed: any ungrounded constant means a nonzero exit and NO output file."
    audit           ;         "Verify anon-address preservation before writing: recompile each member library standalone and require addr(<prefix>.<qualifier>.N) in the catalog to equal addr(N) standalone, for every owned constant (qualification is metadata-only). N+1 extra compiles; violations abort with no output file."
    report          : String; "Write a machine-readable JSON catalog report (versions, lib specs, counts, ungrounded list, canonical root) to this path — written on success, fail-closed abort, and partial publish alike."

  ARGS:
    ...libs : String; "Member library specs `Qualifier=Root[,Root...]` in dependency order (dependencies first), e.g. `Batteries=Batteries HaskellSpec=HaskellSpec`."
]
