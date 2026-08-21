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
public import Ix.Catalog.Lake
public import Ix.TracingTexray

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

/-- Resolve the catalog spec from either `--spec file.json` (parsed by
    `Ix.Catalog.specFromJson`) or the positional
    `Qualifier=Root[,Root...]` form with `--prefix`. The two forms are
    mutually exclusive; the spec file carries its own prefix. -/
private def resolveSpec (p : Cli.Parsed) :
    IO (Except String Ix.Catalog.CatalogSpec) := do
  let rawLibs := (p.variableArgsAs! String).toList
  match p.flag? "spec" with
  | some specFlag =>
    if !rawLibs.isEmpty then
      return .error "--spec is mutually exclusive with positional library specs"
    if (p.flag? "prefix").isSome then
      return .error "--spec files carry the prefix; drop --prefix"
    let path := specFlag.as! String
    let content ← try IO.FS.readFile path
      catch e => return .error s!"cannot read --spec file `{path}`: {e}"
    return do
      let json ← Lean.Json.parse content
        |>.mapError (s!"--spec `{path}`: invalid JSON: {·}")
      Ix.Catalog.specFromJson json |>.mapError (s!"--spec `{path}`: {·}")
  | none =>
    let some prefixFlag := p.flag? "prefix"
      | return .error "--prefix is required (the catalog namespace, e.g. \
`MyCatalog`) unless --spec is given"
    let catalogPrefix := (prefixFlag.as! String).toName
    if rawLibs.isEmpty then
      return .error "at least one `Qualifier=Root[,Root...]` library spec \
is required (or use --spec)"
    let mut libs : Array Ix.Catalog.LibSpec := #[]
    for raw in rawLibs do
      match parseLibSpec raw with
      | .ok lib => libs := libs.push lib
      | .error e => return .error e
    return .ok { catalogPrefix, libs }

def runCatalogCmd (p : Cli.Parsed) : IO UInt32 := do
  let mut spec ← match ← resolveSpec p with
    | .ok spec => pure spec
    | .error e =>
      p.printError s!"error: {e}"
      return 1

  -- --close-roots: extend every member's declared roots to the global
  -- cross-package source-import fixed point through the cwd's Lake
  -- workspace, and re-root at terminal modules. The I5 coverage gate in
  -- the loader stays as the fail-closed backstop.
  if p.hasFlag "close-roots" then
    let declaredRoots := spec.libs.map (·.roots.size) |>.foldl (·+·) 0
    let closed ← try
        Ix.Catalog.closeRoots (← Ix.Catalog.loadCurrentWorkspace) spec
      catch e =>
        p.printError s!"error: --close-roots: {e}"
        return 1
    let closedRoots := closed.libs.map (·.roots.size) |>.foldl (·+·) 0
    println! "[catalog] --close-roots: {declaredRoots} declared roots → \
{closedRoots} terminal roots across {closed.libs.size} members"
    spec := closed

  let catalogPrefix := spec.catalogPrefix
  let libs := spec.libs
  let outPath := (p.flag? "out").map (·.as! String)
    |>.getD (s!"{catalogPrefix}".toLower ++ ".ixe")

  -- --audit-only: validate the subset against the spec up front.
  let auditOnly? : Option (Array Lean.Name) ←
    match p.flag? "audit-only" with
    | none => pure none
    | some flag =>
      let quals := ((flag.as! String).splitOn ",").filterMap fun q =>
        let q := q.trimAscii.toString
        if q.isEmpty then none else some q.toName
      if quals.isEmpty then
        p.printError "error: --audit-only needs at least one qualifier"
        return 1
      for q in quals do
        unless spec.libs.any (·.qualifier == q) do
          p.printError s!"error: --audit-only qualifier `{q}` is not a \
member of the catalog spec"
          return 1
      pure (some quals.toArray)

  -- Copy-vs-share staging threshold (see `defaultCopyStageMaxOwned`);
  -- the corpus tier is where the default gets tuned.
  let copyStageMaxOwned := (p.flag? "copy-stage-max-owned").map (·.as! Nat)
    |>.getD Ix.Catalog.defaultCopyStageMaxOwned

  -- Resolve modules through the current directory's Lake workspace.
  initLeanSearchPath (some (← IO.currentDir))
  -- Peak-RSS accounting for --report (I7): process-tree sampler,
  -- Linux-only (reads back 0 elsewhere).
  TracingTexray.startSampler
  TracingTexray.resetPeakTreeRss

  println! "Building catalog {catalogPrefix} from {libs.size} librar(ies)..."
  let buildStart ← IO.monoMsNow
  let result ← Ix.Catalog.buildCatalog spec copyStageMaxOwned
  let buildElapsed := (← IO.monoMsNow) - buildStart
  for (qualifier, count) in result.perLib do
    println! "[catalog] {qualifier}: {count} owned constants"
  println! "[catalog] replayed {result.replayed} declarations; \
{result.consts.size} constants total in {buildElapsed}ms"

  let auditRan := p.hasFlag "audit" || auditOnly?.isSome
  if auditRan then
    let only := auditOnly?.map fun quals =>
      quals.foldl (init := ({} : Lean.NameSet)) (·.insert ·)
    let scope := match auditOnly? with
      | some quals => s!"members {quals}"
      | none => "all members"
    let auditStart ← IO.monoMsNow
    let audit ← Ix.Catalog.auditCatalog spec result.consts only
    let auditElapsed := (← IO.monoMsNow) - auditStart
    if audit.violations.isEmpty then
      println! "[audit] anon-address preservation: {audit.checked} owned \
constants verified ({scope}) in {auditElapsed}ms"
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

  let peakRssBytes ← TracingTexray.peakTreeRssBytes
  if let some flag := p.flag? "report" then
    let report := Lean.Json.mkObj
      [ ("schemaVersion", Lean.toJson (2 : Nat))
      , ("ixVersion", Lean.Json.str Ix.versionString)
      , ("leanToolchain", Lean.Json.str Lean.versionString)
      , ("ixeFormatVersion", Lean.toJson Ixon.Env.VERSION.toNat)
      , ("catalogPrefix", Lean.Json.str s!"{catalogPrefix}")
      , ("specFile", (p.flag? "spec").map (fun f => Lean.Json.str (f.as! String))
          |>.getD Lean.Json.null)
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
      , ("compileMs", Lean.toJson elapsed)
      -- Process-tree high-water mark (I7); 0 on non-Linux platforms.
      , ("peakRssBytes", Lean.toJson peakRssBytes)
      , ("copyStageMaxOwned", Lean.toJson copyStageMaxOwned)
      , ("auditedQualifiers", match auditRan, auditOnly? with
          | false, _ => Lean.Json.null
          | true, none => Lean.Json.arr <|
              libs.map (Lean.Json.str s!"{·.qualifier}")
          | true, some quals => Lean.Json.arr <|
              quals.map (Lean.Json.str s!"{·}")) ]
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
    "prefix"        : String; "The catalog namespace, e.g. `MyCatalog` (required unless --spec is given)."
    spec            : String; "Path to a JSON spec file `{\"prefix\": ..., \"libs\": [{\"qualifier\": ..., \"roots\": [...]}]}` — the file form of the positional specs, resolved identically and echoed into --report. Mutually exclusive with positional libs and --prefix; the `groups` key is reserved."
    out             : String; "Output path for the serialized .ixe; defaults to the lowercased prefix with `.ixe`."
    "allow-partial" ;         "Serialize the grounded subset and exit 0 even when some catalog constants fail to compile. Default is fail-closed: any ungrounded constant means a nonzero exit and NO output file."
    audit           ;         "Verify anon-address preservation before writing: recompile each member library standalone and require addr(<prefix>.<qualifier>.N) in the catalog to equal addr(N) standalone, for every owned constant (qualification is metadata-only). N+1 extra compiles; violations abort with no output file."
    "audit-only"    : String; "Comma-separated member qualifiers: run the --audit invariant on just these members (a rotating subset keeps the gate viable at corpus scale, where the full audit is N+1 large compiles). Implies --audit; the artifact is still built and written."
    report          : String; "Write a machine-readable JSON catalog report (versions, lib specs, counts, ungrounded list, canonical root, peak RSS, audited qualifiers) to this path — written on success, fail-closed abort, and partial publish alike."
    "copy-stage-max-owned" : Nat; "Copy-vs-share staging threshold: a member owning at most this many constants is copy-staged and its env's olean regions freed; a heavier member is staged sharing its regions, which stay mapped (default 100000). Threshold-0 and default builds are byte-identical; the knob trades resident regions against copy work."
    "close-roots"   ;         "Close every member's roots over cross-package source imports through the cwd's Lake workspace before building: a provider module some member imports that the provider's own roots do not reach becomes additional provider coverage, and each member is re-rooted at its terminal modules. Fail-closed on imports from outside the cataloged members, ambiguous providers, and cross-member module collisions. The workspace must already be fetched (run its `lake build` first); the resolved roots are echoed into --report."

  ARGS:
    ...libs : String; "Member library specs `Qualifier=Root[,Root...]` in dependency order (dependencies first), e.g. `Batteries=Batteries HaskellSpec=HaskellSpec`."
]
