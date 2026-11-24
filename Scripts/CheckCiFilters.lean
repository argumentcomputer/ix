import Std.Data.HashMap
import Std.Data.HashSet

/-! # CI path-filter coverage check (`Scripts/CheckCiFilters.lean`)

Verifies that `.github/workflows/ci.yml`'s `dorny/paths-filter` glob lists cover every
project source file in the pinned SHA-256 definitional closure manifests, as well as the
manifest files themselves and the trust-surface root files fenced by `kernel-trust-surface`:

* `Tests/Fixtures/circuit-composed-closure-manifest.txt` (required) → `refinement:` filter;
* `Tests/Fixtures/security-128-closure-manifest.txt` (required) → `refinement:` filter;
* `Tests/Fixtures/compile-correct-closure-manifest.txt` (checked when present) → `kernel:` filter;
* `Tests/Fixtures/check-bytes-closure-manifest.txt` (checked when present) → `kernel:` filter;
* `Ix/Address/Admission.lean` and `Ix/KernelDisplay/Peek.lean` → `kernel:` filter.

Usage:
  `lean --run Scripts/CheckCiFilters.lean [--self-test]`
-/

namespace CheckCiFilters

/-- Count leading ASCII space characters. -/
def leadingSpaces (s : String) : Nat :=
  (s.toList.takeWhile (· == ' ')).length

/-- Strip an unquoted trailing YAML `# ...` comment and trim surrounding whitespace. -/
def stripYamlComment (s : String) : String := Id.run do
  let mut inSingle := false
  let mut inDouble := false
  let mut out : Array Char := #[]
  for c in s.toList do
    if c == '\'' && !inDouble then inSingle := !inSingle
    else if c == '"' && !inSingle then inDouble := !inDouble
    else if c == '#' && !inSingle && !inDouble then break
    out := out.push c
  return (String.ofList out.toList).trimAscii.toString

/-- Strip matching single or double quotes around a YAML scalar. -/
def stripQuotes (s : String) : String :=
  match s.toList with
  | '\'' :: rest =>
    match rest.reverse with
    | '\'' :: inner => String.ofList inner.reverse
    | _ => s
  | '"' :: rest =>
    match rest.reverse with
    | '"' :: inner => String.ofList inner.reverse
    | _ => s
  | _ => s

/-- Match a single path segment against a wildcard pattern (`*` matches zero or more
characters within the segment; `?` matches any single character). -/
def matchSeg (pat str : String) : Bool := Id.run do
  let p := pat.toList.toArray
  let s := str.toList.toArray
  let mut pi := 0
  let mut si := 0
  let mut starPi : Option Nat := none
  let mut starSi := 0
  while si < s.size do
    if pi < p.size && (p[pi]! == '?' || p[pi]! == s[si]!) then
      pi := pi + 1
      si := si + 1
    else if pi < p.size && p[pi]! == '*' then
      starPi := some pi
      starSi := si
      pi := pi + 1
    else if let some sp := starPi then
      pi := sp + 1
      starSi := starSi + 1
      si := starSi
    else
      return false
  while pi < p.size && p[pi]! == '*' do
    pi := pi + 1
  return pi == p.size

/-- Match slash-split path segments against slash-split glob segments (`**` matches zero or
more segments when followed by another segment, and one or more segments when trailing). -/
def matchSegs (pats paths : List String) : Bool :=
  match pats, paths with
  | [], [] => true
  | ["**"], xs => !xs.isEmpty
  | "**" :: ps, xs =>
    matchSegs ps xs ||
      match xs with
      | _ :: xs' => matchSegs ("**" :: ps) xs'
      | [] => false
  | p :: ps, x :: xs => matchSeg p x && matchSegs ps xs
  | _, _ => false
termination_by pats.length + paths.length

/-- Match a repository-relative path against a `dorny/paths-filter` glob pattern. -/
def globMatch (pattern path : String) : Bool :=
  let norm (s : String) : List String :=
    (s.splitOn "/").filter (!·.isEmpty)
  matchSegs (norm pattern) (norm path)

/-- Whether `path` matches any glob pattern in `globs`. -/
def matchesAny (globs : Array String) (path : String) : Bool :=
  globs.any (fun g => globMatch g path)

/-- Parse the `filters: |` block of `.github/workflows/ci.yml` into a map from filter name
(`refinement`, `kernel`, ...) to its array of glob patterns. -/
def parseCiFilters (yaml : String) : Except String (Std.HashMap String (Array String)) := do
  let lines := yaml.splitOn "\n"
  let mut inFilters := false
  let mut filtersIndent := 0
  let mut currentGroup : Option String := none
  let mut groups : Std.HashMap String (Array String) := {}
  for rawLine in lines do
    let clean := stripYamlComment rawLine
    if !inFilters then
      if clean == "filters: |" then
        inFilters := true
        filtersIndent := leadingSpaces rawLine
    else
      if clean.isEmpty then continue
      let ind := leadingSpaces rawLine
      if ind ≤ filtersIndent then
        break
      if clean.startsWith "- " then
        let some g := currentGroup
          | throw s!"malformed filters block: list item outside a filter group: {clean}"
        let item := stripQuotes ((String.ofList (clean.toList.drop 2)).trimAscii.toString)
        if !item.isEmpty then
          groups := groups.insert g ((groups.getD g #[]).push item)
      else
        match clean.toList.reverse with
        | ':' :: rest =>
          let g := (String.ofList rest.reverse).trimAscii.toString
          currentGroup := some g
          if !groups.contains g then
            groups := groups.insert g #[]
        | _ =>
          throw s!"malformed filters block: unexpected line: {clean}"
  unless inFilters do
    throw "could not find `filters: |` block in .github/workflows/ci.yml"
  return groups

/-- Top-level module prefixes belonging to this repository (external dependencies such as
`Init`, `Std`, `Lean`, `Mathlib`, `Batteries`, `Blake3` are excluded). -/
def projectRoots : List String :=
  ["Ix", "IxCK", "IxSharingVerify", "Aiur", "IxVM", "MultiStark", "IxVMRefinement",
   "Models", "IxSetTheoryModel", "Tests"]

/-- Nested workspace packages whose `M.X` modules live under `M/M/X.lean`. -/
def nestedPackageRoots : List String :=
  ["Aiur", "IxVM", "MultiStark"]

/-- Whether a Lean module name belongs to this repository. -/
def isProjectModule (modName : String) : Bool :=
  let head := (modName.splitOn ".").headD ""
  projectRoots.contains head

/-- Convert a project Lean module name (`A.B.C`) to its repository-relative `.lean` path,
accounting for nested packages (`Aiur.X` → `Aiur/Aiur/X.lean`,
`IxSetTheoryModel.X` → `Models/SetTheory/IxSetTheoryModel/X.lean`, etc.). -/
def moduleToSourcePath (modName : String) : String :=
  let parts := modName.splitOn "."
  let rel := "/".intercalate parts ++ ".lean"
  match parts.head? with
  | some "IxSetTheoryModel" => "Models/SetTheory/" ++ rel
  | some root =>
    if nestedPackageRoots.contains root then root ++ "/" ++ rel else rel
  | none => rel

/-- Extract all imported module names from a Lean source file's header (handling
nested block comments `/- ... -/`, line comments `-- ...`, `module`,
`public`/`private`/`meta`, `import all`, and multiple imports per line).
Scans raw UTF-8 bytes and stops immediately at the first non-header token so
multi-megabyte proof files are parsed in microseconds under `lean --run`. -/
def parseLeanImports (src : String) : Array String := Id.run do
  let bs := src.toUTF8
  let n := bs.size
  let isSpace (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13
  let mut i := 0
  let mut imports : Array String := #[]
  let mut expectMod := false
  while i < n do
    let b := bs[i]!
    if isSpace b then
      i := i + 1
    else if b == 47 && i + 1 < n && bs[i + 1]! == 45 then
      -- Nested block comment `/- ... -/`
      let mut depth := 1
      i := i + 2
      while i < n && depth > 0 do
        if bs[i]! == 47 && i + 1 < n && bs[i + 1]! == 45 then
          depth := depth + 1; i := i + 2
        else if bs[i]! == 45 && i + 1 < n && bs[i + 1]! == 47 then
          depth := depth - 1; i := i + 2
        else
          i := i + 1
    else if b == 45 && i + 1 < n && bs[i + 1]! == 45 then
      -- Line comment `-- ... \n`
      i := i + 2
      while i < n && bs[i]! != 10 do i := i + 1
    else
      -- Read next whitespace/comment-delimited token
      let start := i
      while i < n do
        let c := bs[i]!
        if isSpace c then break
        if c == 47 && i + 1 < n && bs[i + 1]! == 45 then break
        if c == 45 && i + 1 < n && bs[i + 1]! == 45 then break
        i := i + 1
      let tok := String.fromUTF8! (bs.extract start i)
      if expectMod then
        if tok == "all" then
          continue
        imports := imports.push tok
        expectMod := false
      else if tok == "module" || tok == "public" || tok == "private" || tok == "meta" then
        continue
      else if tok == "import" then
        expectMod := true
      else
        -- Reached first declaration/body token after the import header.
        break
  return imports

/-- Walk transitive project-local imports starting from `roots` using source files on disk.
Returns sorted unique repository-relative `.lean` paths. -/
def transitiveProjectPaths (roots : Array String) : IO (Array String) := do
  let mut visited : Std.HashSet String := {}
  let mut todo : Array String := roots
  let mut paths : Array String := #[]
  while h : todo.size > 0 do
    let modName := todo.back
    todo := todo.pop
    if visited.contains modName || !isProjectModule modName then continue
    visited := visited.insert modName
    let p := moduleToSourcePath modName
    if ← (System.FilePath.mk p).pathExists then
      paths := paths.push p
      let src ← IO.FS.readFile p
      for imp in parseLeanImports src do
        if isProjectModule imp && !visited.contains imp then
          todo := todo.push imp
  return paths.qsort (· < ·)

/-- Extract all unique sorted project source paths referenced in a closure manifest file. -/
def manifestProjectPaths (manifestText : String) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  for rawLine in manifestText.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " with
    | _ :: _ :: modName :: _ =>
      if isProjectModule modName then
        let p := moduleToSourcePath modName
        unless seen.contains p do
          seen := seen.insert p
          out := out.push p
    | _ => continue
  return out.qsort (· < ·)

/-- Self-tests for the glob matcher, module path mapping, and YAML filter parser. -/
def selfCheck : IO Unit := do
  -- Exact paths
  unless globMatch "Ix/Ixon.lean" "Ix/Ixon.lean" do
    throw <| IO.userError "self-test failed: exact match"
  if globMatch "Ix/Ixon.lean" "Ix/Ixon/Types.lean" then
    throw <| IO.userError "self-test failed: exact mismatch"
  -- Single-segment `*`
  unless globMatch "Ix/Claim*.lean" "Ix/Claim.lean" do
    throw <| IO.userError "self-test failed: Claim*.lean on Claim.lean"
  unless globMatch "Ix/Claim*.lean" "Ix/ClaimContext.lean" do
    throw <| IO.userError "self-test failed: Claim*.lean on ClaimContext.lean"
  if globMatch "Ix/Claim*.lean" "Ix/Claim/Foo.lean" then
    throw <| IO.userError "self-test failed: `*` crossed `/`"
  -- Trailing `**`
  unless globMatch "IxCK/**" "IxCK/Kernel/Admission.lean" do
    throw <| IO.userError "self-test failed: IxCK/** deep match"
  unless globMatch "IxCK/**" "IxCK/Kernel.lean" do
    throw <| IO.userError "self-test failed: IxCK/** shallow match"
  if globMatch "IxCK/**" "IxCK.lean" then
    throw <| IO.userError "self-test failed: IxCK/** matched sibling file"
  if globMatch "IxCK/**" "IxCK" then
    throw <| IO.userError "self-test failed: IxCK/** matched bare directory"
  -- Leading and interior `**`
  unless globMatch "**/*.rs" "lib.rs" && globMatch "**/*.rs" "crates/ix/src/lib.rs" do
    throw <| IO.userError "self-test failed: **/*.rs"
  if globMatch "**/*.rs" "crates/ix/src/lib.lean" then
    throw <| IO.userError "self-test failed: **/*.rs false positive"
  unless globMatch "a/**/b.lean" "a/b.lean" && globMatch "a/**/b.lean" "a/x/y/b.lean" do
    throw <| IO.userError "self-test failed: a/**/b.lean"
  if globMatch "a/**/b.lean" "a/x/c.lean" then
    throw <| IO.userError "self-test failed: a/**/b.lean false positive"
  -- Module-to-path mapping
  let expectedPaths : List (String × String) := [
    ("Ix.Ixon", "Ix/Ixon.lean"),
    ("Ix.Environment", "Ix/Environment.lean"),
    ("Ix.Address.Admission", "Ix/Address/Admission.lean"),
    ("IxCK.Kernel.Admission", "IxCK/Kernel/Admission.lean"),
    ("Aiur.Generic.AST", "Aiur/Aiur/Generic/AST.lean"),
    ("IxVM.Source", "IxVM/IxVM/Source.lean"),
    ("MultiStark.Basic", "MultiStark/MultiStark/Basic.lean"),
    ("IxVMRefinement.Endpoint.ComposedResidual", "IxVMRefinement/Endpoint/ComposedResidual.lean"),
    ("IxSharingVerify.CanonicalMeaning", "IxSharingVerify/CanonicalMeaning.lean"),
    ("Models.SetTheory.IxSetTheoryModel.Carneiro", "Models/SetTheory/IxSetTheoryModel/Carneiro.lean"),
    ("IxSetTheoryModel.Audit", "Models/SetTheory/IxSetTheoryModel/Audit.lean")]
  for (modName, want) in expectedPaths do
    let got := moduleToSourcePath modName
    unless got == want do
      throw <| IO.userError s!"self-test failed: moduleToSourcePath {modName} = {got}, expected {want}"
  -- Lean import parser (handles comments, modifiers, single-line multi-import)
  let sampleLean :=
    "/- block comment import Fake.One -/\n" ++
    "module public import Init.Core import Ix.HostAdmission -- import Fake.Two\n" ++
    "private meta import all IxCK.Kernel.Audit.Roots\n" ++
    "def body := \"import Fake.Three\"\n"
  let parsedImps := parseLeanImports sampleLean
  unless parsedImps == #["Init.Core", "Ix.HostAdmission", "IxCK.Kernel.Audit.Roots"] do
    throw <| IO.userError s!"self-test failed: parseLeanImports = {parsedImps}"
  -- YAML filter parser
  let sampleYaml :=
    "      - uses: dorny/paths-filter@abc\n" ++
    "        with:\n" ++
    "          filters: |\n" ++
    "            kernel:\n" ++
    "              - 'IxCK/**'\n" ++
    "              - 'Ix/Address/Admission.lean' # hash impl\n" ++
    "            refinement:\n" ++
    "              - 'Aiur/**'\n" ++
    "              - 'Ix/Ixon.lean'\n" ++
    "      - name: Next step\n"
  match parseCiFilters sampleYaml with
  | .error e => throw <| IO.userError s!"self-test failed: parseCiFilters error: {e}"
  | .ok parsed =>
    unless parsed.getD "kernel" #[] == #["IxCK/**", "Ix/Address/Admission.lean"] do
      throw <| IO.userError s!"self-test failed: unexpected kernel globs: {parsed.getD "kernel" #[]}"
    unless parsed.getD "refinement" #[] == #["Aiur/**", "Ix/Ixon.lean"] do
      throw <| IO.userError s!"self-test failed: unexpected refinement globs: {parsed.getD "refinement" #[]}"
  -- Manifest project path extraction (including 128-bit security audits)
  let sampleManifest :=
    "# definitional closure of Security128\n" ++
    "T 0000 Ix.Cert.MultiStark.Security128Audit Ix.Cert.MultiStark.Security128.ud_160_pow20_query_error_le_128\n" ++
    "D 0000 Ix.Aiur.Parameters Aiur.extensionDegreeV6\n" ++
    "T 0000 Mathlib.Data.Real.Basic Real.add_comm\n"
  let parsedManifest := manifestProjectPaths sampleManifest
  unless parsedManifest == #["Ix/Aiur/Parameters.lean", "Ix/Cert/MultiStark/Security128Audit.lean"] do
    throw <| IO.userError s!"self-test failed: manifestProjectPaths = {parsedManifest}"

/-- Required trust-surface root files that must always trigger the `kernel:` CI job. -/
def requiredKernelFiles : Array String := #[
  "Ix/Address/Admission.lean",
  "Ix/KernelDisplay/Peek.lean"]

/-- Required non-Lean and key Lean security-critical files and the CI filter
groups that must cover them. -/
def requiredFilterCoverage : Array (String × String) := #[
  (".config/nextest.toml", "rust"),
  ("rustfmt.toml", "rust"),
  ("crates/stark-shrinker/Cargo.toml", "rust"),
  ("crates/stark-shrinker/Cargo.toml", "cuda"),
  ("tools/gnark/circuit.go", "gnark"),
  ("tools/gnark/circuit.go", "rust"),
  ("contracts/plonk/src/PlonkVerifier.sol", "contracts"),
  ("contracts/groth16/src/IxGroth16Verifier.sol", "contracts"),
  ("c/common.h", "rust"),
  ("c/common.h", "host"),
  ("Aiur/c/execution.c", "rust"),
  ("Aiur/c/execution.c", "formal"),
  ("Scripts/FriSecurity.lean", "host"),
  ("Scripts/FriSecurity.lean", "formal"),
  ("Scripts/CheckFormalKeys.lean", "formal"),
  ("Scripts/CheckAiurCompressionFixtures.lean", "formal"),
  ("Ix/Aiur/Parameters.lean", "formal"),
  ("Ix/Aiur/Parameters.lean", "refinement"),
  ("Ix/MultiStark/Wire.lean", "formal"),
  ("Ix/MultiStark/Wire.lean", "refinement"),
  ("Tests/FormalChecks/Common.lean", "formal"),
  ("Tests/Fixtures/MultiStark/sample.bin", "formal"),
  ("Tests/Ix/Kernel/ModelLaws.lean", "formal"),
  ("Ix/HostAdmission.lean", "kernel"),
  ("Ix/HostAdmission.lean", "refinement"),
  ("Ix/HostAdmission.lean", "formal"),
  ("IxSharingVerify.lean", "kernel"),
  ("IxSharingVerify.lean", "refinement"),
  ("Benchmarks/Kernel/CheckIxeEntry.lean", "kernel"),
  ("Tests/Fixtures/trust-surface/lexer.lean", "kernel"),
  ("Ix/Aggr/Verification.lean", "refinement"),
  ("Ix/Compile/FrontEnd.lean", "refinement"),
  ("Ix/CompileCert/Emission.lean", "refinement"),
  ("Ix/LeanIngress/Expr.lean", "refinement"),
  ("Ix/Sharing/Canon.lean", "refinement")]

/-- `leanchecker` roots and formal-only modules whose entire transitive project
import closure must be covered by the corresponding CI filter group. -/
def transitiveImportChecks : Array (String × String × Array String) := #[
  ("certified-kernel leanchecker roots", "kernel", #[
    "IxCK.Kernel.Audit.Roots",
    "IxCK.Kernel.Admission.Audit",
    "Ix.Ixon.Authenticated.Audit",
    "Ix.Ixon.BlockOrder.Audit",
    "Ix.HostAdmission.Audit",
    "Ix.Cert.ModuleAudit",
    "Ix.Cert.Audit",
    "Ix.Cert.RuntimeAudit",
    "IxSharingVerify.Audit.Statements",
    "IxSharingVerify.Audit.CompiledCode",
    "IxSharingVerify.Audit.SorryFrontier",
    "IxSetTheoryModel.Audit"]),
  ("ixvm-refinement leanchecker roots", "refinement", #[
    "IxVMRefinement.Endpoint.ComposedResidual",
    "IxVMRefinement.Endpoint.ClosureAudit",
    "IxVMRefinement.Endpoint.ConsistencyCorollary",
    "IxVMRefinement.Endpoint.ComposedResidualAudit",
    "Ix.IxVM.ConsistencyAudit",
    "Ix.IxVM.ConsistencyModelAudit",
    "Ix.IxVM.Refinement.Audit",
    "Ix.Cert.MultiStark.Security128Audit",
    "Ix.Cert.Aggr.MonolithicRom",
    "Ix.Cert.Aggr.Security128Audit",
    "Ix.Cert.Compression.Bls12381.Audit",
    "Ix.Cert.Compression.StarkShrinkerAudit",
    "Ix.Cert.Compression.Security128Audit",
    "Ix.Cert.Security128ClosureManifest"]),
  ("formal leanchecker roots and formal-only modules", "formal", #[
    "Aiur.Audit",
    "Ix.IxVM.ConsistencyAudit",
    "Ix.IxVM.ConsistencyModelAudit",
    "Ix.IxVM.Refinement.Audit",
    "Ix.Cert.MultiStark.Security128Audit",
    "Ix.Cert.Aggr.MonolithicRom",
    "Ix.Cert.Aggr.Security128Audit",
    "Ix.Cert.Compression.Bls12381.Audit",
    "Ix.Cert.Compression.StarkShrinkerAudit",
    "Ix.Cert.Compression.Security128Audit",
    "Ix.Cert.Security128ClosureManifest",
    "Tests.FormalPackageMain",
    "Tests.Ix.InstanceSymbols",
    "Tests.Ix.VMSource",
    "Tests.Ix.IxVM.SafeReferencesWalk",
    "Tests.Ix.Kernel.ModelLaws"])]

/-- Closure manifests to verify: `(manifestPath, ciFilterName, required)`. -/
def manifestChecks : Array (String × String × Bool) := #[
  ("Tests/Fixtures/circuit-composed-closure-manifest.txt", "refinement", true),
  ("Tests/Fixtures/security-128-closure-manifest.txt", "refinement", true),
  ("Tests/Fixtures/compile-correct-closure-manifest.txt", "kernel", true),
  ("Tests/Fixtures/check-bytes-closure-manifest.txt", "kernel", true)]

def ciWorkflowPath : System.FilePath := ".github/workflows/ci.yml"

def run : IO UInt32 := do
  let yaml ← IO.FS.readFile ciWorkflowPath
  match parseCiFilters yaml with
  | .error e =>
    IO.eprintln s!"[ci-filters] failed to parse {ciWorkflowPath}: {e}"
    return 1
  | .ok filters =>
    let mut failures := 0
    let mut checkedManifests := 0
    let mut checkedFiles := 0
    for (manifestPath, filterName, required) in manifestChecks do
      match filters[filterName]? with
      | none =>
        IO.eprintln s!"[ci-filters] missing '{filterName}:' filter group in {ciWorkflowPath}"
        failures := failures + 1
      | some globs =>
        if globs.isEmpty then
          IO.eprintln s!"[ci-filters] empty '{filterName}:' filter group in {ciWorkflowPath}"
          failures := failures + 1
          continue
        let exists? ← (System.FilePath.mk manifestPath).pathExists
        if !exists? then
          if required then
            IO.eprintln s!"[ci-filters] required manifest missing: {manifestPath}"
            failures := failures + 1
          else
            IO.println s!"[ci-filters] skipping absent optional manifest: {manifestPath}"
          continue
        checkedManifests := checkedManifests + 1
        unless matchesAny globs manifestPath do
          IO.eprintln s!"[ci-filters] MISSING from '{filterName}:' filter (manifest itself): {manifestPath}"
          failures := failures + 1
        let text ← IO.FS.readFile manifestPath
        let paths := manifestProjectPaths text
        checkedFiles := checkedFiles + paths.size
        for p in paths do
          unless matchesAny globs p do
            IO.eprintln s!"[ci-filters] MISSING from '{filterName}:' filter (from {manifestPath}): {p}"
            failures := failures + 1
    -- Required trust-surface root files in `kernel:`
    match filters["kernel"]? with
    | none =>
      IO.eprintln s!"[ci-filters] missing 'kernel:' filter group in {ciWorkflowPath}"
      failures := failures + 1
    | some kernelGlobs =>
      for p in requiredKernelFiles do
        checkedFiles := checkedFiles + 1
        unless matchesAny kernelGlobs p do
          IO.eprintln s!"[ci-filters] MISSING from 'kernel:' filter (required trust-surface file): {p}"
          failures := failures + 1
    -- Required non-Lean security-critical files (Go gnark, Solidity contracts, C headers)
    for (p, filterName) in requiredFilterCoverage do
      checkedFiles := checkedFiles + 1
      match filters[filterName]? with
      | none =>
        IO.eprintln s!"[ci-filters] missing '{filterName}:' filter group in {ciWorkflowPath} (needed for {p})"
        failures := failures + 1
      | some globs =>
        unless matchesAny globs p do
          IO.eprintln s!"[ci-filters] MISSING from '{filterName}:' filter (required non-Lean file): {p}"
          failures := failures + 1
    -- Transitive Lean import closure of CI leanchecker roots and formal-only modules
    for (label, filterName, roots) in transitiveImportChecks do
      match filters[filterName]? with
      | none =>
        IO.eprintln s!"[ci-filters] missing '{filterName}:' filter group in {ciWorkflowPath} (needed for {label})"
        failures := failures + 1
      | some globs =>
        let paths ← transitiveProjectPaths roots
        checkedFiles := checkedFiles + paths.size
        for p in paths do
          unless matchesAny globs p do
            IO.eprintln s!"[ci-filters] MISSING from '{filterName}:' filter ({label}): {p}"
            failures := failures + 1
    if failures == 0 then
      IO.println s!"[ci-filters] OK: {checkedManifests} manifest(s), {checkedFiles} path checks passed against {ciWorkflowPath}."
      return 0
    else
      IO.eprintln s!"[ci-filters] FAILED: {failures} uncovered path(s) in {ciWorkflowPath}."
      return 1

end CheckCiFilters

def main (args : List String) : IO UInt32 := do
  CheckCiFilters.selfCheck
  if args == ["--self-test"] then
    IO.println "[ci-filters] self-test passed."
    return 0
  CheckCiFilters.run
