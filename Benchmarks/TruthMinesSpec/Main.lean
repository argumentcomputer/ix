/-
  `lake exe truthmines` — the corpus driver: Mathlib-parity ergonomics for
  the TruthMines catalog. Everything is projected from the typed records in
  `Benchmarks.TruthMinesSpec`; there is no version or toolchain handshake
  because ix and the corpus live in one repo on one toolchain.

    gen [--check]   project the workspace files (lakefile.lean,
                    lean-toolchain, Drivers/<Q>.lean per member)
    spec [--mini]   print the member/driver table (qualifier, driver
                    module, roots) for the full or mini tier
    validate [--mini] [--only Q[,Q…]] [--jobs N] [--ceiling-gb N]
             [--no-watchdog]
                    per-library METADATA fidelity: run the 8-phase
                    `ix validate` pipeline (aux-gen congruence, alpha
                    canonicity, decompile both ways, per-constant
                    roundtrip) over each member's Benchmarks/Compile
                    driver — the same import closure its piece compiles
                    from, so the records stay the only pin source. The
                    full tier also validates Palomar.ix as one aggregate
                    library. Exit-code gated, no report artifacts. Heavy members
                    (mathlib-class) hold two compile+decompile states
                    at once, so the default is one member at a time
                    under the box-level ceiling. Sweeps first prebuild
                    their selected drivers in one Lake process, then run
                    --jobs validators with `--no-build` over the quiescent
                    shared package store.
    build [--mini] [--out DIR.ixc] [--jobs N] [--ceiling-gb N]
          [--no-watchdog] [--no-cache] [--palomar-ixc DIR.ixc]
                    gen-check, build the member root oleans (network +
                    `lake exe cache get` on first run), compile each
                    member's piece DIRECTLY INTO the self-contained
                    `.ixc` directory (`<out>/<Q>.ixe`) in a short-lived
                    watchdogged `ix compile` process — `--jobs N`
                    members in flight, peak = max member, never a
                    union — then `ix catalog assemble` (manifest
                    in-place) + `ix catalog verify`. `--mini` targets
                    the small infrastructure tier
                    (`truthmines-mini.ixc/`); the default is the full
                    corpus (`truthmines.ixc/`). The `.ixc` directory is
                    the whole deliverable AND the machine-readable
                    record (`ix catalog info`) — no report artifacts
                    are written. Pieces are cached: a member is
                    recompiled only when its pin closure, toolchain, or
                    ix version changed (`<out>/.cache/<Q>.key`), or
                    with `--no-cache`. On a full build,
                    `--palomar-ixc` flattens the already-verified
                    standalone Palomar catalog into the final manifest;
                    its source workspaces and compatibility patches stay
                    owned by Palomar.ix.
    check [--mini] [--ixc DIR.ixc] [--only Q[,Q…]] [--jobs N]
                    per-piece KERNEL sweep: `ix check-rs --anon` over
                    each member's piece in the `.ixc` directory — the
                    fat-profile rung-1 checking story. Each piece is a
                    self-contained env checked in its own subprocess
                    (embarrassingly parallel, peak = one mmap'd member,
                    ~4–6 GiB RSS, so the default 4 in flight stays
                    light). Output is captured per piece and surfaced
                    only on rejection, with the solo repro command.
                    Exit-code gated, no artifacts.

  The heavy steps run under the typed RAM watchdog (`Ix.Watchdog`,
  shared with `ix bench`): a systemd user scope with cgroup MemoryMax
  and swap off, whole-scope kill on breach (exit 137) — "an unenforced
  ceiling is not a benchmark run". Piece compiles get a PER-MEMBER
  ceiling (`--ceiling-gb`, default 25 GiB — the mathlib-class bound);
  the box never sees more than jobs × ceiling. `--no-watchdog` opts out
  explicitly (required on non-systemd platforms).

  Run from the repo root; `build` needs `lake build ix` first.
-/
import Benchmarks.TruthMinesSpec.Projection
import Ix.Catalog
import Ix.Common
import Ix.Watchdog

open TruthMinesSpec

private def usage : String :=
  "usage: lake exe truthmines <gen [--check] | spec [--mini] | build \
[--mini] [--out DIR.ixc] [--jobs N] [--ceiling-gb N] [--no-watchdog] \
[--no-cache] [--palomar-ixc DIR.ixc] | check [--mini] [--ixc DIR.ixc] \
[--only Q[,Q…]] [--jobs N] | \
validate [--mini] [--only Q[,Q…]] [--jobs N] [--ceiling-gb N] \
[--no-watchdog]>"

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

private structure GenFile where
  path : System.FilePath
  content : String

private def genFiles : List GenFile :=
  [ ⟨workspaceLakefilePath, renderWorkspaceLakefile⟩,
    ⟨workspaceToolchainPath, renderWorkspaceToolchain⟩,
    ⟨compileWorkspaceLakefilePath, renderCompileWorkspaceLakefile⟩,
    ⟨compileWorkspaceToolchainPath, renderWorkspaceToolchain⟩,
    ⟨compilePalomarModulePath, renderCompilePalomarModule⟩ ]
  ++ (driverLibs.map fun lib =>
      ⟨driverModulePath lib.qualifier, renderDriverModule lib⟩).toList
  ++ (driverLibs.map fun lib =>
      ⟨compileMemberModulePath lib.qualifier,
        renderCompileMemberModule lib⟩).toList

private def readIfExists (path : System.FilePath) : IO (Option String) := do
  if (← path.pathExists) then return some (← IO.FS.readFile path)
  return none

/-- Load an existing fat catalog as an external member source. Structural
manifest checks happen in `Ix.Catalog.de`; every referenced piece must also be
present before the caller asks `ix catalog verify` to bind its content root. -/
private def loadExternalCatalog (dir : System.FilePath) :
    IO Ix.Catalog.Catalog := do
  let manifest := dir / "manifest"
  unless ← manifest.pathExists do
    throw <| IO.userError s!"external catalog {dir} has no manifest"
  let catalog ← match Ix.Catalog.de (← IO.FS.readBinFile manifest) with
    | .ok catalog => pure catalog
    | .error message =>
        throw (IO.userError
          s!"external catalog {dir} has an invalid manifest: {message}")
  match catalog.storage with
  | .chunked _ =>
      throw <| IO.userError
        s!"external catalog {dir} is chunked; composition needs fat pieces"
  | .fat pieces =>
      unless pieces.size == catalog.members.size do
        throw <| IO.userError s!"external catalog {dir} has {pieces.size} storage rows for {catalog.members.size} members"
  for member in catalog.members do
    let piece := dir / s!"{member.label}.ixe"
    unless ← piece.pathExists do
      throw <| IO.userError s!"external catalog piece missing: {piece}"
  return catalog

private def stalePaths : IO (List String) := do
  let mut stale := []
  for file in genFiles do
    unless (← readIfExists file.path) == some file.content do
      stale := stale ++ [file.path.toString]
  return stale

private def runGen (check : Bool) : IO UInt32 := do
  let stale ← stalePaths
  if check then
    if stale.isEmpty then
      IO.println "truthmines gen --check: up to date"
      return 0
    IO.eprintln s!"truthmines gen --check: stale generated files {stale} — \
run `lake exe truthmines gen`"
    return 1
  if stale.isEmpty then
    IO.println "truthmines gen: up to date"
    return 0
  for file in genFiles do
    if let some parent := file.path.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile file.path file.content
  IO.println s!"truthmines gen: wrote {stale}"
  return 0

private structure BuildOptions where
  out? : Option String := none
  jobs? : Option Nat := none
  /-- Per-member compile ceiling (GiB); the box-level pressure is
      jobs × this, never a union. -/
  ceilingGb : Option Nat := none
  noWatchdog : Bool := false
  noCache : Bool := false
  /-- Build the mini tier (`catalogMiniSpec`) instead of the full corpus. -/
  mini : Bool := false
  /-- Verified standalone Palomar catalog whose members are appended to the
      full TruthMines manifest. The Palomar sources remain external. -/
  palomarIxc? : Option String := none

/-- Per-member ceiling default: the mathlib-class piece peaks ~19–20
    GiB; 25 leaves headroom without hiding a regression class. -/
private def defaultMemberCeilingGb : Nat := 25

private def parseBuild : List String → Except String BuildOptions
  | [] => .ok {}
  | "--out" :: value :: rest => do pure { ← parseBuild rest with out? := some value }
  | "--jobs" :: value :: rest => do
    let some n := value.toNat? | .error s!"--jobs needs a number, got `{value}`"
    if n == 0 then .error "--jobs must be at least 1" else
    pure { ← parseBuild rest with jobs? := some n }
  | "--ceiling-gb" :: value :: rest => do
    let some gb := value.toNat? | .error s!"--ceiling-gb needs a number, got `{value}`"
    pure { ← parseBuild rest with ceilingGb := some gb }
  | "--no-watchdog" :: rest => do
    pure { ← parseBuild rest with noWatchdog := true }
  | "--no-cache" :: rest => do
    pure { ← parseBuild rest with noCache := true }
  | "--mini" :: rest => do
    pure { ← parseBuild rest with mini := true }
  | "--palomar-ixc" :: value :: rest => do
    pure { ← parseBuild rest with palomarIxc? := some value }
  | arg :: _ => .error s!"unknown build argument `{arg}`"

private def inherited (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args, cwd := some cwd }
  child.wait

/-- Flushed stage banner — long phases follow, and unflushed stdout is
    lost to a watchdog kill under redirection. -/
private def stageLine (line : String) : IO Unit := Ix.progressLine line

/-- Run a heavy step under the typed watchdog's cgroup memory ceiling
    (`Ix.Watchdog.run`: whole-scope kill on breach, exit 137); `none`
    runs it bare (`--no-watchdog`). -/
private def watched (ceiling? : Option Nat) (cmd : String)
    (args : Array String) (cwd : System.FilePath) : IO UInt32 := do
  match ceiling? with
  | none => inherited cmd args cwd
  | some ceiling => Ix.Watchdog.run ceiling cmd args (some cwd)

private def reportOom (exit : UInt32) (ceiling? : Option Nat)
    (step : String) : IO Unit := do
  if exit == Ix.Watchdog.oomExitCode then
    if let some ceiling := ceiling? then
      IO.eprintln s!"{step} hit the {ceiling} GiB memory ceiling (cgroup \
OOM kill, whole scope). Rerun with a higher --ceiling-gb, more RAM, or a \
smaller corpus — the box itself was protected."

/-- The member's catalog record; fail closed on a spec/records drift
    (the `truthmines-spec` suite pins coherence, but the driver must
    not silently build a member it cannot attribute). -/
private def recordOf (lib : CatalogSpecLib) : IO PackageSpec := do
  match catalog.find? (·.qualifier == lib.qualifier) with
  | some record => return record
  | none => throw (IO.userError
      s!"no catalog record for admitted qualifier `{lib.qualifier}`")

/-- Source pin string for the manifest: `git:<url>@<rev>`, empty for
    local fixture packages (the plan's convention). -/
private def pinOf (record : PackageSpec) : String :=
  match record.source with
  | .git source => s!"git:{source.url}@{source.rev}"
  | .local _ => ""

/-- The piece cache key: everything whose change must force a member
    recompile — the member's transitive pin closure over the records,
    the toolchain, the ix version, and the member's roots. Local
    fixture sources contribute their path only (content edits need
    `--no-cache` or a `gen`-level change); pinned git sources are
    exact. -/
private partial def cacheKeyOf (lib : CatalogSpecLib) : IO String := do
  let record ← recordOf lib
  let mut seen : Array String := #[]
  let mut queue : Array String := #[record.lakeName]
  let mut pins : Array String := #[]
  while h : queue.size > 0 do
    let name := queue[queue.size - 1]
    queue := queue.pop
    if seen.contains name then continue
    seen := seen.push name
    let some dep := catalog.find? (·.lakeName == name)
      | throw <| IO.userError s!"member `{lib.qualifier}`: dependency \
`{name}` has no catalog record — the pin closure is incomplete"
    let pin := match dep.source with
      | .git source => s!"{dep.lakeName}@{source.rev}"
      | .local path => s!"{dep.lakeName}@local:{path}"
    pins := pins.push pin
    queue := queue ++ dep.directDeps
  let pinsSorted := pins.qsort (· < ·)
  let roots := lib.roots.map (·.toString (escape := false))
  return s!"ix={Ix.versionString};toolchain={expectedToolchain};\
roots={String.intercalate "," roots.toList};\
pins={String.intercalate "," pinsSorted.toList}"

private structure MemberOutcome where
  qualifier : String
  cached : Bool
  exit : UInt32

/-- Compile one member's piece straight into the `.ixc` directory, in
    a short-lived watchdogged `ix compile` subprocess. Fail-closed per
    member: `.tmp` + rename inside the FFI means no partial piece ever
    exists. Cache keys live under `<ixc>/.cache/` — build metadata
    inside the self-contained tree, ignored by verify. -/
private def compileMember (exe : System.FilePath) (ceiling? : Option Nat)
    (ixcDir : System.FilePath) (noCache : Bool) (lib : CatalogSpecLib) :
    IO MemberOutcome := do
  let q := lib.qualifier.toString (escape := false)
  let piece := ixcDir / s!"{q}.ixe"
  let keyPath := ixcDir / ".cache" / s!"{q}.key"
  let key ← cacheKeyOf lib
  if !noCache && (← piece.pathExists)
      && (← readIfExists keyPath) == some key then
    return { qualifier := q, cached := true, exit := 0 }
  -- A stale or absent key must not survive a failed compile.
  if ← keyPath.pathExists then IO.FS.removeFile keyPath
  let driver := driverModulePath lib.qualifier
  let args := #["compile", driver.toString, "--out", piece.toString]
  let exit ← watched ceiling? exe.toString args (← IO.currentDir)
  if exit == 0 then
    IO.FS.writeFile keyPath key
  return { qualifier := q, cached := false, exit }

/-- Bounded-parallel member compiles: at most `jobs` subprocesses in
    flight; each new member launches as a slot frees. Box-level
    pressure = jobs × per-member ceiling, never a union. -/
private def compileMembers (exe : System.FilePath) (ceiling? : Option Nat)
    (ixcDir : System.FilePath) (noCache : Bool) (jobs : Nat)
    (libs : Array CatalogSpecLib) : IO (Array MemberOutcome) := do
  let mut outcomes : Array MemberOutcome := #[]
  let mut inFlight : Array (Task (Except IO.Error MemberOutcome)) := #[]
  let mut next := 0
  let total := libs.size
  while next < total || !inFlight.isEmpty do
    while next < total && inFlight.size < jobs do
      let lib := libs[next]!
      stageLine s!"[truthmines] ({next + 1}/{total}) \
{lib.qualifier}: compiling piece…"
      inFlight := inFlight.push (← IO.asTask
        (compileMember exe ceiling? ixcDir noCache lib))
      next := next + 1
    -- Wait for the oldest in-flight member (bounded pool; completion
    -- order inside the pool does not matter for correctness).
    let some task := inFlight[0]? | break
    inFlight := inFlight.eraseIdx! 0
    let outcome ← IO.ofExcept task.get
    let status := if outcome.cached then "cached"
      else if outcome.exit == 0 then "ok" else s!"FAILED ({outcome.exit})"
    stageLine s!"[truthmines] {outcome.qualifier}: {status}"
    outcomes := outcomes.push outcome
  return outcomes

/-- Per-member dependency indices for `ix catalog assemble --deps`,
    from the records' `directDeps` restricted to this tier's members
    (dependencies outside the tier would be a spec coherence error the
    `truthmines-spec` suite rejects). -/
private def depsArgument (libs : Array CatalogSpecLib) : IO String := do
  let indexOfLake : String → Option Nat := fun lakeName =>
    (libs.zipIdx.findSome? fun (lib, i) =>
      match catalog.find? (·.qualifier == lib.qualifier) with
      | some record => if record.lakeName == lakeName then some i else none
      | none => none)
  let mut entries : Array String := #[]
  for i in [0:libs.size] do
    let record ← recordOf libs[i]!
    let mut deps : Array Nat := #[]
    for depName in record.directDeps do
      match indexOfLake depName with
      | some j =>
        if j ≥ i then
          throw <| IO.userError s!"member `{libs[i]!.qualifier}` depends \
on `{depName}` at index {j}, not strictly before {i} — spec order broken"
        deps := deps.push j
      | none =>
        throw <| IO.userError s!"member `{libs[i]!.qualifier}` depends on \
`{depName}`, which is not a member of this tier"
    if !deps.isEmpty then
      entries := entries.push
        s!"{i}:{String.intercalate "," (deps.map toString).toList}"
  return String.intercalate ";" entries.toList

/-- Preserve an imported catalog's dependency graph after appending its
members behind the native TruthMines members. -/
private def shiftedDepsArgument (offset : Nat)
    (members : Array Ix.Catalog.Member) : String := Id.run do
  let mut entries : Array String := #[]
  for i in [0:members.size] do
    let deps := members[i]!.deps.map fun dep => offset + dep.toNat
    unless deps.isEmpty do
      entries := entries.push s!"{offset + i}:{String.intercalate "," (deps.map toString).toList}"
  return String.intercalate ";" entries.toList

private def runBuild (options : BuildOptions) : IO UInt32 := do
  let tier := if options.mini then "mini" else "corpus"
  let spec := if options.mini then catalogMiniSpec else catalogSpec
  let out := options.out?.getD <|
    if options.mini then "truthmines-mini.ixc" else "truthmines.ixc"
  let stale ← stalePaths
  unless stale.isEmpty do
    IO.eprintln s!"stale generated workspace files {stale} — \
run `lake exe truthmines gen` first"
    return 1
  unless (← ixExe.pathExists) do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  if options.mini && options.palomarIxc?.isSome then
    IO.eprintln "--palomar-ixc is only valid for the full corpus"
    return 1
  let root ← IO.currentDir
  let exe ← IO.FS.realPath ixExe
  let ixcDir := root / out
  let palomar? : Option (System.FilePath × Ix.Catalog.Catalog) ←
    match options.palomarIxc? with
    | none => pure none
    | some raw => do
        let dir ← IO.FS.realPath (System.FilePath.mk raw)
        stageLine s!"[truthmines] external Palomar catalog: verifying {dir}"
        let exit ← inherited exe.toString
          #["catalog", "verify", dir.toString] root
        if exit != 0 then
          throw <| IO.userError
            s!"external Palomar catalog verification failed ({exit})"
        let external ← loadExternalCatalog dir
        let nativeLabels := spec.libs.map
          (·.qualifier.toString (escape := false))
        let mut seen := nativeLabels
        for member in external.members do
          if seen.contains member.label then
            throw <| IO.userError
              s!"external catalog label `{member.label}` collides with another member"
          seen := seen.push member.label
        pure (some (dir, external))
  -- Resolve ceilings: per-member for piece compiles, box-level for the
  -- workspace olean build. An unenforced ceiling is not a corpus run.
  let ceilings? : Option (Option Nat × Option Nat) ←
    if options.noWatchdog then
      pure (some (none, none))
    else if ← Ix.Watchdog.available then do
      let member := options.ceilingGb.getD defaultMemberCeilingGb
      pure (some (some member, some (← Ix.Watchdog.defaultCeilingGb)))
    else do
      IO.eprintln "RAM watchdog unavailable (systemd user scope with \
cgroup memory.oom.group failed the probe) — pass --no-watchdog to run \
unprotected"
      pure none
  let some (memberCeiling?, boxCeiling?) := ceilings? | return 1
  -- Parallelism: fit jobs × per-member ceiling under the box ceiling.
  let jobs := options.jobs?.getD <| match memberCeiling?, boxCeiling? with
    | some member, some box => max 1 (box / member)
    | _, _ => 1
  if let some ceiling := memberCeiling? then
    stageLine s!"[truthmines] {tier} build: {jobs} job(s) × {ceiling} GiB \
per-member ceiling (cgroup scopes, swap off; --jobs / --ceiling-gb / \
--no-watchdog to change)"
  -- Stage 1: member root oleans. First run needs network and pulls the
  -- mathlib olean cache; `cache get` failure is tolerated — the build
  -- below is authoritative.
  let buildTarget := if options.mini then #["build", "catalogMiniOleans", "Drivers"]
    else #["build", "catalogOleans", "Drivers"]
  stageLine s!"[truthmines] stage 1/4: member root oleans \
(lake exe cache get, then lake {" ".intercalate buildTarget.toList} in \
{workspaceDir}) — lake output follows"
  let _ ← inherited "lake" #["exe", "cache", "get"] workspaceDir
  let buildExit ← watched boxCeiling? "lake" buildTarget workspaceDir
  if buildExit != 0 then
    reportOom buildExit boxCeiling? s!"{tier} workspace build"
    IO.eprintln s!"{tier} workspace build failed ({buildExit})"
    return buildExit
  -- Stage 2: per-member pieces, compiled straight into the
  -- self-contained `.ixc` directory (parallel, watchdogged, cached).
  IO.FS.createDirAll (ixcDir / ".cache")
  stageLine s!"[truthmines] stage 2/4: {spec.libs.size} member pieces → \
{ixcDir} ({jobs} in flight; per-member `ix compile`, fail-closed)"
  let outcomes ← compileMembers exe memberCeiling? ixcDir
    options.noCache jobs spec.libs
  let failures := outcomes.filter (·.exit != 0)
  unless failures.isEmpty do
    for f in failures do
      reportOom f.exit memberCeiling? s!"member {f.qualifier}"
    IO.eprintln s!"[truthmines] {failures.size} member(s) failed: \
{failures.map (·.qualifier)}"
    return 1
  -- Stage 3: write the manifest in place. Native pieces are already inside
  -- the directory; external Palomar pieces are hard-linked in by assemble
  -- (copy fallback), preserving the standalone catalog's labels and pins.
  stageLine s!"[truthmines] stage 3/4: ix catalog assemble → {out}"
  let nativeLabels := spec.libs.map (·.qualifier.toString (escape := false))
  let externalLabels := match palomar? with
    | none => #[]
    | some (_, external) => external.members.map (·.label)
  let labels := nativeLabels ++ externalLabels
  let nativePiecePaths := nativeLabels.map fun q =>
    (ixcDir / s!"{q}.ixe").toString
  let externalPiecePaths := match palomar? with
    | none => #[]
    | some (dir, external) => external.members.map fun member =>
        (dir / s!"{member.label}.ixe").toString
  let piecePaths := nativePiecePaths ++ externalPiecePaths
  let nativePins ← spec.libs.mapM fun lib => return pinOf (← recordOf lib)
  let externalPins := match palomar? with
    | none => #[]
    | some (_, external) => external.members.map (·.sourcePin)
  let pins := nativePins ++ externalPins
  let nativeToolchains := Array.replicate spec.libs.size expectedToolchain
  let externalToolchains := match palomar? with
    | none => #[]
    | some (_, external) => external.members.map (·.toolchain)
  let toolchains := nativeToolchains ++ externalToolchains
  let nativeDepsArg ← depsArgument spec.libs
  let externalDepsArg := match palomar? with
    | none => ""
    | some (_, external) => shiftedDepsArgument spec.libs.size external.members
  let depsArg := if nativeDepsArg.isEmpty then externalDepsArg
    else if externalDepsArg.isEmpty then nativeDepsArg
    else nativeDepsArg ++ ";" ++ externalDepsArg
  let mut assembleArgs := #["catalog", "assemble", ixcDir.toString]
    ++ piecePaths
    ++ #["--labels", String.intercalate "," labels.toList,
         "--toolchains", String.intercalate "," toolchains.toList]
  if pins.any (!·.isEmpty) then
    assembleArgs := assembleArgs
      ++ #["--pins", String.intercalate "," pins.toList]
  if !depsArg.isEmpty then
    assembleArgs := assembleArgs ++ #["--deps", depsArg]
  let assembleExit ← inherited exe.toString assembleArgs root
  if assembleExit != 0 then
    IO.eprintln s!"[truthmines] ix catalog assemble failed ({assembleExit})"
    return assembleExit
  -- Stage 4: verify the self-contained directory (roots recomputed,
  -- every piece's env root + counts checked).
  stageLine s!"[truthmines] stage 4/4: ix catalog verify"
  let verifyExit ← inherited exe.toString
    #["catalog", "verify", ixcDir.toString] root
  if verifyExit != 0 then
    IO.eprintln s!"[truthmines] ix catalog verify failed ({verifyExit})"
    return verifyExit
  -- The `.ixc` directory is the whole deliverable and the machine-
  -- readable record (`ix catalog info`); no report artifact.
  let cached := (outcomes.filter (·.cached)).size
  let externalCount := palomar?.map (·.2.members.size) |>.getD 0
  stageLine s!"[truthmines] done — {out}: {spec.libs.size + externalCount} \
member(s) ({spec.libs.size} native + {externalCount} Palomar), {cached} native \
from cache ({tier} tier, {Ix.versionString})"
  return 0

private structure CheckOptions where
  ixc? : Option String := none
  only : Option (List String) := none
  jobs? : Option Nat := none
  mini : Bool := false

private def parseCheck : List String → Except String CheckOptions
  | [] => .ok {}
  | "--ixc" :: value :: rest => do
    pure { ← parseCheck rest with ixc? := some value }
  | "--only" :: value :: rest => do
    let qs := (value.splitOn ",").filter (!·.isEmpty)
    if qs.isEmpty then .error "--only needs at least one qualifier" else
    pure { ← parseCheck rest with only := some qs }
  | "--jobs" :: value :: rest => do
    let some n := value.toNat? | .error s!"--jobs needs a number, got `{value}`"
    if n == 0 then .error "--jobs must be at least 1" else
    pure { ← parseCheck rest with jobs? := some n }
  | "--mini" :: rest => do
    pure { ← parseCheck rest with mini := true }
  | arg :: _ => .error s!"unknown check argument `{arg}`"

/-- Per-piece kernel sweep: `ix check-rs --anon` over each member's
    piece in the `.ixc` directory. Every piece is a self-contained env
    checked in its own subprocess, so the pool's peak is one mmap'd
    member (~4–6 GiB RSS), never a union — no watchdog needed. Output
    is captured per piece and surfaced only on rejection, with the
    solo repro command for triage. -/
private def runCheck (options : CheckOptions) : IO UInt32 := do
  let tier := if options.mini then "mini" else "corpus"
  let ixc := System.FilePath.mk <| options.ixc?.getD <|
    if options.mini then "truthmines-mini.ixc" else "truthmines.ixc"
  unless (← ixExe.pathExists) do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  unless (← (ixc / "manifest").pathExists) do
    IO.eprintln s!"{ixc} has no manifest — run `lake exe truthmines \
build{if options.mini then " --mini" else ""}` first"
    return 1
  let manifest ← loadExternalCatalog ixc
  let allLabels := manifest.members.map (·.label)
  let labels ← match options.only with
    | none => pure allLabels
    | some wanted => do
      for w in wanted do
        unless allLabels.contains w do
          IO.eprintln s!"--only names `{w}`, which is not a {tier} member"
          return 1
      pure <| allLabels.filter wanted.contains
  let jobs := options.jobs?.getD 4
  let exe ← IO.FS.realPath ixExe
  stageLine s!"[truthmines] check: {labels.size} piece(s), {jobs} in flight \
({tier} tier; per-piece `ix check-rs --anon` over {ixc})"
  let runOne (q : String) : IO (MemberOutcome × String) := do
    let piece := ixc / s!"{q}.ixe"
    unless (← piece.pathExists) do
      return ({ qualifier := q, cached := false, exit := 2 },
        s!"piece {piece} missing — stale manifest or partial build")
    let out ← IO.Process.output {
      cmd := exe.toString
      args := #["check-rs", piece.toString, "--anon"]
      env := #[("IX_MAX_REC_FUEL", some "1000000000")] }
    let tail := if out.exitCode == 0 then "" else
      s!"── {q} stderr (first 4000) ──\n{out.stderr.take 4000}\n\
── {q} stdout (last 1000) ──\n{(out.stdout.takeEnd 1000).toString}"
    return ({ qualifier := q, cached := false, exit := out.exitCode }, tail)
  let mut pending := labels.toList
  let mut inFlight : Array (Task (Except IO.Error (MemberOutcome × String))) := #[]
  let mut failures : List String := []
  let mut passed := 0
  while !pending.isEmpty || !inFlight.isEmpty do
    while !pending.isEmpty && inFlight.size < jobs do
      let q := pending.head!
      pending := pending.tail!
      stageLine s!"[truthmines] checking {q}…"
      inFlight := inFlight.push (← IO.asTask (runOne q))
    let some task := inFlight[0]? | break
    inFlight := inFlight.eraseIdx! 0
    let (outcome, tail) ← IO.ofExcept task.get
    if outcome.exit == 0 then
      passed := passed + 1
      stageLine s!"[truthmines] {outcome.qualifier}: kernel ok"
    else
      failures := failures ++ [s!"{outcome.qualifier} ({outcome.exit})"]
      let piece := ixc / s!"{outcome.qualifier}.ixe"
      stageLine s!"[truthmines] {outcome.qualifier}: kernel REJECTED \
({outcome.exit}) — rerun solo: IX_MAX_REC_FUEL=1000000000 \
{ixExe} check-rs {piece} --anon"
      unless tail.isEmpty do IO.eprintln tail
  stageLine s!"[truthmines] check done: {passed}/{labels.size} piece(s) \
kernel-clean{if failures.isEmpty then "" else s!"; failed: {failures}"}"
  return if failures.isEmpty then 0 else 1

private structure ValidateOptions where
  only : Option (List String) := none
  jobs? : Option Nat := none
  ceilingGb : Option Nat := none
  noWatchdog : Bool := false
  mini : Bool := false

private structure ValidationLib where
  qualifier : String
  driver : System.FilePath
deriving Inhabited

private def parseValidate : List String → Except String ValidateOptions
  | [] => .ok {}
  | "--only" :: value :: rest => do
    let qs := (value.splitOn ",").filter (!·.isEmpty)
    if qs.isEmpty then .error "--only needs at least one qualifier" else
    pure { ← parseValidate rest with only := some qs }
  | "--jobs" :: value :: rest => do
    let some n := value.toNat? | .error s!"--jobs needs a number, got `{value}`"
    if n == 0 then .error "--jobs must be at least 1" else
    pure { ← parseValidate rest with jobs? := some n }
  | "--ceiling-gb" :: value :: rest => do
    let some gb := value.toNat? | .error s!"--ceiling-gb needs a number, got `{value}`"
    pure { ← parseValidate rest with ceilingGb := some gb }
  | "--no-watchdog" :: rest => do
    pure { ← parseValidate rest with noWatchdog := true }
  | "--mini" :: rest => do
    pure { ← parseValidate rest with mini := true }
  | arg :: _ => .error s!"unknown validate argument `{arg}`"

/-- Per-library metadata-fidelity sweep: the 8-phase `ix validate` pipeline
    over each native member's `Benchmarks/Compile` driver plus Palomar.ix as
    one aggregate library in the full tier. Exit-code gated (the validator's
    phase table goes to stdout); no artifacts. -/
private def runValidate (options : ValidateOptions) : IO UInt32 := do
  let tier := if options.mini then "mini" else "corpus"
  let spec := if options.mini then catalogMiniSpec else catalogSpec
  let stale ← stalePaths
  unless stale.isEmpty do
    IO.eprintln s!"stale generated workspace files {stale} — \
run `lake exe truthmines gen` first"
    return 1
  unless (← ixExe.pathExists) do
    IO.eprintln s!"{ixExe} missing — run `lake build ix` first"
    return 1
  let available := spec.libs.map fun lib => {
    qualifier := lib.qualifier.toString (escape := false)
    driver := compileMemberModulePath lib.qualifier
  }
  let available := if options.mini then available else available.push {
    qualifier := "Palomar"
    driver := compilePalomarModulePath
  }
  let libs ← match options.only with
    | none => pure available
    | some wanted => do
      for w in wanted do
        unless available.any (·.qualifier == w) do
          IO.eprintln s!"--only names `{w}`, which is not a {tier} library"
          return 1
      pure <| available.filter fun lib => wanted.contains lib.qualifier
  let ceiling? : Option Nat ←
    if options.noWatchdog then
      pure none
    else if ← Ix.Watchdog.available then
      match options.ceilingGb with
      | some gb => pure (some gb)
      | none => pure (some (← Ix.Watchdog.defaultCeilingGb))
    else do
      IO.eprintln "RAM watchdog unavailable — pass --no-watchdog to run \
unprotected"
      return 1
  -- Validation holds two compile states plus a decompile state at
  -- mathlib scale: one member at a time under the box ceiling is the
  -- safe default. Validation must never race separate Lake builds against
  -- the shared package store: prebuild every selected driver in one Lake
  -- process, then tell each validator to skip its implicit build. This also
  -- makes the single-job path use the same deterministic boundary.
  let jobs := options.jobs?.getD 1
  stageLine s!"[truthmines] prebuilding {libs.size} selected driver(s) in one Lake process…"
  let buildArgs := #["build"] ++ libs.map fun lib => s!"Members.{lib.qualifier}"
  let buildExit ← watched ceiling? "lake" buildArgs compileWorkspaceDir
  if buildExit != 0 then
    reportOom buildExit ceiling? "validate prebuild"
    IO.eprintln s!"selected-driver prebuild failed ({buildExit})"
    return 1
  let exe ← IO.FS.realPath ixExe
  let root ← IO.currentDir
  stageLine s!"[truthmines] validate: {libs.size} libraries, {jobs} in \
flight ({tier} tier; 8-phase ix validate per Benchmarks/Compile driver)"
  let runOne (lib : ValidationLib) : IO MemberOutcome := do
    let exit ← watched ceiling? exe.toString
      #["validate", lib.driver.toString, "--no-build"] root
    return { qualifier := lib.qualifier, cached := false, exit }
  let mut pending := libs.toList
  let mut inFlight : Array (Task (Except IO.Error MemberOutcome)) := #[]
  let mut failures : List String := []
  let mut passed := 0
  while !pending.isEmpty || !inFlight.isEmpty do
    while !pending.isEmpty && inFlight.size < jobs do
      let lib := pending.head!
      pending := pending.tail!
      stageLine s!"[truthmines] validating {lib.qualifier}…"
      inFlight := inFlight.push (← IO.asTask (runOne lib))
    let some task := inFlight[0]? | break
    inFlight := inFlight.eraseIdx! 0
    let outcome ← IO.ofExcept task.get
    if outcome.exit == 0 then
      passed := passed + 1
      stageLine s!"[truthmines] {outcome.qualifier}: fidelity ok"
    else
      reportOom outcome.exit ceiling? s!"validate {outcome.qualifier}"
      failures := failures ++ [s!"{outcome.qualifier} ({outcome.exit})"]
      stageLine s!"[truthmines] {outcome.qualifier}: fidelity FAILED \
({outcome.exit})"
  stageLine s!"[truthmines] validate done: {passed}/{libs.size} libraries \
clean{if failures.isEmpty then "" else s!"; failed: {failures}"}"
  return if failures.isEmpty then 0 else 1

private def runSpec (mini : Bool) : IO UInt32 := do
  let spec := if mini then catalogMiniSpec else catalogSpec
  for lib in spec.libs do
    let driver := driverModulePath lib.qualifier
    let roots := lib.roots.map (·.toString (escape := false))
    IO.println s!"{lib.qualifier}\t{driver}\t{String.intercalate "," roots.toList}"
  return 0

def main (args : List String) : IO UInt32 := do
  unless (← (("Benchmarks" : System.FilePath) / "TruthMinesSpec").pathExists) do
    IO.eprintln "run `lake exe truthmines` from the ix repo root"
    return 1
  match args with
  | ["gen"] => runGen (check := false)
  | ["gen", "--check"] => runGen (check := true)
  | ["spec"] => runSpec (mini := false)
  | ["spec", "--mini"] => runSpec (mini := true)
  | "build" :: rest =>
    match parseBuild rest with
    | .ok options => runBuild options
    | .error message => IO.eprintln message; IO.eprintln usage; return 1
  | "check" :: rest =>
    match parseCheck rest with
    | .ok options => runCheck options
    | .error message => IO.eprintln message; IO.eprintln usage; return 1
  | "validate" :: rest =>
    match parseValidate rest with
    | .ok options => runValidate options
    | .error message => IO.eprintln message; IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
