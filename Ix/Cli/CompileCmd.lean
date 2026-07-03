module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.Meta
public import Ix.Cli.ConstsFile
public import Ix.Cli.ValidateCmd

public section

open System (FilePath)

private def defaultOutPathFor (pathStr : String) : String :=
  let path := FilePath.mk pathStr
  let stem := path.fileStem.getD (path.fileName.getD pathStr)
  stem.toLower ++ ".ixe"

def runCompileCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.positionalArg? "path"
    | p.printError "error: must specify <path> to a Lean source file"
      return 1
  let pathStr := path.as! String
  let outPath : String :=
    (p.flag? "out").map (·.as! String) |>.getD (defaultOutPathFor pathStr)

  buildFile pathStr
  let leanEnv ← getFileEnv pathStr

  println! "Running Ix compiler on {pathStr}"

  -- Build the exclusion set from `--exclude` (comma-separated) +
  -- `--exclude-file` (one per line). Names in this set are stripped
  -- from the seed list before transitive closure; if no other seed
  -- references them, they don't make it into the compiled env. Note
  -- the exclusion only affects the SEED set, not the closure — a
  -- referenced excluded name still gets pulled in via deps.
  let excludeSet : Std.HashSet Lean.Name ← do
    let mut s : Std.HashSet Lean.Name := {}
    if let some flag := p.flag? "exclude" then
      for n in parsePrefixes (flag.as! String) do s := s.insert n
    if let some flag := p.flag? "exclude-file" then
      -- Shared names-file grammar (Ix.Cli.ConstsFile); names resolve here
      -- via `toName` like the `--exclude` comma-list.
      for n in ← Ix.Cli.ConstsFile.read (flag.as! String) do
        s := s.insert n.toName
    pure s
  if !excludeSet.isEmpty then
    IO.println s!"[compile] exclude: {excludeSet.size} name(s) will be dropped from seed set"

  -- Optional `--module Foo.Bar,Baz` filter. Filters by the SOURCE MODULE
  -- a constant came from (via `Lean.Environment.getModuleIdxFor?` +
  -- `allImportedModuleNames`), not by the constant's own name. This
  -- catches consts whose name doesn't carry the namespace prefix —
  -- e.g. macro-emitted decls like `good_def basicDef : Type := Prop`
  -- inside `namespace Tests.Ix.Kernel.TutorialDefs` that register
  -- under bare `basicDef`. The module that elaborated them is
  -- `Tests.Ix.Kernel.TutorialDefs`, so the prefix still matches.
  -- Seeds pass through `collectDeps` for the transitive-dep closure.
  -- Flag name is `--module` (not `--ns`) because the match is against
  -- the source module name, not the decl's own namespace.
  -- `--consts` / `--consts-file`: seed by EXACT constant name, transitive
  -- deps via `collectDeps` — a closure-only env (e.g. one benchmark constant
  -- + deps) instead of the whole import env. Resolution tries `String.toName`
  -- first, then a displayed-form scan so `_private`/numeric components
  -- round-trip. Mutually exclusive with `--module`; `--exclude` doesn't
  -- apply (the seed list is already explicit).
  let constsSeeds ← Ix.Cli.ConstsFile.gather p
  if !constsSeeds.isEmpty && (p.flag? "module").isSome then
    p.printError "error: --consts/--consts-file and --module are mutually exclusive"
    return 1
  let constList ←
    if !constsSeeds.isEmpty then do
      let mut seeds : List Lean.Name := []
      let mut missing : List String := []
      for n in constsSeeds do
        let name := n.toName
        if leanEnv.constants.contains name then
          seeds := name :: seeds
        else
          match leanEnv.constants.toList.find? (fun (m, _) => toString m == n) with
          | some (m, _) => seeds := m :: seeds
          | none => missing := n :: missing
      if !missing.isEmpty then
        p.printError s!"error: no constant(s) named {missing} in the environment"
        return 1
      IO.println s!"[compile] consts: {seeds.length} seed constant(s)"
      let closed := collectDeps leanEnv seeds
      IO.println s!"[compile] consts: {closed.length} constants after transitive-dep closure"
      pure closed
    else match p.flag? "module" with
    | none =>
      if excludeSet.isEmpty then pure leanEnv.constants.toList
      else
        let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
          if excludeSet.contains n then none else some n
        IO.println s!"[compile] exclude applied to full env: {seeds.length} seed constants"
        pure (collectDeps leanEnv seeds)
    | some flag =>
      let raw := flag.as! String
      let prefixes := parsePrefixes raw
      if prefixes.isEmpty then
        IO.println s!"[compile] warning: --module '{raw}' parsed to empty list; compiling full env"
        pure leanEnv.constants.toList
      else
        let moduleNames := leanEnv.allImportedModuleNames
        let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
          if excludeSet.contains n then none
          else match leanEnv.getModuleIdxFor? n with
          | none => none  -- locally-elaborated, no module — drop under `--ns`
          | some idx =>
            let mod := moduleNames[idx.toNat]!
            if prefixes.any (·.isPrefixOf mod) then some n else none
        IO.println s!"[compile] filter: {prefixes.length} module-prefix(es), {seeds.length} seed constants"
        let closed := collectDeps leanEnv seeds
        IO.println s!"[compile] filter: {closed.length} constants after transitive-dep closure"
        pure closed

  let totalConsts := constList.length
  println! "Total constants: {totalConsts}"

  let start ← IO.monoMsNow
  let bytes ← Ix.CompileM.rsCompileEnvBytesFFI constList
  let elapsed := (← IO.monoMsNow) - start

  println! "Compiled {fmtBytes bytes.size} env in {elapsed.formatMs}"
  -- Machine-readable line for CI benchmark tracking
  IO.println s!"##benchmark## {elapsed} {bytes.size} {totalConsts}"

  -- Persist the serialized IxonEnv (`Env::put` bytes) to disk so subsequent
  -- runs (e.g. `ix check-ixon`) can skip the Lean → IxOn compile step. The
  -- resulting file is the canonical streaming format produced by
  -- `Ixon.Env::put` (see `src/ix/ixon/serialize.rs:1093-1297`); it round-trips
  -- through `Ixon.Env::get`.
  let writeStart ← IO.monoMsNow
  IO.FS.writeBinFile outPath bytes
  let writeMs := (← IO.monoMsNow) - writeStart
  println! "Wrote {fmtBytes bytes.size} to {outPath} in {writeMs.formatMs}"
  return 0


def compileCmd : Cli.Cmd := `[Cli|
  compile VIA runCompileCmd;
  "Compile Lean file to Ixon"

  FLAGS:
    out            : String; "Output path for serialized Ixon.Env bytes; defaults to the lowercased input file stem with `.ixe` (e.g. CompileMathlib.lean -> compilemathlib.ixe)"
    consts         : String; "Comma-separated EXACT constant names to compile (transitive deps pulled in automatically) instead of the whole import env — e.g. `Nat.add_comm`. Same flag/shape as `ix check --consts`. Mutually exclusive with --module; --exclude does not apply."
    "consts-file"  : String; "Additionally read seed constant names from a file (one per line; `#` comments and blank lines ignored). Unions with --consts."
    module         : String; "Comma-separated module-name prefixes to filter on (e.g. 'Tests.Ix.Kernel.TutorialDefs,Tests.Ix.Kernel.NatReduction'). Match is against the SOURCE MODULE a constant came from (via `Lean.Environment.getModuleIdxFor?`), not the constant's own name — so macro-emitted decls that register under unqualified names still get caught when their host module's name matches. Transitive deps are pulled in automatically."
    exclude        : String; "Comma-separated exact Lean.Name(s) to strip from the seed set. Excluded names that are still referenced by another seed will reappear via the transitive-dep closure."
    "exclude-file" : String; "Path to a file with one Lean.Name per line to strip from the seed set. Same semantics as --exclude; same line format as `ix check --consts-file`."

  ARGS:
    path : String; "Path to the Lean source file to compile."
]

end
