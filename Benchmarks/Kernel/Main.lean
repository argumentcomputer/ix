/-
  Comparative kernel benchmark.

  Measures wall-clock time for typechecking declarations across multiple
  kernel implementations. Supports checking a single declaration
  (and its transitive deps) or an entire module.

  Checkers:
    - lean4:     Lean 4 C++ kernel (Kernel.Environment.addDeclCore)
    - lean4lean: lean4lean Lean reimplementation (Lean4Lean.addDecl)
    - nanoda:    Rust external checker (subprocess)
    - ix-lean:   Ix Lean NbE kernel (Ix.Kernel.typecheckAll)
    - ix-rust:   Ix Rust NbE kernel (Ix.Kernel.rsCheckEnv via FFI)
-/
import Cli
import Lean
import Lean4Checker.Replay
import Lean4Lean.Environment
import Ix.Meta
import Ix.Kernel
import Ix.Kernel.Convert
import Ix.CompileM
import Ix.Benchmark.Bench

/-! ## Helpers -/

def mkGroupName (target : String) : String := s!"compare-checkers/{target}"

/-- Project root (Benchmarks/Kernel/), resolved at compile time. -/
def projectDir : System.FilePath :=
  (this_file!).parent.getD "."

/-- Local deps directory for non-Lake dependencies (nanoda, lean4export). -/
def depsDir : System.FilePath :=
  projectDir / "deps"

/-- Collect the transitive dependency closure of a declaration. -/
partial def collectDeps (name : Lean.Name) (consts : Lean.ConstMap)
    (visited : Lean.NameSet := {}) : Lean.NameSet :=
  if visited.contains name then visited
  else
    let visited := visited.insert name
    match consts.find? name with
    | none => visited
    | some ci =>
      ci.getUsedConstantsAsSet.foldl (init := visited) fun acc dep =>
        collectDeps dep consts acc

/-! ## lean4lean replay (Lean4Lean.addDecl) -/

namespace L4LReplay

structure Context where
  newConstants : Std.HashMap Lean.Name Lean.ConstantInfo
  verbose : Bool := false

structure State where
  env : Lean.Kernel.Environment
  remaining : Lean.NameSet := {}
  pending : Lean.NameSet := {}
  numAdded : Nat := 0
  hasStrings : Bool := false

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Lean.Name) : M Bool := do
  if (← get).remaining.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def throwKernelException (ex : Lean.Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

def addDecl (d : Lean.Declaration) : M Unit := do
  if (← read).verbose then
    for name in d.getNames do
      IO.println s!"  adding {name}"
  match Lean4Lean.addDecl (← get).env d true with
  | .ok env => modify fun s => { s with env, numAdded := s.numAdded + 1 }
  | .error ex => throwKernelException ex

private def hasStrLitExpr (e : Lean.Expr) : Bool := (e.find? Lean.Expr.isStringLit).isSome

private def hasStrLitCI (ci : Lean.ConstantInfo) : Bool :=
  hasStrLitExpr ci.type || ci.value?.any hasStrLitExpr

mutual
partial def replayConstant (name : Lean.Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    let mut deps := ci.getUsedConstantsAsSet
    -- String literals need String.ofList and Char.ofNat available
    unless (← get).hasStrings do
      if hasStrLitCI ci then
        deps := deps.insert ``String.ofList
        deps := deps.insert ``Char.ofNat
        modify ({ · with hasStrings := true })
    replayConstants deps
    if (← get).pending.contains name then
      match ci with
      | .defnInfo v   => addDecl (.defnDecl v)
      | .thmInfo v    => addDecl (.thmDecl v)
      | .axiomInfo v  => addDecl (.axiomDecl v)
      | .opaqueInfo v => addDecl (.opaqueDecl v)
      | .inductInfo info =>
        let all ← info.all.mapM fun n => do pure (← read).newConstants[n]!
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun c => do
          pure (c, ← c.inductiveVal!.ctors.mapM fun n => do pure (← read).newConstants[n]!)
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List Lean.InductiveType := ctorInfo.map fun ⟨c, ctors⟩ =>
          { name := c.name, type := c.type,
            ctors := ctors.map fun ct => { name := ct.name, type := ct.type } }
        addDecl (.inductDecl info.levelParams info.numParams types false)
      | .ctorInfo _ => pure ()
      | .recInfo _ => pure ()
      | .quotInfo _ => addDecl .quotDecl
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : Lean.NameSet) : M Unit := do
  for n in names do replayConstant n
end

/-- Replay all constants from scratch using lean4lean's kernel.
    Returns the number of declarations checked. -/
def replay (constMap : Std.HashMap Lean.Name Lean.ConstantInfo) (verbose : Bool := false) : IO Nat := do
  let mut remaining : Lean.NameSet := {}
  for (n, ci) in constMap.toList do
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let freshEnv ← Lean.mkEmptyEnvironment
  let kenv := freshEnv.toKernelEnv
  let (_, s) ← StateRefT'.run (s := { env := kenv, remaining }) do
    ReaderT.run (r := { newConstants := constMap, verbose }) do
      for n in remaining do
        replayConstant n
  pure s.numAdded

end L4LReplay

/-! ## Checkers -/

/-- lean4: Replay constants using the C++ kernel (`Kernel.Environment.addDeclCore`)
    via lean4checker's `replay'`. Setup (import, dep collection) is not timed;
    only `replay'` is measured by `oneShotBench`. -/
def benchLean4 (group : String) (constMap : Std.HashMap Lean.Name Lean.ConstantInfo)
    (verbose : Bool) : IO BenchReport := do
  IO.println s!"[lean4] Typechecking {constMap.size} constants via C++ kernel..."
  if verbose then
    for (name, _) in constMap.toList do
      IO.println s!"  {name}"
  oneShotBench group
    (benchIO "lean4" (fun _ => do
      let freshEnv ← Lean.mkEmptyEnvironment
      let _ ← freshEnv.replay' constMap) ())
    { oneShot := true }

/-- lean4lean: Replay constants using lean4lean's Lean kernel (`Lean4Lean.addDecl`).
    Setup is not timed; only `L4LReplay.replay` is measured by `oneShotBench`. -/
def benchLean4Lean (group : String) (constMap : Std.HashMap Lean.Name Lean.ConstantInfo)
    (verbose : Bool) : IO BenchReport := do
  IO.println s!"[lean4lean] Typechecking {constMap.size} constants via lean4lean kernel..."
  oneShotBench group
    (benchIO "lean4lean" (fun _ => do
      let _ ← L4LReplay.replay constMap verbose) ())
    { oneShot := true }

/-- nanoda: Run nanoda as a subprocess. Export generation and config writing
    happen as setup before `oneShotBench`; only the nanoda invocation is timed. -/
def benchNanoda (group : String) (target : String) (isModule : Bool) (modName : String) (threads : String) : IO BenchReport := do
  let nanodaBin := depsDir / "nanoda_lib" / "target" / "release" / "nanoda_bin"
  let nanodaDir := depsDir / "nanoda_lib"
  let configPath := nanodaDir / "bench-config.json"
  let exportDir := depsDir / "lean4export"
  let exportBin := exportDir / ".lake" / "build" / "bin" / "lean4export"
  -- Generate a target-specific export file (not timed)
  let exportFile := nanodaDir / "bench.export"
  let exportArgs := if isModule then
    #[target]
  else
    -- lean4export supports: lean4export <module> -- <const1> <const2> ...
    -- It transitively dumps all deps of the specified constants
    #[modName, "--", target]
  IO.println s!"[nanoda] Generating export file for {target}..."
  let genResult ← IO.Process.output {
    cmd := "lake"
    args := #["env", exportBin.toString] ++ exportArgs
    cwd := exportDir
  }
  if genResult.exitCode != 0 then
    IO.eprintln s!"[nanoda] Export generation failed:\n{genResult.stderr}"
    return { function := "nanoda", newBench := .oneShot ⟨0⟩, baseBench := none, percentChange := none }
  IO.FS.writeFile exportFile genResult.stdout
  -- Configure nanoda (not timed)
  IO.FS.writeFile configPath s!"\{
    \"export_file_path\": \"{exportFile}\",
    \"permitted_axioms\": [\"propext\", \"Classical.choice\", \"Quot.sound\", \"Lean.trustCompiler\"],
    \"unpermitted_axiom_hard_error\": false,
    \"nat_extension\": true,
    \"string_extension\": true,
    \"num_threads\": {threads},
    \"print_success_message\": true
}"
  IO.println s!"[nanoda] Running nanoda (threads={threads})..."
  oneShotBench group
    (benchIO s!"nanoda(j={threads})" (fun _ => do
      let result ← IO.Process.output { cmd := nanodaBin.toString, args := #[configPath.toString] }
      if result.exitCode != 0 then
        IO.eprintln s!"[nanoda] FAILED (exit {result.exitCode}):\n{result.stderr}"
      else
        for line in result.stdout.splitOn "\n" do
          if line.containsSubstr "Checked" then IO.println s!"[nanoda] {line.trim}") ())
    { oneShot := true }

/-- ix-lean: Ix Lean NbE kernel. Compile + convert are setup (not timed);
    only `typecheckAllIO` is measured by `oneShotBench`. -/
def benchIxLean (group : String) (constList : List (Lean.Name × Lean.ConstantInfo)) (verbose : Bool) : IO BenchReport := do
  IO.println s!"[ix-lean] Compiling {constList.length} constants to Ixon..."
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  let ixonEnv := rawEnv.toEnv
  IO.println s!"[ix-lean] Converting Ixon -> Kernel types..."
  let (kenv, prims, quotInit) ← match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .ok v => pure v
    | .error e => throw (IO.userError s!"[ix-lean] Conversion error: {e}")
  IO.println s!"[ix-lean] Typechecking {kenv.size} constants..."
  oneShotBench group
    (benchIO "ix-lean" (fun _ => do
      match ← Ix.Kernel.typecheckAllIO kenv prims quotInit verbose with
      | .ok () => pure ()
      | .error e => throw (IO.userError s!"[ix-lean] typecheck failed: {e}")) ())
    { oneShot := true }

/-- ix-rust: Ix Rust NbE kernel via FFI.
    Note: rsCheckEnvFFI internally includes compile + convert time. -/
@[extern "ix_set_verbose"]
private opaque setVerbose : @& Bool → IO Unit

def benchIxRust (group : String) (constList : List (Lean.Name × Lean.ConstantInfo))
    (verbose : Bool) (threads : String) : IO BenchReport := do
  IO.println s!"[ix-rust] Running Rust NbE kernel on {constList.length} constants (threads={threads})..."
  setVerbose verbose
  oneShotBench group
    (benchIO s!"ix-rust(j={threads})" (fun _ => do
      let errors ← Ix.Kernel.rsCheckEnvFFI constList
      if !errors.isEmpty then
        IO.eprintln s!"[ix-rust] {errors.size} error(s)") ())
    { oneShot := true }

/-! ## CLI -/

def allCheckers : Array String :=
  #["lean4", "lean4lean", "nanoda", "ix-lean", "ix-rust"]

def defaultCheckers : Array String := allCheckers

def runBench (p : Cli.Parsed) : IO UInt32 := do
  let target := (p.flag? "target" |>.map (·.as! String)).getD "Nat.add_comm"
  let verbose := p.hasFlag "verbose"
  let checkerList := (p.flag? "checkers" |>.map (·.as! String)).getD
    (String.intercalate "," defaultCheckers.toList)
  let checkers := checkerList.splitOn "," |>.map String.trim |>.toArray
    |>.filter allCheckers.contains

  -- Thread count: CLI flag > env var > nproc
  let threads ← match p.flag? "threads" |>.map (·.as! Nat) with
    | some n => pure (toString n)
    | none => do
      let out ← IO.Process.output { cmd := "nproc" }
      pure out.stdout.trim

  IO.println s!"Target: {target}"
  IO.println s!"Checkers: {checkers.toList}"
  IO.println s!"Threads: {threads}"
  IO.println ""

  -- Determine if the target is a module or a declaration.
  -- If --from is passed, the target is a declaration within that module.
  -- Otherwise, auto-detect: if an olean exists for the target name, it's a module.
  let targetName := target.toName
  Lean.initSearchPath (← Lean.findSysroot)
  let moduleSource := p.flag? "from" |>.map (·.as! String |>.toName)
  let isModule := moduleSource.isNone &&
    (← do try pure (← (← Lean.findOLean targetName).pathExists) catch _ => pure false)
  let modName := if isModule then targetName else moduleSource.getD `Init

  IO.println s!"Loading {modName}..."
  let env ← Lean.importModules #[{ module := modName }] {}

  -- Validate declaration exists
  if !isModule then
    unless env.constants.contains targetName do
      IO.eprintln s!"Declaration '{targetName}' not found in {modName}."
      -- Suggest --from based on the first component of the name
      let firstComponent := targetName.getRoot
      if firstComponent != .anonymous && firstComponent != modName then
        IO.eprintln s!"Try: --from {firstComponent}"
      else
        IO.eprintln s!"Hint: use --from <module> if the declaration is not in {modName}."
      return 1

  -- Build constant list
  let constList : List (Lean.Name × Lean.ConstantInfo) :=
    if isModule then
      env.constants.map₁.toList
    else
      let deps := collectDeps targetName env.constants
      deps.foldl (init := []) fun acc name =>
        match env.constants.find? name with
        | some ci => (name, ci) :: acc
        | none => acc

  let mut constMap : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for (name, ci) in constList do
    constMap := constMap.insert name ci

  IO.println s!"Scope: {if isModule then "module" else "declaration"} ({constList.length} constants)"
  IO.println ""

  let group := mkGroupName target
  let mut reports : Array BenchReport := #[]

  if checkers.contains "lean4" then
    reports := reports.push (← benchLean4 group constMap verbose)
    IO.println ""

  if checkers.contains "lean4lean" then
    reports := reports.push (← benchLean4Lean group constMap verbose)
    IO.println ""

  if checkers.contains "nanoda" then
    reports := reports.push (← benchNanoda group target isModule modName.toString threads)
    IO.println ""

  if checkers.contains "ix-lean" then
    reports := reports.push (← benchIxLean group constList verbose)
    IO.println ""

  if checkers.contains "ix-rust" then
    reports := reports.push (← benchIxRust group constList verbose threads)
    IO.println ""

  if reports.isEmpty then
    IO.println "No checkers were run."
  else
    let table := mkReportPretty group reports
    IO.println table
    IO.FS.writeFile "benchmark-report-compare-checkers.md" table
    IO.println "Report written to benchmark-report-compare-checkers.md"

  return 0

def benchCmd : Cli.Cmd := `[Cli|
  "bench-kernel" VIA runBench;
  "Compare kernel performance across implementations"

  FLAGS:
    t, target : String;   "Declaration or module to check (default: Nat.add_comm)"
    c, checkers : String; "checkers. Options: lean4,lean4lean,nanoda,ix-lean,ix-rust (default: all)"
    «from» : String; "Module to load when target is a declaration (default: Init)"
    v, verbose;           "Verbose output (per-constant timing)"
    j, threads : Nat;     "Thread count for parallel checkers: nanoda, ix-rust (default: nproc; 1 = single-threaded)"
]

def main (args : List String) : IO UInt32 :=
  benchCmd.validate args
