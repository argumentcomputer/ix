/-
  `ix codegen`: write the IxVM kernel, the MultiStark recursive
  verifier, and the ixAggr aggregation system as Rust source files via
  the Bytecode → Rust codegen pass.

  Output paths are fixed at compile time:
  - `crates/ixvm-codegen/src/aiur_ixvm.rs` (the IxVM kernel)
  - `crates/ixvm-codegen/src/aiur_multi_stark.rs` (the recursive verifier)
  - `crates/ixvm-codegen/src/aiur_ix_aggr.rs` (the heterogeneous aggregator)
  The generated files are the single destinations; no flag overrides.

  Output per target: a Rust module body containing one `fn aiur_fn_N(...)`
  per Aiur function, plus per-fn `IN_N` / `OUT_N` / `INPUT_SIZE_N`
  size constants and the dispatch entry `execute_generated`. The two
  files never collide — each is its own Rust module, and every
  generated item is module-scoped.

  Before integrating into the build pipeline:
  1. Generate code for a single small Aiur fn (e.g. `klimbs_add`).
  2. Drop the generated source into a Rust test crate.
  3. Run both backends (`execute_generated` vs the interpreter
     `execute::execute`) on identical input.
  4. Diff the resulting `QueryRecord`. Any divergence ⇒ invalid
     witnesses ⇒ proving fails hard.

  Only after parity is confirmed should this be wired into the main
  ix build pipeline as a build-script step.
-/
module
public import Cli
public import Ix.Aggr
public import Ix.Aiur.Compiler
public import Ix.Aiur.Stages.Codegen
public import Ix.Aiur.Stages.TraceReport
public import Ix.Aiur.Stages.TraceCodegen
public import Ix.Aiur.Stages.TraceCuda
public import Ix.IxVM
public import Ix.IxVM.Toplevel
public import Ix.MultiStark

public section

namespace Ix.Cli.CodegenCmd

open Aiur

/-- One codegen target: a human label, the Aiur toplevel to compile, and the
    fixed destination path (compile-time constant, no CLI override). -/
structure Target where
  label : String
  source : Except Aiur.Global Aiur.Source.Toplevel
  outPath : String
  groups : Array (String × Array String)

def targets : List Target := [
  -- the generated kernel is the kernel. Every consumer of
  -- `execute_ixvm` must select the SAME toplevel for its function-index
  -- table (CheckCmd / ProveCmd / VerifyCmd), or `funIdx` lookups
  -- resolve against a different function set than the generated code.
  { label := "ixvm", source := IxVM.ixVM,
    outPath := "crates/ixvm-codegen/src/aiur_ixvm.rs", groups := IxVM.functionGroups },
  { label := "multi-stark", source := MultiStark.multiStark,
    outPath := "crates/ixvm-codegen/src/aiur_multi_stark.rs",
    groups := MultiStark.verifierFunctionGroups },
  -- `ix aggregate` proving/verification must select the SAME toplevel for its
  -- function-index table (`Aggr.ixAggr`), or `ix_aggr` lookups resolve
  -- against a different function set than the generated code.
  { label := "ix-aggr", source := Aggr.ixAggr,
    outPath := "crates/ixvm-codegen/src/aiur_ix_aggr.rs", groups := Aggr.functionGroups }
]

/-- Emit one target. In `--check` mode, compares against the on-disk file
    without writing; otherwise writes. Returns `false` on any failure
    (source/compile error, missing or stale file in check mode). -/
def emitTarget (checkOnly : Bool) (t : Target) : IO Bool := do
  let src ← match t.source with
    | .ok src => pure src
    | .error e => IO.eprintln s!"{t.label} source error: {repr e}"; return false
  let compiled ← match src.compile with
    | .ok c => pure c
    | .error e => IO.eprintln s!"{t.label} Aiur compile error: {e}"; return false
  let rustSource := Aiur.Codegen.emit compiled.bytecode
  if checkOnly then
    -- CI mode: compare emitted source against the on-disk file.
    -- Does not write.
    let existing ← try
      pure (some (← IO.FS.readFile t.outPath))
    catch _ => pure none
    match existing with
    | none =>
      IO.eprintln s!"[codegen --check] {t.outPath} missing"
      return false
    | some onDisk =>
      if onDisk == rustSource then
        IO.println s!"[codegen --check] {t.outPath} up to date \
          ({rustSource.length} bytes, {compiled.bytecode.functions.size} aiur fns)"
        return true
      else
        IO.eprintln s!"[codegen --check] {t.outPath} STALE: \
          on-disk {onDisk.length} bytes, would emit {rustSource.length} bytes. \
          Re-run `ix codegen` and commit the result."
        return false
  IO.FS.writeFile t.outPath rustSource
  IO.println s!"[codegen] wrote {rustSource.length} bytes to {t.outPath} \
    ({compiled.bytecode.functions.size} aiur fns)"
  return true

def traceReportTarget (target : Target) : Except String Lean.Json := do
  let source ← target.source.mapError fun error => s!"source error: {repr error}"
  let compiled ← source.compile
  -- Reports describe production grouping independent of the runtime override.
  let grouped ← compiled.groupFunctions target.groups
  TraceReport.program target.label grouped

/-- The production selection is intentionally small; every selected writer is
generated from the same bytecode library as its host seed packer. -/
def traceBundle : Except String (Array (String × String)) := do
  let mut files := #[]
  let mut units := #[]
  for target in targets do
    let source ← target.source.mapError fun error => s!"{target.label}: {repr error}"
    let compiled ← source.compile
    let grouped ← compiled.groupFunctions target.groups
    let some function := compiled.getFuncIdx `blake3_compress
      | throw s!"{target.label}: missing blake3_compress"
    let selected := some #[function]
    let unit := target.label.replace "-" "_"
    let cuda ← TraceCuda.emit grouped.bytecode unit selected
    let path := s!"cuda/generated/production/{unit}.cu"
    let digest := (Blake3.Rust.hash cuda.toUTF8).val.data.map fun n => Lean.toJson n.toNat
    units := units.push (Lean.Json.mkObj [("source", Lean.toJson path), ("digest", Lean.Json.arr digest)])
    files := files ++ #[
      (s!"crates/aiur/src/trace_codegen/programs/{unit}.rs", ← TraceCodegen.emit grouped.bytecode "crate" selected),
      (s!"crates/aiur/src/trace_codegen/programs/{unit}_cuda.rs", ← TraceCuda.registry grouped.bytecode unit "crate" selected),
      (s!"crates/aiur/{path}", cuda)]
  let manifest := Lean.Json.mkObj [("abi", Lean.toJson (1 : Nat)), ("units", Lean.Json.arr units)]
  pure (files.push ("crates/aiur/cuda/generated/production/trace-manifest.json", manifest.pretty ++ "\n"))

def emitTraceBundle (checkOnly : Bool) : IO UInt32 := do
  let files ← match traceBundle with
    | .ok files => pure files
    | .error error => IO.eprintln s!"trace bundle: {error}"; return 1
  for (path, source) in files do
    if checkOnly then
      let existing ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
      unless existing == some source do
        IO.eprintln s!"{path} is missing or stale; run ix codegen --trace-bundle"
        return 1
    else
      if let some parent := (System.FilePath.mk path).parent then IO.FS.createDirAll parent
      IO.FS.writeFile path source
    IO.println s!"{path}: {source.utf8ByteSize} bytes"
  return 0

def runCodegenCmd (p : Cli.Parsed) : IO UInt32 := do
  let checkOnly := p.hasFlag "check"
  let traceReport := p.hasFlag "trace-report"
  let traceRust := p.hasFlag "trace-rust"
  let traceCuda := p.hasFlag "trace-cuda"
  let traceRegistry := p.hasFlag "trace-cuda-registry"
  let bundle := p.hasFlag "trace-bundle"
  if (#[checkOnly && !bundle, bundle, traceReport, traceRust, traceCuda, traceRegistry].filter id).size > 1 then
    IO.eprintln "Select one codegen mode: --check, --trace-bundle [--check], --trace-report, --trace-rust, --trace-cuda, or --trace-cuda-registry"
    return 1
  if bundle then
    if p.hasFlag "target" || p.hasFlag "trace-functions" then
      IO.eprintln "--trace-bundle emits the production selection for all three targets"
      return 1
    return ← emitTraceBundle checkOnly
  let selected ← match (p.flag? "target").map (·.as! String) with
    | none => pure targets
    | some label =>
      let selected := targets.filter (·.label == label)
      if selected.isEmpty then
        IO.eprintln s!"Unknown codegen target {label}; expected ixvm, multi-stark, or ix-aggr"
        return 1
      pure selected
  if traceCuda || traceRegistry then
    let [target] := selected | do
      IO.eprintln "CUDA emission requires one --target"
      return 1
    let some functions := (p.flag? "trace-functions").map (·.as! String) | do
      IO.eprintln "CUDA emission requires --trace-functions with comma-separated constrained function indices"
      return 1
    let emitted : Except String String := do
      let mut indices := #[]
      for item in functions.splitOn "," do
        let some index := item.trimAscii.toString.toNat? | throw s!"invalid function index {item}"
        indices := indices.push index
      let source ← target.source.mapError (fun error => s!"{repr error}")
      let compiled ← source.compile
      let grouped ← compiled.groupFunctions target.groups
      let unit := target.label.replace "-" "_"
      if traceCuda then Aiur.TraceCuda.emit grouped.bytecode unit (some indices)
      else Aiur.TraceCuda.registry grouped.bytecode unit "aiur" (some indices)
    match emitted with
    | .ok source => IO.print source; return 0
    | .error error => IO.eprintln s!"{target.label} CUDA codegen: {error}"; return 1
  if traceRust then
    let [target] := selected | do
      IO.eprintln "--trace-rust requires one --target"
      return 1
    let emitted : Except String String := do
      let mut selected := none
      if let some functions := (p.flag? "trace-functions").map (·.as! String) then
        let mut indices := #[]
        for item in functions.splitOn "," do
          let some index := item.trimAscii.toString.toNat? | throw s!"invalid function index {item}"
          indices := indices.push index
        selected := some indices
      let source ← target.source.mapError (fun error => s!"{repr error}")
      let compiled ← source.compile
      let grouped ← compiled.groupFunctions target.groups
      Aiur.TraceCodegen.emit grouped.bytecode "aiur" selected
    match emitted with
    | .ok source => IO.print source; return 0
    | .error error => IO.eprintln s!"{target.label} trace codegen: {error}"; return 1
  if traceReport then
    let mut reports := #[]
    for target in selected do
      match traceReportTarget target with
      | .ok report => reports := reports.push report
      | .error error =>
        IO.eprintln s!"{target.label} trace report: {error}"
        return 1
    IO.println (TraceReport.document reports).compress
    return 0
  let mut ok := true
  for t in selected do
    ok := (← emitTarget checkOnly t) && ok
  return if ok then 0 else 1

end Ix.Cli.CodegenCmd

open Ix.Cli.CodegenCmd in
def codegenCmd : Cli.Cmd := `[Cli|
  "codegen" VIA runCodegenCmd;
  "Compile the IxVM kernel, MultiStark verifier, and single-entrypoint ixAggr system to Rust via the Bytecode → Rust codegen pass (fixed output paths, no override). PARITY UNVERIFIED — run their generated/interpreter fixture checks before trusting any witness."

  FLAGS:
    "trace-bundle"; "Generate production CUDA units, host seed writers, and registry manifests for all three programs; --check detects stale files."
    "check"; "Compare selected emitted Rust sources against disk and exit 0 if identical, 1 otherwise. Does not modify files."
    "trace-cuda"; "Emit CUDA row writers for --trace-functions in one --target."
    "trace-cuda-registry"; "Emit the Rust registry for the same CUDA function selection."
    "trace-functions" : String; "Comma-separated constrained function indices from --trace-report; required for CUDA emission."
    "trace-rust"; "Emit experimental scalar trace writers and read-only seed packers to stdout for one --target."
    "trace-report"; "Print a static GPU trace-plan inventory as JSON, with production groups and explicit missing row weights. Does not write generated source."
    "target" : String; "Select ixvm, multi-stark, or ix-aggr (default: all three)."
]

end
