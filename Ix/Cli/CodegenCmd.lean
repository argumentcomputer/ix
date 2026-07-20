/-
  `ix codegen`: write the IxVM kernel and the MultiStark recursive
  verifier as Rust source files via the Bytecode → Rust codegen pass.

  Output paths are fixed at compile time:
  - `crates/ixvm-codegen/src/aiur_ixvm.rs` (the IxVM kernel)
  - `crates/ixvm-codegen/src/aiur_multi_stark.rs` (the recursive verifier)
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
public import Ix.Aiur.Compiler
public import Ix.Aiur.Stages.Codegen
public import Ix.IxVM
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

def targets : List Target := [
  { label := "ixvm", source := IxVM.ixVM,
    outPath := "crates/ixvm-codegen/src/aiur_ixvm.rs" },
  { label := "multi-stark", source := MultiStark.multiStark,
    outPath := "crates/ixvm-codegen/src/aiur_multi_stark.rs" }
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

def runCodegenCmd (p : Cli.Parsed) : IO UInt32 := do
  let checkOnly := p.hasFlag "check"
  let mut ok := true
  for t in targets do
    ok := (← emitTarget checkOnly t) && ok
  return if ok then 0 else 1

end Ix.Cli.CodegenCmd

open Ix.Cli.CodegenCmd in
def codegenCmd : Cli.Cmd := `[Cli|
  "codegen" VIA runCodegenCmd;
  "Compile the IxVM Aiur kernel and the MultiStark recursive verifier to Rust source via the Bytecode → Rust codegen pass. Writes to `crates/ixvm-codegen/src/aiur_ixvm.rs` and `crates/ixvm-codegen/src/aiur_multi_stark.rs` (fixed paths, no override). PARITY UNVERIFIED — run the generated code on test fixtures against the interpreter before trusting any witness it produces."

  FLAGS:
    "check"; "CI mode: compare the emitted source against the on-disk files at `crates/ixvm-codegen/src/aiur_ixvm.rs` and `crates/ixvm-codegen/src/aiur_multi_stark.rs` and exit 0 if identical, 1 otherwise. Does not modify the files."
]

end
