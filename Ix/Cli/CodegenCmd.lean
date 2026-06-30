/-
  `ix codegen`: write the IxVM kernel as a Rust source file via the
  Bytecode → Rust codegen pass.

  Output path is fixed at compile time: `src/ix/aiur_ixvm.rs`. The
  generated file is the single destination; no flag overrides.

  Output: a Rust module body containing one `fn aiur_fn_N(...)` per
  Aiur kernel function, plus per-fn `IN_N` / `OUT_N` / `INPUT_SIZE_N`
  size constants and the dispatch entry `execute_generated`.

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

public section

namespace Ix.Cli.CodegenCmd

open Aiur

/-- Fixed destination — compile-time constant, no CLI override. -/
def codegenOutPath : String := "src/ix/aiur_ixvm.rs"

def runCodegenCmd (_p : Cli.Parsed) : IO UInt32 := do
  -- Compile the IxVM source to bytecode.
  let src ← match IxVM.ixVM with
    | .ok src => pure src
    | .error e => IO.eprintln s!"IxVM source error: {repr e}"; return 1
  let compiled ← match src.compile with
    | .ok c => pure c
    | .error e => IO.eprintln s!"Aiur compile error: {e}"; return 1
  let rustSource := Aiur.Codegen.emit compiled.bytecode
  IO.FS.writeFile codegenOutPath rustSource
  IO.println s!"[codegen] wrote {rustSource.length} bytes to {codegenOutPath} \
    ({compiled.bytecode.functions.size} aiur fns)"
  return 0

end Ix.Cli.CodegenCmd

open Ix.Cli.CodegenCmd in
def codegenCmd : Cli.Cmd := `[Cli|
  "codegen" VIA runCodegenCmd;
  "Compile the IxVM Aiur kernel to Rust source via the Bytecode → Rust codegen pass. Writes to `src/ix/aiur_ixvm.rs` (fixed path, no override). PARITY UNVERIFIED — run the generated code on test fixtures against the interpreter before trusting any witness it produces."
]

end
