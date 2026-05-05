/-
  `ix ingress --path <file>`: run only the Lean → Ixon → KEnv ingress
  pipeline against a Lean file's environment, stopping before the kernel
  typecheck loop. Mirrors `ix check` (build the file, load its env, ship
  to Rust) but pipes the env through `rs_kernel_ingress` instead of
  `rs_kernel_check_consts`.

  Pipeline (Rust side, `src/ffi/kernel.rs::rs_kernel_ingress`):
    Lean env  →  compile_env  →  ixon_ingress  →  KEnv  (stop)

  Use it like
    `lake exe ix ingress --path Benchmarks/Compile/CompileMathlib.lean`
  to time the ingress-only pipeline against a full Mathlib environment
  without paying for the typecheck pass. Useful when profiling
  `compile_env` / `ixon_ingress` regressions in isolation.

  Flags:
  - `--path <file>` (required): file whose env should be ingressed.

  No `--ns` filter: ingress always processes the whole IxonEnv (the
  filter on `ix check` only controls which constants we *assert* on; it
  doesn't shrink the ingressed env, so it has no effect on this path).
-/
module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.Meta

public section

open System (FilePath)

namespace Ix.Cli.IngressCmd

/-- FFI: ingress a Lean environment through the compile + kernel-ingress
    pipeline, stopping before typechecking. Returns the number of kernel
    constants ingressed.

    Implemented in `src/ffi/kernel.rs::rs_kernel_ingress`. The Rust side
    prints `[rs_kernel_ingress] read env / compile / ingress` timing lines
    to stderr, mirroring `rs_kernel_check_consts`. -/
@[extern "rs_kernel_ingress"]
opaque rsKernelIngressFFI :
    @& List (Lean.Name × Lean.ConstantInfo) → IO USize

def runIngressCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.flag? "path"
    | p.printError "error: must specify --path"
      return 1
  let pathStr := path.as! String

  -- `buildFile` also runs `lake exe cache get` if the target depends on
  -- Mathlib, so a fresh checkout works without a prior `lake build`.
  buildFile pathStr
  let leanEnv ← getFileEnv pathStr

  let totalConsts := leanEnv.constants.toList.length
  IO.println s!"Running Ix ingress on {pathStr}"
  IO.println s!"Total constants in env: {totalConsts}"

  let start ← IO.monoMsNow
  let kenvLen ← rsKernelIngressFFI leanEnv.constants.toList
  let elapsed := (← IO.monoMsNow) - start

  IO.println s!"[ingress] ingressed {kenvLen} kernel consts in {elapsed.formatMs}"
  -- Machine-readable line for CI benchmark tracking, mirrors
  -- `ix compile`'s `##benchmark##` shape.
  IO.println s!"##ingress## {elapsed} {kenvLen} {totalConsts}"
  return 0

end Ix.Cli.IngressCmd

open Ix.Cli.IngressCmd in
def ingressCmd : Cli.Cmd := `[Cli|
  ingress VIA runIngressCmd;
  "Ingress a Lean file's env through the Ix kernel pipeline (compile + ingress only, no typecheck) for performance analysis"

  FLAGS:
    path : String; "Path to file whose env should be ingressed"
]

end
