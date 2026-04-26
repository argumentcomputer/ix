/-
  Kernel typechecking FFI bindings.

  Exposes `rsCheckConstsFFI` and the `CheckError` ADT shared by:
  - `Ix.Cli.CheckCmd`           — the `lake exe ix check` CLI entry point.
  - `Tests.Ix.Kernel.Tutorial`  — the targeted-batch test harness.
  - `Tests.Ix.Kernel.CheckEnv`  — the full-environment test runner.

  Centralising the binding means the FFI symbol (`rs_kernel_check_consts`,
  defined in `src/ffi/kernel.rs`) has a single Lean-side `@[extern]`
  declaration, and every caller agrees on the `CheckError` constructor
  layout (tag 0 = `kernelException`, tag 1 = `compileError`).
-/
module
public import Lean.Data.Name
public import Lean.Declaration

public section

namespace Ix.KernelCheck

/-- Type-check errors returned from the Rust kernel FFI.

    Two variants:
    - `kernelException msg` — rejection during kernel typechecking (tag 0).
    - `compileError    msg` — rejection during `compile_env` (tag 1), emitted
      when `compile_env`'s tolerant scheduler records a block as ungrounded
      (e.g. `inductBadNonSort` failing `compute_is_large_and_k`).

    **Important**: keep at least two constructors so Lean's LCNF trivial
    structure optimization does NOT elide the enum to just `String`. With
    only one ctor + one field, `hasTrivialStructure?` fires and the runtime
    representation becomes identical to `String`, which breaks any FFI that
    allocates a heap ctor. See
    `refs/lean4/src/Lean/Compiler/LCNF/MonoTypes.lean:20-28`.

    Tags are stable across the Rust FFI — see `KERNEL_EXCEPTION_TAG` and
    `COMPILE_ERROR_TAG` in `src/ffi/kernel.rs`. -/
inductive CheckError where
  | kernelException (msg : String)
  | compileError    (msg : String)
  deriving Repr

/-- Render a `CheckError` as a single-line, prefixed message suitable for
    log lines. Pulls the message string out of either ctor without going
    through `repr` — derived `Repr` for long multi-line kernel diagnostics
    is seconds-slow per call and can make a check appear to hang. -/
def CheckError.message : CheckError → String
  | .kernelException m => s!"kernel: {m}"
  | .compileError    m => s!"compile: {m}"

/-- FFI: type-check a batch of constants through the full pipeline
    (Lean env → Ixon compile → kernel ingress → typecheck).

    Implemented in `src/ffi/kernel.rs::rs_kernel_check_consts`. Note: this
    used to be gated behind the `test-ffi` Cargo feature. It is now part
    of the production build so `lake exe ix check` can drive it directly.

    The trailing `Bool` toggles ephemeral progress printing on the Rust
    side:
    - `false` (verbose): every constant is logged on its own line with
      elapsed time and `def_eq` depth — ideal for small, targeted batches
      where every result matters.
    - `true` (quiet / ephemeral): the current `[i/N] name ...` label is
      rewritten in place, and only slow constants (>=7s by default), unexpected
      passes/failures, and ungrounded compile errors are promoted to
      persistent lines. Ideal for full-env runs where thousands of fast
      constants would otherwise swamp the log. Parallel quiet mode also
      prints periodic done/total, rate, ETA, and oldest in-flight
      constants. Tune with `IX_KERNEL_CHECK_PROGRESS_MS`,
      `IX_KERNEL_CHECK_SLOW_MS`, `IX_KERNEL_CHECK_ACTIVE_SLOW_MS`, and
      `IX_KERNEL_CHECK_INFLIGHT`.

    Results come back in input-array order — the caller pairs each
    `results[i]` with its `names[i]`. We pass `Lean.Name` structurally
    (rather than shipping `name.toString` strings) because Lean's
    default `toString` wraps non-identifier components in `«…»`, and
    round-tripping that through a Rust string parser was brittle:
    names like `Lean.Order.«term_⊑_»` failed lookup against the
    kernel's unescaped `Lean.Order.term_⊑_` key. Rust decodes each
    `Lean.Name` structurally via `decode_name_array`, so the kernel
    lookup is an exact structural match. -/
@[extern "rs_kernel_check_consts"]
opaque rsCheckConstsFFI :
    @& List (Lean.Name × Lean.ConstantInfo) →
    @& Array Lean.Name →
    @& Array Bool →
    @& Bool →
    IO (Array (Option CheckError))

end Ix.KernelCheck

end
