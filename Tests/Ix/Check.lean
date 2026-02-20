/-
  Kernel type-checker integration tests.
  Tests both the Rust kernel (via FFI) and the Lean NbE kernel.
-/

import Ix.Kernel
import Ix.Common
import Ix.Meta
import Ix.CompileM
import Lean
import LSpec

open LSpec

namespace Tests.Check

/-! ## Rust kernel tests -/

def testCheckEnv : TestSeq :=
  .individualIO "Rust kernel check_env" (do
    let leanEnv ← get_env!
    let totalConsts := leanEnv.constants.toList.length

    IO.println s!"[Check] Environment has {totalConsts} constants"

    let start ← IO.monoMsNow
    let errors ← Ix.Kernel.rsCheckEnv leanEnv
    let elapsed := (← IO.monoMsNow) - start

    IO.println s!"[Check] Rust kernel checked {totalConsts} constants in {elapsed.formatMs}"

    if errors.isEmpty then
      IO.println s!"[Check] All constants passed"
      return (true, none)
    else
      IO.println s!"[Check] {errors.size} error(s):"
      for (name, err) in errors[:min 20 errors.size] do
        IO.println s!"  {repr name}: {repr err}"
      return (false, some s!"Kernel check failed with {errors.size} error(s)")
  ) .done

def testCheckConst (name : String) : TestSeq :=
  .individualIO s!"check {name}" (do
    let leanEnv ← get_env!
    let start ← IO.monoMsNow
    let result ← Ix.Kernel.rsCheckConst leanEnv name
    let elapsed := (← IO.monoMsNow) - start
    match result with
    | none =>
      IO.println s!"  [ok] {name} ({elapsed.formatMs})"
      return (true, none)
    | some err =>
      IO.println s!"  [fail] {name}: {repr err} ({elapsed.formatMs})"
      return (false, some s!"{name} failed: {repr err}")
  ) .done

/-! ## Lean NbE kernel tests -/

def testKernelCheckEnv : TestSeq :=
  .individualIO "Lean NbE kernel check_env" (do
    let leanEnv ← get_env!

    IO.println s!"[Kernel-NbE] Compiling to Ixon..."
    let compileStart ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileElapsed := (← IO.monoMsNow) - compileStart
    let numConsts := ixonEnv.consts.size
    IO.println s!"[Kernel-NbE] Compiled {numConsts} constants in {compileElapsed.formatMs}"

    IO.println s!"[Kernel-NbE] Converting..."
    let convertStart ← IO.monoMsNow
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[Kernel-NbE] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, prims, quotInit) =>
      let convertElapsed := (← IO.monoMsNow) - convertStart
      IO.println s!"[Kernel-NbE] Converted {kenv.size} constants in {convertElapsed.formatMs}"

      IO.println s!"[Kernel-NbE] Typechecking {kenv.size} constants..."
      let checkStart ← IO.monoMsNow
      match ← Ix.Kernel.typecheckAllIO kenv prims quotInit with
      | .error e =>
        let elapsed := (← IO.monoMsNow) - checkStart
        IO.println s!"[Kernel-NbE] typecheckAll error in {elapsed.formatMs}: {e}"
        return (false, some s!"Kernel NbE check failed: {e}")
      | .ok () =>
        let elapsed := (← IO.monoMsNow) - checkStart
        IO.println s!"[Kernel-NbE] All constants passed in {elapsed.formatMs}"
        return (true, none)
  ) .done

/-! ## Test suites -/

def checkSuiteIO : List TestSeq := [
  testCheckConst "Nat.add",
]

def checkAllSuiteIO : List TestSeq := [
  testCheckEnv,
]

def kernelSuiteIO : List TestSeq := [
  testKernelCheckEnv,
]

end Tests.Check
