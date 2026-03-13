/-
  Kernel env conversion tests: convertEnv in meta and anon modes.
-/
import Ix.Kernel
import Ix.Kernel.Convert
import Ix.CompileM
import Ix.Common
import Ix.Meta
import Tests.Ix.Kernel.Helpers
import LSpec

open LSpec
open Tests.Ix.Kernel.Helpers (leanNameToIx)

namespace Tests.Ix.Kernel.Convert

/-- Test that convertEnv in .meta mode produces all expected constants. -/
def testConvertEnv : TestSeq :=
  .individualIO "kernel rsCompileEnv + convertEnv" (do
    let leanEnv ← get_env!
    let leanCount := leanEnv.constants.toList.length
    IO.println s!"[kernel-convert] Lean env: {leanCount} constants"
    let start ← IO.monoMsNow
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let compileMs := (← IO.monoMsNow) - start
    let ixonCount := ixonEnv.consts.size
    let namedCount := ixonEnv.named.size
    IO.println s!"[kernel-convert] rsCompileEnv: {ixonCount} consts, {namedCount} named in {compileMs.formatMs}"
    let convertStart ← IO.monoMsNow
    match Ix.Kernel.Convert.convertEnv .meta ixonEnv with
    | .error e =>
      IO.println s!"[kernel-convert] convertEnv error: {e}"
      return (false, some e)
    | .ok (kenv, _, _) =>
      let convertMs := (← IO.monoMsNow) - convertStart
      let kenvCount := kenv.size
      IO.println s!"[kernel-convert] convertEnv: {kenvCount} consts in {convertMs.formatMs} ({ixonCount - kenvCount} muts blocks)"
      -- Verify every Lean constant is present in the Kernel.Env
      let mut missing : Array String := #[]
      let mut notCompiled : Array String := #[]
      let mut checked := 0
      for (leanName, _) in leanEnv.constants.toList do
        let ixName := leanNameToIx leanName
        match ixonEnv.named.get? ixName with
        | none => notCompiled := notCompiled.push (toString leanName)
        | some named =>
          checked := checked + 1
          if !kenv.containsAddr named.addr then
            missing := missing.push (toString leanName)
      if !notCompiled.isEmpty then
        IO.println s!"[kernel-convert] {notCompiled.size} Lean constants not in ixonEnv.named (unexpected)"
        for n in notCompiled[:min 10 notCompiled.size] do
          IO.println s!"  not compiled: {n}"
      if missing.isEmpty then
        IO.println s!"[kernel-convert] All {checked} named constants found in Kernel.Env"
        return (true, none)
      else
        IO.println s!"[kernel-convert] {missing.size}/{checked} named constants missing from Kernel.Env"
        for n in missing[:min 20 missing.size] do
          IO.println s!"  missing: {n}"
        return (false, some s!"{missing.size} constants missing from Kernel.Env")
  ) .done

/-- Test that convertEnv in .anon mode produces the same number of constants. -/
def testAnonConvert : TestSeq :=
  .individualIO "kernel anon mode conversion" (do
    let leanEnv ← get_env!
    let ixonEnv ← Ix.CompileM.rsCompileEnv leanEnv
    let metaResult := Ix.Kernel.Convert.convertEnv .meta ixonEnv
    let anonResult := Ix.Kernel.Convert.convertEnv .anon ixonEnv
    match metaResult, anonResult with
    | .ok (metaEnv, _, _), .ok (anonEnv, _, _) =>
      let metaCount := metaEnv.size
      let anonCount := anonEnv.size
      IO.println s!"[kernel-anon] meta: {metaCount}, anon: {anonCount}"
      if metaCount == anonCount then
        return (true, none)
      else
        return (false, some s!"meta ({metaCount}) != anon ({anonCount})")
    | .error e, _ => return (false, some s!"meta conversion failed: {e}")
    | _, .error e => return (false, some s!"anon conversion failed: {e}")
  ) .done

def convertSuite : List TestSeq := [testConvertEnv]
def anonConvertSuite : List TestSeq := [testAnonConvert]

end Tests.Ix.Kernel.Convert
