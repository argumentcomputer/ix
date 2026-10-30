module

public import Ix.Compile.ReadyQueue
import all Ix.CompileDriver
import all Ix.Cert.Compile

/-! Checked IO composition for the experimental ready executor. The pure
compiler and its checks remain the specification; no default route changes. -/

public section

namespace Ix.Compile.ReadyCompile

open Ix.CompileM

abbrev DriverResult := Except String (Ixon.Env × Nat × CompileEnv)
abbrev ReportResult := Except String (Ixon.Env × Ix.Cert.Failures)

def validate (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Except String Unit := do
  if let some message := missingBlockRefs? blocks then throw message
  validateInductiveFlags env
  validateMutualSafety env blocks

def initial (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (limits : Ix.Sharing.Exact.Limits) : FoldState :=
  let view : Ix.Environment := { consts := {}, fallback? := some env.get? }
  let cenv := { CompileEnv.new view with sharingLimits := limits }
  FoldState.init cenv blocks (FoldSchedule.of blocks)

def finish (env : Ix.Environment) (result : Except String FoldState) : DriverResult := do
  let state ← result
  let (artifact, bytes, cenv) ← finalizeEnv state.acc
  return (artifact, bytes, { cenv with env })

theorem driver_decomposition (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (dbg : Bool) (limits : Ix.Sharing.Exact.Limits) (width : Nat) :
    compileEnvFold env blocks dbg limits width = (do
      validate env blocks
      finish env (foldWaves blocks (FoldSchedule.of blocks) width dbg
        (blocks.blocks.size + 1) (initial env blocks limits))) := by
  unfold compileEnvFold validate initial finish
  cases missing : missingBlockRefs? blocks with
  | some message => simp [missing]
  | none =>
    simp only [missing]
    cases validateInductiveFlags env <;> cases validateMutualSafety env blocks <;> rfl

def driverIO (config : ReadyQueue.Config) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) (dbg : Bool := false)
    (limits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (width : Nat := foldWaveTasks) :
    IO ({ result : DriverResult // result = compileEnvFold env blocks dbg limits width } ×
      ReadyQueue.Metrics) := do
  let validation ← IO.lazyPure fun _ =>
    (⟨validate env blocks, rfl⟩ : { result : Except String Unit // result = validate env blocks })
  match checked : validation.val with
  | .error message =>
    return (⟨.error message, by
      rw [driver_decomposition, ← validation.property, checked]
      rfl⟩, {})
  | .ok _ =>
    let (state, metrics) ← ReadyQueue.run config blocks (FoldSchedule.of blocks) width dbg
      (blocks.blocks.size + 1) (initial env blocks limits)
    let result ← IO.lazyPure fun _ =>
      (⟨finish env state.val, by
        rw [driver_decomposition, ← validation.property, checked]
        exact congrArg (finish env) state.property⟩ :
        { result : DriverResult // result = compileEnvFold env blocks dbg limits width })
    return (result, metrics)

def reportFromDriver (env : Ix.Environment)
    (split : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.GroundError)
    (blocks : Ix.CondensedBlocks) (driver : DriverResult) : ReportResult := do
  let (artifact, _, cenv) ← driver
  let ungrounded := split.2.fold (init := {}) fun map name error =>
    map.insert name (error.refusal split.2.contains)
  let failures : Ix.Cert.Failures := { ungrounded, blocks := cenv.ungrounded }
  Ix.Cert.checkReport env cenv (artifact, failures) blocks
  return (artifact, failures)

theorem report_decomposition (env : Ix.Environment) :
    reportFromDriver env (Ix.Cert.groundSplit { consts := env.consts })
      (Ix.CondenseM.run (Ix.Cert.groundSplit { consts := env.consts }).1)
      (compileEnvFold { consts := env.consts }
        (Ix.CondenseM.run (Ix.Cert.groundSplit { consts := env.consts }).1)) =
      Ix.Cert.compileReport env := by
  rw [Ix.Cert.compileReport_eq_shared]
  unfold Ix.Cert.compileReportShared Ix.Cert.compileUncheckedWith reportFromDriver
  cases compileEnvFold { consts := env.consts }
      (Ix.CondenseM.run (Ix.Cert.groundSplit { consts := env.consts }).1) <;> rfl

/-- The result carries equality to the complete checked pure report, including
its original failure map and every report check. -/
def reportIO (config : ReadyQueue.Config) (env : Ix.Environment) :
    IO ({ result : ReportResult // result = Ix.Cert.compileReport env } × ReadyQueue.Metrics) := do
  let split ← IO.lazyPure fun _ =>
    (⟨Ix.Cert.groundSplit { consts := env.consts }, rfl⟩ :
      { result // result = Ix.Cert.groundSplit { consts := env.consts } })
  let blocks ← IO.lazyPure fun _ =>
    (⟨Ix.CondenseM.run split.val.1, rfl⟩ : { result // result = Ix.CondenseM.run split.val.1 })
  let (driver, metrics) ← driverIO config { consts := env.consts } blocks.val
  let result ← IO.lazyPure fun _ =>
    (⟨reportFromDriver env split.val blocks.val driver.val, by
      rw [driver.property, blocks.property, split.property]
      exact report_decomposition env⟩ : { result : ReportResult // result = Ix.Cert.compileReport env })
  return (result, metrics)

end Ix.Compile.ReadyCompile
