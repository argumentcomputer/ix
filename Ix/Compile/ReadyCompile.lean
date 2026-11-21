module

public import Ix.Compile.ReadyQueue
import all Ix.CompileDriver
import all Ix.Cert.Compile

/-! Checked IO composition for the dependency-ready executor. The pure
compiler and its checks remain the specification. -/

public section

namespace Ix.Compile.ReadyCompile

open Ix.CompileM

abbrev DriverResult := Except String (Ixon.Env × Nat × CompileEnv)
abbrev ReportResult := Except String (Ixon.Env × Ix.Cert.Failures)

def validate (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Except String Unit := do
  if let some message := missingBlockRefs? blocks then throw message
  validateInductiveFlags env
  validateMutualSafety env blocks

@[expose] def validatePar (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Except String Unit :=
  let missingTask := Task.spawn fun _ => missingBlockRefs? blocks
  let flagsTask := Task.spawn fun _ => validateInductiveFlags env
  let safetyTask := Task.spawn fun _ => validateMutualSafety env blocks
  match missingTask.get with
  | some message => .error message
  | none =>
    match flagsTask.get with
    | .error e => .error e
    | .ok () => safetyTask.get

@[csimp] theorem validate_eq_par : @validate = @validatePar := by
  funext env blocks
  unfold validate validatePar
  cases missingBlockRefs? blocks with
  | some message => rfl
  | none =>
    dsimp only
    cases validateInductiveFlags env <;> rfl

def initialWith (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (sched : FoldSchedule) (limits : Ix.Sharing.Exact.Limits) : FoldState :=
  let view : Ix.Environment := env.lookupView
  let cenv := { CompileEnv.new view with sharingLimits := limits }
  FoldState.init cenv blocks sched

def initial (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (limits : Ix.Sharing.Exact.Limits) : FoldState :=
  initialWith env blocks (FoldSchedule.of blocks) limits

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
  unfold compileEnvFold validate initial initialWith finish
  cases missing : missingBlockRefs? blocks with
  | some message => simp
  | none =>
    dsimp only
    cases validateInductiveFlags env <;> cases validateMutualSafety env blocks <;> rfl

def driverIO (config : ReadyQueue.Config) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) (dbg : Bool := false)
    (limits : Ix.Sharing.Exact.Limits := compilerSharingLimits)
    (width : Nat := foldWaveTasks) :
    IO ({ result : DriverResult // result = compileEnvFold env blocks dbg limits width } ×
      ReadyQueue.Metrics) := do
  let validationTask ← IO.asTask do
    return (⟨validate env blocks, rfl⟩ : { result : Except String Unit // result = validate env blocks })
  let sched := FoldSchedule.of blocks
  let initSt := initialWith env blocks sched limits
  let validation ← IO.ofExcept validationTask.get
  match checked : validation.val with
  | .error message =>
    return (⟨.error message, by
      rw [driver_decomposition, ← validation.property, checked]
      rfl⟩, {})
  | .ok _ =>
    let (state, metrics) ← ReadyQueue.run config blocks sched width dbg
      (blocks.blocks.size + 1) initSt
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
    reportFromDriver env (Ix.Cert.groundSplit env.materialized)
      (Ix.CondenseM.run (Ix.Cert.groundSplit env.materialized).1)
      (compileEnvFold env.materialized
        (Ix.CondenseM.run (Ix.Cert.groundSplit env.materialized).1)) =
      Ix.Cert.compileReport env := by
  rw [Ix.Cert.compileReport_eq_shared]
  dsimp only [Ix.Cert.compileReportShared, Ix.Cert.compileUncheckedWith, reportFromDriver]
  cases compileEnvFold env.materialized
      (Ix.CondenseM.run (Ix.Cert.groundSplit env.materialized).1) with
  | error message => rfl
  | ok result =>
    obtain ⟨artifact, bytes, cenv⟩ := result
    rfl

/-- The result carries equality to the complete checked pure report, including
its original failure map and every report check. -/
def reportIO (config : ReadyQueue.Config) (env : Ix.Environment) :
    IO ({ result : ReportResult // result = Ix.Cert.compileReport env } × ReadyQueue.Metrics) := do
  let split ← IO.lazyPure fun _ =>
    (⟨Ix.Cert.groundSplit env.materialized, rfl⟩ :
      { result // result = Ix.Cert.groundSplit env.materialized })
  let blocks ← IO.lazyPure fun _ =>
    (⟨Ix.CondenseM.run split.val.1, rfl⟩ : { result // result = Ix.CondenseM.run split.val.1 })
  let (driver, metrics) ← driverIO config env.materialized blocks.val
  let result ← IO.lazyPure fun _ =>
    (⟨reportFromDriver env split.val blocks.val driver.val, by
      rw [driver.property, blocks.property, split.property]
      exact report_decomposition env⟩ : { result : ReportResult // result = Ix.Cert.compileReport env })
  return (result, metrics)

end Ix.Compile.ReadyCompile
