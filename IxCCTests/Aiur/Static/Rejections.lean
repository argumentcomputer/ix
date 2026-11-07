import IxCCTests.Aiur.Static.Fixtures

namespace IxCCTests.Aiur.Static

open IxCC.Aiur
open _root_.Aiur (G)
open Execution (provider)

def runRejections (count : IO.Ref Nat) : IO Unit := do
  let counter := inputProgram false
  let trace := Execution.counterTrace
  need count "missing ranks rejected" (failed (certify counter trace #[] inputReplies) (.assignment .rankCount))
  need count "extra ranks rejected" (failed (certify counter trace #[0, 0, 0, 0] inputReplies) (.assignment .rankCount))
  need count "equal ranked edge rejected"
    (failed (certify fallbackProgram trace #[0, 0, 0] inputReplies) (.assignment .dependencies))
  need count "backward ranked edge rejected"
    (failed (certify fallbackProgram trace #[2, 1, 0] inputReplies) (.assignment .dependencies))
  need count "all duplicate providers must advance"
    (failed (certify fallbackProgram duplicateTrace #[0, 1, 0, 2] duplicateReplies) (.assignment .dependencies))
  need count "duplicate attack still has valid local rows"
    (OracleEval.checkRows fallbackProgram OracleEval.unrestrictedAdvice duplicateTrace {} duplicateReplies)
  need count "self cycle passes local replay"
    (OracleEval.checkRows Execution.selfLoopProgram OracleEval.unrestrictedAdvice Execution.selfLoopTrace {} #[[[99]]])
  need count "self cycle fails certificate construction"
    (failed (certify Execution.selfLoopProgram Execution.selfLoopTrace #[0] #[[[99]]]) (.assignment .dependencies))
  need count "mutual cycle passes local replay"
    (OracleEval.checkRows Execution.mutualLoopProgram OracleEval.unrestrictedAdvice Execution.mutualLoopTrace {}
      #[[[99]], [[99]]])
  need count "mutual cycle fails certificate construction"
    (failed (certify Execution.mutualLoopProgram Execution.mutualLoopTrace #[0, 1] #[[[99]], [[99]]])
      (.assignment .dependencies))
  let falseCounter : Trace :=
    ⟨[provider (.function 0 [2] [0]) [.function 0 [2] [0]] 2], [.function 0 [2] [0]]⟩
  need count "wrong counter equation is balanced" falseCounter.validate.isOk
  need count "analyzer acceptance does not replace the row equation"
    (failed (certify counter falseCounter #[0] #[[[0]]]) (.assignment .dependencies))
  let unknown : Trace := ⟨[provider (.function 999 [] [0])], [.function 999 [] [0]]⟩
  need count "unknown function cannot use fallback facts"
    (failed (certify counter unknown #[0] #[[]]) (.assignment .providerBinding))
  let arity : Trace := ⟨[provider (.function 0 [] [0])], [.function 0 [] [0]]⟩
  need count "function input arity binds provider"
    (failed (certify counter arity #[0] #[[]]) (.assignment .providerBinding))
  let missingOutput : Trace := ⟨[provider (.function 0 [7] [])], [.function 0 [7] []]⟩
  need count "counter output cannot default to zero"
    (failed (certify (outputProgram true) missingOutput #[0] #[[[0]]]) (.assignment .providerBinding))
  let unconstrained := { counter with functions := counter.functions.map fun fn => { fn with constrained := false } }
  need count "replay alone does not bind the constrained flag"
    (OracleEval.checkRows unconstrained OracleEval.unrestrictedAdvice trace {} inputReplies)
  need count "unconstrained function cannot provide a constrained row"
    (failed (certify unconstrained trace #[0, 0, 0] inputReplies) (.assignment .providerBinding))
  need count "rank bound enforced even on unused rank data"
    (failed (certify counter trace #[1, 0, 0] inputReplies { assignment.maxRank := 0 }) (.assignment .rankLimit))
  need count "rank at two-to-48 rejected"
    (failed (certify fallbackProgram trace #[0, 1, 2 ^ 48] inputReplies) (.assignment .rankLimit))
  need count "dependency matrix budget enforced"
    (failed (certify counter trace #[0, 0, 0] inputReplies { assignment.maxPairs := 8 })
      (.assignment .dependencyLimit))
  need count "trace row budget enforced"
    (failed (certify counter trace #[0, 0, 0] inputReplies { trace.maxRows := 2 }) (.trace .resourceLimit))
  need count "trace unit-slot budget enforced"
    (failed (certify counter trace #[0, 0, 0] inputReplies { trace.maxUnitSlots := 5 }) (.trace .resourceLimit))
  need count "trace field budget enforced"
    (failed (certify counter trace #[0, 0, 0] inputReplies { trace.maxMessageFields := 1 }) (.trace .resourceLimit))
  need count "replay fuel still checked"
    (failed (certify counter trace #[0, 0, 0] inputReplies { replay.maxSteps := 1 }) (.replay .rowsRejected))
  need count "replay observation budget still checked"
    (failed (certify counter trace #[0, 0, 0] inputReplies { replay.maxObservationFields := 0 })
      (.replay .rowsRejected))
  need count "missing row tapes still checked"
    (failed (certify counter trace #[0, 0, 0] #[]) (.replay .rowWitnessCount))
  need count "malformed answer tape still checked"
    (failed (certify counter trace #[0, 0, 0] #[[], [], []]) (.replay .rowsRejected))
  need count "denied advice still rejected"
    (failed (certify (outputProgram true) (outputTrace true) #[0, 0, 0] (outputReplies true)
      {} (fun _ _ => false)) (.replay .rowsRejected))
  need count "false arithmetic cannot hide behind acyclic dependencies"
    (failed (certify Execution.constantProgram Execution.falseClaimTrace #[0] #[[]]) (.replay .rowsRejected))
  need count "false gadget provider remains rejected"
    (failed (certify Execution.xorProgram Execution.falseGadgetTrace #[0, 0] #[[[9]], []]) (.replay .rowsRejected))
  need count "false callee output remains rejected"
    (failed (certify orderedProgram (Execution.callTrace 99) #[0, 0] #[[[99]], []]) (.replay .rowsRejected))
  let inactive : Trace := ⟨[provider (.function 0 [0] [0]) [] 1 false], [.function 0 [0] [0]]⟩
  need count "inactive provider remains rejected"
    (failed (certify counter inactive #[0] #[[]]) (.trace .inactiveProvider))
  let unbalanced : Trace := ⟨[provider (.function 0 [0] [0]) [] 2], [.function 0 [0] [0]]⟩
  need count "wrong multiplicity remains rejected"
    (failed (certify counter unbalanced #[0] #[[]]) (.trace .unbalanced))
  let incoherent : Trace :=
    ⟨[provider (.memory 1 7 [0]), provider (.memory 1 7 [1])], [.memory 1 7 [0], .memory 1 7 [1]]⟩
  need count "incoherent memory remains rejected"
    (failed (certify WireFixtures.empty incoherent #[0, 0] #[[], []]) (.trace .inconsistentMemory))
  match Static.prepare {} counter with
  | .error error => throw (IO.userError s!"counter plan rejected: {repr error}")
  | .ok program =>
      let leaf : Trace := ⟨[provider (.memory 1 7 [0]) [.function 0 [0] [0]]], []⟩
      need count "memory provider must be a leaf"
        (failed (Static.checkAssignment program leaf {} {} #[0]) .providerBinding)
      let leaf : Trace := ⟨[provider (.gadget 3 [1, 2, 3]) [.function 0 [0] [0]]], []⟩
      need count "gadget provider must be a leaf"
        (failed (Static.checkAssignment program leaf {} {} #[0]) .providerBinding)
      need count "standalone assignment enforces structural limits"
        (failed (Static.checkAssignment program trace { maxRows := 2 } {} #[0, 0, 0]) .traceLimit)

end IxCCTests.Aiur.Static
