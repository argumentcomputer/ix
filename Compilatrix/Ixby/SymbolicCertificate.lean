import Compilatrix.Ixby.Arguments
import Compilatrix.Ixby.Certificate
import Compilatrix.Ixby.SymbolicTargetSound

/-! Reusable, input-independent translation validation for the actual compiler
image. The admitted fragment has a finite symbolic control path and a data
result; opaque arguments may flow through closures, PAPs and constructors but
cannot determine a branch or be inspected. No concrete input is evaluated by
this checker, and the proof quantifies over every admitted argument array. -/

namespace Compilatrix.Ixby

def symbolicSourceInput (parameters : Nat) : List SymbolicSource.Value :=
  ((List.range parameters).map SymbolicSource.Value.parameter).reverse

def symbolicTargetInput (parameters : Nat) : Array SymbolicTarget.Value :=
  ((List.range parameters).map SymbolicTarget.Value.parameter).toArray

structure SymbolicImage (source : Source) (config : Config) (program : Ix.Ixby.Program) where
  admitted : Ix.Ixby.validateProgram config.limits program = .ok ()
  sourceFuel : Nat
  targetFuel : Nat
  dataDepth : Nat
  sourceValue : SymbolicSource.Value
  sourceChecked : SymbolicSource.eval source.ctx sourceFuel (symbolicSourceInput source.parameters)
    source.main = some sourceValue
  frame : SymbolicTarget.Frame
  entered : SymbolicTarget.enter config.limits program program.entry
    (symbolicTargetInput source.parameters) = .ok frame
  targetValue : SymbolicTarget.Value
  targetChecked : SymbolicTarget.run config.limits program targetFuel
    { control := .eval frame } = .ok targetValue
  result : DataExpr
  sourceData : DataExpr.ofSource dataDepth sourceValue = some result
  targetData : DataExpr.ofTarget source dataDepth targetValue = some result

/-- Independently check a complete candidate image. This is also useful for
detecting valid bytecode mutations that change the source result. -/
def certifySymbolicImage (source : Source) (config : Config) (program : Ix.Ixby.Program)
    (sourceFuel : Nat := 10000) (targetFuel : Nat := 100000) (dataDepth : Nat := 1000) :
    Except String (SymbolicImage source config program) := do
  let admitted ← match admitted : Ix.Ixby.validateProgram config.limits program with
    | .error error => throw s!"Ixby symbolic image validation: {reprStr error}"
    | .ok () => pure (PLift.up admitted)
  match sourceChecked : SymbolicSource.eval source.ctx sourceFuel
      (symbolicSourceInput source.parameters) source.main with
  | none => throw "Ixby symbolic source rejection: opaque inspection, failure, or fuel exhaustion"
  | some sourceValue =>
      match entered : SymbolicTarget.enter config.limits program program.entry
          (symbolicTargetInput source.parameters) with
      | .error error => throw s!"Ixby symbolic entry: {reprStr error}"
      | .ok frame =>
          match targetChecked : SymbolicTarget.run config.limits program targetFuel
              { control := .eval frame } with
          | .error error => throw s!"Ixby symbolic target rejection: {reprStr error}"
          | .ok targetValue =>
              match sourceData : DataExpr.ofSource dataDepth sourceValue with
              | none => throw "Ixby symbolic source result is outside the bounded data ABI"
              | some sourceResult =>
                  match targetData : DataExpr.ofTarget source dataDepth targetValue with
                  | none => throw "Ixby symbolic target result is outside the bounded data ABI"
                  | some result =>
                      if equal : DataExpr.equal sourceResult result then
                        have same := DataExpr.eq_of_equal _ _ equal
                        return {
                          admitted := admitted.down
                          sourceFuel, targetFuel, dataDepth, sourceValue, sourceChecked
                          frame, entered, targetValue, targetChecked, result
                          sourceData := same ▸ sourceData
                          targetData }
                      else throw "Ixby symbolic source/target data disagreement"

/-- Reusable evidence indexed by the actual successful compiler result. -/
structure SymbolicCertificate {source config} (compiled : Compiled source config)
    extends SymbolicImage source config compiled.program

/-- Certify one compiled program for all admitted inputs. Fuel bounds symbolic
checking once; runtime input values are never supplied to this checker. -/
def Compiled.certifySymbolic {source config} (compiled : Compiled source config)
    (sourceFuel : Nat := 10000) (targetFuel : Nat := 100000) (dataDepth : Nat := 1000) :
    Except String (SymbolicCertificate compiled) := do
  let image ← certifySymbolicImage source config compiled.program sourceFuel targetFuel dataDepth
  return { toSymbolicImage := image }

def SymbolicCertificate.abi {source config compiled}
    (certificate : @SymbolicCertificate source config compiled) (inputDepth : Nat) :
    Ix.Ixby.ABI (Arguments source config inputDepth) Data :=
  { encodeInput := Arguments.raw, decodeOutput := decodeData source (inputDepth + certificate.dataDepth) }

theorem SymbolicCertificate.source_evaluates {source config compiled inputDepth}
    (certificate : @SymbolicCertificate source config compiled)
    (args : Arguments source config inputDepth) :
    source.EvaluatesData args.data (certificate.result.instantiate args.dataAt) := by
  have sourceRun := SymbolicSource.eval_sound certificate.sourceChecked
    (fun i => (args.dataAt i).toValue)
  have sourceValue := DataExpr.ofSource_sound certificate.sourceData args.dataAt
  have environment :
      (symbolicSourceInput source.parameters).map
          (SymbolicSource.Value.instantiate (fun i => (args.dataAt i).toValue)) =
        args.data.toList.reverse.map Data.toValue := by
    simpa [symbolicSourceInput, List.map_reverse, List.map_map,
      SymbolicSource.Value.instantiate, Function.comp_def] using
        congrArg (fun values => values.reverse.map Data.toValue) args.data_range
  rw [environment, sourceValue] at sourceRun
  obtain ⟨fuel, observed⟩ := (certificate.result.instantiate args.dataAt).observe_toValue
  exact ⟨certificate.sourceFuel, _, fuel, sourceRun, observed⟩

/-- The upstream reflection contract for every admitted runtime input and
every successful target fuel. The source execution follows from the checked
structural derivation; it is not a premise supplied separately by the caller. -/
theorem SymbolicCertificate.refinement {source config compiled}
    (certificate : @SymbolicCertificate source config compiled) (inputDepth : Nat) :
    Ix.Ixby.ExecutionRefinement
      (fun candidate (args : Arguments source config inputDepth) result => candidate.EvaluatesData args.data result)
      source config.limits compiled.program (certificate.abi inputDepth) := by
  intro args output evaluated
  have inputEq : (symbolicTargetInput source.parameters).map
      (SymbolicTarget.Value.instantiate args.rawAt) = args.raw := by
    simpa [symbolicTargetInput, List.map_map, Function.comp_def,
      SymbolicTarget.Value.instantiate] using args.raw_range
  have executed : Ix.Ixby.Evaluates config.limits compiled.program
      ((symbolicTargetInput source.parameters).map (SymbolicTarget.Value.instantiate args.rawAt)) output := by
    simpa only [inputEq, SymbolicCertificate.abi] using evaluated
  have same := SymbolicTarget.reflects_output certificate.entered certificate.targetChecked args.rawAt executed
  refine ⟨certificate.result.instantiate args.dataAt, ?_, certificate.source_evaluates args⟩
  change decodeData source (inputDepth + certificate.dataDepth) output = _
  rw [same]
  exact DataExpr.ofTarget_sound certificate.targetData args.dataAt args.rawAt inputDepth args.represented

end Compilatrix.Ixby
