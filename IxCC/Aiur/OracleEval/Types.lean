import Ix.Aiur.Stages.Bytecode
import IxCC.Aiur.Trace

/-! Local bytecode replay uses an answer tape. Its fuel counts local machine
transitions, not recursive calls, source fuel, or AIR rows. Advice records
allowed answers; it does not silently compute an honest hint. -/

namespace IxCC.Aiur.OracleEval

open _root_.Aiur (G)

abbrev Values := List G

inductive AdviceRequest where
  | call (function : Nat) (inputs : Values) (outputSize : Nat)
  | ioGetInfo (channel : G) (key : Values)
  | ioRead (channel index : G) (size : Nat)
  | bigUintDivMod (left right : G)
  | gToBytes (value : G)
  | gInverse (value : G)
  | u32Add (left right : Values)
  | u32Add3 (first second third : Values)
  deriving DecidableEq, BEq, Repr

/-- An allowed-answer relation. Identical requests may receive different
answers, as they can in different satisfying rows. A transcript supplies
the actual choices; this predicate supplies no determinism assumption. -/
abbrev AdviceOracle := AdviceRequest → Values → Bool

def AdviceRequest.inputFields : AdviceRequest → Nat
  | .call _ inputs _ => inputs.length + 2
  | .ioGetInfo _ key => key.length + 1
  | .ioRead .. => 3
  | .bigUintDivMod .. => 2
  | .gToBytes .. | .gInverse .. => 1
  | .u32Add left right => left.length + right.length
  | .u32Add3 first second third => first.length + second.length + third.length

def unrestrictedAdvice : AdviceOracle := fun _ _ => true

structure AdviceObservation where
  request : AdviceRequest
  answer : Values
  deriving DecidableEq, BEq, Repr

def AdviceAllowed (oracle : AdviceOracle) (observations : List AdviceObservation) : Prop :=
  ∀ observation ∈ observations, oracle observation.request observation.answer = true

inductive Outcome where
  | returned (selector : Nat) (values : Values)
  | yielded (selector : Nat) (values : Values)
  deriving DecidableEq, BEq, Repr

def Outcome.values : Outcome → Values
  | .returned _ values | .yielded _ values => values

structure Limits where
  maxSteps : Nat := 65536
  maxValues : Nat := 65536
  maxReplies : Nat := 65536
  maxReplyFields : Nat := 1048576
  maxObservationFields : Nat := 1048576
  deriving Repr

inductive Error where
  | fuelExhausted
  | valueLimit
  | answerLimit
  | observationLimit
  | invalidIndex (index : Nat)
  | invalidFunction (function : Nat)
  | inputArity (function expected actual : Nat)
  | operandArity (expected actual : Nat)
  | missingReply
  | replyArity (expected actual : Nat)
  | unusedReplies
  | assertionFailed
  | noMatch
  | yieldArity (expected actual : Nat)
  | rowWitnessCount
  | rowsRejected
  deriving DecidableEq, BEq, Repr

structure State where
  values : Array G
  replies : List Values
  demandsRev : List Message := []
  adviceRev : List AdviceObservation := []
  remainingFields : Nat := 1048576
  deriving Repr

structure Result where
  outcome : Outcome
  demands : List Message
  advice : List AdviceObservation
  deriving DecidableEq, Repr

def Result.outputs (result : Result) : Values := result.outcome.values

end IxCC.Aiur.OracleEval
