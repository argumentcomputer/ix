module
public import Ix.MultiStark.Verify.Ood.Lookup

/-! Pure native composition/quotient checks, including public-claim lookup
balance. Success here is ONLY an OOD-phase result: the committed openings
still require the separate PCS/FRI authentication phase. -/

public section
@[expose] section

namespace MultiStark.Verify.Ood

def claimFingerprint (gamma : Ext) (claim : Array Field) : Ext :=
  claim.toList.foldr (fun value acc => (acc.mul gamma).add (Arithmetic.embed value)) Arithmetic.zero

def initialAccumulatorFrom (challenges : Transcript.Challenges) :
    List (Array Field) → Ext → Except Error Ext
  | [], accumulator => .ok accumulator
  | claim :: claims, accumulator => do
    let message := challenges.lookup.add (claimFingerprint challenges.fingerprint claim)
    let reciprocal ← (Arithmetic.inverse message).mapError Error.arithmetic
    initialAccumulatorFrom challenges claims (accumulator.add reciprocal)

def initialAccumulator (challenges : Transcript.Challenges) (claims : Array (Array Field)) :
    Except Error Ext := initialAccumulatorFrom challenges claims.toList Arithmetic.zero

def quotientFrom (pointPowerN : Ext) : List Ext → Ext → Ext → Except Error Ext
  | [], _, result => .ok result
  | c0 :: c1 :: rest, power, result =>
    let value := c0.add (c1.mul Arithmetic.basis)
    quotientFrom pointPowerN rest (power.mul pointPowerN) (result.add (power.mul value))
  | [_], _, _ => .error .width

def recombineQuotient (values : Shape.CircuitValues) (pointPowerN : Ext) : Except Error Ext := do
  let count := Shape.quotientDegree values.circuit
  ensure (values.quotient.size == 2 * count) .width
  quotientFrom pointPowerN values.quotient.toList Arithmetic.one Arithmetic.zero

structure Evaluation where
  constraints : Array Ext
  composition : Ext
  quotient : Ext
  invVanishing : Ext
  deriving BEq, DecidableEq, Repr

def evaluate (challenges : Transcript.Challenges) (initial final : Ext)
    (values : Shape.CircuitValues) : Except Error Evaluation := do
  let selectors ← selectors values.logDegree challenges.zeta
  let view : View := { values, publics := publicValues challenges initial final, selectors }
  let computed ← sweep view
  let constraints := (← roots values.circuit computed) ++ (← lookupValues view computed)
  ensure (constraints.size == values.circuit.constraintCount) .count
  let composition := constraints.foldl (fun acc value => (acc.mul challenges.alpha).add value) Arithmetic.zero
  let quotient ← recombineQuotient values selectors.pointPowerN
  return { constraints, composition, quotient, invVanishing := selectors.invVanishing }

def balanced (accumulators : Array Ext) : Bool :=
  match accumulators.back? with
  | some value => value == Arithmetic.zero
  | none => false

def checkFrom (challenges : Transcript.Challenges) :
    List Shape.CircuitValues → List Ext → Ext → Except Error (List Evaluation)
  | [], [], _ => .ok []
  | values :: rest, final :: finals, accumulator => do
    let evaluation ← evaluate challenges accumulator final values
    ensure (evaluation.composition.mul evaluation.invVanishing == evaluation.quotient) .mismatch
    let evaluations ← checkFrom challenges rest finals final
    return evaluation :: evaluations
  | _, _, _ => .error .count

def check (challenges : Transcript.Challenges) (claims : Array (Array Field))
    (values : Array Shape.CircuitValues) (accumulators : Array Ext) :
    Except Error (Array Evaluation) := do
  ensure (balanced accumulators) .balance
  ensure (values.size == accumulators.size) .count
  let accumulator ← initialAccumulator challenges claims
  return (← checkFrom challenges values.toList accumulators.toList accumulator).toArray

end MultiStark.Verify.Ood
