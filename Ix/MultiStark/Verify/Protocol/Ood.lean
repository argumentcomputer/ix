module
public import Ix.MultiStark.Verify.Protocol.Arithmetic
public import Ix.MultiStark.Verify.Protocol.Graph
public import Ix.MultiStark.Verify.Ood

/-! OOD relation over authenticated opening values. These are the selector,
expression, and logUp equations themselves; they do not call the executable
OOD checker or assume a native acceptance result. Authentication remains a
separate PCS/FRI obligation. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

open Arithmetic (Coordinates)

def SelectorsAt (logDegree : Nat) (point : Ext) (result : Ood.Selectors) : Prop :=
  ∃ generator lastRoot first last invVanishing normalization,
    TwoAdicGenerator logDegree generator ∧ BaseInverse generator lastRoot ∧
    let pointPowerN := Arithmetic.pow2 point logDegree
    let vanishing := pointPowerN.sub Arithmetic.one
    let transition := point.sub (Arithmetic.embed lastRoot)
    Division vanishing (point.sub Arithmetic.one) first ∧
    Division vanishing transition last ∧ ExtensionInverse vanishing invVanishing ∧
    BaseInverse ((Ix.Ixby.Goldilocks.reduce (2 ^ logDegree)).mul generator) normalization ∧
    Ood.Selectors.mk first last transition invVanishing (Arithmetic.embed normalization) pointPowerN = result

def References (computed : Array Ext) : List Nat → List Ext → Prop
  | [], [] => True
  | index :: indices, value :: values => computed[index]? = some value ∧ References computed indices values
  | _, _ => False

def CoordinateRead (row : Array Ext) (offset : Nat) (value : Coordinates) : Prop :=
  row[offset]? = some value.c0 ∧ row[offset + 1]? = some value.c1

def LookupMessage (computed : Array Ext) (beta gamma : Coordinates) (lookup : Lookup)
    (result : Coordinates) : Prop :=
  ∃ values, References computed lookup.args.toList values ∧
    beta.add (values.foldr (fun value acc => (acc.mul gamma).add (Coordinates.embed value)) Coordinates.zero) = result

def LookupEntries (computed : Array Ext) (beta gamma : Coordinates) :
    List Lookup → List (Coordinates × Ext) → Prop
  | [], [] => True
  | lookup :: lookups, (message, multiplicity) :: entries =>
    LookupMessage computed beta gamma lookup message ∧ computed[lookup.multiplicity]? = some multiplicity ∧
      LookupEntries computed beta gamma lookups entries
  | _, _ => False

def GroupEquation (computed : Array Ext) (group : Array Lookup) (beta gamma delta : Coordinates)
    (result : Coordinates) : Prop :=
  ∃ entries, LookupEntries computed beta gamma group.toList entries ∧
    let messages := entries.map Prod.fst
    let product := messages.foldl Coordinates.mul Coordinates.one
    (entries.zipIdx.foldl (fun acc (entry, index) =>
      let others := (messages.take index ++ messages.drop (index + 1)).foldl Coordinates.mul Coordinates.one
      acc.sub (others.scale entry.2)) (product.mul delta)) = result

def LookupTarget (view : Ood.View) (injection : Coordinates) (group : Nat) (result : Coordinates) : Prop :=
  if group + 1 < view.values.circuit.lookupGroups then
    CoordinateRead view.values.stage2.1 (2 * (group + 1)) result
  else ∃ next, CoordinateRead view.values.stage2.2 0 next ∧ next.add injection = result

def LookupGroups (view : Ood.View) (computed : Array Ext) (beta gamma injection : Coordinates) :
    Nat → Nat → List Ext → Prop
  | _, 0, values => [] = values
  | group, remaining + 1, values =>
    ∃ source target equation rest,
      CoordinateRead view.values.stage2.1 (2 * group) source ∧
      LookupTarget view injection group target ∧
      (let groupSize := max 1 view.values.circuit.lookupGroupSize
       GroupEquation computed
         (view.values.circuit.lookups.extract (group * groupSize) ((group + 1) * groupSize))
         beta gamma (target.sub source) equation) ∧
      LookupGroups view computed beta gamma injection (group + 1) remaining rest ∧
      equation.c0 :: equation.c1 :: rest = values

def LookupValues (view : Ood.View) (computed values : Array Ext) : Prop :=
  (view.values.stage2.1.size = view.values.circuit.stage2Width ∧
    view.values.stage2.2.size = view.values.circuit.stage2Width) ∧
  ∃ beta gamma initial final,
    CoordinateRead view.publics 0 beta ∧ CoordinateRead view.publics 2 gamma ∧
    CoordinateRead view.publics 4 initial ∧ CoordinateRead view.publics 6 final ∧
    LookupGroups view computed beta gamma
      (((final.sub initial).scale view.selectors.injectionNorm).scale view.selectors.last)
      0 view.values.circuit.lookupGroups values.toList

def ClaimPolynomial (gamma : Ext) (claim : Array Field) : Ext :=
  claim.toList.foldr (fun value acc => (acc.mul gamma).add (Arithmetic.embed value)) Arithmetic.zero

def InitialAccumulator (challenges : Transcript.Challenges) :
    List (Array Field) → Ext → Ext → Prop
  | [], initial, final => initial = final
  | claim :: claims, initial, final =>
    ∃ reciprocal,
      ExtensionInverse (challenges.lookup.add (ClaimPolynomial challenges.fingerprint claim)) reciprocal ∧
      InitialAccumulator challenges claims (initial.add reciprocal) final

def QuotientSum (pointPowerN : Ext) : List Ext → Ext → Ext → Ext → Prop
  | [], _, initial, result => initial = result
  | c0 :: c1 :: rest, power, initial, result =>
    QuotientSum pointPowerN rest (power.mul pointPowerN)
      (initial.add (power.mul (c0.add (c1.mul Arithmetic.basis)))) result
  | [_], _, _, _ => False

def QuotientValue (values : Shape.CircuitValues) (pointPowerN result : Ext) : Prop :=
  values.quotient.size = 2 * Shape.quotientDegree values.circuit ∧
    QuotientSum pointPowerN values.quotient.toList Arithmetic.one Arithmetic.zero result

def OodEvaluation (challenges : Transcript.Challenges) (initial final : Ext)
    (values : Shape.CircuitValues) (result : Ood.Evaluation) : Prop :=
  ∃ selectors computed userConstraints lookupConstraints quotient,
    SelectorsAt values.logDegree challenges.zeta selectors ∧
    (let publics := #[Arithmetic.embed challenges.lookup.c0, Arithmetic.embed challenges.lookup.c1,
        Arithmetic.embed challenges.fingerprint.c0, Arithmetic.embed challenges.fingerprint.c1,
        Arithmetic.embed initial.c0, Arithmetic.embed initial.c1,
        Arithmetic.embed final.c0, Arithmetic.embed final.c1]
     let view : Ood.View := { values, publics, selectors }
     GraphValues view #[] values.circuit.nodes.toList computed ∧
     References computed values.circuit.zeros.toList userConstraints.toList ∧
     LookupValues view computed lookupConstraints) ∧
    (userConstraints ++ lookupConstraints).size = values.circuit.constraintCount ∧
    QuotientValue values selectors.pointPowerN quotient ∧
    (let constraints := userConstraints ++ lookupConstraints
     Ood.Evaluation.mk constraints
       (constraints.foldl (fun acc value => (acc.mul challenges.alpha).add value) Arithmetic.zero)
       quotient selectors.invVanishing) = result

def OodChain (challenges : Transcript.Challenges) :
    List Shape.CircuitValues → List Ext → Ext → List Ood.Evaluation → Prop
  | [], [], _, [] => True
  | values :: rest, final :: finals, initial, evaluation :: evaluations =>
    OodEvaluation challenges initial final values evaluation ∧
    evaluation.composition.mul evaluation.invVanishing = evaluation.quotient ∧
    OodChain challenges rest finals final evaluations
  | _, _, _, _ => False

def OodAccepted (challenges : Transcript.Challenges) (claims : Array (Array Field))
    (values : Array Shape.CircuitValues) (accumulators : Array Ext) (evaluations : Array Ood.Evaluation) : Prop :=
  accumulators.back? = some Arithmetic.zero ∧ values.size = accumulators.size ∧
    ∃ initial, InitialAccumulator challenges claims.toList Arithmetic.zero initial ∧
      OodChain challenges values.toList accumulators.toList initial evaluations.toList

end MultiStark.Verify.Protocol
