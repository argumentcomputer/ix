/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ProofShape
import Ix.Aiur.LogUp
import Ix.Aiur.Quotient

/-! Total arithmetic on the opened rows of an active circuit. The ordering,
coordinate embedding and boundary normalization follow the pinned native
verifier. Challenges are explicit inputs; this does not authenticate them
or the polynomial openings.
-/

namespace Aiur.NativeAIR.VerifierArithmetic

open ProofCodec (Extension)
open ProofShape (Row Pair)

structure Challenges where
  beta : Extension
  gamma : Extension
  alpha : Extension
  zeta : Extension
  deriving DecidableEq, Repr

def pairColumns (pair : Pair) : RowOffset → Array Extension
  | .current => pair.current.toArray
  | .next => pair.next.toArray

def rowColumns (row : Row) : Source → RowOffset → Array Extension
  | .preprocessed => match row.preprocessed with
    | none => fun _ => #[]
    | some pair => pairColumns pair
  | .main => pairColumns row.stage1
  | .stage2 => pairColumns row.stage2

/-- Each extension value contributes its two base coordinates, each embedded
separately into the working extension field. -/
def publics (challenges : Challenges) (entering leaving : Extension) : Array Extension :=
  #[Extension.ofBase challenges.beta.c0, Extension.ofBase challenges.beta.c1,
    Extension.ofBase challenges.gamma.c0, Extension.ofBase challenges.gamma.c1,
    Extension.ofBase entering.c0, Extension.ofBase entering.c1,
    Extension.ofBase leaving.c0, Extension.ofBase leaving.c1]

def deltaScaled (domain : Domain.Subgroup) (entering leaving : Extension) : Array Extension :=
  let normalizer := Extension.ofBase (Domain.normalizer domain).inverse
  #[(Extension.ofBase leaving.c0 - Extension.ofBase entering.c0) * normalizer,
    (Extension.ofBase leaving.c1 - Extension.ofBase entering.c1) * normalizer]

def view (challenges : Challenges) (row : Row) (entering : Extension)
    (selectors : Domain.Selectors Extension) : Values Extension :=
  ⟨rowColumns row, publics challenges entering row.accumulator,
    selectors.isFirst, selectors.isLast, selectors.isTransition⟩

structure Evaluation where
  domain : Domain.Subgroup
  selectors : Domain.Selectors Extension
  nodeValues : Array Extension
  userValues : List Extension
  lookupValues : List Extension
  quotientValue : Extension
  deriving DecidableEq, Repr

def Evaluation.constraints (result : Evaluation) : List Extension :=
  result.userValues ++ result.lookupValues

def Evaluation.accepts (result : Evaluation) (alpha : Extension) : Bool :=
  Quotient.composition alpha result.constraints * result.selectors.invVanishing == result.quotientValue

def evaluate (challenges : Challenges) (row : Row) (entering : Extension) : Option Evaluation := do
  let domain ← Domain.ofLogSize row.logDegree.toNat
  let selectors ← Domain.selectors domain challenges.zeta
  let values := view challenges row entering selectors
  let nodes ← row.circuit.graph.sweep Extension.evalOps values
  let userValues ← readNodes nodes row.circuit.graph.zeros
  let lookupValues ← LogUp.constraintValues row.circuit.graph.lookups nodes
    (values.columns .stage2 .current) (values.columns .stage2 .next) values.publics
    (deltaScaled domain entering row.accumulator) values.isLastRow row.circuit.lookupGroupSize
  let quotientValue ← Quotient.evaluate domain challenges.zeta row.quotient
  return ⟨domain, selectors, nodes, userValues, lookupValues, quotientValue⟩

def check (challenges : Challenges) (row : Row) (entering : Extension) : Option Bool := do
  return (← evaluate challenges row entering).accepts challenges.alpha

/-- The leaving accumulator of each accepted row enters the next active row. -/
def checkRows (challenges : Challenges) : List Row → Extension → Option Extension
  | [], entering => some entering
  | row :: rows, entering => do
    if ← check challenges row entering then checkRows challenges rows row.accumulator else none

def claimMessage (challenges : Challenges) (claim : List G) : Extension :=
  challenges.beta + (LogUp.fingerprint (LogUp.Coordinates.fromExtension challenges.gamma) claim).toExtension

def initialAccumulator (challenges : Challenges) (claims : List (List G)) : Option Extension := do
  let inverses ← claims.mapM fun claim => (claimMessage challenges claim).tryInverse
  return LogUp.sum inverses

def verify (challenges : Challenges) (claims : List (List G)) (rows : List Row) : Option Bool := do
  if rows.isEmpty then none else do
    let entering ← initialAccumulator challenges claims
    return (← checkRows challenges rows entering) == 0

end Aiur.NativeAIR.VerifierArithmetic
