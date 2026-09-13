module
public import Ix.MultiStark.Verify.Arithmetic
public import Ix.MultiStark.Verify.Shape
public import Ix.MultiStark.Verify.Transcript.Replay

/-! Pure OOD selectors and compiled constraint-graph evaluation. All scalar
operations are on the challenge field, while lookup coordinates remain a
separate two-coordinate algebra. No native graph sweep or inverse is called. -/

public section
@[expose] section

namespace MultiStark.Verify.Ood

inductive Error where
  | arithmetic (error : Arithmetic.Error)
  | reference | width | count | balance | mismatch
  deriving BEq, DecidableEq, Repr, Inhabited

def getAt {α : Type} (values : Array α) (index : Nat) : Except Error α :=
  match values[index]? with | some value => .ok value | none => .error .reference

structure Selectors where
  first : Ext
  last : Ext
  transition : Ext
  invVanishing : Ext
  injectionNorm : Ext
  pointPowerN : Ext
  deriving BEq, DecidableEq, Repr

/-- Trace domains have shift one. Raw first/last selectors are NOT normalized
Lagrange basis polynomials; the last-row normalization is applied separately
to the public accumulator delta, exactly as in the native protocol. -/
def selectors (logDegree : Nat) (point : Ext) : Except Error Selectors := do
  let generator ← (Arithmetic.twoAdicGenerator logDegree).mapError Error.arithmetic
  let last ← (Arithmetic.inverseBase generator).mapError Error.arithmetic
  let pointPowerN := Arithmetic.pow2 point logDegree
  let vanishing := pointPowerN.sub Arithmetic.one
  let transition := point.sub (Arithmetic.embed last)
  let first ← (Arithmetic.divide vanishing (point.sub Arithmetic.one)).mapError Error.arithmetic
  let last ← (Arithmetic.divide vanishing transition).mapError Error.arithmetic
  let invVanishing ← (Arithmetic.inverse vanishing).mapError Error.arithmetic
  let normalization := (Ix.Ixby.Goldilocks.reduce (2 ^ logDegree)).mul generator
  let normalization ← (Arithmetic.inverseBase normalization).mapError Error.arithmetic
  return { first, last, transition, invVanishing, injectionNorm := Arithmetic.embed normalization, pointPowerN }

def publicValues (challenges : Transcript.Challenges) (initial final : Ext) : Array Ext :=
  #[Arithmetic.embed challenges.lookup.c0, Arithmetic.embed challenges.lookup.c1,
    Arithmetic.embed challenges.fingerprint.c0, Arithmetic.embed challenges.fingerprint.c1,
    Arithmetic.embed initial.c0, Arithmetic.embed initial.c1,
    Arithmetic.embed final.c0, Arithmetic.embed final.c1]

structure View where
  values : Shape.CircuitValues
  publics : Array Ext
  selectors : Selectors

def evalNode (view : View) (computed : Array Ext) : Node → Except Error Ext
  | .const value => .ok (Arithmetic.embed value)
  | .var source next column =>
    let rows := match source with
      | .preprocessed => view.values.preprocessed
      | .main => view.values.stage1
      | .stage2 => view.values.stage2
    getAt (if next then rows.2 else rows.1) column
  | .public index => getAt view.publics index
  | .first => .ok view.selectors.first
  | .last => .ok view.selectors.last
  | .transition => .ok view.selectors.transition
  | .add left right => do return (← getAt computed left).add (← getAt computed right)
  | .sub left right => do return (← getAt computed left).sub (← getAt computed right)
  | .mul left right => do return (← getAt computed left).mul (← getAt computed right)
  | .neg child => return Arithmetic.neg (← getAt computed child)

/-- Explicit first-order recursion makes the graph's data dependency and
finite termination visible to both the source compiler and refinement proof. -/
def sweepFrom (view : View) : Array Ext → List Node → Except Error (Array Ext)
  | previous, [] => .ok previous
  | previous, node :: nodes => do
    let value ← evalNode view previous node
    sweepFrom view (previous.push value) nodes

def sweep (view : View) : Except Error (Array Ext) :=
  sweepFrom view #[] view.values.circuit.nodes.toList

def readRefs (computed : Array Ext) : List Nat → Except Error (List Ext)
  | [] => .ok []
  | index :: indices => do
    let value ← getAt computed index
    let rest ← readRefs computed indices
    return value :: rest

def roots (circuit : Circuit) (computed : Array Ext) : Except Error (Array Ext) := do
  return (← readRefs computed circuit.zeros.toList).toArray

end MultiStark.Verify.Ood
