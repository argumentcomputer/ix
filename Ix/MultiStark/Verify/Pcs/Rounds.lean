module
public import Ix.MultiStark.Verify.Pcs.Basic
public import Ix.MultiStark.Verify.Shape

public section
@[expose] section

namespace MultiStark.Verify.Pcs

inductive Error where
  | arithmetic (error : Arithmetic.Error)
  | shape (error : Shape.Error)
  | count
  deriving BEq, DecidableEq, Repr, Inhabited

def twoPoints (logDegree width : Nat) (zeta : Ext) (rows : Array Ext × Array Ext) :
    Except Error Matrix := do
  let g ← (Arithmetic.twoAdicGenerator logDegree).mapError Error.arithmetic
  return ⟨logDegree, width, #[⟨zeta, rows.1⟩, ⟨Arithmetic.scale zeta g, rows.2⟩]⟩

def activeMatrices (zeta : Ext) : List Shape.CircuitValues → Except Error (List Matrix × List Matrix × List Matrix)
  | [] => .ok ([], [], [])
  | value :: values => do
    let main ← twoPoints value.logDegree value.circuit.mainWidth zeta value.stage1
    let lookup ← twoPoints value.logDegree value.circuit.stage2Width zeta value.stage2
    let quotient := Matrix.mk value.logDegree (2 * Shape.quotientDegree value.circuit) #[⟨zeta, value.quotient⟩]
    let (mains, lookups, quotients) ← activeMatrices zeta values
    return (main :: mains, lookup :: lookups, quotient :: quotients)

def preprocessedMatrix (circuit : Circuit) (values : Array Shape.CircuitValues) (zeta : Ext) (index : Nat) :
    Except Error Matrix :=
  match values.find? (·.index == index) with
  | some value => twoPoints value.logDegree circuit.preprocessedWidth zeta value.preprocessed
  | none => .ok ⟨circuit.preprocessedHeight.log2, circuit.preprocessedWidth, #[]⟩

def preprocessedMatrices (key : Key) (values : Array Shape.CircuitValues) (zeta : Ext) :
    List Circuit → Nat → Except Error (List Matrix)
  | [], _ => .ok []
  | circuit :: circuits, index =>
    match key.preprocessedIndices[index]? with
    | some (some _) => do
      let matrix ← preprocessedMatrix circuit values zeta index
      let rest ← preprocessedMatrices key values zeta circuits (index + 1)
      return matrix :: rest
    | some none => preprocessedMatrices key values zeta circuits (index + 1)
    | none => .error .count

/-- Reconstruct the native PCS rounds from the key and admitted active proof
shape. Quotient slices use the TRACE domain, not the larger quotient domain.
Preprocessed matrices retain all canonical slots, including inactive ones. -/
def rounds (key : Key) (proof : Proof) (zeta : Ext) : Except Error (Array Round) := do
  let values ← (Shape.check key proof).mapError Error.shape
  let (main, lookup, quotient) ← activeMatrices zeta values.toList
  let result := #[⟨proof.commitments.stage1, main.toArray⟩, ⟨proof.commitments.stage2, lookup.toArray⟩,
    Round.mk proof.commitments.quotient quotient.toArray]
  match key.preprocessed with
  | none => return result
  | some commitment =>
    let matrices ← preprocessedMatrices key values zeta key.circuits.toList 0
    return result.push ⟨commitment, matrices.toArray⟩

end MultiStark.Verify.Pcs
