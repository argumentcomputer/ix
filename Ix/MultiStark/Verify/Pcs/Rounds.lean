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

/-- Reconstruct the native PCS rounds from the key and admitted active proof
shape. Quotient slices use the TRACE domain, not the larger quotient domain.
Preprocessed matrices retain all canonical slots, including inactive ones. -/
def rounds (key : Key) (proof : Proof) (zeta : Ext) : Except Error (Array Round) := do
  let values ← (Shape.check key proof).mapError Error.shape
  let mut main := #[]
  let mut lookup := #[]
  let mut quotient := #[]
  for value in values do
    main := main.push (← twoPoints value.logDegree value.circuit.mainWidth zeta value.stage1)
    lookup := lookup.push (← twoPoints value.logDegree value.circuit.stage2Width zeta value.stage2)
    quotient := quotient.push (Matrix.mk value.logDegree (2 * Shape.quotientDegree value.circuit)
      #[⟨zeta, value.quotient⟩])
  let mut result := #[⟨proof.commitments.stage1, main⟩, ⟨proof.commitments.stage2, lookup⟩,
    Round.mk proof.commitments.quotient quotient]
  match key.preprocessed with
  | none => return result
  | some commitment =>
    let mut matrices := #[]
    for index in [0:key.circuits.size] do
      match key.preprocessedIndices[index]?, key.circuits[index]? with
      | some (some _), some circuit =>
        match values.find? (·.index == index) with
        | some value =>
          let matrix ← twoPoints value.logDegree circuit.preprocessedWidth zeta value.preprocessed
          matrices := matrices.push matrix
        | none => matrices := matrices.push ⟨circuit.preprocessedHeight.log2, circuit.preprocessedWidth, #[]⟩
      | some none, some _ => pure ()
      | _, _ => throw .count
    result := result.push ⟨commitment, matrices⟩
    return result

end MultiStark.Verify.Pcs
