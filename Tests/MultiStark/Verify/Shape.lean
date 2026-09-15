module
import Tests.Ixby.Common
import Ix.MultiStark.Verify.Shape

namespace Tests.MultiStark.Verify.Shape

open _root_.MultiStark.Verify
open Tests.Ixby (Check runChecks)

private def zero : Ext := ⟨0, 0⟩
private def params : Parameters := ⟨1, 0, 0, 1, 3, 0, 0⟩
private def circuit : Circuit := ⟨1, 0, 0, 1, 1, #[.const 0], #[0], #[]⟩
private def key : Key := ⟨params, #[circuit], none, #[none]⟩
private def proof : Proof := {
  active := #[true], commitments := ⟨#[], #[], #[]⟩
  accumulators := #[zero], logDegrees := #[2], fri := ⟨#[], #[], #[], #[], #[], 0⟩
  quotient := #[#[#[zero, zero]]], preprocessed := none
  stage1 := #[#[#[zero], #[zero]]], stage2 := #[#[#[zero, zero], #[zero, zero]]] }
private def rejected (proof : Proof) : Bool := !(Shape.check key proof).isOk

private def prepCircuit : Circuit := { circuit with preprocessedWidth := 1, preprocessedHeight := 4 }
private def prepKey : Key := {
  params, circuits := #[prepCircuit, circuit, prepCircuit]
  preprocessed := some #[⟨Array.replicate 32 0, by simp⟩]
  preprocessedIndices := #[some 0, none, some 1] }
private def prepProof : Proof := { proof with
  active := #[false, true, true], accumulators := #[zero, zero], logDegrees := #[3, 2]
  quotient := proof.quotient ++ proof.quotient, stage1 := proof.stage1 ++ proof.stage1
  stage2 := proof.stage2 ++ proof.stage2
  preprocessed := some #[#[], #[#[zero], #[zero]]] }

private def checks : IO (List Check) := do
  return [
    ("one active circuit has the expected shape", (Shape.check key proof).isOk),
    ("shape admission is not cryptographic verification", (Shape.check key
      { proof with accumulators := #[⟨1, 0⟩] }).isOk),
    ("sparse arrays follow active position, not canonical index", match Shape.check prepKey prepProof with
      | .ok values => values.map (·.index) == #[1, 2] && values.map (·.logDegree) == #[3, 2]
      | .error _ => false),
    ("empty activation rejected", rejected { proof with active := #[] }),
    ("all-inactive activation rejected", rejected { proof with active := #[false] }),
    ("extra activation flag rejected", rejected { proof with active := #[true, false] }),
    ("missing accumulator rejected", rejected { proof with accumulators := #[] }),
    ("extra degree rejected", rejected { proof with logDegrees := #[2, 2] }),
    ("missing stage1 circuit rejected", rejected { proof with stage1 := #[] }),
    ("extra stage2 circuit rejected", rejected { proof with stage2 := proof.stage2 ++ proof.stage2 }),
    ("wrong point count rejected", rejected { proof with stage1 := #[#[#[zero]]] }),
    ("extra point rejected", rejected { proof with stage1 := #[#[#[zero], #[zero], #[zero]]] }),
    ("wrong stage1 width rejected", rejected { proof with stage1 := #[#[#[], #[]]] }),
    ("wrong stage2 width rejected", rejected { proof with stage2 := proof.stage1 }),
    ("quotient point count rejected", rejected { proof with quotient := #[#[#[zero, zero], #[]]] }),
    ("quotient width includes both extension coordinates", rejected { proof with quotient := #[#[#[zero]]] }),
    ("oversized trace shift rejected", rejected { proof with logDegrees := #[255] }),
    ("two-adicity boundary accepted by shape alone", (Shape.check key { proof with logDegrees := #[31] }).isOk),
    ("two-adicity overflow rejected", rejected { proof with logDegrees := #[32] }),
    ("inactive preprocessing matrix must be opened at no points", !(Shape.check prepKey
      { prepProof with preprocessed := some #[#[#[zero], #[zero]], #[#[zero], #[zero]]] }).isOk),
    ("inactive preprocessing slot cannot be omitted", !(Shape.check prepKey
      { prepProof with preprocessed := some #[#[#[zero], #[zero]]] }).isOk),
    ("active preprocessing width checked", !(Shape.check prepKey
      { prepProof with preprocessed := some #[#[], #[#[], #[]]] }).isOk),
    ("active preprocessing height pinned to key", !(Shape.check prepKey
      { prepProof with logDegrees := #[3, 3] }).isOk),
    ("absent preprocessing opens no matrices", rejected { proof with preprocessed := some #[#[]] }),
    ("empty preprocessing Option matches native shape semantics", (Shape.check key
      { proof with preprocessed := some #[] }).isOk),
    ("invalid key cannot enter shape checking", !(Shape.check
      { key with circuits := #[{ circuit with nodes := #[.neg 0] }] } proof).isOk),
    ("quotient padding follows the native next-power-of-two rule",
      #[0, 1, 2, 3, 4, 5, 6, 9].map (fun degree => Shape.quotientDegree
        { circuit with maxConstraintDegree := degree }) == #[1, 1, 1, 2, 4, 4, 8, 8])
  ]

public def suite : IO UInt32 := runChecks "stage2-shape" checks

end Tests.MultiStark.Verify.Shape
