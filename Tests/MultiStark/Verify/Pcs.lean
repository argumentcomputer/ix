module
import Tests.Ixby.Common
import Ix.MultiStark.Verify.Pcs

namespace Tests.MultiStark.Verify.Pcs

open _root_.MultiStark.Verify
open Tests.Ixby (Check runChecks)

private def e (n : Nat) : Ext := Arithmetic.fromNat n
private def cap (tag : UInt8) : MerkleCap := #[⟨Array.replicate 32 tag, by simp⟩]
private def okEquals {ε α : Type} [BEq α] (result : Except ε α) (expected : α) : Bool :=
  match result with | .ok actual => actual == expected | .error _ => false

private def checks : IO (List Check) := do
  let params : Parameters := ⟨1, 0, 0, 1, 1, 0, 0⟩
  let main : Circuit := ⟨2, 0, 0, 3, 1, #[.var .main false 0, .mul 0 0, .mul 1 0], #[2], #[]⟩
  let table := { main with mainWidth := 1, preprocessedWidth := 1, preprocessedHeight := 4 }
  let key : Key := ⟨params, #[table, main, { table with preprocessedHeight := 8 }],
    some (cap 4), #[some 0, none, some 1]⟩
  let proof : Proof := {
    active := #[false, true, true], commitments := ⟨cap 1, cap 2, cap 3⟩
    accumulators := #[e 0, e 0], logDegrees := #[2, 3]
    fri := ⟨#[], #[], #[], #[], #[], 0⟩
    quotient := #[#[#[e 41, e 42, e 43, e 44]], #[#[e 51, e 52, e 53, e 54]]]
    preprocessed := some #[#[], #[#[e 61], #[e 62]]]
    stage1 := #[#[#[e 11, e 12], #[e 13, e 14]], #[#[e 21], #[e 22]]]
    stage2 := #[#[#[e 31, e 32], #[e 33, e 34]], #[#[e 35, e 36], #[e 37, e 38]]] }
  let zeta : Ext := ⟨5, 7⟩
  let vector : Except Arithmetic.Error (List Check) := do
    let g2 ← Arithmetic.twoAdicGenerator 2
    let g3 ← Arithmetic.twoAdicGenerator 3
    let expected : Array Pcs.Round := #[
      ⟨cap 1, #[⟨2, 2, #[⟨zeta, #[e 11, e 12]⟩, ⟨Arithmetic.scale zeta g2, #[e 13, e 14]⟩]⟩,
        ⟨3, 1, #[⟨zeta, #[e 21]⟩, ⟨Arithmetic.scale zeta g3, #[e 22]⟩]⟩]⟩,
      ⟨cap 2, #[⟨2, 2, #[⟨zeta, #[e 31, e 32]⟩, ⟨Arithmetic.scale zeta g2, #[e 33, e 34]⟩]⟩,
        ⟨3, 2, #[⟨zeta, #[e 35, e 36]⟩, ⟨Arithmetic.scale zeta g3, #[e 37, e 38]⟩]⟩]⟩,
      ⟨cap 3, #[⟨2, 4, #[⟨zeta, #[e 41, e 42, e 43, e 44]⟩]⟩,
        ⟨3, 4, #[⟨zeta, #[e 51, e 52, e 53, e 54]⟩]⟩]⟩,
      ⟨cap 4, #[⟨2, 1, #[]⟩, ⟨3, 1, #[⟨zeta, #[e 61]⟩, ⟨Arithmetic.scale zeta g3, #[e 62]⟩]⟩]⟩]
    let reconstructed := Pcs.rounds key proof zeta
    let active : Shape.CircuitValues := ⟨2, { table with preprocessedHeight := 8 }, 3,
      (#[e 21], #[e 22]), (#[e 35, e 36], #[e 37, e 38]), (#[e 61], #[e 62]), #[e 51, e 52, e 53, e 54]⟩
    let simpleKey : Key := ⟨params, #[main], none, #[none]⟩
    let simpleProof := { proof with
      active := #[true], accumulators := #[e 0], logDegrees := #[2]
      quotient := proof.quotient.extract 0 1, preprocessed := none
      stage1 := proof.stage1.extract 0 1, stage2 := proof.stage2.extract 0 1 }
    return [
      (s!"sparse PCS rounds match all independent points and coordinates ({repr (reconstructed.map (fun _ => ()))})",
        okEquals reconstructed expected),
      ("quotient matrices use trace degrees, not padded quotient degrees", match reconstructed with
        | .ok rounds => match rounds[2]? with
          | some round => round.matrices.map (·.logDegree) == #[2, 3] && round.matrices.map (·.width) == #[4, 4]
          | none => false
        | .error _ => false),
      ("unpreprocessed key yields exactly three PCS rounds", match Pcs.rounds simpleKey simpleProof zeta with
        | .ok rounds => rounds.size == 3 | .error _ => false),
      ("two-point matrix preserves current/next coordinate order", okEquals
        (Pcs.twoPoints 2 1 zeta (#[e 71], #[e 72]))
        ⟨2, 1, #[⟨zeta, #[e 71]⟩, ⟨Arithmetic.scale zeta g2, #[e 72]⟩]⟩),
      ("two-point matrix rejects unsupported subgroup", !(Pcs.twoPoints 33 1 zeta (#[e 71], #[e 72])).isOk),
      ("inactive table matrix retains its key-owned degree and width", okEquals
        (Pcs.preprocessedMatrix table #[active] zeta 0) ⟨2, 1, #[]⟩),
      ("active preprocessing matches canonical index instead of active position", okEquals
        (Pcs.preprocessedMatrix active.circuit #[active] zeta 2)
        ⟨3, 1, #[⟨zeta, #[e 61]⟩, ⟨Arithmetic.scale zeta g3, #[e 62]⟩]⟩),
      ("preprocessing reconstruction checks every slot-map lookup", !(Pcs.preprocessedMatrices
        { key with preprocessedIndices := #[] } #[active] zeta key.circuits.toList 0).isOk),
      ("PCS round reconstruction rejects a permuted table map", !(Pcs.rounds
        { key with preprocessedIndices := #[some 1, none, some 0] } proof zeta).isOk),
      ("PCS round reconstruction rejects a mismatched table trace height", !(Pcs.rounds key
        { proof with logDegrees := #[2, 2] } zeta).isOk),
      ("inactive preprocessing data cannot enter the reconstructed points", !(Pcs.rounds key
        { proof with preprocessed := some #[#[#[e 1], #[e 2]], #[#[e 61], #[e 62]]] } zeta).isOk),
      ("PCS reconstruction rejects an omitted inactive table slot", !(Pcs.rounds key
        { proof with preprocessed := some #[#[#[e 61], #[e 62]]] } zeta).isOk)
    ]
  return match vector with
    | .ok checks => checks
    | .error error => [(s!"construct PCS subgroup vector ({repr error})", false)]

public def suite : IO UInt32 := runChecks "stage2-pcs" checks

end Tests.MultiStark.Verify.Pcs
