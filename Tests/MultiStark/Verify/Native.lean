module
import Tests.MultiStark
import Ix.MultiStark.Verify.Codec
import Ix.MultiStark.Verify.Key
import Ix.MultiStark.Verify.Shape
import Ix.MultiStark.Verify.Transcript
import Ix.MultiStark.Verify.Ood
import Ix.MultiStark.Verify.Pcs
import Ix.MultiStark.Verify.Check

/-! Opt-in differential against a genuinely proved, natively verified current
Stage 2 multiproof. The production pure codec imports none of this test FFI. -/

namespace Tests.MultiStark.Verify.Native

open LSpec Aiur

public def suite : IO UInt32 := do
  let compiled ← match Tests.MultiStark.factorialProgram.compile with
    | .error error => IO.eprintln s!"factorial compile: {error}"; return 1
    | .ok compiled => pure compiled
  let some index := compiled.getFuncIdx `fact_entry
    | IO.eprintln "missing factorial entry"; return 1
  let system := AiurSystem.build compiled.bytecode
    Tests.MultiStark.recCommitParams Tests.MultiStark.innerFri
  let (claim, proof, _) ← match system.prove index #[Aiur.G.ofNat 5] default with
    | .error error => IO.eprintln s!"native proof: {error}"; return 1
    | .ok result => pure result
  let advice ← match system.proofToAdviceBytes claim proof with
    | .error error => IO.eprintln s!"native verify/serialize: {error}"; return 1
    | .ok bytes => pure bytes
  let native := proof.toBytes
  let nativeKey := system.vkBytes
  let nativeClaims := Tests.MultiStark.serializeClaims #[claim]
  let decodedKey := _root_.MultiStark.Verify.Codec.decodeKey {} nativeKey.data
  let decodedClaims := _root_.MultiStark.Verify.Codec.decodeClaims {} nativeClaims.data
  let keyChecks := match decodedKey with
    | .error error => test s!"pure native key decode: {repr error}" false
    | .ok checked =>
      let admission := _root_.MultiStark.Verify.validateKey checked.value
      let roundTrip : Bool := match _root_.MultiStark.Verify.Codec.encodeKey {} checked.value with
        | .ok bytes => bytes == nativeKey.data | .error _ => false
      test "native key pure exact byte round trip" roundTrip ++
      test s!"native key structural admission ({repr admission})" admission.isOk ++
      test "native key pins current query count" (checked.value.params.numQueries == 3) ++
      test "native key plus trailing byte is rejected"
        (!(_root_.MultiStark.Verify.Codec.decodeKey {} (nativeKey.data.push 0)).isOk)
  let decoded := _root_.MultiStark.Verify.Codec.decodeProof {} native.data
  let phaseChecks := match decodedKey, decodedClaims, decoded with
    | .ok key, .ok claims, .ok proof =>
      let shape := _root_.MultiStark.Verify.Shape.check key.value proof.value
      let transcript := _root_.MultiStark.Verify.Transcript.replay {} key.value claims.value proof.value
      let complete := _root_.MultiStark.Verify.checkTyped {} key.value claims.value proof.value
      let oodChecks := match shape, transcript with
        | .ok values, .ok (challenges, state) =>
          let ood := _root_.MultiStark.Verify.Ood.check challenges claims.value values proof.value.accumulators
          let pcs := _root_.MultiStark.Verify.Pcs.check {} key.value proof.value challenges.zeta state
          let pcsRejects (fri : _root_.MultiStark.Verify.FriProof) : Bool :=
            !(_root_.MultiStark.Verify.Pcs.check {} key.value
              { proof.value with fri } challenges.zeta state).isOk
          let wrongQuotient := values.modify 0 fun value =>
            { value with quotient := value.quotient.modify 0 (·.add _root_.MultiStark.Verify.Arithmetic.one) }
          let wrongClaims := claims.value.map fun claim => claim.modify (claim.size - 1) (·.add 1)
          let wrongClaimResult : Bool := match
              _root_.MultiStark.Verify.Transcript.replay {} key.value wrongClaims proof.value with
            | .error _ => false
            | .ok (challenges, _) =>
              !(_root_.MultiStark.Verify.Ood.check challenges wrongClaims values proof.value.accumulators).isOk
          test s!"native AIR/logUp/OOD equations ({repr (ood.map (fun _ => ()))})" ood.isOk ++
          test s!"native complete pure MMCS/PCS/FRI ({repr (pcs.map (fun _ => ()))})" pcs.isOk ++
          test "PCS rejects missing input authentication hashes"
            (pcsRejects { proof.value.fri with
              inputOpenings := proof.value.fri.inputOpenings.map fun opening => { opening with frontier := #[] } }) ++
          test "PCS rejects missing FRI authentication hashes"
            (pcsRejects { proof.value.fri with
              commitOpenings := proof.value.fri.commitOpenings.map fun opening => { opening with frontier := #[] } }) ++
          test "PCS rejects a changed private input row"
            (pcsRejects { proof.value.fri with
              inputOpenings := proof.value.fri.inputOpenings.modify 0 fun opening => { opening with
                values := opening.values.modify 0 fun query =>
                  query.modify 0 fun row => row.modify 0 (·.add 1) } }) ++
          test "PCS rejects a changed FRI sibling value"
            (pcsRejects { proof.value.fri with
              commitOpenings := proof.value.fri.commitOpenings.modify 0 fun opening => { opening with
                siblings := opening.siblings.modify 0 fun row =>
                  row.modify 0 (·.add _root_.MultiStark.Verify.Arithmetic.one) } }) ++
          test "PCS rejects a changed final polynomial"
            (pcsRejects { proof.value.fri with
              finalPoly := proof.value.fri.finalPoly.modify 0 (·.add _root_.MultiStark.Verify.Arithmetic.one) }) ++
          test "PCS rejects zero folding arity"
            (pcsRejects { proof.value.fri with
              commitOpenings := proof.value.fri.commitOpenings.modify 0 fun opening => { opening with logArity := 0 } }) ++
          test "OOD rejects a changed quotient coefficient"
            (!(_root_.MultiStark.Verify.Ood.check challenges claims.value wrongQuotient proof.value.accumulators).isOk) ++
          test "OOD rejects a changed public claim after transcript replay" wrongClaimResult ++
          test "OOD rejects a singular evaluation point"
            (!(_root_.MultiStark.Verify.Ood.check
              { challenges with zeta := _root_.MultiStark.Verify.Arithmetic.one }
              claims.value values proof.value.accumulators).isOk)
        | _, _ => test "shape and transcript available for native OOD checks" false
      let claimRoundTrip : Bool := match _root_.MultiStark.Verify.Codec.encodeClaims {} claims.value with
        | .ok bytes => bytes == nativeClaims.data | .error _ => false
      test "native claims exact byte round trip" claimRoundTrip ++
      test s!"unified pure typed verifier ({repr complete})" complete.isOk ++
      test s!"native proof shape ({repr (shape.map (fun _ => ()))})" shape.isOk ++
      test s!"native Fiat-Shamir prefix replay ({repr (transcript.map (fun _ => ()))})" transcript.isOk ++
      test "native proof missing active openings rejected"
        (!(_root_.MultiStark.Verify.Shape.check key.value { proof.value with stage1 := #[] }).isOk) ++
      test "native proof oversized trace height rejected"
        (!(_root_.MultiStark.Verify.Shape.check key.value
          { proof.value with logDegrees := proof.value.logDegrees.set! 0 255 }).isOk) ++ oodChecks
    | _, _, _ => test "native key, claims, and proof decoded for phase checks" false
  let checks := match decoded with
    | .error error => test s!"pure native multiproof decode: {repr error}" false
    | .ok decoded =>
      let roundTrip : Bool := match
          _root_.MultiStark.Verify.Codec.encodeProof {} decoded.value with
        | .ok bytes => bytes == native.data
        | .error _ => false
      test "native proof and verified advice use the same current transport" (native == advice) ++
      test "native proof has nonempty active circuit set" (decoded.value.active.any id) ++
      test "native proof active-indexed arrays agree"
        ((decoded.value.active.filter id).size == decoded.value.accumulators.size &&
          decoded.value.accumulators.size == decoded.value.logDegrees.size) ++
      test "native input multiproofs preserve all query rows"
        (decoded.value.fri.inputOpenings.all (·.values.size == 3)) ++
      test "native commit-phase multiproofs preserve all query rows"
        (decoded.value.fri.commitOpenings.all (·.siblings.size == 3)) ++
      test "pure codec exact byte round trip" roundTrip ++
      test "native proof plus trailing byte is rejected"
        (!(_root_.MultiStark.Verify.Codec.decodeProof {} (native.data.push 0)).isOk)
  IO.println s!"Current native Stage 2 multiproof codec vector: {native.size} bytes"
  IO.println s!"Current native Stage 2 dense-v5 key vector: {nativeKey.size} bytes"
  lspecIO (.ofList [("stage2-codec-real", [keyChecks ++ phaseChecks ++ checks])]) []

end Tests.MultiStark.Verify.Native
