module
import Tests.Ixby.Common
import Ix.MultiStark.Verify.Codec.Key
import Ix.MultiStark.Verify.Key

namespace Tests.MultiStark.Verify.Key

open _root_.MultiStark.Verify
open _root_.MultiStark.Verify.Codec
open Tests.Ixby (Check runChecks)

private def params : Parameters := ⟨1, 0, 0, 1, 3, 0, 0⟩
private def circuit : Circuit := ⟨1, 0, 0, 1, 1, #[.const 42], #[0], #[]⟩
private def key : Key := ⟨params, #[circuit], none, #[none]⟩
private def digest : Digest := ⟨Array.replicate 32 7, by simp⟩
private def allNodes : Circuit := {
  mainWidth := 2, preprocessedWidth := 1, preprocessedHeight := 2
  maxConstraintDegree := 2, lookupGroupSize := 1
  nodes := #[.const 42, .const 65536, .public 7, .first, .last, .transition,
    .var .preprocessed false 0, .var .preprocessed true 0,
    .var .main false 0, .var .main true 1,
    .var .stage2 false 0, .var .stage2 true 1,
    .add 0 1, .sub 12 2, .mul 13 6, .neg 14]
  zeros := #[15], lookups := #[⟨0, #[8]⟩]
}
private def fullKey : Key := ⟨params, #[allNodes], some #[digest], #[some 0]⟩

/-- Independently spelled wire, including u16 counts, no record prefix,
small constant tag 0, and the 0xffff absent-index sentinel. -/
private def golden : Bytes := #[
  1, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 1, 0,
  1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0,
  0, 42, 0, 1, 0, 0, 0, 0, 0, 0, 255, 255]

private def encoded (key : Key) : Bytes :=
  match encodeKey {} key with | .ok bytes => bytes | .error _ => #[]
private def roundTrip (key : Key) : Bool :=
  match decodeKey {} (encoded key) with
  | .ok checked => checked.value == key | .error _ => false
private def errorIs {α : Type} (result : Except DecodeError α) (error : DecodeError) : Bool :=
  match result with | .error actual => actual == error | .ok _ => false
private def rejected (circuit : Circuit) : Bool :=
  !(validateKey { key with circuits := #[circuit] }).isOk

private def okEquals {ε α : Type} [BEq α] (result : Except ε α) (expected : α) : Bool :=
  match result with | .ok actual => actual == expected | .error _ => false

private def degreeChecks : IO (List Check) := do
  let degrees := #[0, 2, 3, 5, 11]
  let lookups : Array Lookup := #[⟨4, #[1, 2]⟩, ⟨0, #[3]⟩, ⟨4, #[]⟩]
  let grouped := { circuit with lookups, lookupGroupSize := 2 }
  let doubling := { circuit with
    nodes := #[.var .main false 0] ++ (Array.range 16).map (fun index => .mul index index) }
  return [
    ("all node tags have independently expected degrees", okEquals (KeyValidation.degrees allNodes)
      #[0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1]),
    ("root degree follows checked maximum, including empty roots", okEquals (KeyValidation.maxRoots degrees #[1, 3, 2]) 5 &&
      okEquals (KeyValidation.maxRoots degrees #[]) 0),
    ("lookup degree pairs preserve message/multiplicity order", okEquals (KeyValidation.lookupDegrees degrees lookups.toList)
      [(3, 11), (5, 0), (0, 11)]),
    ("group degree includes high multiplicity times other messages", okEquals (KeyValidation.groupDegree degrees (lookups.extract 0 2)) 16),
    ("empty message multiplicity still contributes its degree", okEquals (KeyValidation.groupDegree degrees lookups) 19),
    ("empty lookup group retains the accumulator-difference degree", okEquals (KeyValidation.groupDegree degrees #[]) 1),
    ("grouped degree uses exact chunks including a partial last chunk", okEquals (KeyValidation.logupDegree grouped degrees) 16),
    ("lookup degree rejects missing multiplicity instead of truncating", !(KeyValidation.lookupDegrees degrees [⟨5, #[]⟩]).isOk),
    ("lookup degree rejects missing argument instead of defaulting", !(KeyValidation.lookupDegrees degrees [⟨0, #[5]⟩]).isOk),
    ("intermediate degree bound is exact", (KeyValidation.degrees { doubling with nodes := doubling.nodes.pop }).isOk &&
      !(KeyValidation.degrees doubling).isOk),
    ("parallel key mapping rejects either length mismatch", !(KeyValidation.circuits params 0 [circuit] [] 0).isOk &&
      !(KeyValidation.circuits params 0 [] [none] 0).isOk),
    ("canonical preprocessing slots advance only at table circuits", (validateKey {
      params, circuits := #[allNodes, circuit, allNodes], preprocessed := some #[digest],
      preprocessedIndices := #[some 0, none, some 1] }).isOk)
  ]

private def checks : IO (List Check) := do
  let bigSmall := golden.extract 0 29 ++ #[1, 42, 0, 0, 0, 0, 0, 0, 0] ++
    golden.extract 32 golden.size
  let noncanonical := golden.extract 0 29 ++ #[1, 1, 0, 0, 0, 255, 255, 255, 255] ++
    golden.extract 32 golden.size
  return (← degreeChecks) ++ [
    ("dense-v5 independent golden wire is 41 bytes", golden.size == 41 && encoded key == golden),
    ("all 16 dense node tags round trip", roundTrip fullKey),
    ("key admission is separate from canonical parsing", roundTrip
      { key with circuits := #[{ circuit with nodes := #[.neg 0] }] }),
    ("every key prefix rejected", (List.range golden.size).all (fun size =>
      !(decodeKey {} (golden.extract 0 size)).isOk)),
    ("trailing key bytes rejected", errorIs (decodeKey {} (golden.push 0)) .trailing),
    ("unknown node tag rejected", errorIs (decodeKey {} (golden.set! 29 16)) .tag),
    ("unknown preprocessed Option rejected", errorIs (decodeKey {} (golden.set! 38 2)) .tag),
    ("alternate big encoding of small constant rejected", errorIs (decodeKey {} bigSmall) .nonCanonical),
    ("noncanonical big field rejected without reduction", errorIs (decodeKey {} noncanonical) .field),
    ("u16 parameter narrowing rejected", errorIs
      (encodeKey {} { key with params := { params with numQueries := 65536 } }) .integerRange),
    ("u8 public index narrowing rejected", errorIs (encodeKey {}
      { key with circuits := #[{ circuit with nodes := #[.public 256] }] }) .integerRange),
    ("preprocessed index cannot collide with absent sentinel", errorIs
      (encodeKey {} { key with preprocessedIndices := #[some 65535] }) .integerRange),
    ("index trailer length must equal circuit count", errorIs
      (encodeKey {} { key with preprocessedIndices := #[] }) .shape),
    ("decoder byte bound enforced", errorIs (decodeKey { bytes := 40 } golden) .byteLimit),
    ("encoder byte bound enforced", errorIs (encodeKey { bytes := 40 } key) .byteLimit),
    ("decoder vector bound enforced", errorIs (decodeKey { vector := 1 } (encoded fullKey)) .vectorLimit),
    ("encoder vector bound enforced", errorIs (encodeKey { vector := 1 } fullKey) .vectorLimit),
    ("decoder global item bound enforced", errorIs (decodeKey { items := 2 } golden) .itemLimit),
    ("encoder global item bound enforced", errorIs (encodeKey { items := 2 } key) .itemLimit),
    ("simple and all-node keys structurally admitted", (validateKey key).isOk && (validateKey fullKey).isOk),
    ("no-circuit system rejected", !(validateKey ⟨params, #[], none, #[]⟩).isOk),
    ("non-progressing FRI arity rejected", !(validateKey
      { key with params := { params with maxLogArity := 0 } }).isOk),
    ("Goldilocks two-adicity bound enforced", !(validateKey
      { key with params := { params with logBlowup := 33 } }).isOk),
    ("query-free parameters rejected", !(validateKey
      { key with params := { params with numQueries := 0 } }).isOk),
    ("self-reference rejected", rejected { circuit with nodes := #[.neg 0] }),
    ("forward-reference rejected", rejected { circuit with nodes := #[.neg 1, .const 0] }),
    ("out-of-range root rejected", rejected { circuit with zeros := #[1] }),
    ("out-of-range multiplicity rejected", rejected { circuit with lookups := #[⟨1, #[]⟩] }),
    ("out-of-range lookup argument rejected", rejected { circuit with lookups := #[⟨0, #[1]⟩] }),
    ("out-of-range main column rejected", rejected { circuit with nodes := #[.var .main false 1] }),
    ("out-of-range preprocessed column rejected", rejected
      { circuit with nodes := #[.var .preprocessed false 0] }),
    ("out-of-range stage2 column rejected", rejected { circuit with nodes := #[.var .stage2 true 2] }),
    ("public input width is eight base coordinates", rejected { circuit with nodes := #[.public 8] }),
    ("zero lookup group rejected", rejected { circuit with lookupGroupSize := 0 }),
    ("oversized lookup group rejected", rejected { circuit with lookupGroupSize := 9 }),
    ("incorrect advertised degree rejected", rejected { circuit with maxConstraintDegree := 2 }),
    ("non-power-of-two preprocessing rejected", !(validateKey { fullKey with
      circuits := #[{ allNodes with preprocessedHeight := 3 }] }).isOk),
    ("missing preprocessing rejected", !(validateKey { fullKey with preprocessed := none }).isOk),
    ("out-of-range preprocessing slot rejected", !(validateKey
      { fullKey with preprocessedIndices := #[some 1] }).isOk),
    ("duplicate preprocessing slot rejected", !(validateKey { fullKey with
      circuits := #[allNodes, allNodes], preprocessedIndices := #[some 0, some 0] }).isOk),
    ("preprocessing slot permutation rejected", !(validateKey { fullKey with
      circuits := #[allNodes, allNodes], preprocessedIndices := #[some 1, some 0] }).isOk),
    ("lookup-free pass-through contributes two constraints and columns",
      circuit.shapeWords == #[3, 1, 0, 0, 1, 2, 1]),
    ("grouped lookups derive their shape from actual count", let grouped :=
      { allNodes with lookupGroupSize := 2, lookups := #[⟨0, #[8]⟩, ⟨0, #[8]⟩, ⟨0, #[8]⟩] };
      grouped.lookupGroups == 2 && grouped.stage2Width == 4 && grouped.constraintCount == 5)
  ]

public def suite : IO UInt32 := runChecks "stage2-key" checks

end Tests.MultiStark.Verify.Key
