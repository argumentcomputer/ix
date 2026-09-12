module
public import Ix.MultiStark.Verify.Codec.Wire
public import Ix.MultiStark.Verify.Key.Basic

/-! Canonical pure codec for `crates/aiur/src/vk_codec.rs` at the PR's current
revision. The executable native encoder (not its stale module-header diagram)
uses u16 node/zero/lookup counts and NO per-circuit length prefix. This format
has no in-band version byte; the caller must pin the dense-v5 protocol identity.
Unknown tags, noncanonical field constants, alternate small-constant forms,
trailing bytes, narrowing, and resource exhaustion all fail explicitly. -/

public section
@[expose] section

namespace MultiStark.Verify.Codec

namespace KeyWire

open Wire

def readParameters : Reader Parameters := return {
  logBlowup := ← readNat 2, capHeight := ← readNat 2,
  logFinalPolyLen := ← readNat 2, maxLogArity := ← readNat 2,
  numQueries := ← readNat 2, commitPowBits := ← readNat 2, queryPowBits := ← readNat 2 }

def writeParameters (params : Parameters) : Writer Unit :=
  writeList (writeNat 2) params.words.toList

def readNode : Reader Node := do
  match ← readByte with
  | 0 => return .const (Ix.Ixby.Goldilocks.reduce (← readNat 2))
  | 1 => return .const (← readField)
  | 2 => return .public (← readNat 1)
  | 3 => return .first
  | 4 => return .last
  | 5 => return .transition
  | 6 => return .add (← readNat 2) (← readNat 2)
  | 7 => return .sub (← readNat 2) (← readNat 2)
  | 8 => return .mul (← readNat 2) (← readNat 2)
  | 9 => return .neg (← readNat 2)
  | 10 => return .var .preprocessed false (← readNat 2)
  | 11 => return .var .preprocessed true (← readNat 2)
  | 12 => return .var .main false (← readNat 2)
  | 13 => return .var .main true (← readNat 2)
  | 14 => return .var .stage2 false (← readNat 2)
  | 15 => return .var .stage2 true (← readNat 2)
  | _ => throw .tag

def writeNode : Node → Writer Unit
  | .const value => do
    if value.val < 65536 then writeByte 0; writeNat 2 value.val
    else writeByte 1; writeField value
  | .public index => do writeByte 2; writeNat 1 index
  | .first => writeByte 3
  | .last => writeByte 4
  | .transition => writeByte 5
  | .add left right => do writeByte 6; writeNat 2 left; writeNat 2 right
  | .sub left right => do writeByte 7; writeNat 2 left; writeNat 2 right
  | .mul left right => do writeByte 8; writeNat 2 left; writeNat 2 right
  | .neg child => do writeByte 9; writeNat 2 child
  | .var source next column => do
    let source := match source with | .preprocessed => 0 | .main => 1 | .stage2 => 2
    writeByte (10 + 2 * source + if next then 1 else 0)
    writeNat 2 column

def readLookup : Reader Lookup := return ⟨← readNat 2, ← readVectorWidth 2 (readNat 2)⟩

def writeLookup (lookup : Lookup) : Writer Unit := do
  writeNat 2 lookup.multiplicity
  writeVectorWidth 2 (writeNat 2) lookup.args

def readCircuit : Reader Circuit := return {
  mainWidth := ← readNat 2, preprocessedWidth := ← readNat 2,
  preprocessedHeight := ← readNat 4, maxConstraintDegree := ← readNat 2,
  lookupGroupSize := ← readNat 1, nodes := ← readVectorWidth 2 readNode,
  zeros := ← readVectorWidth 2 (readNat 2), lookups := ← readVectorWidth 2 readLookup }

def writeCircuit (circuit : Circuit) : Writer Unit := do
  writeNat 2 circuit.mainWidth
  writeNat 2 circuit.preprocessedWidth
  writeNat 4 circuit.preprocessedHeight
  writeNat 2 circuit.maxConstraintDegree
  writeNat 1 circuit.lookupGroupSize
  writeVectorWidth 2 writeNode circuit.nodes
  writeVectorWidth 2 (writeNat 2) circuit.zeros
  writeVectorWidth 2 writeLookup circuit.lookups

def readIndex : Reader (Option Nat) := do
  let index ← readNat 2
  return if index == 65535 then none else some index

def writeIndex : Option Nat → Writer Unit
  | none => writeNat 2 65535
  | some index => do
    if index ≥ 65535 then throw .integerRange
    writeNat 2 index

def read : Reader Key := do
  let params ← readParameters
  let circuits ← readVectorWidth 2 readCircuit
  let preprocessed ← readOption (readVectorWidth 2 readDigest)
  let preprocessedIndices ← readCounted circuits.size readIndex
  return { params, circuits, preprocessed, preprocessedIndices }

def write (key : Key) : Writer Unit := do
  unless key.preprocessedIndices.size == key.circuits.size do throw .shape
  writeParameters key.params
  writeVectorWidth 2 writeCircuit key.circuits
  writeOption (writeVectorWidth 2 writeDigest) key.preprocessed
  writeCounted writeIndex key.preprocessedIndices

end KeyWire

def encodeKey (limits : DecodeLimits) (key : Key) : Except DecodeError Bytes :=
  Wire.encode limits (KeyWire.write key)

def decodeKey (limits : DecodeLimits) (bytes : Bytes) :
    Except DecodeError (Canonical (encodeKey limits) bytes) := do
  let key ← Wire.decode limits bytes KeyWire.read
  Wire.canonicalize (encodeKey limits) bytes key

end MultiStark.Verify.Codec
