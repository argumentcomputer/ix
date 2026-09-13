/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ExpressionGraph

/-! Total host codec for the dense v5 verifying-key format in `vk_codec.rs`.
The decoded graph retains every serialized field. Derived widths, degrees,
lookup prefixes and constraint counts use the native Goldilocks extension
degree two. This module does not implement the PCS or instantiate a native
verifier refinement assumption. -/

namespace Aiur.NativeAIR.KeyCodec

abbrev Reader := StateT (List UInt8) Option

def readByte : Reader UInt8
  | [] => none
  | byte :: rest => some (byte, rest)

def readNat : Nat → Reader Nat
  | 0 => pure 0
  | count + 1 => do
    let byte ← readByte
    let rest ← readNat count
    return byte.toNat + 256 * rest

def readMany (read : Reader α) : Nat → Reader (List α)
  | 0 => pure []
  | count + 1 => do
    let first ← read
    let rest ← readMany read count
    return first :: rest

def readVector (read : Reader α) : Reader (List α) := do
  readMany read (← readNat 2)

def encodeNat : Nat → Nat → List UInt8
  | 0, _ => []
  | count + 1, value => value.toUInt8 :: encodeNat count (value / 256)

def encodeVector (encode : α → List UInt8) (values : List α) : List UInt8 :=
  encodeNat 2 values.length ++ values.flatMap encode

def readNode : Reader Node := do
  match (← readByte).toNat with
  | 0 => return .konst (G.ofNat (← readNat 2))
  | 1 => return .konst (G.ofNat (← readNat 8))
  | 2 => return .publicInput (← readNat 1)
  | 3 => return .isFirstRow
  | 4 => return .isLastRow
  | 5 => return .isTransition
  | 6 => return .add (← readNat 2) (← readNat 2)
  | 7 => return .sub (← readNat 2) (← readNat 2)
  | 8 => return .mul (← readNat 2) (← readNat 2)
  | 9 => return .neg (← readNat 2)
  | 10 => return .var ⟨.preprocessed, .current, ← readNat 2⟩
  | 11 => return .var ⟨.preprocessed, .next, ← readNat 2⟩
  | 12 => return .var ⟨.main, .current, ← readNat 2⟩
  | 13 => return .var ⟨.main, .next, ← readNat 2⟩
  | 14 => return .var ⟨.stage2, .current, ← readNat 2⟩
  | 15 => return .var ⟨.stage2, .next, ← readNat 2⟩
  | _ => failure

def encodeNode : Node → List UInt8
  | .konst value => if value.n < 65536 then 0 :: encodeNat 2 value.n else 1 :: encodeNat 8 value.n
  | .publicInput index => 2 :: encodeNat 1 index
  | .isFirstRow => [3]
  | .isLastRow => [4]
  | .isTransition => [5]
  | .add a b => 6 :: (encodeNat 2 a ++ encodeNat 2 b)
  | .sub a b => 7 :: (encodeNat 2 a ++ encodeNat 2 b)
  | .mul a b => 8 :: (encodeNat 2 a ++ encodeNat 2 b)
  | .neg child => 9 :: encodeNat 2 child
  | .var column =>
    let tag : UInt8 := match column.source, column.offset with
      | .preprocessed, .current => 10 | .preprocessed, .next => 11
      | .main, .current => 12 | .main, .next => 13
      | .stage2, .current => 14 | .stage2, .next => 15
    tag :: encodeNat 2 column.index

def readLookup : Reader Lookup := do
  let multiplicity ← readNat 2
  let args ← readVector (readNat 2)
  return ⟨multiplicity, args⟩

def encodeLookup (lookup : Lookup) : List UInt8 :=
  encodeNat 2 lookup.multiplicity ++ encodeVector (encodeNat 2) lookup.args

structure Circuit where
  mainWidth : Nat
  preprocessedWidth : Nat
  preprocessedHeight : Nat
  maxConstraintDegree : Nat
  lookupGroupSize : Nat
  graph : Graph
  deriving DecidableEq, Repr

def Circuit.groups (circuit : Circuit) : Nat :=
  max 1 ((circuit.graph.lookups.length + circuit.lookupGroupSize - 1) / circuit.lookupGroupSize)

def Circuit.widths (circuit : Circuit) : GraphWidths :=
  ⟨circuit.preprocessedWidth, circuit.mainWidth, circuit.groups * 2, 8⟩

def Circuit.constraintCount (circuit : Circuit) : Nat :=
  circuit.graph.zeros.length + circuit.groups * 2

def nodeDegree (degrees : Array Nat) : Node → Option Nat
  | .konst _ | .publicInput _ | .isTransition => some 0
  | .var _ | .isFirstRow | .isLastRow => some 1
  | .add a b | .sub a b => return max (← degrees[a]?) (← degrees[b]?)
  | .mul a b => do
    let sum := (← degrees[a]?) + (← degrees[b]?)
    if sum < 2^32 then some sum else none
  | .neg child => degrees[child]?

def nodeDegreesFrom : List Node → Array Nat → Option (Array Nat)
  | [], degrees => some degrees
  | node :: nodes, degrees => do
    nodeDegreesFrom nodes (degrees.push (← nodeDegree degrees node))

def lookupDegrees (degrees : Array Nat) (lookup : Lookup) : Option (Nat × Nat) := do
  let multiplicity ← degrees[lookup.multiplicity]?
  let args ← lookup.args.mapM (fun index => degrees[index]?)
  return (multiplicity, args.foldr max 0)

/-- The at-most-eight-term native analytic logUp degree calculation. `Nat`
arithmetic agrees with its u64 intermediates when all node degrees fit u32. -/
def groupDegree (degrees : List (Nat × Nat)) : Nat :=
  let sum := (degrees.map Prod.snd).sum
  (degrees.map (fun (multiplicity, message) => multiplicity + sum - message)).foldr max (sum + 1)

def Circuit.computedDegree (circuit : Circuit) : Option Nat := do
  let degrees ← nodeDegreesFrom circuit.graph.nodes #[]
  let zeros ← circuit.graph.zeros.mapM (fun index => degrees[index]?)
  let lookups ← circuit.graph.lookups.mapM (lookupDegrees degrees)
  let groups := (List.range circuit.groups).map fun index =>
    groupDegree ((lookups.drop (index * circuit.lookupGroupSize)).take circuit.lookupGroupSize)
  return groups.foldr max (max 1 (zeros.foldr max 0))

def Circuit.valid (circuit : Circuit) : Bool :=
  1 ≤ circuit.lookupGroupSize && circuit.lookupGroupSize ≤ 8 &&
    (checkedGraphPrefix circuit.widths circuit.graph).isSome &&
    circuit.computedDegree == some circuit.maxConstraintDegree

def readCircuitData : Reader Circuit := do
  let main ← readNat 2
  let preprocessed ← readNat 2
  let height ← readNat 4
  let degree ← readNat 2
  let group ← readNat 1
  let nodes ← readVector readNode
  let zeros ← readVector (readNat 2)
  let lookups ← readVector readLookup
  return ⟨main, preprocessed, height, degree, group, ⟨nodes, zeros, lookups⟩⟩

def readCircuit : Reader Circuit := do
  let circuit ← readCircuitData
  if circuit.valid then return circuit else failure

def encodeCircuit (circuit : Circuit) : List UInt8 :=
  encodeNat 2 circuit.mainWidth ++ encodeNat 2 circuit.preprocessedWidth ++
  encodeNat 4 circuit.preprocessedHeight ++ encodeNat 2 circuit.maxConstraintDegree ++
  encodeNat 1 circuit.lookupGroupSize ++ encodeVector encodeNode circuit.graph.nodes ++
  encodeVector (encodeNat 2) circuit.graph.zeros ++ encodeVector encodeLookup circuit.graph.lookups

structure Parameters where
  logBlowup : Nat
  capHeight : Nat
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitProofOfWorkBits : Nat
  queryProofOfWorkBits : Nat
  deriving DecidableEq, Repr

def readParameters : Reader Parameters := do
  return ⟨← readNat 2, ← readNat 2, ← readNat 2, ← readNat 2,
    ← readNat 2, ← readNat 2, ← readNat 2⟩

def encodeParameters (parameters : Parameters) : List UInt8 :=
  [parameters.logBlowup, parameters.capHeight, parameters.logFinalPolyLen,
    parameters.maxLogArity, parameters.numQueries, parameters.commitProofOfWorkBits,
    parameters.queryProofOfWorkBits].flatMap (encodeNat 2)

abbrev MerkleCap := List (List UInt8)

def readCommitment : Reader (Option MerkleCap) := do
  match (← readByte).toNat with
  | 0 => return none
  | 1 =>
    let cap ← readVector (readMany readByte 32)
    if cap.length.isPowerOfTwo then return some cap else failure
  | _ => failure

def encodeCommitment : Option MerkleCap → List UInt8
  | none => [0]
  | some cap => 1 :: encodeVector id cap

def readIndex : Reader (Option Nat) := do
  let index ← readNat 2
  return if index = 65535 then none else some index

def encodeIndex (index : Option Nat) : List UInt8 :=
  encodeNat 2 (index.getD 65535)

structure Key where
  parameters : Parameters
  circuits : List Circuit
  preprocessedCommitment : Option MerkleCap
  preprocessedIndices : List (Option Nat)
  deriving DecidableEq, Repr

def readKey : Reader Key := do
  let parameters ← readParameters
  let circuits ← readVector readCircuit
  let commitment ← readCommitment
  let indices ← readMany readIndex circuits.length
  return ⟨parameters, circuits, commitment, indices⟩

def encodeKey (key : Key) : List UInt8 :=
  encodeParameters key.parameters ++ encodeVector encodeCircuit key.circuits ++
  encodeCommitment key.preprocessedCommitment ++ key.preprocessedIndices.flatMap encodeIndex

/-- Complete consumption is mandatory; an extra suffix is not another key. -/
def decode (bytes : ByteArray) : Option Key := do
  let (key, rest) ← readKey bytes.data.toList
  if rest.isEmpty then some key else none

def encode (key : Key) : ByteArray := (encodeKey key).toByteArray

/-- Optional canonical-byte gate. The native decoder also accepts big-tag
small constants and reduces u64 field constants; canonical encoding does not. -/
def decodeCanonical (bytes : ByteArray) : Option Key := do
  let key ← decode bytes
  if encode key = bytes then some key else none

end Aiur.NativeAIR.KeyCodec
