module
public import Ix.MultiStark.Verify.Codec.Wire
public import Ix.MultiStark.Verify.Key.Basic
public import Ix.Ixby.Blake3

/-! Pure `SerializingChallenger64<Goldilocks, HashChallenger<u8, Blake3, 32>>`
at Plonky3 3152b14a. Byte draws pop from the END of the digest, observations
discard pending output, and rejected field draws are consumed, not reduced.
The caller chooses an explicit per-field rejection bound. Exhaustion rejects;
there is no theorem that a finite hash must eventually produce a field word. -/

public section
@[expose] section

namespace MultiStark.Verify.Transcript

structure Challenger where
  input : Bytes := #[]
  output : Bytes := #[]
  deriving BEq, DecidableEq, Repr

structure Limits where
  observationBytes : Nat := 16777216
  sampleAttempts : Nat := 64
  deriving BEq, DecidableEq, Repr

inductive Error where
  | observationLimit | sampleExhausted | fieldRange | bitRange | pow
  deriving BEq, DecidableEq, Repr, Inhabited

abbrev Action := StateT Challenger (Except Error)

def observeBytes (limits : Limits) (bytes : Bytes) : Action Unit := fun state =>
  if bytes.isEmpty then .ok ((), state)
  else if state.input.size + bytes.size > limits.observationBytes then .error .observationLimit
  else .ok ((), { input := state.input ++ bytes, output := #[] })

def observeField (limits : Limits) (value : Field) : Action Unit :=
  observeBytes limits (Codec.Wire.littleEndian 8 value.val)

def observeNat (limits : Limits) (value : Nat) : Action Unit := do
  if canonical : value < Ix.Ixby.goldilocksModulus then observeField limits ⟨value, canonical⟩
  else throw .fieldRange

def observeChunks (limits : Limits) : List Bytes → Action Unit
  | [] => pure ()
  | bytes :: rest => do
    observeBytes limits bytes
    observeChunks limits rest

def observeNats (limits : Limits) : List Nat → Action Unit
  | [] => pure ()
  | value :: rest => do
    observeNat limits value
    observeNats limits rest

def observeExt (limits : Limits) (value : Ext) : Action Unit :=
  observeChunks limits [Codec.Wire.littleEndian 8 value.c0.val,
    Codec.Wire.littleEndian 8 value.c1.val]

def observeExts (limits : Limits) : List Ext → Action Unit
  | [] => pure ()
  | value :: rest => do
    observeExt limits value
    observeExts limits rest

def observeCap (limits : Limits) (cap : MerkleCap) : Action Unit :=
  observeChunks limits (cap.toList.map (·.bytes))

/-- Empty caps perform no observations (and hence do not discard output),
matching the native element-by-element cap observation. -/
def observeFields (limits : Limits) (values : Array Field) : Action Unit :=
  observeChunks limits (values.toList.map (fun value => Codec.Wire.littleEndian 8 value.val))

def drawByte (state : Challenger) : UInt8 × Challenger :=
  match state.output.back? with
  | some value => (value, { state with output := state.output.pop })
  | none =>
    let digest := Ix.Ixby.Blake3.hash state.input
    let last : 31 < digest.size := by rw [Ix.Ixby.Blake3.hash_size]; decide
    (digest[31], { input := digest, output := digest.pop })

def draw64 (state : Challenger) : Nat × Challenger := Id.run do
  let mut bytes := #[]
  let mut state := state
  for _ in [0:8] do
    let (byte, next) := drawByte state
    bytes := bytes.push byte
    state := next
  return (Codec.Wire.fromLittleEndian bytes, state)

def sampleFieldWith : Nat → Challenger → Except Error (Field × Challenger)
  | 0, _ => .error .sampleExhausted
  | attempts + 1, state =>
    let (raw, next) := draw64 state
    if canonical : raw < Ix.Ixby.goldilocksModulus then .ok (⟨raw, canonical⟩, next)
    else sampleFieldWith attempts next

def sampleField (limits : Limits) : Action Field := sampleFieldWith limits.sampleAttempts

def sampleExt (limits : Limits) : Action Ext :=
  return ⟨← sampleField limits, ← sampleField limits⟩

/-- This uses a raw u64 draw, NOT a rejection-sampled field draw. Even a
zero-bit sample consumes eight bytes. Only the zero-bit PoW shortcut is inert. -/
def sampleBits (bits : Nat) : Action Nat := fun state =>
  if bits ≥ 64 then .error .bitRange
  else
    let (raw, next) := draw64 state
    .ok (raw % 2 ^ bits, next)

def checkWitness (limits : Limits) (bits : Nat) (witness : Field) : Action Unit := fun state =>
  if bits == 0 then .ok ((), state)
  else if bits ≥ 64 then .error .bitRange
  else
    match observeField limits witness state with
    | .error error => .error error
    | .ok (_, observed) =>
      match sampleBits bits observed with
      | .error error => .error error
      | .ok (value, final) => if value == 0 then .ok ((), final) else .error .pow

def observeParameters (limits : Limits) : List Nat → Action Unit
  | [] => pure ()
  | word :: rest =>
    -- Parameters are fixed u16 on the key wire. Check rather than truncate
    -- an independently constructed out-of-range source record.
    if word ≥ 65536 then throw .fieldRange
    else do
      observeBytes limits (Codec.Wire.littleEndian 8 word)
      observeParameters limits rest

def seed (limits : Limits) (params : Parameters) : Except Error Challenger := do
  let action : Action Unit := do
    observeBytes limits "multi-stark/v0".toUTF8.data
    observeParameters limits params.words.toList
  let (_, state) ← action.run {}
  return state

end MultiStark.Verify.Transcript
