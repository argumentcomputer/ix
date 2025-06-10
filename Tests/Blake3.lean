import LSpec

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

namespace Utilities

def randArray (rng : StdGen) (length : Nat) : Array UInt32 :=
  let rec randArrayInner (rng : StdGen) (length : Nat) (array: Array UInt32) : Array UInt32 :=
    match length with
    | 0 => array
    | length' + 1 =>
      let (g₁, g₂) := RandomGen.split rng
      let (next, _) := RandomGen.next g₁
      randArrayInner g₂ length' (array.push next.toUInt32)

  randArrayInner rng length Array.empty

def rand8 (rng : StdGen) : Vector UInt32 8 :=
  let array := randArray rng 8
  array.toVector

def rand16 (rng : StdGen) : Vector UInt32 16 :=
  let array := randArray rng 16
  array.toVector

def transpose (initial : Array (Array UInt32)) (rowLen : Nat) : Array (Array UInt32) :=
  let rec transposeInner (initial : Array (Array UInt32)) (tmp : Array (Array UInt32)) (rowLen: Nat): Array (Array UInt32) :=
    match rowLen with
    | 0 => tmp.reverse
    | idx + 1 =>
      let col := Array.ofFn (n := initial.size) fun i => initial[i]![idx - 1]!
      transposeInner initial (tmp.push col ) idx

  transposeInner initial Array.empty rowLen

end Utilities

namespace Blake3

def IV : Vector UInt32 8 := #v[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
def MSG_PERMUTATION : Vector (Fin 16) 16  := #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
def A : Vector (Fin 32) 8 := #v[0, 1, 2, 3, 0, 1, 2, 3]
def B : Vector (Fin 32) 8 := #v[4, 5, 6, 7, 5, 6, 7, 4]
def C : Vector (Fin 32) 8 := #v[8, 9, 10, 11, 10, 11, 8, 9]
def D : Vector (Fin 32) 8 := #v[12, 13, 14, 15, 15, 12, 13, 14]
def MX : Vector (Fin 32) 8 := #v[16, 18, 20, 22, 24, 26, 28, 30]
def MY : Vector (Fin 32) 8 := #v[17, 19, 21, 23, 25, 27, 29, 31]

def permute (state: Array UInt32) : Array UInt32 :=
  let left := state.extract 0 16
  let right := state.extract 16 32
  let permuted := right.mapIdx (fun i _ =>
      let idx := 16 + MSG_PERMUTATION[i]!.toNat
      state[idx]!
  )

  left ++ permuted

def transition (state: Array UInt32) (j : Fin 8) : Array UInt32 :=
  let aIn := state[(A[j])]!
  let bIn := state[(B[j])]!
  let cIn := state[(C[j])]!
  let dIn := state[(D[j])]!
  let mxIn := state[(MX[j])]!
  let myIn := state[(MY[j])]!

  let a0 := aIn.add (bIn.add mxIn)
  let d0 := UInt32.ofBitVec ((dIn.xor a0).toBitVec.rotateRight 16)
  let c0 := cIn.add d0
  let b0 := UInt32.ofBitVec ((bIn.xor c0).toBitVec.rotateRight 12)

  let a1 := a0.add (b0.add myIn)
  let d1 := UInt32.ofBitVec ((d0.xor a1).toBitVec.rotateRight 8)
  let c1 := c0.add d1
  let b1 := UInt32.ofBitVec ((b0.xor c1).toBitVec.rotateRight 7)

  let state := state.modify (A[j]).toNat fun _ => a1
  let state := state.modify (B[j]).toNat fun _ => b1
  let state := state.modify (C[j]).toNat fun _ => c1
  let state := state.modify (D[j]).toNat fun _ => d1

  state

def roundNoPermute (state : Array UInt32) : Array (Array UInt32) × Array UInt32 :=
  -- every round includes 8 transitions
  let monadic : StateM (Array (Array UInt32) × Array UInt32) (Array (Array UInt32) × Array UInt32) := do
    for i in [0:8] do
      modify fun (transitions, state) =>
        let newState := transition state (Fin.ofNat' 8 i)
        (transitions.push newState, newState)
    get

  let transitions := Array.empty
  monadic (transitions, state) |>.1

def round (state: Array UInt32) : Array (Array UInt32) × Array UInt32 :=
  let (transition, state) := roundNoPermute state
  Prod.mk transition (permute state)


def compress (cv : Vector UInt32 8) (blockWords : Vector UInt32 16) (counter : UInt64) (blockLen flags : UInt32) : Array (Array UInt32) × Array UInt32 :=
  let counterLow := UInt32.ofBitVec (counter.toBitVec.truncate 32)
  let counterHigh := UInt32.ofBitVec ((counter.shiftRight 32).toBitVec.truncate 32)

  let state := cv.toArray ++ (IV.extract 0 4).toArray ++ #[counterLow, counterHigh, blockLen, flags] ++ blockWords.toArray

  -- every compression includes 7 rounds (where last round doesn't include permutation)
  let monadic : StateM (Array (Array UInt32) × Array UInt32) (Array (Array UInt32) × Array UInt32) := do
    for _ in [0:6] do
      modify fun (transitions, state) =>
        let (tmp, state') := round state
        (transitions.append tmp, state')

    modify fun (transitions, state) =>
      let (tmp, state') := roundNoPermute state
      (transitions.append tmp, state')
    get


  let (transitions, state) := monadic (#[state], state) |>.1

  let temp := ((state.extract 0 8).zipWith (Xor.xor) (state.extract 8 16))
  let state := temp.append (state.extract 8 32)
  let temp := (state.extract 8 16).zipWith (Xor.xor) cv.toArray
  let state := state.extract 0 8 ++ temp ++ state.extract 16 32

  -- pad state transitions with 6 zero-arrays for correct transposing
  let zeroes := Array.ofFn (n := 32) (fun _ => (0 : UInt32))
  let transitions := transitions.append (Array.ofFn (n := 6) (fun _ => zeroes))

  Prod.mk (Utilities.transpose transitions 32) (state.extract 0 16)

end Blake3

namespace TraceGeneration

def generateTraces (rng : StdGen) (length : Nat) :  Array (Array UInt32) × Array (Array UInt32) :=
  let rec generateTracesInner (rng : StdGen) (length : Nat) (transitions :  Array (Array UInt32)) (array : Array (Array UInt32)) :  Array (Array UInt32) × Array (Array UInt32) :=
    match length with
    | 0 => Prod.mk transitions array
    | length' + 1 =>

      let cvGen : StateM StdGen (Vector UInt32 8) := do
        let (g₁, g₂) := RandomGen.split (← get)
        set g₂
        pure (Utilities.rand8 g₁)

      let blockGen : StateM StdGen (Vector UInt32 16) := do
        let (g₁, g₂) := RandomGen.split (← get)
        set g₂
        pure (Utilities.rand16 g₁)

      let uint32Gen : StateM StdGen UInt32 := do
        let (val, rng) := RandomGen.next (← get)
        set rng
        pure val.toUInt32

      let uint64Gen : StateM StdGen UInt64 := do
        let (val, rng) := RandomGen.next (← get)
        set rng
        pure val.toUInt64

      let (g₁, g₂) := RandomGen.split rng
      let cv := cvGen g₁ |>.1
      let block := blockGen g₁ |>.1
      let counter := uint64Gen g₁ |>.1
      let blockLen := uint32Gen g₁ |>.1
      let flags := uint32Gen g₁ |>.1

      let (transition, expected) := Blake3.compress cv block counter blockLen flags

      -- we extend 'transitions' inner arrays via concatenating new transition arrays to them
      let transitions' := if transitions.isEmpty then transition else (transitions.zip transition).map (fun (a, b) => a ++ b)
      generateTracesInner g₂ length' transitions' (array.push expected)

  generateTracesInner rng length Array.empty Array.empty

end TraceGeneration

open TraceGeneration
open Blake3
open LSpec

def Tests.Blake3.suite : List LSpec.TestSeq :=
[
  test "Blake3 compression" (
    let cv : Vector UInt32 8 := #v[0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff]
    let blockWords : Vector UInt32 16 := #v[0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000]
    let counter : UInt64 := 0xbbbbbbbbcccccccc
    let blockLen : UInt32 := 0xeeeeeeee
    let flags : UInt32 := 0xdddddddd
    let expected : Array UInt32 := #[0x8980fe15, 0x55898ce0, 0x8cf4fbde, 0x5e8537e9, 0x3d2e54f, 0x7e46753f, 0x5d151bb8, 0x2559b733, 0x24560929, 0x6625b1bf, 0xaaccc80e, 0xc5d4287a, 0x2848c46b, 0x94f666c, 0x3adaaeb3, 0x12011250]

    let (_, actual) := compress cv blockWords counter blockLen flags
    expected == actual
  ),

  test "Traces generating" (
    -- here we just check that trace generating works
    let (_traces, _expected) := generateTraces (mkStdGen 50) 100
    true
  )
]
