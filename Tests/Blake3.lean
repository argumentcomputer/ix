import LSpec

namespace Utilities

partial def inner (rng : StdGen) (length : Nat) (array: Array UInt32) : Array UInt32 :=
  match length with
  | 0 => array
  | _ =>
    let (g₁, g₂) := RandomGen.split rng
    let (next, _) := RandomGen.next g₁
    inner g₂ (length - 1) (array.push next.toUInt32)

--#eval inner (mkStdGen 0) 5 Array.empty
--#eval inner (mkStdGen 0) 10 Array.empty

-- TODO: ask Arthur, whether it is possible to easily convert Array to Vector
def rand8 (rng : StdGen) : Vector UInt32 8 :=
  let array := inner rng 8 Array.empty
  #v[array[0]!, array[1]!, array[2]!, array[3]!, array[4]!, array[5]!, array[6]!, array[7]!]

--#eval rand8 (mkStdGen 0)

def rand16 (rng : StdGen) : Vector UInt32 16 :=
  let array := inner rng 16 Array.empty
  #v[
    array[0]!, array[1]!, array[2]!, array[3]!, array[4]!, array[5]!, array[6]!, array[7]!,
    array[8]!, array[9]!, array[10]!, array[11]!, array[12]!, array[13]!, array[14]!, array[15]!
  ]

--#eval rand16 (mkStdGen 0)

partial def transpose (initial : Array (Array UInt32)) (tmp : Array (Array UInt32)) (rowLen: Nat): Array (Array UInt32) :=
  match rowLen with
  | 0 => tmp.reverse
  | idx =>
    let col := Array.ofFn (n := initial.size) fun i => initial[i]![idx - 1]!
    transpose initial (tmp.push col ) (idx - 1)

--#eval let orig := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]; transpose orig Array.empty 3
--#eval let orig := #[#[1, 2, 3, 0], #[4, 5, 6, 0], #[7, 8, 9, 0]]; transpose orig Array.empty 4
--#eval let orig := #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9], #[0, 0, 0]]; transpose orig Array.empty 3

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


def roundNoPermute(state: Array UInt32) : Array (Array UInt32) × Array UInt32 :=
  let transitions := Array.empty

  -- TODO: Ask Arthur about idiomatic looping instead of sequential 'transition' invocation one by one
  let state := transition state 0
  let transitions := transitions.push state
  let state := transition state 1
  let transitions := transitions.push state
  let state := transition state 2
  let transitions := transitions.push state
  let state := transition state 3
  let transitions := transitions.push state
  let state := transition state 4
  let transitions := transitions.push state
  let state := transition state 5
  let transitions := transitions.push state
  let state := transition state 6
  let transitions := transitions.push state
  let state := transition state 7
  let transitions := transitions.push state

  Prod.mk transitions state


def round (state: Array UInt32) : Array (Array UInt32) × Array UInt32 :=
  let (transition, state) := roundNoPermute state
  Prod.mk transition (permute state)


def compress (cv : Vector UInt32 8) (blockWords : Vector UInt32 16) (counter : UInt64) (blockLen flags : UInt32) : Array (Array UInt32) × Array UInt32 :=
  let counterLow := UInt32.ofBitVec (counter.toBitVec.truncate 32)
  let counterHigh := UInt32.ofBitVec ((counter.shiftRight 32).toBitVec.truncate 32)


  let state := cv.toArray ++ (IV.extract 0 4).toArray ++ #[counterLow, counterHigh, blockLen, flags] ++ blockWords.toArray

  let transitions := #[state]

  -- TODO: Ask Arthur about idiomatic looping instead of sequential 'round' invocation one by one
  let (tmp, state) := round state
  let transitions := transitions.append tmp
  let (tmp, state) := round state
  let transitions := transitions.append tmp
  let (tmp, state) := round state
  let transitions := transitions.append tmp
  let (tmp, state) := round state
  let transitions := transitions.append tmp
  let (tmp, state) := round state
  let transitions := transitions.append tmp
  let (tmp, state) := round state
  let transitions := transitions.append tmp
  let (tmp, state) := roundNoPermute state
  let transitions := transitions.append tmp

  let temp := ((state.extract 0 8).zipWith (Xor.xor) (state.extract 8 16))
  let state := temp.append (state.extract 8 32)
  let temp := (state.extract 8 16).zipWith (Xor.xor) cv.toArray
  let state := state.extract 0 8 ++ temp ++ state.extract 16 32

  -- pad state transitions with 6 zero-arrays for correct transposing
  let zeroes := Array.ofFn (n := 32) (fun _ => (0 : UInt32))
  let transitions := transitions.append (Array.ofFn (n := 6) (fun _ => zeroes))

  Prod.mk (Utilities.transpose transitions Array.empty 32) (state.extract 0 16)

end Blake3

namespace TraceGeneration
-- TODO: Ask Arthur about more elegant usage of RNG
partial def generateTraces
(rng : StdGen)
(length : Nat)
(transitions : Array (Array (Array UInt32)))
(array : Array (Array UInt32))
: Array (Array (Array UInt32)) × Array (Array UInt32) :=
  match length with
  | 0 => Prod.mk transitions array
  | _ =>
    -- to ensure that we will have independent RNGs for every piece of data,
    -- we prepare multiple RNG instances
    let (g₁, g₂) := RandomGen.split rng
    let (g₃, g₄) := RandomGen.split g₁
    let (g₅, g₆) := RandomGen.split g₂
    let (g₇, g₈) := RandomGen.split g₃
    let (g₉, g₁₀) := RandomGen.split g₄

    let cv := Utilities.rand8 g₅
    let block := Utilities.rand16 g₆
    let counter := (RandomGen.next g₇).fst.toUInt64
    let blockLen := (RandomGen.next g₈).fst.toUInt32
    let flags := (RandomGen.next g₉).fst.toUInt32

    let (transition, expected) := Blake3.compress cv block counter blockLen flags
    generateTraces g₁₀ (length - 1) (transitions.push transition) (array.push expected)


--#eval (generateTraces (mkStdGen 50) 10 Array.empty Array.empty).snd
--#eval (generateTraces (mkStdGen 50) 10 Array.empty Array.empty).fst

end TraceGeneration

open TraceGeneration
open Blake3
open LSpec

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

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
    -- here we just check that it is feasible to generate some big amount of traces
    let (_traces, _expected) := generateTraces (mkStdGen 50) 100000 Array.empty Array.empty
    true
  )
]
