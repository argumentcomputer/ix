import LSpec

namespace Blake3

def IV : Array UInt32 := #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
def MSG_PERMUTATION : Array (Fin 16) := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
def A : Array (Fin 32) := #[0, 1, 2, 3, 0, 1, 2, 3]
def B : Array (Fin 32) := #[4, 5, 6, 7, 5, 6, 7, 4]
def C : Array (Fin 32) := #[8, 9, 10, 11, 10, 11, 8, 9]
def D : Array (Fin 32) := #[12, 13, 14, 15, 15, 12, 13, 14]
def MX : Array (Fin 32) := #[16, 18, 20, 22, 24, 26, 28, 30]
def MY : Array (Fin 32) := #[17, 19, 21, 23, 25, 27, 29, 31]

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


def roundNoPermute(state: Array UInt32) : Array UInt32 :=
  let state := transition state 0
  let state := transition state 1
  let state := transition state 2
  let state := transition state 3
  let state := transition state 4
  let state := transition state 5
  let state := transition state 6
  let state := transition state 7
  state

def round (state: Array UInt32) : Array UInt32 :=
  let state := roundNoPermute state
  permute state


def compress (cv blockWords : Array UInt32) (counter : UInt64) (blockLen flags : UInt32) : Array UInt32 :=
  let counterLow := UInt32.ofBitVec (counter.toBitVec.truncate 32)
  let counterHigh := UInt32.ofBitVec ((counter.shiftRight 32).toBitVec.truncate 32)

  let state := #[
    cv[0]!,
    cv[1]!,
    cv[2]!,
    cv[3]!,
    cv[4]!,
    cv[5]!,
    cv[6]!,
    cv[7]!,
    IV[0]!,
    IV[1]!,
    IV[2]!,
    IV[3]!,
    counterLow,
    counterHigh,
    blockLen,
    flags,
    blockWords[0]!,
    blockWords[1]!,
    blockWords[2]!,
    blockWords[3]!,
    blockWords[4]!,
    blockWords[5]!,
    blockWords[6]!,
    blockWords[7]!,
    blockWords[8]!,
    blockWords[9]!,
    blockWords[10]!,
    blockWords[11]!,
    blockWords[12]!,
    blockWords[13]!,
    blockWords[14]!,
    blockWords[15]!,
  ]


  let state := round state
  let state := round state
  let state := round state
  let state := round state
  let state := round state
  let state := round state
  let state := roundNoPermute state

  let temp := ((state.extract 0 8).zipWith (Xor.xor) (state.extract 8 16))
  let state := temp.append (state.extract 8 32)
  let temp := (state.extract 8 16).zipWith (Xor.xor) cv
  let state := state.extract 0 8 ++ temp ++ state.extract 16 32

  state.extract 0 16

end Blake3


open Blake3
open LSpec

def Tests.Blake3.suite : List LSpec.TestSeq :=
[
  test "Blake3 compression" (
    let cv : Array UInt32 := #[0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff]
    let blockWords : Array UInt32 := #[0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000]
    let counter : UInt64 := 0xbbbbbbbbcccccccc
    let blockLen : UInt32 := 0xeeeeeeee
    let flags : UInt32 := 0xdddddddd
    let expected := #[0x8980fe15, 0x55898ce0, 0x8cf4fbde, 0x5e8537e9, 0x3d2e54f, 0x7e46753f, 0x5d151bb8, 0x2559b733, 0x24560929, 0x6625b1bf, 0xaaccc80e, 0xc5d4287a, 0x2848c46b, 0x94f666c, 0x3adaaeb3, 0x12011250]

    let actual := compress cv blockWords counter blockLen flags
    expected == actual
  ),
]
