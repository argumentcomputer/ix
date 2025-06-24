import LSpec
import Ix.Archon.Circuit
import Ix.Archon.Protocol

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

def transpose (initial : Array (Array UInt32)) (rowLen : Nat) : Array (Array UInt32) :=
  let rec transposeInner (initial : Array (Array UInt32)) (tmp : Array (Array UInt32)) (rowLen: Nat): Array (Array UInt32) :=
    match rowLen with
    | 0 => tmp.reverse
    | idx + 1 =>
      let col := Array.ofFn (n := initial.size) fun i => initial[i]![idx]!
      transposeInner initial (tmp.push col) idx
  transposeInner initial Array.empty rowLen

def arrayEq (a b : Array UInt32) : Bool :=
      if a.size != b.size then
        false
      else
        let rec loop (i : Nat) : Bool :=
          if i < a.size then
            if a[i]! != b[i]! then false else loop (i + 1)
          else
            true
        loop 0

def byteArrayToUInt32Array (b : ByteArray) : Array UInt32 :=
  let len := b.size / 4
  Array.ofFn (n := len) (fun i =>
    let base := i.toNat * 4
    let b0 := b.get! base
    let b1 := b.get! (base + 1)
    let b2 := b.get! (base + 2)
    let b3 := b.get! (base + 3)
    UInt32.ofNat (b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24))
  )

end Utilities

namespace TraceGenerator

structure Traces where
  transitionTraces : Array (Array UInt32)
  cvTraces : Array UInt32
  state08Traces : Array UInt32
  state816Traces : Array UInt32
  stateXorTraces : Array UInt32
  cvXorTraces : Array UInt32
  aInTraces : Array UInt32
  bInTraces : Array UInt32
  cInTraces : Array UInt32
  dInTraces : Array UInt32
  mxInTraces : Array UInt32
  myInTraces : Array UInt32
  a0TmpTraces : Array UInt32
  a0Traces : Array UInt32
  b0Traces : Array UInt32
  c0Traces : Array UInt32
  d0Traces : Array UInt32
  a1TmpTraces : Array UInt32
  a1Traces : Array UInt32
  b1Traces : Array UInt32
  c1Traces : Array UInt32
  d1Traces : Array UInt32
  coutTraces : Array (Array UInt32)

structure TransitionOutput where
  aIn : UInt32
  bIn : UInt32
  cIn : UInt32
  dIn : UInt32
  mxIn : UInt32
  myIn : UInt32
  a0Tmp : UInt32
  a0 : UInt32
  b0 : UInt32
  c0 : UInt32
  d0 : UInt32
  a1Tmp : UInt32
  a1 : UInt32
  b1 : UInt32
  c1 : UInt32
  d1 : UInt32
  couts : Array UInt32

structure CompressionOutput where
  transition : Array (Array UInt32)
  state08 : Array UInt32
  state816 : Array UInt32
  stateXor : Array UInt32
  cvXor : Array UInt32
  aIn : Array UInt32
  bIn : Array UInt32
  cIn : Array UInt32
  dIn : Array UInt32
  mxIn : Array UInt32
  myIn : Array UInt32
  a0Tmp : Array UInt32
  a0 : Array UInt32
  b0 : Array UInt32
  c0 : Array UInt32
  d0 : Array UInt32
  a1Tmp : Array UInt32
  a1 : Array UInt32
  b1 : Array UInt32
  c1 : Array UInt32
  d1 : Array UInt32
  couts : Array (Array UInt32)


def IV : Vector UInt32 8 := #v[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
def MSG_PERMUTATION : Vector (Fin 16) 16  := #v[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
def A : Vector (Fin 32) 8 := #v[0, 1, 2, 3, 0, 1, 2, 3]
def B : Vector (Fin 32) 8 := #v[4, 5, 6, 7, 5, 6, 7, 4]
def C : Vector (Fin 32) 8 := #v[8, 9, 10, 11, 10, 11, 8, 9]
def D : Vector (Fin 32) 8 := #v[12, 13, 14, 15, 15, 12, 13, 14]
def MX : Vector (Fin 32) 8 := #v[16, 18, 20, 22, 24, 26, 28, 30]
def MY : Vector (Fin 32) 8 := #v[17, 19, 21, 23, 25, 27, 29, 31]

def AdditionOperationsNumber : Nat := 6

def permute (state: Array UInt32) : Array UInt32 :=
  let left := state.extract 0 16
  let right := state.extract 16 32
  let permuted := right.mapIdx (fun i _ =>
      let idx := 16 + MSG_PERMUTATION[i]!.toNat
      state[idx]!
  )

  left ++ permuted

def transition (state: Array UInt32) (j : Fin 8) : TransitionOutput × Array UInt32 :=
  let add (a : UInt32) (b : UInt32) : UInt32 × UInt32 × UInt32 :=
    let zout := a.add b
    let carry : UInt32 := if zout < a then 1 else 0
    let cin := (a.toBitVec.xor b.toBitVec).xor zout.toBitVec
    let cout := (carry <<< 31) ||| (cin.toNat.toUInt32 >>> 1)
    (cin.toNat.toUInt32, cout, zout)

  let cins : Array UInt32 := #[]
  let couts : Array UInt32 := #[]

  let aIn := state[(A[j])]!
  let bIn := state[(B[j])]!
  let cIn := state[(C[j])]!
  let dIn := state[(D[j])]!
  let mxIn := state[(MX[j])]!
  let myIn := state[(MY[j])]!

  let (cin, cout, a0Tmp) := add aIn bIn
  let cins := cins.push cin
  let couts := couts.push cout

  let (cin, cout, a0) := add a0Tmp mxIn
  let cins := cins.push cin
  let couts := couts.push cout

  let d0 := UInt32.ofBitVec ((dIn.xor a0).toBitVec.rotateRight 16)

  let (cin, cout, c0) := add cIn d0
  let cins := cins.push cin
  let couts := couts.push cout

  let b0 := UInt32.ofBitVec ((bIn.xor c0).toBitVec.rotateRight 12)

  let (cin, cout, a1Tmp) := add a0 b0
  let cins := cins.push cin
  let couts := couts.push cout

  let (cin, cout, a1) := add a1Tmp myIn
  let cins := cins.push cin
  let couts := couts.push cout

  let d1 := UInt32.ofBitVec ((d0.xor a1).toBitVec.rotateRight 8)

  let (cin, cout, c1) := add c0 d1
  let cins := cins.push cin
  let couts := couts.push cout

  let b1 := UInt32.ofBitVec ((b0.xor c1).toBitVec.rotateRight 7)

  let state := state.modify (A[j]).toNat fun _ => a1
  let state := state.modify (B[j]).toNat fun _ => b1
  let state := state.modify (C[j]).toNat fun _ => c1
  let state := state.modify (D[j]).toNat fun _ => d1

  (
    { aIn, bIn, cIn, dIn, mxIn, myIn, a0Tmp, a0, b0, c0, d0, a1Tmp, a1, b1, c1, d1, couts },
    state
  )

def roundNoPermute (state : Array UInt32) : Array TransitionOutput × Array (Array UInt32) × Array UInt32 :=
  let indices := List.range 8
  aux #[] #[] state indices
where aux outputs transitions state indices := match indices with
  | [] => (outputs, transitions, state)
  | i :: is =>
    let (tOutput, newState) := transition state (Fin.ofNat' 8 i)
    aux (outputs.push tOutput) (transitions.push newState) newState is

def round (state: Array UInt32) : Array TransitionOutput × Array (Array UInt32) × Array UInt32 :=
  let (outputs, transition, state) := roundNoPermute state
  (outputs, transition, (permute state))

def compress (cv : Array UInt32) (blockWords : Array UInt32) (counter : UInt64) (blockLen flags : UInt32) : CompressionOutput × Array UInt32 :=
  let counterLow := UInt32.ofBitVec (counter.toBitVec.truncate 32)
  let counterHigh := UInt32.ofBitVec ((counter.shiftRight 32).toBitVec.truncate 32)

  let state := cv ++ (IV.extract 0 4).toArray ++ #[counterLow, counterHigh, blockLen, flags] ++ blockWords

  -- every compression includes 7 rounds (where last round doesn't include permutation)
  let rec runRounds (outputs: Array TransitionOutput) (transitions : Array (Array UInt32)) (state : Array UInt32) (indices : List Nat) :
      Array TransitionOutput × Array (Array UInt32) × Array UInt32 :=
    match indices with
    | [] => (outputs, transitions, state)
    | i :: is =>
      let (roundOutputs, roundTransitions, newState) :=
        if i == 6 then roundNoPermute state else round state
      runRounds (outputs.append roundOutputs) (transitions.append roundTransitions) newState is

  let (outputs, transitions, state) := runRounds #[] #[state] state (List.range 7)

  let state08 := state.extract 0 8
  let state816 := state.extract 8 16

  let temp := (state08.zipWith (Xor.xor) state816)
  let stateXor := temp
  let state := temp.append (state.extract 8 32)
  let temp := (state.extract 8 16).zipWith (Xor.xor) cv
  let cvXor := temp
  let state := state.extract 0 8 ++ temp ++ state.extract 16 32
  let transitions := transitions.push state

  -- pad state transitions with 6 32-zero arrays for correct transposing
  let zeroes32 := Array.ofFn (n := 32) (fun _ => (0 : UInt32))
  let transitions := transitions.append (Array.ofFn (n := 6) (fun _ => zeroes32))

  -- pad temp variables for correct witness population
  let zeroes8 := Array.ofFn (n := 8) (fun _ => (0 : UInt32))
  let aIns := outputs.map (fun o => o.aIn) ++ zeroes8
  let bIns := outputs.map (fun o => o.bIn) ++ zeroes8
  let cIns := outputs.map (fun o => o.cIn) ++ zeroes8
  let dIns := outputs.map (fun o => o.dIn) ++ zeroes8
  let mxIns := outputs.map (fun o => o.mxIn) ++ zeroes8
  let myIns := outputs.map (fun o => o.myIn) ++ zeroes8

  let a0Tmp := outputs.map (fun o => o.a0Tmp) ++ zeroes8
  let a0 := outputs.map (fun o => o.a0) ++ zeroes8
  let b0 := outputs.map (fun o => o.b0) ++ zeroes8
  let c0 := outputs.map (fun o => o.c0) ++ zeroes8
  let d0 := outputs.map (fun o => o.d0) ++ zeroes8
  let a1Tmp := outputs.map (fun o => o.a1Tmp) ++ zeroes8
  let a1 := outputs.map (fun o => o.a1) ++ zeroes8
  let b1 := outputs.map (fun o => o.b1) ++ zeroes8
  let c1 := outputs.map (fun o => o.c1) ++ zeroes8
  let d1 := outputs.map (fun o => o.d1) ++ zeroes8

  -- pad couts with 8 zero arrays (each of unpadded cout array size) for correct transposing
  let couts := outputs.map (fun o => o.couts)
  let zeroesCoutsSize := Array.ofFn (n := couts.size) (fun _ => (0 : UInt32))
  let couts := couts.append (Array.ofFn (n := 8) (fun _ => zeroesCoutsSize))

  let out : CompressionOutput := {
    transition := (Utilities.transpose transitions 32),
    state08,
    state816,
    stateXor,
    cvXor,
    aIn := aIns,
    bIn := bIns,
    cIn := cIns,
    dIn := dIns,
    mxIn := mxIns,
    myIn := myIns,
    a0Tmp,
    a0,
    b0,
    c0,
    d0,
    a1Tmp,
    a1,
    b1,
    c1,
    d1,
    couts := Utilities.transpose couts AdditionOperationsNumber,
  }

  ( out, (state.extract 0 16))

abbrev ExpectedStates := Array (Array UInt32)

def mkTraces (rng : StdGen) (length : Nat) : Traces × ExpectedStates :=
  let rec generateTracesInner (rng : StdGen) (length : Nat) (traces :  Traces) (array : ExpectedStates) : Traces × ExpectedStates :=
    match length with
    | 0 => (traces, array)
    | length' + 1 =>

      let compressionInputGen : StateM StdGen (Array UInt32 × Array UInt32 × UInt64 × UInt32 × UInt32) := do
        let (g₁, g₂) := RandomGen.split (← get)
        let cv := Utilities.randArray g₁ 8
        set g₂

        let (g₁, g₂) := RandomGen.split (← get)
        let block := Utilities.randArray g₁ 16
        set g₂

        let (counter, g₂) := RandomGen.next (← get)
        set g₂

        let (blockLen, g₂) := RandomGen.next (← get)
        set g₂

        let (flags, _) := RandomGen.next (← get)
        pure (cv, block, counter.toUInt64, blockLen.toUInt32, flags.toUInt32)

      let (g₁, g₂) := RandomGen.split rng
      let (cv, block, counter, blockLen, flags) := compressionInputGen g₁ |>.1

      let (compressionOut, expected) := compress cv block counter blockLen flags

      -- Now, on each recursion call, we extend 'Traces' inner arrays via concatenating new trace data from a given compression to them
      let transitions := traces.transitionTraces
      let transition := compressionOut.transition
      let transitions' := if transitions.isEmpty then transition else (transitions.zip transition).map (fun (a, b) => a ++ b)

      let cvTraces := traces.cvTraces
      let cvTraces' := if cvTraces.isEmpty then cv else cvTraces ++ cv

      let state08Traces := traces.state08Traces
      let state08Trace := compressionOut.state08
      let state08Traces' := if state08Traces.isEmpty then state08Trace else state08Traces ++ state08Trace

      let state816Traces := traces.state816Traces
      let state816Trace := compressionOut.state816
      let state816Traces' := if state816Traces.isEmpty then state816Trace else state816Traces ++ state816Trace

      let stateXorTraces := traces.stateXorTraces
      let stateXorTrace := compressionOut.stateXor
      let stateXorTraces' := if stateXorTraces.isEmpty then stateXorTrace else stateXorTraces ++ stateXorTrace

      let cvXorTraces := traces.cvXorTraces
      let cvXorTrace := compressionOut.cvXor
      let cvXorTraces' := if cvXorTraces.isEmpty then cvXorTrace else cvXorTraces ++ cvXorTrace

      let aInTraces := traces.aInTraces
      let aInTrace := compressionOut.aIn
      let aInTraces' := if aInTraces.isEmpty then aInTrace else aInTraces ++ aInTrace

      let bInTraces := traces.bInTraces
      let bInTrace := compressionOut.bIn
      let bInTraces' := if bInTraces.isEmpty then bInTrace else bInTraces ++ bInTrace

      let cInTraces := traces.cInTraces
      let cInTrace := compressionOut.cIn
      let cInTraces' := if cInTraces.isEmpty then cInTrace else cInTraces ++ cInTrace

      let dInTraces := traces.dInTraces
      let dInTrace := compressionOut.dIn
      let dInTraces' := if dInTraces.isEmpty then dInTrace else dInTraces ++ dInTrace

      let mxInTraces := traces.mxInTraces
      let mxInTrace := compressionOut.mxIn
      let mxInTraces' := if mxInTraces.isEmpty then mxInTrace else mxInTraces ++ mxInTrace

      let myInTraces := traces.myInTraces
      let myInTrace := compressionOut.myIn
      let myInTraces' := if myInTraces.isEmpty then myInTrace else myInTraces ++ myInTrace

      let a0TmpTraces := traces.a0TmpTraces
      let a0TmpTrace := compressionOut.a0Tmp
      let a0TmpTraces' := if a0TmpTraces.isEmpty then a0TmpTrace else a0TmpTraces ++ a0TmpTrace

      let a0Traces := traces.a0Traces
      let a0Trace := compressionOut.a0
      let a0Traces' := if a0Traces.isEmpty then a0Trace else a0Traces ++ a0Trace

      let b0Traces := traces.b0Traces
      let b0Trace := compressionOut.b0
      let b0Traces' := if b0Traces.isEmpty then b0Trace else b0Traces ++ b0Trace

      let c0Traces := traces.c0Traces
      let c0Trace := compressionOut.c0
      let c0Traces' := if c0Traces.isEmpty then c0Trace else c0Traces ++ c0Trace

      let d0Traces := traces.d0Traces
      let d0Trace := compressionOut.d0
      let d0Traces' := if d0Traces.isEmpty then d0Trace else d0Traces ++ d0Trace

      let a1TmpTraces := traces.a1TmpTraces
      let a1TmpTrace := compressionOut.a1Tmp
      let a1TmpTraces' := if a1TmpTraces.isEmpty then a1TmpTrace else a1TmpTraces ++ a1TmpTrace

      let a1Traces := traces.a1Traces
      let a1Trace := compressionOut.a1
      let a1Traces' := if a1Traces.isEmpty then a1Trace else a1Traces ++ a1Trace

      let b1Traces := traces.b1Traces
      let b1Trace := compressionOut.b1
      let b1Traces' := if b1Traces.isEmpty then b1Trace else b1Traces ++ b1Trace

      let c1Traces := traces.c1Traces
      let c1Trace := compressionOut.c1
      let c1Traces' := if c1Traces.isEmpty then c1Trace else c1Traces ++ c1Trace

      let d1Traces := traces.d1Traces
      let d1Trace := compressionOut.d1
      let d1Traces' := if d1Traces.isEmpty then d1Trace else d1Traces ++ d1Trace

      let coutTraces := traces.coutTraces
      let coutTrace := compressionOut.couts
      let coutTraces' := if coutTraces.isEmpty then coutTrace else (coutTraces.zip coutTrace).map (fun (a, b) => a ++ b)

      let traces' := { traces with
        transitionTraces := transitions',
        cvTraces := cvTraces',
        state08Traces := state08Traces',
        state816Traces := state816Traces'
        stateXorTraces := stateXorTraces'
        cvXorTraces := cvXorTraces'
        aInTraces := aInTraces'
        bInTraces := bInTraces'
        cInTraces := cInTraces'
        dInTraces := dInTraces'
        mxInTraces := mxInTraces'
        myInTraces := myInTraces'
        a0TmpTraces := a0TmpTraces'
        a0Traces := a0Traces'
        b0Traces := b0Traces'
        c0Traces := c0Traces'
        d0Traces := d0Traces'
        a1TmpTraces := a1TmpTraces'
        a1Traces := a1Traces'
        b1Traces := b1Traces'
        c1Traces := c1Traces'
        d1Traces := d1Traces'
        coutTraces := coutTraces'
      }

      generateTracesInner g₂ length' traces' (array.push expected)

  let emptyTraces : Traces := {
    transitionTraces := Array.empty,
    cvTraces := Array.empty,
    state08Traces := Array.empty,
    state816Traces := Array.empty,
    stateXorTraces := Array.empty,
    cvXorTraces := Array.empty,
    aInTraces := Array.empty,
    bInTraces := Array.empty,
    cInTraces := Array.empty,
    dInTraces := Array.empty,
    mxInTraces := Array.empty,
    myInTraces := Array.empty,
    a0TmpTraces := Array.empty,
    a0Traces := Array.empty,
    b0Traces := Array.empty,
    c0Traces := Array.empty,
    d0Traces := Array.empty,
    a1TmpTraces := Array.empty,
    a1Traces := Array.empty,
    b1Traces := Array.empty,
    c1Traces := Array.empty,
    d1Traces := Array.empty,
    coutTraces := Array.empty,
  }

  generateTracesInner rng length emptyTraces Array.empty

end TraceGenerator

open TraceGenerator
open LSpec
open Archon

def StateSize : Nat := 32
def LogU32Bits : USize := 5
def TestLogCompressionsNum : Nat := 5
def OutHeight : Nat := 8
def SingleCompressionNVars : Nat := 6
def SingleCompressionHeight : Nat := 2 ^ SingleCompressionNVars
def ProjectedSelectorInput : UInt64 := 0
def ProjectedSelectorOutput : UInt64 := 57

def testCompression : TestSeq :=
  let cv : Array UInt32 := #[0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff]
  let blockWords : Array UInt32 := #[0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000, 0xaa000000]
  let counter : UInt64 := 0xbbbbbbbbcccccccc
  let blockLen : UInt32 := 0xeeeeeeee
  let flags : UInt32 := 0xdddddddd
  let expected : Array UInt32 := #[0x8980fe15, 0x55898ce0, 0x8cf4fbde, 0x5e8537e9, 0x3d2e54f, 0x7e46753f, 0x5d151bb8, 0x2559b733, 0x24560929, 0x6625b1bf, 0xaaccc80e, 0xc5d4287a, 0x2848c46b, 0x94f666c, 0x3adaaeb3, 0x12011250]

  let (_, actual) := compress cv blockWords counter blockLen flags

  test "Blake3 compression is OK" (expected == actual)


/-- this test is intended to check that state transition is correctly mapped into traces:
* every state transition takes 64 elements
* every state transition ends with 6 zeroes
-/
def testTraceGenerating : TestSeq :=
    let (traces, _expected) := mkTraces (mkStdGen 0) 1

    let lenExpected := traces.transitionTraces.all (fun a => a.size == 64)
    let endExpected := traces.transitionTraces.all (fun a => if a.size < 6 then false else
      let tail := a.extract (a.size - 6) a.size
      tail.all (fun x => x == 0)
    )

    test "Trace generating is OK" (lenExpected && endExpected)

def testArchonStateTransitionModule : TestSeq := Id.run do
    let mkColumns (circuitModule: CircuitModule) (length : Nat) (f : TowerField) (name: String) : CircuitModule × Array OracleIdx × Array OracleIdx × Array OracleIdx :=
      let rec mkColumnsInner
        (circuitModule: CircuitModule)
        (length : Nat)
        (f : TowerField)
        (name: String)
        (committed : Array OracleIdx)
        (input : Array OracleIdx)
        (output : Array OracleIdx) : CircuitModule × Array OracleIdx × Array OracleIdx × Array OracleIdx :=
          match length with
          | 0 => (circuitModule, committed, input, output)
          | length' + 1 =>
            let (committed', circuitModule):= circuitModule.addCommitted (String.append name (toString length)) f .base
            let (input', circuitModule) := circuitModule.addProjected (String.append (String.append name (toString length)) "input") committed' ProjectedSelectorInput SingleCompressionHeight.toUSize
            let (output', circuitModule) := circuitModule.addProjected (String.append (String.append name (toString length)) "output") committed' ProjectedSelectorOutput SingleCompressionHeight.toUSize
            mkColumnsInner circuitModule length' f (String.append name (toString length')) (committed.push committed') (input.push input') (output.push output')

      mkColumnsInner circuitModule length f name Array.empty Array.empty Array.empty

    -- TODO: Assert that traces and states should have same size
    let writeTraces (witnessModule : WitnessModule) (traces : Array (Array UInt32)) (states : Array OracleIdx) (f: TowerField) : WitnessModule :=
      let rec writeTracesInner (witnessModule : WitnessModule) (traces : List (Array UInt32)) (states : List OracleIdx) (f: TowerField) : WitnessModule :=
        match traces, states with
        | [], _ => witnessModule
        | _, [] => witnessModule
        | t :: traces', s :: states' =>
          let (entryId, witnessModule) := witnessModule.addEntry
          let witnessModule := witnessModule.pushUInt32sTo t entryId
          let witnessModule := witnessModule.bindOracleTo s entryId f
          writeTracesInner witnessModule traces' states' f

      writeTracesInner witnessModule traces.toList states.toList f


    let tracesNum := 2 ^ TestLogCompressionsNum
    let (traces, expected) := mkTraces (mkStdGen 0) tracesNum

    let logHeight := Nat.log2 (tracesNum * SingleCompressionHeight) |>.toUInt8
    let mode := .active logHeight 0

    let circuitModule := CircuitModule.new 0
    let (circuitModule, state, _, output) := mkColumns circuitModule StateSize .b32 "stateTransition"
    let circuitModule := circuitModule.freezeOracles
    let witnessModule := circuitModule.initWitnessModule
    let witnessModule := writeTraces witnessModule traces.transitionTraces state .b32
    let witnessModule := witnessModule.populate mode

    -- get data as ByteArray of every actually computed cv and convert it to Array UInt32 for comparison
    let actual := (Array.ofFn (n := 16) fun i => witnessModule.getData output[i]!).map (fun bytes => Utilities.byteArrayToUInt32Array bytes)
    let expected := Utilities.transpose expected 16

    let witness := compileWitnessModules #[witnessModule] #[mode]
    withExceptOk "[Archon] state transition module testing is OK" (validateWitness #[circuitModule] #[] witness) fun _ =>
      test "output is expected" ((actual.zip expected).all (fun (a, b) => Utilities.arrayEq a b))

def testArchonCVOutputModule : TestSeq := Id.run do
  let tracesNum := 2 ^ TestLogCompressionsNum
  let (traces, expected) := mkTraces (mkStdGen 0) tracesNum

  let logHeight := Nat.log2 (tracesNum * OutHeight) |>.toUInt8
  let mode := .active logHeight 0

  let circuitModule := CircuitModule.new 0

  let (cv, circuitModule):= circuitModule.addCommitted "cv" .b32 .base
  let (state08, circuitModule):= circuitModule.addCommitted "state08" .b32 .base
  let (state816, circuitModule):= circuitModule.addCommitted "state816" .b32 .base
  let (state08xor816, circuitModule) := circuitModule.addLinearCombination "state08 xor state816" 0 #[(state08, 1), (state816, 1)] .base
  let (state816xorCv, circuitModule) := circuitModule.addLinearCombination "state816 xor cv" 0 #[(cv, 1), (state816, 1)] .base

  let circuitModule := circuitModule.freezeOracles
  let witnessModule := circuitModule.initWitnessModule
  let (cvEntry, witnessModule) := witnessModule.addEntry
  let (state08Entry, witnessModule) := witnessModule.addEntry
  let (state816Entry, witnessModule) := witnessModule.addEntry

  let witnessModule := witnessModule.pushUInt32sTo traces.cvTraces cvEntry
  let witnessModule := witnessModule.pushUInt32sTo traces.state08Traces state08Entry
  let witnessModule := witnessModule.pushUInt32sTo traces.state816Traces state816Entry

  let witnessModule := witnessModule.bindOracleTo cv cvEntry .b32
  let witnessModule := witnessModule.bindOracleTo state08 state08Entry .b32
  let witnessModule := witnessModule.bindOracleTo state816 state816Entry .b32

  let witnessModule := witnessModule.populate mode

  let a := Utilities.byteArrayToUInt32Array (witnessModule.getData state08xor816)
  let b := Utilities.byteArrayToUInt32Array (witnessModule.getData state816xorCv)

  let a := Array.ofFn (n := 16) (fun i => a.extract (8 * i) (8 * i + 8))
  let b := Array.ofFn (n := 16) (fun i => b.extract (8 * i) (8 * i + 8))
  let actual := (a.zip b).map (fun (a, b) => a ++ b)

  let witness := compileWitnessModules #[witnessModule] #[mode]
  withExceptOk "[Archon] cv output module testing is OK" (validateWitness #[circuitModule] #[] witness) fun _ =>
    test "output is expected" ((actual.zip expected).all (fun (a, b) => Utilities.arrayEq a b))

def testArchonAdditionXorRotateModule : TestSeq := Id.run do
  let sumAssertZero (circuitModule : CircuitModule) (indices : List Nat) (name : String) (xins : Array OracleIdx) (yins : Array OracleIdx) (cins : Array OracleIdx) (zouts : Array OracleIdx) : CircuitModule :=
    let rec sumAssertZeroInner (circuitModule : CircuitModule) (indices : List Nat) (name : String) (xins : Array OracleIdx) (yins : Array OracleIdx) (cins : Array OracleIdx) (zouts : Array OracleIdx) : CircuitModule :=
      match indices with
      | [] => circuitModule
      | i :: indices' =>
        let circuitModule' := circuitModule.assertZero (String.append name s!"{i}") #[xins[i]!, yins[i]!, cins[i]!, zouts[i]!] (ArithExpr.oracle xins[i]! + ArithExpr.oracle yins[i]! + ArithExpr.oracle cins[i]! + ArithExpr.oracle zouts[i]!)
        sumAssertZeroInner circuitModule' indices' name xins yins cins zouts

    sumAssertZeroInner circuitModule indices name xins yins cins zouts

  let carryAssertZero (circuitModule : CircuitModule) (indices : List Nat) (name : String) (xins : Array OracleIdx) (yins : Array OracleIdx) (cins : Array OracleIdx) (couts : Array OracleIdx) : CircuitModule :=
    let rec carryAssertZeroInner (circuitModule : CircuitModule) (indices : List Nat) (name : String) (xins : Array OracleIdx) (yins : Array OracleIdx) (cins : Array OracleIdx) (couts : Array OracleIdx) : CircuitModule :=
      match indices with
      | [] => circuitModule
      | i :: indices' =>
        let circuitModule' := circuitModule.assertZero (String.append name s!"{i}") #[xins[i]!, yins[i]!, cins[i]!, couts[i]!] ((ArithExpr.oracle xins[i]! + ArithExpr.oracle cins[i]!) * (ArithExpr.oracle yins[i]! + ArithExpr.oracle cins[i]!) + ArithExpr.oracle cins[i]! + ArithExpr.oracle couts[i]!)
        carryAssertZeroInner circuitModule' indices' name xins yins cins couts

    carryAssertZeroInner circuitModule indices name xins yins cins couts

  let mkColumns (circuitModule: CircuitModule) (length : Nat) (f : TowerField) (name: String) : CircuitModule × Array OracleIdx × Array OracleIdx :=
        let rec mkColumnsInner
          (circuitModule: CircuitModule)
          (length : Nat)
          (f : TowerField)
          (name: String)
          (couts : Array OracleIdx)
          (cins : Array OracleIdx) : CircuitModule × Array OracleIdx × Array OracleIdx :=
            match length with
            | 0 => (circuitModule, couts, cins)
            | length' + 1 =>
              let (cout, circuitModule):= circuitModule.addCommitted (String.append (String.append name (toString length)) "cin") f .base
              let (cin, circuitModule) := circuitModule.addShifted (String.append (String.append name (toString length)) "cin") cout 1 5 ShiftVariant.logicalLeft

              mkColumnsInner circuitModule length' f (String.append name (toString length')) (couts.push cout) (cins.push cin)

        mkColumnsInner circuitModule length f name Array.empty Array.empty

  let tracesNum := 2 ^ TestLogCompressionsNum
  let (traces, _expected) := mkTraces (mkStdGen 0) tracesNum

  let logHeight := Nat.log2 (tracesNum * SingleCompressionHeight) |>.toUInt8
  let mode := .active (logHeight + 5) 0

  let circuitModule := CircuitModule.new 0
  let (aIn, circuitModule) := circuitModule.addCommitted "aIn" .b1 .base
  let (bIn, circuitModule) := circuitModule.addCommitted "bIn" .b1 .base
  let (cIn, circuitModule) := circuitModule.addCommitted "cIn" .b1 .base
  let (dIn, circuitModule) := circuitModule.addCommitted "dIn" .b1 .base
  let (mxIn, circuitModule) := circuitModule.addCommitted "mxIn" .b1 .base
  let (myIn, circuitModule) := circuitModule.addCommitted "myIn" .b1 .base

  let (a0, circuitModule) := circuitModule.addCommitted "a0" .b1 .base
  let (a0Tmp, circuitModule) := circuitModule.addCommitted "a0Tmp" .b1 .base
  let (c0, circuitModule) := circuitModule.addCommitted "c0" .b1 .base
  let (a1, circuitModule) := circuitModule.addCommitted "a1" .b1 .base
  let (a1Tmp, circuitModule) := circuitModule.addCommitted "a1Tmp" .b1 .base
  let (c1, circuitModule) := circuitModule.addCommitted "c1" .b1 .base

  let (bInXorC0, circuitModule) := circuitModule.addLinearCombination "bInXorC0" 0 #[(bIn, 1), (c0, 1)] .base
  let (dInXorA0, circuitModule) := circuitModule.addLinearCombination "dInXorA0" 0 #[(dIn, 1), (a0, 1)] .base

  let (b0, circuitModule) := circuitModule.addShifted "b0" bInXorC0 (32 - 12) LogU32Bits ShiftVariant.circularLeft
  let (d0, circuitModule) := circuitModule.addShifted "d0" dInXorA0 (32 - 16) LogU32Bits ShiftVariant.circularLeft

  let (d0XorA1, circuitModule) := circuitModule.addLinearCombination "d0XorA1" 0 #[(d0, 1), (a1, 1)] .base
  let (b0XorC1, circuitModule) := circuitModule.addLinearCombination "b0XorC1" 0 #[(b0, 1), (c1, 1)] .base

  let (d1, circuitModule) := circuitModule.addShifted "d1" d0XorA1 (32 - 8) LogU32Bits ShiftVariant.circularLeft
  let (_, circuitModule) := circuitModule.addShifted "b1" b0XorC1 (32 - 7) LogU32Bits ShiftVariant.circularLeft

  let (circuitModule, couts, cins) := mkColumns circuitModule AdditionOperationsNumber .b1 "additionCinCout"

  let xins := #[aIn, a0Tmp, cIn, a0, a1Tmp, c0]
  let yins := #[bIn, mxIn, d0, b0, myIn, d1]
  let zouts := #[a0Tmp, a0, c0, a1Tmp, a1, c1]

  let circuitModule := sumAssertZero circuitModule (List.range 6) "sum" xins yins cins zouts
  let circuitModule := carryAssertZero circuitModule (List.range 6) "carry" xins yins cins couts

  let circuitModule := circuitModule.freezeOracles

  let mut witnessModule := circuitModule.initWitnessModule

  let xinTraces := #[traces.aInTraces, traces.a0TmpTraces, traces.cInTraces, traces.a0Traces, traces.a1TmpTraces, traces.c0Traces]
  let yinTraces := #[traces.bInTraces, traces.mxInTraces, traces.d0Traces, traces.b0Traces, traces.myInTraces, traces.d1Traces]
  let zoutTraces := #[traces.a0TmpTraces, traces.a0Traces, traces.c0Traces, traces.a1TmpTraces, traces.a1Traces, traces.c1Traces]

  for xy in [0:AdditionOperationsNumber] do
    let (coutEntry, witnessModule') := witnessModule.addEntry
    witnessModule := witnessModule'
    let (xinEntry, witnessModule') := witnessModule.addEntry
    witnessModule := witnessModule'
    let (yinEntry, witnessModule') := witnessModule.addEntry
    witnessModule := witnessModule'
    let (zoutEntry, witnessModule') := witnessModule.addEntry
    witnessModule := witnessModule'

    witnessModule := witnessModule.pushUInt32sTo xinTraces[xy]! xinEntry
    witnessModule := witnessModule.pushUInt32sTo yinTraces[xy]! yinEntry
    witnessModule := witnessModule.pushUInt32sTo traces.coutTraces[xy]! coutEntry
    witnessModule := witnessModule.pushUInt32sTo zoutTraces[xy]! zoutEntry

    witnessModule := witnessModule.bindOracleTo xins[xy]! xinEntry .b1
    witnessModule := witnessModule.bindOracleTo yins[xy]! yinEntry .b1
    witnessModule := witnessModule.bindOracleTo couts[xy]! coutEntry .b1
    witnessModule := witnessModule.bindOracleTo zouts[xy]! zoutEntry .b1

  -- not to forget about dIn
  let (dInEntry, witnessModule') := witnessModule.addEntry
  witnessModule := witnessModule'
  witnessModule := witnessModule.pushUInt32sTo traces.dInTraces dInEntry
  witnessModule := witnessModule.bindOracleTo dIn dInEntry .b1

  witnessModule := witnessModule.populate mode

  let witness := compileWitnessModules #[witnessModule] #[mode]
  withExceptOk "[Archon] addition/xor/rotate module testing is OK" (validateWitness #[circuitModule] #[] witness) fun _ => .done

def Tests.Blake3.suite : List LSpec.TestSeq :=
[
  testCompression,
  testTraceGenerating,
  testArchonStateTransitionModule,
  testArchonCVOutputModule,
  testArchonAdditionXorRotateModule,
]
