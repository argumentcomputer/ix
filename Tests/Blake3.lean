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
  let indices := List.range 8
  aux #[] state indices
where aux transitions state indices := match indices with
  | [] => (transitions, state)
  | i :: is =>
    let newState := transition state (Fin.ofNat' 8 i)
    aux (transitions.push newState) newState is

def round (state: Array UInt32) : Array (Array UInt32) × Array UInt32 :=
  let (transition, state) := roundNoPermute state
  Prod.mk transition (permute state)

def compress (cv : Array UInt32) (blockWords : Array UInt32) (counter : UInt64) (blockLen flags : UInt32) : Array (Array UInt32) × Array UInt32 :=
  let counterLow := UInt32.ofBitVec (counter.toBitVec.truncate 32)
  let counterHigh := UInt32.ofBitVec ((counter.shiftRight 32).toBitVec.truncate 32)

  let state := cv ++ (IV.extract 0 4).toArray ++ #[counterLow, counterHigh, blockLen, flags] ++ blockWords

  -- every compression includes 7 rounds (where last round doesn't include permutation)
  let rec runRounds (transitions : Array (Array UInt32)) (state : Array UInt32) (indices : List Nat) :
      Array (Array UInt32) × Array UInt32 :=
    match indices with
    | [] => (transitions, state)
    | i :: is =>
      let (roundTransitions, newState) :=
        if i == 6 then roundNoPermute state else round state
      runRounds (transitions.append roundTransitions) newState is

  let (transitions, state) := runRounds #[state] state (List.range 7)

  let temp := ((state.extract 0 8).zipWith (Xor.xor) (state.extract 8 16))
  let state := temp.append (state.extract 8 32)
  let temp := (state.extract 8 16).zipWith (Xor.xor) cv
  let state := state.extract 0 8 ++ temp ++ state.extract 16 32
  let transitions := transitions.push state

  -- pad state transitions with 6 zero-arrays for correct transposing
  let zeroes := Array.ofFn (n := 32) (fun _ => (0 : UInt32))
  let transitions := transitions.append (Array.ofFn (n := 6) (fun _ => zeroes))

  Prod.mk (Utilities.transpose transitions 32) (state.extract 0 16)

end Blake3

namespace TraceGeneration

abbrev ExpectedStates := Array (Array UInt32)

def generateTraces (rng : StdGen) (length : Nat) :  Array (Array UInt32) × ExpectedStates :=
  let rec generateTracesInner (rng : StdGen) (length : Nat) (transitions :  Array (Array UInt32)) (array : ExpectedStates) :  Array (Array UInt32) × ExpectedStates :=
    match length with
    | 0 => Prod.mk transitions array
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

      let (transition, expected) := Blake3.compress cv block counter blockLen flags

      -- we extend 'transitions' inner arrays via concatenating new transition arrays to them
      let transitions' := if transitions.isEmpty then transition else (transitions.zip transition).map (fun (a, b) => a ++ b)
      generateTracesInner g₂ length' transitions' (array.push expected)

  generateTracesInner rng length Array.empty Array.empty

end TraceGeneration

open TraceGeneration
open Blake3
open LSpec
open Archon

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
    let (traces, _expected) := generateTraces (mkStdGen 0) 1

    let lenExpected := traces.all (fun a => a.size == 64)
    let endExpected := traces.all (fun a => if a.size < 6 then false else
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
            let (committed', circuitModule):= circuitModule.addCommitted (String.append name (toString length)) f
            let (input', circuitModule) := circuitModule.addProjected (String.append (String.append name (toString length)) "input") committed' 0 64
            let (output', circuitModule) := circuitModule.addProjected (String.append (String.append name (toString length)) "output") committed' 57 64

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

    let arrayEq (a b : Array UInt32) : Bool :=
      if a.size != b.size then
        false
      else
        let rec loop (i : Nat) : Bool :=
          if i < a.size then
            if a[i]! != b[i]! then false else loop (i + 1)
          else
            true
        loop 0

    let byteArrayToUInt32Array (b : ByteArray) : Array UInt32 :=
      let len := b.size / 4
      Array.ofFn (n := len) (fun i =>
        let base := i.toNat * 4
        let b0 := b.get! base
        let b1 := b.get! (base + 1)
        let b2 := b.get! (base + 2)
        let b3 := b.get! (base + 3)
        UInt32.ofNat (b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24))
      )

    let compressionsLogTest := 5
    let tracesNum := 2 ^ compressionsLogTest
    let (traces, expected) := TraceGeneration.generateTraces (mkStdGen 0) tracesNum

    let nVars := Nat.log2 (tracesNum * (Nat.pow 2 6))

    let height := 2 ^ nVars
    let circuitModule := CircuitModule.new 0
    let (circuitModule, state, _, output) := mkColumns circuitModule 32 .b32 "stateTransition"
    let circuitModule := circuitModule.freezeOracles
    let witnessModule := circuitModule.initWitnessModule
    let witnessModule := writeTraces witnessModule traces state .b32
    let witnessModule := witnessModule.populate height.toUInt64

    -- get data as ByteArray of every actually computed cv and convert it to Array UInt32 for comparison
    let actual := (Array.ofFn (n := 16) fun i => witnessModule.getData output[i]!).map (fun bytes => byteArrayToUInt32Array bytes)
    let expected := Utilities.transpose expected 16

    let witness := compileWitnessModules #[witnessModule] #[height.toUInt64]
    withExceptOk "[Archon] state transition module testing is OK" (validateWitness #[circuitModule] #[] witness) fun _ =>
      test "output is expected" ((actual.zip expected).all (fun (a, b) => arrayEq a b))

def Tests.Blake3.suite : List LSpec.TestSeq :=
[
  testCompression,
  testTraceGenerating,
  testArchonStateTransitionModule,
]
