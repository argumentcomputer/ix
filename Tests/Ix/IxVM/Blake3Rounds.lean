module

public import Ix.IxVM.Toplevel
public import Tests.Aiur.Common

public section

namespace Tests.Ix.IxVM.Blake3Rounds

open Aiur LSpec

-- This reference operates on wrapping UInt32 words. It does not use the
-- Aiur byte arithmetic, batching, lookup expressions or stage counter.
private def rotr (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def mix (s : Array UInt32) (ai bi ci di : Nat)
    (x y : UInt32) : Array UInt32 :=
  let a := s[ai]! + s[bi]! + x
  let d := rotr (s[di]! ^^^ a) 16
  let c := s[ci]! + d
  let b := rotr (s[bi]! ^^^ c) 12
  let a := a + b + y
  let d := rotr (d ^^^ a) 8
  let c := c + d
  let b := rotr (b ^^^ c) 7
  (((s.set! ai a).set! bi b).set! ci c).set! di d

private def reference (input : Array UInt32) : Array UInt32 := Id.run do
  let mut s := input.extract 0 16
  let mut m := input.extract 16 32
  for _ in [:7] do
    s := mix s 0 4 8 12 m[0]! m[1]!
    s := mix s 1 5 9 13 m[2]! m[3]!
    s := mix s 2 6 10 14 m[4]! m[5]!
    s := mix s 3 7 11 15 m[6]! m[7]!
    s := mix s 0 5 10 15 m[8]! m[9]!
    s := mix s 1 6 11 12 m[10]! m[11]!
    s := mix s 2 7 8 13 m[12]! m[13]!
    s := mix s 3 4 9 14 m[14]! m[15]!
    m := #[m[2]!, m[6]!, m[3]!, m[10]!, m[7]!, m[0]!, m[4]!, m[13]!,
      m[1]!, m[11]!, m[12]!, m[5]!, m[9]!, m[14]!, m[15]!, m[8]!]
  return (Array.range 8).map fun i => s[i]! ^^^ s[i+8]!

private def wordsToBytes (words : Array UInt32) : Array Aiur.G :=
  words.flatMap fun w => (Array.range 4).map fun i =>
    G.ofNat ((w.toNat / 256^i) % 256)

private def entries := ⟦
  pub fn blake3_rounds_test(state: [[U8; 4]; 32]) -> [[U8; 4]; 8] {
    blake3_compress(state)
  }
⟧

private def source (counters : Bool) : Except Global Source.Toplevel := do
  let vm ← IxVM.ixVMFull
  let vm ← vm.merge entries
  pure { vm.prune [`blake3_rounds_test] with counterRanks := counters }

private def states : Array (Array UInt32) :=
  #[Array.replicate 32 0, Array.replicate 32 0xffffffff,
    (Array.range 32).map fun i => if i % 2 == 0 then 0 else 0xffffffff] ++
  (#[0, 1, 255, 256, 65535, 65536, 0x7fffffff, 0x80000000,
    0xfffffffe, 0xffffffff] : Array UInt32).map fun seed =>
      (Array.range 32).map fun i =>
        seed + 0x9e3779b9 * (i+1).toUInt32

private def structureChecks (compiled : CompiledToplevel) : TestSeq :=
  let result := do
    let idx ← compiled.getFuncIdx `blake3_compress
    let f ← compiled.bytecode.functions[idx]?
    let component ← compiled.bytecode.callComponents[idx]?
    pure (!component.ranked && f.layout.inputSize == 128 &&
      f.layout.selectors == 1 && f.body.collectConstrainedCallees.isEmpty)
  test "compression is a single acyclic row with no constrained callees" (result == some true) ++
  test "compression bytecode passes component validation" compiled.bytecode.validCallComponents

def run : IO UInt32 := do
  let mut status : UInt32 := 0
  for counters in [false, true] do
    let env ← IO.ofExcept (AiurTestEnv.build (source counters))
    let structural ← lspecIO (.ofList [(s!"BLAKE3 rounds counters={counters}",
      [structureChecks env.compiled])]) []
    let cases := states.toList.zipIdx |>.map fun (state, i) =>
      { functionName := `blake3_rounds_test, label := s!"BLAKE3 word reference {i}"
        input := wordsToBytes state, expectedOutput := wordsToBytes (reference state)
        interpret := true, withProof := i < 3 || i == 12 : AiurTestCase }
    let results ← lspecEachIO cases fun tc => pure (env.runTestCase tc)
    if structural != 0 || results != 0 then status := 1
  return status

end Tests.Ix.IxVM.Blake3Rounds

end
