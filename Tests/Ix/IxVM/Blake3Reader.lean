module

public import Ix.IxVM.Toplevel
public import Tests.Aiur.Common
public import Blake3.Rust

/-!
The bounded BLAKE3 reader must preserve byte order, its exact remainder,
partial-block padding and the block/chunk flags used by its caller. Compare
boundary inputs against the Rust hash, with ordinary ranks and with the
independently checked reader counter used by the production kernel.
-/

public section

namespace Tests.Ix.IxVM.Blake3Reader

open Aiur LSpec

private def entries := ⟦
  pub fn blake3_reader_test() -> (G, [[U8; 4]; 16], [[U8; 4]; 8]) {
    let (idx, len) = io_get_info(0, [0]);
    let input = #read_byte_stream(0, idx, len);
    let (rest, acc, count) = blake3_read_block(input, store(ListNode.Nil), 0);
    let block = bytes_to_block(pad_block(acc, 64 - count));
    (count, block, @blake3(rest))
  }

  pub fn blake3_binding_test(expected: [U8; 32]) {
    let (idx, len) = io_get_info(0, [0]);
    let input = #read_byte_stream(0, idx, len);
    verify_bytes_against(input, expected);
  }
⟧

private def source (counters : Bool) : Except Global Source.Toplevel := do
  let vm ← IxVM.ixVMFull
  let vm ← vm.merge entries
  pure { vm.prune [`blake3_test, `blake3_reader_test, `blake3_binding_test] with
    counterRanks := counters }

private def bytes (size : Nat) : Array UInt8 :=
  (Array.range size).map fun i => (73 * i + i / 251 + 19).toUInt8

private def digest (data : Array UInt8) : Array Aiur.G :=
  (Blake3.Rust.hash ⟨data⟩).val.data.map G.ofUInt8

private def buffer (data : Array UInt8) : IOBuffer :=
  ⟨.ofList [(0, data.map G.ofUInt8)],
    .ofList [((0, #[0]), ⟨0, data.size⟩)]⟩

private def hashCase (data : Array UInt8) (proof : Bool := false)
    (interp : Bool := false) (label : String := "") : AiurTestCase :=
  { functionName := `blake3_test, label := s!"reader hash {data.size} {label}"
    expectedOutput := digest data
    inputIOBuffer := buffer data, expectedIOBuffer := buffer data
    interpret := interp, withProof := proof }

private def readerCase (size : Nat) : AiurTestCase :=
  let data := bytes size
  let count := min size 64
  let block := data.extract 0 count ++ Array.replicate (64 - count) 0
  { functionName := `blake3_reader_test, label := s!"reader block/remainder {size}"
    expectedOutput := #[G.ofNat count] ++ block.map G.ofUInt8 ++ digest (data.extract count size)
    inputIOBuffer := buffer data, expectedIOBuffer := buffer data
    interpret := size == 65, withProof := size == 65 }

private def structureChecks (compiled : CompiledToplevel) (counters : Bool) : TestSeq :=
  let result := do
    let idx ← compiled.getFuncIdx `blake3_read_block
    let f ← compiled.bytecode.functions[idx]?
    let component ← compiled.bytecode.callComponents[idx]?
    let counter ← Bytecode.UnitCounter.find? idx f
    pure (f.layout.inputSize == 3 && component.ranked == !counters &&
      counter.mode == .input && counter.column == 2 && counter.step == 1)
  test "reader has the expected checked unit-step input and rank mode" (result == some true) ++
  test "reader bytecode passes the component certificate checker" compiled.bytecode.validCallComponents

private def bindingChecks (compiled : CompiledToplevel) : TestSeq := Id.run do
  let some idx := compiled.getFuncIdx `blake3_binding_test
    | return test "binding entrypoint exists" false
  let mut seq := .done
  for size in [0, 63, 64, 65, 1024, 1025] do
    let data := bytes size
    let expected := digest data
    -- Keep the forged digest in the byte range so this tests the content
    -- binding assertion, including both sides of block/chunk boundaries.
    let wrong := expected.set! 0 (if expected[0]?.getD 0 == 0 then 1 else 0)
    let rejects : Bool := match compiled.bytecode.execute idx wrong (buffer data) with
      | .error _ => true
      | .ok _ => false
    seq := seq ++ test s!"reader rejects a wrong digest for {size} bytes" rejects
  return seq

def run : IO UInt32 := do
  let mut status : UInt32 := 0
  for counters in [false, true] do
    let .ok env := AiurTestEnv.build (source counters)
      | IO.eprintln s!"BLAKE3 reader setup failed (counters={counters})"; return 1
    let structural ← lspecIO (.ofList [(s!"reader counters={counters}",
      [structureChecks env.compiled counters, bindingChecks env.compiled])]) []
    let proofSizes := if counters then [0, 64, 65, 1024, 1025, 2049] else [64, 1025]
    let cases := [0, 1, 31, 32, 63, 64, 65, 127, 128, 129,
      1023, 1024, 1025, 2047, 2048, 2049, 3071, 3072, 3073].map fun size =>
        hashCase (bytes size) (proofSizes.contains size) (size == 0 || size == 65)
    let hashes ← lspecEachIO cases fun tc => pure (env.runTestCase tc)
    let blocks ← lspecEachIO ([0, 1, 63, 64, 65, 127, 128, 129].map readerCase)
      fun tc => pure (env.runTestCase tc)
    let values ← lspecEachIO [
      hashCase (Array.replicate 65 0) (label := "zero bytes"),
      hashCase (Array.replicate 65 255) (label := "max bytes")]
      fun tc => pure (env.runTestCase tc)
    let data := bytes 65
    let bindingCase : AiurTestCase := {
      functionName := `blake3_binding_test
      label := "reader verifies the digest of the shared byte stream"
      input := digest data, expectedOutput := #[]
      inputIOBuffer := buffer data, expectedIOBuffer := buffer data
      interpret := false, withProof := true }
    let binding ← lspecEachIO [bindingCase] fun tc => pure (env.runTestCase tc)
    if structural != 0 || hashes != 0 || blocks != 0 || values != 0 || binding != 0 then
      status := 1
  return status

end Tests.Ix.IxVM.Blake3Reader

end
