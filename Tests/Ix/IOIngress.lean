module
public import Tests.Aiur.Common
public import Ix.IxVM.Toplevel
public import Ix.Aggr
public import Ix.Ixon

/-!
# Every byte a circuit reads from IO is range-checked

`read_checked_byte_stream` (`Ix/Aiur/Library/ByteStream.lean`) is the one
reader for byte streams on IO channels. It proves the stream finite and every
element below 256 before anything hashes or parses it. The check matters
because BLAKE3 absorbs message bytes only as packed 32-bit words: elements
that are not bytes could keep a stream's digest while the parsers read other
fields out of them.

Two kinds of check:

* **Structural**, over the compiled IxVM, `ix_aggr` and multi-stark verifier
  toplevels:
  - `io_read` occurs only in the stream materializer and the multi-stark
    proof-stream readers;
  - the unchecked materializer is called only by the checked reader and by
    IxVM's advisory channel-3 hint;
  - the checked reader is never called unconstrained, and it calls
    `assert_byte_stream` constrained.

  A new IO read path that bypasses the checked reader fails here.
* **Execution**, for one IxVM constant read, one `ix_aggr` claim-preimage read
  and one verifying-key read: genuine bytes are accepted. The same bytes with
  one word's elements shifted out of byte range, keeping the word's packed
  value, are refused by the range check before anything is hashed.
-/

public section

namespace Tests.IOIngress

open LSpec Aiur

/-! ## Structural -/

/-- Every op of a function body, through every match arm and continuation. -/
def blockOps (body : Bytecode.Block) : Array Bytecode.Op := Id.run do
  let mut stack := #[body]
  let mut ops := #[]
  while !stack.isEmpty do
    let block := stack.back!
    stack := stack.pop
    ops := ops ++ block.ops
    match block.ctrl with
    | .match _ cases dflt => stack := stack ++ cases.map (·.2) ++ dflt.toArray
    | .matchContinue _ cases dflt _ _ _ continuation =>
      stack := (stack ++ cases.map (·.2) ++ dflt.toArray).push continuation
    | .return .. | .yield .. => pure ()
  return ops

/-- The functions that may read IO cells directly.
* `read_byte_stream_unchecked` materializes a byte stream as advice, for the
  checked reader to verify.
* `read_u8_at` and `read_u64_at` read the multi-stark proof stream. The proof
  is advice read as field values; the transcript and the Merkle and FRI checks
  bind those values, so the stream is never hashed and re-parsed
  (`MultiStark/Deserialize.lean`). -/
def ioReadAllowed : List String :=
  ["read_byte_stream_unchecked", "read_u8_at", "read_u64_at"]

/-- The callers allowed to use the unchecked materializer.
* `read_checked_byte_stream` checks every element it returns.
* `read_byte_stream_unchecked` recurses.
* `load_constant_hint` reads IxVM's channel-3 reducibility hint. It is
  advisory: the hint only selects a reduction heuristic and def-eq is sound
  under any value, so no content of it is unsafe. -/
def uncheckedCallers : List String :=
  ["read_checked_byte_stream", "read_byte_stream_unchecked", "load_constant_hint"]

/-- The ingress violations of one compiled toplevel. -/
def violations (label : String) (compiled : CompiledToplevel) : Array String := Id.run do
  let names : Std.HashMap Nat (Array String) :=
    compiled.nameMap.fold (init := {}) fun acc global index =>
      acc.insert index ((acc.getD index #[]).push (toString global))
  let nameOf (index : Nat) := ", ".intercalate (names.getD index #[s!"<fn {index}>"]).toList
  let isOneOf (index : Nat) (allowed : List String) := (names.getD index #[]).any allowed.contains
  let some unchecked := compiled.getFuncIdx `read_byte_stream_unchecked
    | return #[s!"{label}: no read_byte_stream_unchecked"]
  let some checked := compiled.getFuncIdx `read_checked_byte_stream
    | return #[s!"{label}: no read_checked_byte_stream"]
  let some walk := compiled.getFuncIdx `assert_byte_stream
    | return #[s!"{label}: no assert_byte_stream"]
  let mut found := #[]
  let mut walkConstrained := false
  for (function, index) in compiled.bytecode.functions.zipIdx do
    for op in blockOps function.body do
      match op with
      | .ioRead .. =>
        unless isOneOf index ioReadAllowed do
          found := found.push s!"{label}: {nameOf index} reads IO cells directly"
      | .call callee _ _ unconstrained =>
        if callee == unchecked && !isOneOf index uncheckedCallers then
          found := found.push s!"{label}: {nameOf index} calls read_byte_stream_unchecked"
        if callee == checked && unconstrained then
          found := found.push
            s!"{label}: {nameOf index} calls read_checked_byte_stream unconstrained"
        if index == checked && callee == walk && !unconstrained then
          walkConstrained := true
      | _ => pure ()
  unless walkConstrained do
    found := found.push
      s!"{label}: read_checked_byte_stream does not call assert_byte_stream constrained"
  return found

/-- The toplevels whose IO reads must all be checked: IxVM with its test and
benchmark entrypoints, and the production `ix_aggr` and multi-stark verifier
toplevels. The multi-stark library's indexed IO hasher (`b3_io`) is a
test helper outside every production toplevel; were a production entrypoint
to reach it, its `io_read` would be reported here. -/
def targets : List (String × Except Global Source.Toplevel) :=
  [("ixvm", IxVM.ixVMFull), ("ix_aggr", Aggr.ixAggr), ("multi_stark", MultiStark.multiStark)]

def structural : IO TestSeq := do
  let mut tests := TestSeq.done
  for (label, toplevel) in targets do
    let compiled ← IO.ofExcept ((toplevel.mapError toString).bind (·.compile))
    let found := violations label compiled
    for violation in found do IO.eprintln violation
    tests := tests ++ test s!"{label}: every IO read goes through the checked reader"
      found.isEmpty
  return tests

/-! ## Execution -/

def ixvmProbe := ⟦
  pub fn ingress_constant_probe(addr: [U8; 32]) {
    let _constant = load_verified_constant(store(addr));
    ()
  }
⟧

def aggrProbe := ⟦
  pub fn ingress_preimage_probe(digest: [G; 8]) {
    let _bytes = aggr_load_preimage(digest);
    ()
  }

  pub fn ingress_vk_probe(digest: [G; 8]) {
    let _system = aggr_load_sys(0, digest, digest);
    ()
  }
⟧

def ixvmProbeToplevel : Except Global Source.Toplevel := do
  let vm ← IxVM.ixVMFull
  let vm ← vm.merge ixvmProbe
  return vm.prune [`ingress_constant_probe]

def aggrProbeToplevel : Except Global Source.Toplevel := do
  let t ← Aggr.ixAggrFull
  let t ← t.merge aggrProbe
  return t.prune [`ingress_preimage_probe, `ingress_vk_probe]

def bytesGs (bytes : ByteArray) : Array Aiur.G := bytes.data.map .ofUInt8

/-- `bytes` as IO elements with one 4-byte word's elements moved out of byte
range: element `k` gains 256 and element `k + 1`, in the same word, loses 1,
so the word's packed value `b0 + 2^8 b1 + 2^16 b2 + 2^24 b3` is unchanged. -/
def shifted (bytes : ByteArray) : Option (Array Aiur.G) := do
  let k ← (List.range (bytes.size - 1)).find? fun k => k % 4 != 3 && bytes[k + 1]! != 0
  let raised : Aiur.G := .ofNat (bytes[k]!.toNat + 256)
  let lowered : Aiur.G := .ofNat (bytes[k + 1]!.toNat - 1)
  return ((bytesGs bytes).set! k raised).set! (k + 1) lowered

/-- Accepted on genuine bytes, refused by the range check on shifted ones. -/
def checkIngress (label : String) (compiled : CompiledToplevel) (entry : Lean.Name)
    (input : Array Aiur.G) (bytes : ByteArray) (buffer : Array Aiur.G → IOBuffer) :
    IO TestSeq := do
  let some index := compiled.getFuncIdx entry
    | throw (IO.userError s!"{label}: missing entrypoint {entry}")
  let some bad := shifted bytes
    | throw (IO.userError s!"{label}: no word to shift")
  let genuine ← match compiled.bytecode.execute index input (buffer (bytesGs bytes)) with
    | .ok _ => pure true
    | .error e => do
      IO.eprintln s!"{label}: genuine bytes failed: {e}"
      pure false
  let refused ← match compiled.bytecode.execute index input (buffer bad) with
    | .ok _ => do
      IO.eprintln s!"{label}: shifted bytes were accepted"
      pure false
    | .error e => do
      let byRangeCheck : Bool := (e.splitOn "out of u8 range").length > 1
      unless byRangeCheck do IO.eprintln s!"{label}: shifted bytes failed otherwise: {e}"
      pure byRangeCheck
  return test s!"{label}: genuine bytes accepted" genuine ++
    test s!"{label}: shifted bytes refused by the range check" refused

def execution : IO TestSeq := do
  let vm ← IO.ofExcept ((ixvmProbeToplevel.mapError toString).bind (·.compile))
  let constant : Ixon.Constant :=
    { info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 },
      sharing := #[], refs := #[Address.blake3 "io ingress".toUTF8], univs := #[] }
  let constantBytes := Ixon.serConstant constant
  let address := Address.blake3 constantBytes
  let constantTest ← checkIngress "IxVM constant" vm `ingress_constant_probe
    (bytesGs address.hash) constantBytes
    fun elements => (default : IOBuffer).extend 2 (bytesGs address.hash) elements

  let aggr ← IO.ofExcept ((aggrProbeToplevel.mapError toString).bind (·.compile))
  let preimage := "a claim preimage on channel 4".toUTF8
  let preimageTest ← checkIngress "ix_aggr preimage" aggr `ingress_preimage_probe
    (MultiStark.digestGs preimage) preimage
    fun elements => (default : IOBuffer).extend 4 (MultiStark.digestGs preimage) elements

  let system := AiurSystem.build aggr.bytecode commitmentParameters friParameters
  let vk := system.vkBytes
  let vkTest ← checkIngress "verifying key" aggr `ingress_vk_probe
    (MultiStark.digestGs vk) vk
    fun elements => (default : IOBuffer).extend 1 #[.ofNat 0] elements
  return constantTest ++ preimageTest ++ vkTest

def suite : IO (List TestSeq) := do
  return [← structural, ← execution]

end Tests.IOIngress

end
