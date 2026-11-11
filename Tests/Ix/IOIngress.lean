import Tests.Ix.IxVM.Sources
import Tests.Ix.IxVM.Exploits
import LSpec

/-!
# Every byte a program reads from IO is range-checked

The IxVM, `ix_aggr` and multi-stark verifier programs read their IO streams
through hints (`hint::<T>("channel", key)`), which return arbitrary field
elements. A byte must be proved below 256 (`UInt8::from_field`, a byte-table
lookup) before anything hashes or parses it: BLAKE3 absorbs message bytes as
packed 32-bit words, so elements that are not bytes could keep a stream's
digest while the parsers read other fields out of them.

Two kinds of check:

* **Structural**, over the programs' source text
  (`Tests.Ix.IxVM.programSources`):
  - each byte-reading channel (`*.read*`) is read only by its pinned reader
    functions, and each of them passes what it reads to `UInt8::from_field`;
  - every other hint channel is a pinned channel, read only by its pinned
    functions: offsets and lengths, and IxVM's advisory reducibility hint,
    which only selects a reduction heuristic, def-eq being sound under any
    value.

  A new IO read path, or a byte reader that skips the range check, fails here
  until it is reviewed and pinned.
* **Execution**, through the IxVM program: a constant whose bytes are genuine
  is read; the same bytes with one word's elements shifted out of byte range,
  keeping the word's packed value, are refused.
-/

namespace Tests.IOIngress

open LSpec Tests.Ix.IxVM

/-- The module directories of the programs whose IO reads are checked: IxVM,
and the multi-stark verifier with `ix_aggr` (the verifier plus the aggregation
modules), which share one directory and are scanned as their union. -/
def bundles : List System.FilePath :=
  ["IxVM/IxVM/Source", "MultiStark/MultiStark/Modules"]

/-- The byte-reading channels and the functions allowed to read each. -/
def byteReaders : List (String × List String) := [
  ("ixvm.io.read", ["IxByteStream::read_byte_stream"]),
  ("stark.io.read1", ["StarkIO::read_byte_stream", "ProofDeserialize::read_u8_at"]),
  ("stark.io.read8", ["ProofDeserialize::read_u64_at"])]

/-- The other hint channels, which read offsets, lengths and advisory values,
and the functions allowed to read each (`none`: any function). -/
def otherChannels : List (String × Option (List String)) := [
  ("ixvm.io.info", some ["IxVMCompat::io_get_info"]),
  ("ixvm.io.claim", some ["KernelClaim::run_claim"]),
  ("ixvm.io.tag", some ["Ingress::load_constant_hint"]),
  -- The binder data of the conversion (D2): untrusted, validated by the kernel's rules.
  ("ixvm.pw", some ["Convert::read_pw"]),
  ("ixvm.pw.param", some ["Convert::pw_params"]),
  ("ixvm.pw.share", some ["Convert::read_pw_share"]),
  -- `ix_aggr` locates every advice section by `(slot, key)`; the sections it
  -- reads are byte streams read through `StarkIO::read_byte_stream`.
  ("stark.io.info", none), ("stark.io.address", none), ("stark.io.digest", none)]

/-- The ingress violations of the programs' sources. -/
def violations : IO (Array String) := do
  let mut found := #[]
  let mut seen : Std.HashSet String := {}
  for bundle in bundles do
    for f in Sources.functions (← programSources bundle) do
      for channel in Sources.hintChannels f.body do
        seen := seen.insert channel
        if let some (_, readers) := byteReaders.find? (·.1 == channel) then
          unless readers.contains f.name do
            found := found.push s!"{f.name} ({f.file}) reads bytes from {channel} directly"
          unless (f.body.splitOn "UInt8::from_field(").length > 1 do
            found := found.push s!"{f.name} ({f.file}) reads {channel} without UInt8::from_field"
        else match otherChannels.find? (·.1 == channel) with
          | some (_, some readers) =>
            unless readers.contains f.name do
              found := found.push s!"{f.name} ({f.file}) reads {channel}"
          | some (_, none) => pure ()
          | none => found := found.push s!"{f.name} ({f.file}) reads a new hint channel {channel}"
  -- The scanner still finds every byte reader: a change in the sources' shape
  -- that hides them fails rather than passes.
  for (channel, _) in byteReaders do
    unless seen.contains channel do
      found := found.push s!"no function reads {channel}: the scanner no longer reads the sources"
  return found

def structural : TestSeq :=
  .individualIO "every IO byte the IxVM and multi-stark programs read is range-checked" none (do
    let found ← violations
    let ok := found.isEmpty
    return (ok, if ok then 1 else 0, 1,
      if ok then none else some ("; ".intercalate found.toList))) .done

def suite : List TestSeq := [structural]

/-! ## Execution -/

/-- `w` with the bytes of the constant at `addr` on channel 2 changed: the
first four-byte word whose second byte is nonzero gets its first element raised
by 256 and its second lowered by one, which keeps the word's packed value. -/
def shiftOutOfRange (w : IxVM.ClaimHarness.ClaimWitness) (addr : Address) :
    Except String IxVM.ClaimHarness.ClaimWitness := do
  let key : Array Aiur.G := addr.hash.data.map .ofUInt8
  let some info := w.inputIOBuffer.map[((2 : Aiur.G), key)]?
    | throw "the witness carries no bytes for the constant"
  let arena := w.inputIOBuffer.data.getD 2 #[]
  let some i := ((List.range (info.len / 4)).map (4 * ·)).find? (fun i =>
      (arena[info.idx + i + 1]?.map (·.n)).getD 0 > 0)
    | throw "the constant has no word with a nonzero second byte"
  let byteAt (j : Nat) := (arena[info.idx + j]?.map (·.n)).getD 0
  let arena := (arena.set! (info.idx + i) (.ofNat (byteAt i + 256))).set! (info.idx + i + 1)
    (.ofNat (byteAt (i + 1) - 1))
  return { w with inputIOBuffer := { w.inputIOBuffer with
    data := w.inputIOBuffer.data.insert 2 arena } }

/-- A `Reveal` of `unsafe axiom _ : Sort 0` read from genuine bytes, and from
the same bytes with a word shifted out of byte range. -/
def cases : Except String (Array Case) := do
  let (env, addr) := Exploits.storeAt {} Exploits.unsafePropAxiom
  let claim : Ix.Claim := .reveal addr (.axio (some true) (some 0) none)
  let genuine ← Case.ofClaim "ingress: genuine constant bytes are read" env claim
  let shifted ← shiftOutOfRange genuine.witness addr
  return #[genuine,
    { genuine with label := "ingress: a constant byte out of range, packed word kept, is refused"
                   accept := false, witness := shifted }]

def run : IO UInt32 := do
  runCases "ixvm-io-ingress" ((← IO.ofExcept cases).map fun c _ => pure c)

end Tests.IOIngress
