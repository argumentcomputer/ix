import IxCCTests.Rt.Decoder
import IxCCTests.Rt.Native
import IxCCTests.Src.Support

/-! The independent decoder (`IxCCTests.Rt.Decoder`) on hand-made regions, for
`tests-rt`: its type and signature parsers on the text forms `Rt.FoTy.encode`
and `Rt.Sig.encode` write, and its decoding against `Rt.readback` and against
a written expectation, on well-formed results and on the ways a result fails to
decode (an even `Nat` word, a constructor with fields as an immediate, a wrong
field count, a tag out of range, a pointer outside the region, fuel exhausted).
The native suites compare the two decoders on every result they decode; these
cases reach the failures, which well-formed native results do not. -/

namespace IxCCTests.Rt.DecoderChecks

open IxCC IxCCTests.Src

def base : Nat := 0x10000
def size : Nat := 4096

/-- A region whose bytes from `base + 16` are zero except the words given. -/
def region (words : List (Nat × Nat)) : ByteArray := Id.run do
  let mut b : ByteArray := ⟨Array.replicate (size - 16) 0⟩
  for (a, w) in words do
    for k in List.range 8 do
      b := b.set! (a - (base + 16) + k) (UInt8.ofNat (w / 256 ^ k))
  return b

/-- A cell header: the tag in bits 16 to 31, the field count in bits 0 to 7. -/
def header (tag scan : Nat) : Nat := tag * 65536 + scan

/-- Both decoders on `w`, against `want`. -/
def both (a : Assert) (label : String) (sig : Rt.Sig) (ty : Rt.FoTy) (live : ByteArray) (fuel w : Nat)
    (want : Option String) : IO Unit := do
  let view : Decoder.View := { base := UInt64.ofNat base, size := UInt64.ofNat size, live }
  let independent := Decoder.decodeText ty.encode sig.encode view fuel (UInt64.ofNat w)
  let lean := (Rt.readback sig fuel (Native.liveMemory base size (base + size) live) ty (UInt64.ofNat w)).map
    Rt.renderObs
  expectEq a independent want s!"independent decoder, {label}"
  expectEq a lean want s!"Rt.readback, {label}"

def run (a : Assert) : IO (Array String) := do
  -- the parsers
  expectEq a (Decoder.parseType "n") (some (-1)) "parse n"
  expectEq a (Decoder.parseType "i12") (some 12) "parse i12"
  for bad in ["", "x", "i", "n1", "i1x", "i-1"] do
    expectEq a (Decoder.parseType bad) none s!"parse {bad}"
  let sig : Rt.Sig := { inds := [[[], []], [[.nat, .nat]], [[], [.nat]]] }
  expectEq a sig.encode "()()/(n,n)/()(n)" "the signature's text"
  expectEq a (Decoder.parseSig sig.encode) (some #[#[#[], #[]], #[#[-1, -1]], #[#[], #[-1]]]) "parse the signature"
  expectEq a (Decoder.parseSig "") (some #[]) "parse the empty signature"
  for bad in ["(", "(n", "(n;n)", "()x", "(q)"] do
    expectEq a (Decoder.parseSig bad) none s!"parse the signature {bad}"
  -- decoding: a list of naturals, `#0` nil and `#1(head, tail)` cons
  let list : Rt.Sig := { inds := [[[], [.nat, .ind 0]]] }
  let c1 := base + 640
  let c2 := base + 664
  let good := region [(c1, header 1 2), (c1 + 8, 11), (c1 + 16, c2), (c2, header 1 2), (c2 + 8, 13), (c2 + 16, 1)]
  both a "a Nat" list .nat good 4 15 (some "7")
  both a "an even Nat word" list .nat good 4 14 none
  both a "nil" list (.ind 0) good 4 1 (some "#0")
  both a "cons as an immediate" list (.ind 0) good 4 3 none
  both a "a two-cell list" list (.ind 0) good 4 c1 (some "#1(5,#1(6,#0))")
  both a "fuel for one cell" list (.ind 0) good 1 c1 none
  both a "a pointer below the region's data" list (.ind 0) good 4 (base + 8) none
  both a "an inductive outside the signature" list (.ind 1) good 4 1 none
  let badScan := region [(c1, header 1 3), (c1 + 8, 11), (c1 + 16, 1)]
  both a "a wrong field count" list (.ind 0) badScan 4 c1 none
  let badTag := region [(c1, header 2 2), (c1 + 8, 11), (c1 + 16, 1)]
  both a "a tag out of range" list (.ind 0) badTag 4 c1 none
  let late := region [(base + size - 16, header 1 2), (base + size - 8, 11)]
  both a "a field past the region" list (.ind 0) late 4 (base + size - 16) none
  return #["the independent decoder: its type and signature parsers on 15 texts; with Rt.readback, 11 results decoded or refused alike"]

end IxCCTests.Rt.DecoderChecks
