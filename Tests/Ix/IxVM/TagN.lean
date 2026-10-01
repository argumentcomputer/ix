/-
  TagN in the IxVM circuit.

  The circuit carries its own TagN readers (`get_tagn0/2/4`,
  `Ix/IxVM/IxonDeserialize.lean`) and writers (`put_tagn0/2/4`,
  `Ix/IxVM/IxonSerialize.lean`). These tests hold them to the host codec
  (`Ixon.putTagN` / `Ixon.getTagN`) on the vectors of `Tests.Ixon.tagNUnits`:
  every rung boundary for f = 0, 2 and 4 with the lowest and the highest flag,
  the expected encodings, the rejection vectors, the 2^64 limit of the 8-byte
  rung, truncations, and a sweep of one- and two-byte strings.

  A string the circuit accepts must decode to the host's flag and value and
  re-encode to the same bytes (checked inside the circuit); a string the host
  rejects, the circuit must reject. The explicit vectors also run through the
  source interpreter, and one value per rung is proved and verified.
-/
import Ix.Ixon
import Ix.IxVM.Toplevel
import Ix.Aiur.Compiler
import Ix.Aiur.Interpret
import Tests.Aiur.Common
import LSpec

open LSpec

namespace Tests.Ix.IxVM.TagN

/-- Test entrypoints over the production codec modules. -/
def entrypoints := ⟦
  -- Decode the TagN integer on ch 0 with an `f`-bit flag, require every
  -- byte consumed, re-encode the value and require the same bytes.
  pub fn tagn_codec(f: G) -> (G, U64) {
    let (idx, len) = io_get_info(0, [0]);
    let bytes = read_byte_stream(0, idx, len);
    match f {
      0 =>
        let (value, rest) = get_tagn0(bytes);
        assert_eq!(load(rest), ListNode.Nil, "trailing TagN bytes");
        assert_eq!(put_tagn0(value, store(ListNode.Nil)), bytes,
          "TagN re-encoding differs");
        (0, value),
      2 =>
        let (tag, rest) = get_tagn2(bytes);
        let (flag, value) = tag;
        assert_eq!(load(rest), ListNode.Nil, "trailing TagN bytes");
        assert_eq!(put_tagn2(flag, value, store(ListNode.Nil)), bytes,
          "TagN re-encoding differs");
        (flag, value),
      4 =>
        let (tag, rest) = get_tagn4(bytes);
        let (flag, value) = tag;
        assert_eq!(load(rest), ListNode.Nil, "trailing TagN bytes");
        assert_eq!(put_tagn4(flag, value, store(ListNode.Nil)), bytes,
          "TagN re-encoding differs");
        (flag, value),
    }
  }

  -- Decode only: a rejection here is the reader's alone.
  pub fn tagn_decode(f: G) {
    let (idx, len) = io_get_info(0, [0]);
    let bytes = read_byte_stream(0, idx, len);
    let rest = match f {
      0 =>
        let (_, r) = get_tagn0(bytes);
        r,
      2 =>
        let (_, r) = get_tagn2(bytes);
        r,
      4 =>
        let (_, r) = get_tagn4(bytes);
        r,
    };
    assert_eq!(load(rest), ListNode.Nil, "trailing TagN bytes");
  }
⟧

def toplevel : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← Aiur.Library.core.merge Aiur.Library.byteStream
  let vm ← vm.merge IxVM.ixon
  let vm ← vm.merge IxVM.ixonSerialize
  let vm ← vm.merge IxVM.ixonDeserialize
  let vm ← vm.merge entrypoints
  return vm.prune [`tagn_codec, `tagn_decode]

def buffer (bytes : ByteArray) : Aiur.IOBuffer :=
  (default : Aiur.IOBuffer).extend 0 #[0] (bytes.data.map .ofUInt8)

/-- The entrypoint output for a decoded flag and value: the flag, then the
value's eight little-endian bytes. -/
def output (flag : UInt8) (value : UInt64) : Array Aiur.G :=
  #[.ofNat flag.toNat] ++
    (Array.range 8).map fun i => .ofNat ((value.toNat >>> (8 * i)) % 256)

/-- The host reading of `bytes`, as the circuit should report it. -/
def host (f : Nat) (bytes : ByteArray) : Option (Array Aiur.G) :=
  match Ixon.runGetExact (Ixon.getTagN f) bytes with
  | .ok t => some (output t.flag t.value)
  | .error _ => none

/-- Run `entry` on `bytes` in the bytecode executor: the output, or `none` if
execution fails. -/
def run (env : AiurTestEnv) (entry : Lean.Name) (f : Nat) (bytes : ByteArray) :
    Option (Array Aiur.G) :=
  match env.compiled.getFuncIdx entry with
  | none => none
  | some idx =>
    match env.compiled.bytecode.execute idx #[.ofNat f] (buffer bytes) with
    | .ok (out, _, _) => some out
    | .error _ => none

/-- Run `entry` on `bytes` in the source interpreter. -/
def interpret (env : AiurTestEnv) (entry : Lean.Name) (f : Nat) (bytes : ByteArray) :
    Option (Array Aiur.G) :=
  let name := Aiur.Global.mk entry
  match env.decls.getByKey name with
  | some (.function function) =>
    let inputs := Aiur.unflattenInputs env.decls #[.ofNat f] (function.inputs.map (·.2))
    match Aiur.runFunction env.decls name inputs (buffer bytes) with
    | (.ok value, _) =>
      some (Aiur.flattenValue env.decls (fun g => env.compiled.getFuncIdx g.toName) value)
    | (.error _, _) => none
  | _ => none

/-- The circuit agrees with the host on `bytes`: the same value when the host
accepts (and the circuit's re-encoding is the input), a rejection when it does
not. With `decode`, a host rejection must also reject in the decode-only
entrypoint, so it cannot come from the writer. -/
def agrees (env : AiurTestEnv) (f : Nat) (bytes : ByteArray) (decode : Bool := true) :
    Bool :=
  match host f bytes with
  | some expected => run env `tagn_codec f bytes == some expected
  | none =>
    (run env `tagn_codec f bytes).isNone &&
      (!decode || (run env `tagn_decode f bytes).isNone)

/-- `agrees`, and the source interpreter agrees as well. -/
def agreesEverywhere (env : AiurTestEnv) (f : Nat) (bytes : ByteArray) : Bool :=
  agrees env f bytes &&
    match host f bytes with
    | some expected => interpret env `tagn_codec f bytes == some expected
    | none =>
      (interpret env `tagn_codec f bytes).isNone &&
        (interpret env `tagn_decode f bytes).isNone

def tagNBytes (f : Nat) (flag : UInt8) (v : Nat) : ByteArray :=
  Ixon.runPut (Ixon.putTagN f flag v.toUInt64)

/-- Rung boundary values for an `f`-bit flag, plus the `UInt64` extremes. -/
def boundaries (f : Nat) : List Nat :=
  let ends := [Ixon.tagNEnd1 f, Ixon.tagNEnd2 f, Ixon.tagNEnd3 f, Ixon.tagNEnd4 f,
    Ixon.tagNEnd5 f]
  [0, 1, 2 ^ 64 - 1] ++ ends.flatMap fun e => [e - 1, e, e + 1]

/-- The encoding of `v`, its proper prefixes, and the encoding with a
trailing byte: the first decodes to `v`, the others are rejected. -/
def encodingChecks (env : AiurTestEnv) (f : Nat) (flag : UInt8) (v : Nat) : Bool :=
  let bytes := tagNBytes f flag v
  host f bytes == some (output flag v.toUInt64) &&
    agreesEverywhere env f bytes &&
    agrees env f (bytes.push 0) &&
    (List.range bytes.size).all fun n => agrees env f (bytes.extract 0 n)

def boundaryTests (env : AiurTestEnv) : TestSeq :=
  [0, 2, 4].foldl (init := .done) fun acc f =>
    [0, (2 ^ f - 1 : Nat)].foldl (init := acc) fun acc flag =>
      (boundaries f).foldl (init := acc) fun acc v =>
        acc ++ test s!"circuit TagN f={f} flag={flag} value={v}: decode, re-encode, \
          truncations and trailing byte" (encodingChecks env f flag.toUInt8 v)

/-- The expected encodings of `Tests.Ixon.tagNUnits`, as the circuit reads and
writes them. -/
def expectedVectors : List (Nat × UInt8 × Nat × Array UInt8) := [
  (4, 0xA, 7, #[0xA7]),
  (4, 0xA, 8, #[0xA8, 0x00]),
  (4, 0x1, 1031, #[0x1B, 0xFF]),
  (4, 0, 1032, #[0x0C, 0x00, 0x00]),
  (4, 0, 66567, #[0x0C, 0xFF, 0xFF]),
  (4, 0, 66568, #[0x0D, 0, 0, 0]),
  (4, 0, 16843783, #[0x0D, 0xFF, 0xFF, 0xFF]),
  (4, 0, 16843784, #[0x0E, 0, 0, 0, 0]),
  (4, 0, 4311811079, #[0x0E, 0xFF, 0xFF, 0xFF, 0xFF]),
  (4, 0, 4311811080, #[0x0F, 0, 0, 0, 0, 0, 0, 0, 0]),
  (0, 0, 127, #[0x7F]),
  (0, 0, 128, #[0x80, 0x00]),
  (0, 0, 16512, #[0xC0, 0x00, 0x00]),
  (0, 0, 82047, #[0xC0, 0xFF, 0xFF]),
  (0, 0, 82048, #[0xC1, 0, 0, 0]),
  (0, 0, 16859263, #[0xC1, 0xFF, 0xFF, 0xFF]),
  (0, 0, 16859264, #[0xC2, 0, 0, 0, 0]),
  (0, 0, 4311826560, #[0xC3, 0, 0, 0, 0, 0, 0, 0, 0]),
  (0, 0, 2 ^ 64 - 1, #[0xC3, 0x7F, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]),
  (2, 3, 32, #[0xE0, 0x00]),
  (2, 3, 4128, #[0xF0, 0x00, 0x00]),
  (2, 3, 69663, #[0xF0, 0xFF, 0xFF]),
  (2, 3, 69664, #[0xF1, 0, 0, 0]),
  (2, 3, 16846879, #[0xF1, 0xFF, 0xFF, 0xFF]),
  (2, 3, 16846880, #[0xF2, 0, 0, 0, 0]),
  (2, 3, 4311814176, #[0xF3, 0, 0, 0, 0, 0, 0, 0, 0])
]

def expectedTests (env : AiurTestEnv) : TestSeq :=
  expectedVectors.foldl (init := .done) fun acc (f, flag, v, bytes) =>
    let bytes := ByteArray.mk bytes
    acc ++ test s!"circuit TagN f={f} bytes of {v}"
      (tagNBytes f flag v == bytes && agreesEverywhere env f bytes &&
        run env `tagn_codec f bytes == some (output flag v.toUInt64))

/-- Little-endian bytes of `x`, `n` of them. -/
def le (n x : Nat) : Array UInt8 :=
  (Array.range n).map fun i => ((x >>> (8 * i)) % 256).toUInt8

/-- The rejection vectors of `Tests.Ixon.tagNUnits`, plus the exact 2^64
limit of the 8-byte rung for every flag width. -/
def rejectedVectors : List (String × Nat × Array UInt8) := [
  ("f=2 code 4", 2, #[0x34]),
  ("f=2 code 15", 2, #[0x3F]),
  ("f=0 code 4", 0, #[0xC4]),
  ("f=0 code 63", 0, #[0xFF]),
  ("f=0 code 4 with eight payload bytes", 0, #[0xC4, 0, 0, 0, 0, 0, 0, 0, 0]),
  ("f=4 overflow", 4, #[0x0F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  ("f=2 overflow", 2, #[0xF3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  ("f=0 overflow", 0, #[0xC3, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  ("truncated rung 2", 4, #[0x08]),
  ("truncated rung 4", 4, #[0x0D, 0x00, 0x00]),
  ("truncated rung 6", 4, #[0x0F, 0x00, 0x00, 0x00]),
  ("trailing byte", 4, #[0x07, 0x00])
] ++ [0, 2, 4].map fun f =>
  -- Code 3 sits at payload 3h + 3, h = 2^(6 - f).
  (s!"f={f} value 2^64", f,
    #[Ixon.tagNHeader f 0 (3 * 2 ^ (6 - f) + 3)] ++ le 8 (2 ^ 64 - Ixon.tagNEnd5 f))

def rejectedTests (env : AiurTestEnv) : TestSeq :=
  rejectedVectors.foldl (init := .done) fun acc (name, f, bytes) =>
    let bytes := ByteArray.mk bytes
    acc ++ test s!"circuit TagN rejects {name}"
      ((host f bytes).isNone && agreesEverywhere env f bytes)

/-- Every one-byte string, and every header followed by a sample of second
bytes: the circuit's verdict and value match the host's on each. -/
def sweepTests (env : AiurTestEnv) : TestSeq :=
  let seconds : List UInt8 := [0x00, 0x01, 0x7F, 0x80, 0xFE, 0xFF]
  [0, 2, 4].foldl (init := .done) fun acc f =>
    let strings := (List.range 256).flatMap fun a =>
      ByteArray.mk #[a.toUInt8] :: seconds.map fun b => ByteArray.mk #[a.toUInt8, b]
    let disagreements := strings.filter fun bytes => !agrees env f bytes (decode := false)
    acc ++ test s!"circuit TagN f={f}: {strings.length} one- and two-byte strings \
      agree with the host ({disagreements.length} disagree)" disagreements.isEmpty

/-- Prove and verify one value per rung for f = 4, and the largest value for
f = 0 and 2, through the codec entrypoint. -/
def proofTests (env : AiurTestEnv) : IO TestSeq := do
  let some idx := env.compiled.getFuncIdx `tagn_codec
    | return test "tagn_codec entrypoint present" false
  let values : List (Nat × UInt8 × Nat) :=
    [(4, 0xB, 7), (4, 0xB, 8), (4, 0xB, 1032), (4, 0xB, 66568), (4, 0xB, 16843784),
     (4, 0xB, 4311811080), (2, 3, 2 ^ 64 - 1), (0, 0, 2 ^ 64 - 1)]
  let mut tests : TestSeq := .done
  for (f, flag, v) in values do
    let bytes := tagNBytes f flag v
    let ok : Bool := match env.aiurSystem.prove idx #[.ofNat f] (buffer bytes) with
      | .ok (claim, proof, _) =>
        claim == Aiur.buildClaim idx #[.ofNat f] (output flag v.toUInt64) &&
          (env.aiurSystem.verify claim (Aiur.Proof.ofBytes proof.toBytes)).toOption.isSome
      | .error _ => false
    tests := tests ++ test s!"circuit TagN f={f} value={v}: prove and verify" ok
  return tests

def runSuite : IO UInt32 := do
  IO.println "ixvm-tagn"
  match AiurTestEnv.build toplevel with
  | .error e => IO.eprintln s!"TagN codec toplevel failed: {e}"; return 1
  | .ok env =>
    let proofs ← proofTests env
    LSpec.lspecIO (.ofList [("ixvm-tagn",
      [expectedTests env, rejectedTests env, boundaryTests env, sweepTests env, proofs])]) []

end Tests.Ix.IxVM.TagN
