import MultiStark.CompressGL
import Blake3.Rust

/-! CompressGL for one pinned wrapper key: `CompressGL::verify_root` of
`MultiStark.CompressGL` with the verified system's key in this program's
fixed tables instead of IO channel 1.

The public call and statement are `CompressWrap::verify_root`'s: the
statement digest is the BLAKE3 of the domain-separated pair of key and
claims digests. The key digest is computed from the same bytes at export and
fixed in a table, so the statement still names the key actually verified;
the key bytes themselves are fixed columns, so this program's own key commits
to them. The claims stay data on channel 2. The key is parsed in circuit by
`SystemDeserialize::read_system` from a stream rebuilt from the tabled words,
exactly as the generic verifier parses the channel's bytes, and the proof is
verified by `StarkVerifier::verify_batch_at`, as in
`MultiStark::verify_multi_stark_proof`. -/
namespace MultiStark.CompressGLFixed
open Aiur

private def template : Modules.Program Nat := aiur⟦
module CompressGL {
  -- Replaced, with every table below, by `source`.
  const KEY_WORDS: Field = 0;
  const KEY_OFFSET: Field = 0;
  table key_inputs: (Field,) {}
  table key_values: [Field; 4] {}
  map key_word(index: Field) -> [Field; 4] = key_inputs => key_values;
  table key_digest_inputs: () {}
  table key_digest_outputs: [Field; 32] {}
  map key_digest_bytes() -> [Field; 32] = key_digest_inputs => key_digest_outputs;

  fn key_stream(index: Field, remaining: Field) -> Bytes::Stream {
    match remaining {
      0 => &(Lists::Node::Nil),
      _ => {
        let w = key_word(index);
        let (b0, b1) = UInt8::from_fields(w[0], w[1]);
        let (b2, b3) = UInt8::from_fields(w[2], w[3]);
        let tail = key_stream(index + 1, remaining - 1);
        &(Lists::Node::Cons(b0, &(Lists::Node::Cons(b1,
          &(Lists::Node::Cons(b2, &(Lists::Node::Cons(b3, tail))))))))
      },
    }
  }

  fn skip_bytes(stream: Bytes::Stream, count: Field) -> Bytes::Stream {
    match count {
      0 => stream,
      _ => {
        let Lists::Node::Cons(_byte, rest) = *stream;
        skip_bytes(rest, count - 1)
      },
    }
  }

  inline fn key_digest() -> [UInt32::U32; 8] {
    let d = key_digest_bytes();
    [UInt32::from_fields([d[0], d[1], d[2], d[3]]), UInt32::from_fields([d[4], d[5], d[6], d[7]]),
     UInt32::from_fields([d[8], d[9], d[10], d[11]]), UInt32::from_fields([d[12], d[13], d[14], d[15]]),
     UInt32::from_fields([d[16], d[17], d[18], d[19]]), UInt32::from_fields([d[20], d[21], d[22], d[23]]),
     UInt32::from_fields([d[24], d[25], d[26], d[27]]), UInt32::from_fields([d[28], d[29], d[30], d[31]])]
  }

  fn verify_root(reserved: [Field; 8], statement_digest: [Field; 8]) -> () {
      assert_eq!(reserved, [0; 8], "compression wrapper reserved words must be zero");
      let (cidx, clen) = hint::<(Field, Field)>("stark.io.info", (2, 0));
      let claims_bytes = StarkIO::read_byte_stream(2, cidx, clen);
      let claims_digest = Blake3::hash(claims_bytes);
      let bytes = CompressWrap::statement_bytes(key_digest(), claims_digest);
      assert_eq!(Blake3::pack_digest(Blake3::hash(bytes)), statement_digest,
        "compression wrapper statement digest mismatch");
      let (sys, srest) = SystemDeserialize::read_system(skip_bytes(key_stream(0, KEY_WORDS), KEY_OFFSET));
      let Lists::Node::Nil = (*(srest));
      let (claims, crest) = StarkVerifier::read_claims(claims_bytes);
      let Lists::Node::Nil = (*(crest));
      let (idx, len) = hint::<(Field, Field)>("stark.io.info", (0, 0));
      assert_eq!(StarkVerifier::verify_batch_at(sys, idx, len, claims), 1);
      ()
    }
}
⟧

def entry : String := MultiStark.CompressGL.entry

#aiur_check MultiStark.CompressGL.libraries.append MultiStark.compressWrapSource |>.append template

/-- The template with `key`'s words, offset and digest. Leading zero bytes,
skipped by `KEY_OFFSET`, make whole words. -/
def source (key : ByteArray) : Modules.Program Nat :=
  let pad := (4 - key.size % 4) % 4
  let padded := (ByteArray.mk (Array.replicate pad 0)).append key
  let words := padded.size / 4
  let literal (n : Nat) : Generic.Expr Nat := .literal n
  let row (values : List Nat) : Generic.Expr Nat := .array (values.map literal)
  let digest := (Blake3.Rust.hash key).val
  let tables : List (Generic.Table Nat) := [
    ⟨"key_inputs", .tuple [.field], (List.range words).map fun i => .tuple [literal i]⟩,
    ⟨"key_values", .array .field 4, (List.range words).map fun i =>
      row ((List.range 4).map fun j => (padded.get! (4 * i + j)).toNat)⟩,
    ⟨"key_digest_inputs", .tuple [], [.tuple []]⟩,
    ⟨"key_digest_outputs", .array .field 32, [row (digest.data.toList.map (·.toNat))]⟩]
  let consts := [("KEY_WORDS", words), ("KEY_OFFSET", pad)]
  { template with modules := template.modules.map fun m =>
    { m with body := match m.body with
      | .definitions d => .definitions { d with program := { d.program with
          tables := tables
          consts := d.program.consts.map fun c =>
            match consts.find? (·.1 == c.name) with
            | some (_, v) => ⟨c.name, .literal v⟩
            | none => c } }
      | body => body } }

/-- `MultiStark.CompressGL.program` with this module in place of the alias of
`CompressWrap`. -/
def program (key : ByteArray) : Modules.Program MultiStark.CompressGL.F :=
  Library.Blake3.BN254.program.append (Library.Option.declarations.toField MultiStark.CompressGL.F)
    |>.append Library.Field.Goldilocks.Emulated.program
    |>.append ((MultiStark.compressWrapSource.append (source key)).toField MultiStark.CompressGL.F)

/-- `MultiStark.CompressGL.compilePackage` of `program key`. -/
def compilePackage (key : ByteArray) (trace : Bool := true)
    (groups : List (String × List String) := MultiStark.functionGroups) : IO ByteArray := do
  let prepared ← IO.ofExcept (Modules.prepare (program key) [entry])
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, circuits) ← if trace then do
      let (exported, circuits) ← Trace.exportPlanParallelWide MultiStark.CompressGL.modulus ZMod.val
        prepared.environment.source prepared.entries exported groups
      pure (exported, some circuits)
    else pure (exported, none)
  IO.ofExcept (Artifact.packageWide exported MultiStark.CompressGL.modulus ZMod.val circuits)

end MultiStark.CompressGLFixed
