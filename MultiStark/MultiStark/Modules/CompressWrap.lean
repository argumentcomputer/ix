import Aiur.Modules.Frontend

/-! A stable compression entry point for arbitrary authenticated root systems.
The public digest commits to a domain-separated pair of key and claims digests;
the reserved public words keep its statement prefix independent of either. -/

namespace MultiStark.Source

def compressWrap : Aiur.Modules.Program Nat := aiur⟦
module CompressWrap {
  inline fn statement_bytes(key_digest: [UInt32::U32; 8], claims_digest: [UInt32::U32; 8]) -> Bytes::Stream {
      let tail = StarkHash::b3_flatten_onto(key_digest,
        StarkHash::b3_flatten_onto(claims_digest, (&(Lists::Node::Nil))));
      StarkVerifier::b8_onto(
        [UInt8::BYTE_105, UInt8::BYTE_120, UInt8::BYTE_47, UInt8::BYTE_99,
         UInt8::BYTE_111, UInt8::BYTE_109, UInt8::BYTE_112, UInt8::BYTE_114],
        StarkVerifier::b8_onto(
          [UInt8::BYTE_101, UInt8::BYTE_115, UInt8::BYTE_115, UInt8::BYTE_45,
           UInt8::BYTE_119, UInt8::BYTE_114, UInt8::BYTE_97, UInt8::BYTE_112],
          StarkHash::b3_w4_onto(UInt32::from_bytes(
            [UInt8::BYTE_47, UInt8::BYTE_118, UInt8::BYTE_49, UInt8::BYTE_0]), tail)))
    }

  fn verify_root(reserved: [Field; 8], statement_digest: [Field; 8]) -> () {
      assert_eq!(reserved, [0; 8], "compression wrapper reserved words must be zero");
      let (sidx, slen) = hint::<(Field, Field)>("stark.io.info", (1, 0));
      let system_bytes = StarkIO::read_byte_stream(1, sidx, slen);
      let (cidx, clen) = hint::<(Field, Field)>("stark.io.info", (2, 0));
      let claims_bytes = StarkIO::read_byte_stream(2, cidx, clen);
      let key_digest = Blake3::hash(system_bytes);
      let claims_digest = Blake3::hash(claims_bytes);
      let bytes = statement_bytes(key_digest, claims_digest);
      assert_eq!(Blake3::pack_digest(Blake3::hash(bytes)), statement_digest,
        "compression wrapper statement digest mismatch");
      MultiStark::verify_multi_stark_proof(
        Blake3::pack_digest(key_digest), Blake3::pack_digest(claims_digest));
      ()
    }
}
⟧

end MultiStark.Source
