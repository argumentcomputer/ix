import Aiur.Modules.Frontend

/-! # MultiStark module `AiurExec`, aggregation of chained Aiur executions

The entry point `AiurExec::aiur_exec` aggregates proofs of one Aiur program's
entry, each of the form `entry(m, d) = m'`, into a claim that a chain of `n` such
executions takes `m₀` to `mₙ` over the data `d₁ … dₙ`. The program is fixed by
its verifying key, supplied as data and bound by its BLAKE3 digest in the
identity blob; nothing about it is built into this module, so another program
changes neither this module nor `MultiStark::ix_aggr`.

Identity blob (80 bytes, channel 3), laid out as `Aggr.allowedBlob`:
`program key digest ‖ program entry index (u64) ‖ own key digest ‖ own entry
index (u64)`.

Output claim (104 bytes): `n (u64) ‖ H(m₀) ‖ H(mₙ) ‖ data root`, where `H` is
BLAKE3 over the canonical little-endian field words, a leaf's data root is
`H(d)` and a join's is `aggr_node_hash(left, right)`. Leaf and node preimages
have different lengths (`8·dataWords` and 65 bytes), so they never collide.

An entry claim is `[1, entry index, m (modelWords), d (dataWords), m' (modelWords)]`;
the word counts are this module's parameters, here `Fixed::train_block`'s: 331
model words and 7,601 data words (the learning rate, then 20 batches' inputs of
20 × 8, then their targets of 20 × 11). `aiurExec` is the same module for
`Fixed::step`; only these counts differ.

Shapes (channel 6): 0 a leaf over one program proof; 1 a join of two
aggregate proofs whose chains meet (`H(mₙ)` of the left is `H(m₀)` of the
right); 2 a wrap of one aggregate proof, passing its claim through. -/

namespace MultiStark.Source

def aiurExecBlock : Aiur.Modules.Program Nat := aiur⟦
module AiurExec {
  fn ax_parse(bytes: Bytes::Stream)
        -> (Field, Bytes::AddressRef, Bytes::AddressRef, Bytes::AddressRef) {
      let (count, s) = ProofDeserialize::read_u64(bytes);
      let (first, s) = Aggregation::aggr_read_address(s);
      let (last, s) = Aggregation::aggr_read_address(s);
      let (data, s) = Aggregation::aggr_read_address(s);
      let Lists::Node::Nil = (*(s));
      (UInt64::to_field(count), first, last, data)
    }

  fn ax_output(out_claim_digest: [Field; 8])
        -> (Field, Bytes::AddressRef, Bytes::AddressRef, Bytes::AddressRef) {
      let (oidx, olen) = hint::<(Field, Field)>("stark.io.info", (2, 2));
      assert_eq!(olen, 104, "aiur_exec: output claim must be 104 bytes");
      let bytes = StarkIO::read_byte_stream(2, oidx, olen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(bytes)), out_claim_digest,
        "aiur_exec: output claim digest mismatch");
      ax_parse(bytes)
    }

  fn ax_load_key(kind: Field, digest: [Field; 8]) -> SystemDeserialize::Sys {
      let (sidx, slen) = hint::<(Field, Field)>("stark.io.info", (1, kind));
      let sbytes = StarkIO::read_byte_stream(1, sidx, slen);
      Aggregation::aggr_assert_digest(Blake3::pack_digest(Blake3::hash(sbytes)), digest);
      let (sys, srest) = SystemDeserialize::read_system(sbytes);
      let Lists::Node::Nil = (*(srest));
      sys
    }

  fn ax_child(sys: SystemDeserialize::Sys, slot: Field)
        -> (Lists::List<UInt64::U64>, Bytes::Stream) {
      let (idx, len) = hint::<(Field, Field)>("stark.io.info", (0, slot));
      let (cidx, clen) = hint::<(Field, Field)>("stark.io.info", (2, slot));
      let cbytes = StarkIO::read_byte_stream(2, cidx, clen);
      let (claims, crest) = StarkVerifier::read_claims(cbytes);
      let Lists::Node::Nil = (*(crest));
      assert_eq!(StarkVerifier::verify_batch_at(sys, idx, len, claims), 1);
      (Aggregation::aggr_only_claim(claims), cbytes)
    }

  fn ax_aggregate_child(sys: SystemDeserialize::Sys, slot: Field, self_idx: Field,
        allowed_digest: [Field; 8]) -> [Field; 8] {
      let (claim, _bytes) = ax_child(sys, slot);
      assert_eq!(Lists::length(claim), 18,
        "aiur_exec: an aggregate child exposes an 18-word claim");
      assert_eq!(Aggregation::aggr_claim_field(claim, 0), 1,
        "aiur_exec: child has the wrong claim channel");
      assert_eq!(Aggregation::aggr_claim_field(claim, 1), self_idx,
        "aiur_exec: aggregate child has the wrong entrypoint");
      Aggregation::aggr_assert_digest(Aggregation::aggr_claim_digest(claim, 2), allowed_digest);
      Aggregation::aggr_claim_digest(claim, 10)
    }

  fn ax_leaf(program_digest: [Field; 8], program_idx: Field,
        out_claim_digest: [Field; 8]) -> () {
      let sys = ax_load_key(0, program_digest);
      let (claim, cbytes) = ax_child(sys, 0);
      assert_eq!(Lists::length(claim), 8265,
        "aiur_exec: a program claim has 8265 words");
      assert_eq!(Aggregation::aggr_claim_field(claim, 0), 1,
        "aiur_exec: program claim has the wrong claim channel");
      assert_eq!(Aggregation::aggr_claim_field(claim, 1), program_idx,
        "aiur_exec: program claim has the wrong entrypoint");
      let words = Lists::drop(cbytes, 32);
      let first = Blake3::bytes_to_addr(Lists::take(words, 2648));
      let rest = Lists::drop(words, 2648);
      let data = Blake3::bytes_to_addr(Lists::take(rest, 60808));
      let rest = Lists::drop(rest, 60808);
      let last = Blake3::bytes_to_addr(Lists::take(rest, 2648));
      let Lists::Node::Nil = (*(Lists::drop(rest, 2648)));
      let (count, ofirst, olast, odata) = ax_output(out_claim_digest);
      assert_eq!(count, 1, "aiur_exec: a leaf covers one execution");
      assert_eq!(Bytes::address_eq(ofirst, first), 1, "aiur_exec: leaf input digest");
      assert_eq!(Bytes::address_eq(olast, last), 1, "aiur_exec: leaf output digest");
      assert_eq!(Bytes::address_eq(odata, data), 1, "aiur_exec: leaf data digest");
      ()
    }

  fn ax_join(self_digest: [Field; 8], self_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let sys = ax_load_key(1, self_digest);
      let left_digest = ax_aggregate_child(sys, 0, self_idx, allowed_digest);
      let right_digest = ax_aggregate_child(sys, 1, self_idx, allowed_digest);
      let (lcount, lfirst, llast, ldata) = ax_parse(Aggregation::aggr_load_preimage(left_digest));
      let (rcount, rfirst, rlast, rdata) = ax_parse(Aggregation::aggr_load_preimage(right_digest));
      let (count, first, last, data) = ax_output(out_claim_digest);
      assert_eq!(Bytes::address_eq(llast, rfirst), 1,
        "aiur_exec: the left chain does not end where the right one starts");
      assert_eq!(count, lcount + rcount, "aiur_exec: join count");
      assert_eq!(Bytes::address_eq(first, lfirst), 1, "aiur_exec: join input digest");
      assert_eq!(Bytes::address_eq(last, rlast), 1, "aiur_exec: join output digest");
      assert_eq!(Bytes::address_eq(data, Aggregation::aggr_node_hash(ldata, rdata)), 1,
        "aiur_exec: join data root");
      ()
    }

  fn ax_wrap(self_digest: [Field; 8], self_idx: Field, allowed_digest: [Field; 8],
        out_claim_digest: [Field; 8]) -> () {
      let sys = ax_load_key(1, self_digest);
      let child = ax_aggregate_child(sys, 0, self_idx, allowed_digest);
      Aggregation::aggr_assert_digest(child, out_claim_digest)
    }

  fn aiur_exec(allowed_digest: [Field; 8], out_claim_digest: [Field; 8]) -> () {
      let (aidx, alen) = hint::<(Field, Field)>("stark.io.info", (3, 0));
      assert_eq!(alen, 80, "aiur_exec: identity blob must be exactly 80 bytes");
      let allowed_bytes = StarkIO::read_byte_stream(3, aidx, alen);
      assert_eq!(Blake3::pack_digest(Blake3::hash(allowed_bytes)), allowed_digest,
        "aiur_exec: identity blob digest mismatch");
      let (program_addr, as1) = Aggregation::aggr_read_address(allowed_bytes);
      let (program_idx_limb, as2) = ProofDeserialize::read_u64(as1);
      let (self_addr, as3) = Aggregation::aggr_read_address(as2);
      let (self_idx_limb, astop) = ProofDeserialize::read_u64(as3);
      let Lists::Node::Nil = (*(astop));
      let program_digest = Aggregation::aggr_pack_address(program_addr);
      let self_digest = Aggregation::aggr_pack_address(self_addr);
      let program_idx = UInt64::to_field(program_idx_limb);
      let self_idx = UInt64::to_field(self_idx_limb);
      let (hidx, hlen) = hint::<(Field, Field)>("stark.io.info", (6, 0));
      assert_eq!(hlen, 1, "aiur_exec: shape hint must be exactly one byte");
      let hint = StarkIO::read_byte_stream(6, hidx, hlen);
      let (shape, hstop) = Aggregation::aggr_read_byte(hint);
      let Lists::Node::Nil = (*(hstop));
      match UInt8::to_field(shape) {
        0 => { ax_leaf(program_digest, program_idx, out_claim_digest) } ,
        1 => { ax_join(self_digest, self_idx, allowed_digest, out_claim_digest) } ,
        2 => { ax_wrap(self_digest, self_idx, allowed_digest, out_claim_digest) } ,
      }
    }
}
⟧

end MultiStark.Source
