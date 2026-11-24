import Aiur.Modules.Frontend

/-! # MultiStark module `StarkHash`

BLAKE3 hashing of rows and digests, including Protocol `v6` BLAKE3 `derive_key`
domain-separated hashing (`V6_MERKLE_LEAF`, `V6_MERKLE_COMPRESS`, `V6_TRANSCRIPT_BATCH`).

Formal Aiur source, written as Lean syntax (`aiur⟦ … ⟧`). `MultiStark.recursionSource`
and `MultiStark.aggregateSource` (`MultiStark/MultiStark/Program.lean`) compose the modules. -/

namespace MultiStark.Source

def starkHash : Aiur.Modules.Program Nat := aiur⟦
module StarkHash {
  -- Precomputed BLAKE3 `derive_key` context CV for `"multi-stark/v6/merkle/leaf"`.
  inline fn v6_merkle_leaf_cv() -> [UInt32::U32; 8] {
      [UInt32::from_bytes([UInt8::BYTE_25, UInt8::BYTE_40, UInt8::BYTE_4, UInt8::BYTE_119]),
       UInt32::from_bytes([UInt8::BYTE_79, UInt8::BYTE_208, UInt8::BYTE_29, UInt8::BYTE_90]),
       UInt32::from_bytes([UInt8::BYTE_184, UInt8::BYTE_11, UInt8::BYTE_141, UInt8::BYTE_47]),
       UInt32::from_bytes([UInt8::BYTE_50, UInt8::BYTE_120, UInt8::BYTE_210, UInt8::BYTE_57]),
       UInt32::from_bytes([UInt8::BYTE_246, UInt8::BYTE_48, UInt8::BYTE_42, UInt8::BYTE_85]),
       UInt32::from_bytes([UInt8::BYTE_153, UInt8::BYTE_152, UInt8::BYTE_108, UInt8::BYTE_84]),
       UInt32::from_bytes([UInt8::BYTE_239, UInt8::BYTE_168, UInt8::BYTE_16, UInt8::BYTE_133]),
       UInt32::from_bytes([UInt8::BYTE_102, UInt8::BYTE_205, UInt8::BYTE_236, UInt8::BYTE_131])]
    }

  -- Precomputed BLAKE3 `derive_key` context CV for `"multi-stark/v6/merkle/compress"`.
  inline fn v6_merkle_compress_cv() -> [UInt32::U32; 8] {
      [UInt32::from_bytes([UInt8::BYTE_51, UInt8::BYTE_118, UInt8::BYTE_77, UInt8::BYTE_204]),
       UInt32::from_bytes([UInt8::BYTE_236, UInt8::BYTE_47, UInt8::BYTE_73, UInt8::BYTE_248]),
       UInt32::from_bytes([UInt8::BYTE_253, UInt8::BYTE_177, UInt8::BYTE_4, UInt8::BYTE_87]),
       UInt32::from_bytes([UInt8::BYTE_181, UInt8::BYTE_166, UInt8::BYTE_105, UInt8::BYTE_45]),
       UInt32::from_bytes([UInt8::BYTE_181, UInt8::BYTE_235, UInt8::BYTE_113, UInt8::BYTE_168]),
       UInt32::from_bytes([UInt8::BYTE_13, UInt8::BYTE_97, UInt8::BYTE_57, UInt8::BYTE_100]),
       UInt32::from_bytes([UInt8::BYTE_230, UInt8::BYTE_107, UInt8::BYTE_232, UInt8::BYTE_137]),
       UInt32::from_bytes([UInt8::BYTE_52, UInt8::BYTE_42, UInt8::BYTE_226, UInt8::BYTE_2])]
    }

  -- Precomputed BLAKE3 `derive_key` context CV for `"multi-stark/v6/transcript/batch"`.
  inline fn v6_transcript_batch_cv() -> [UInt32::U32; 8] {
      [UInt32::from_bytes([UInt8::BYTE_72, UInt8::BYTE_85, UInt8::BYTE_148, UInt8::BYTE_86]),
       UInt32::from_bytes([UInt8::BYTE_194, UInt8::BYTE_178, UInt8::BYTE_174, UInt8::BYTE_11]),
       UInt32::from_bytes([UInt8::BYTE_221, UInt8::BYTE_40, UInt8::BYTE_188, UInt8::BYTE_176]),
       UInt32::from_bytes([UInt8::BYTE_153, UInt8::BYTE_38, UInt8::BYTE_190, UInt8::BYTE_158]),
       UInt32::from_bytes([UInt8::BYTE_130, UInt8::BYTE_79, UInt8::BYTE_178, UInt8::BYTE_215]),
       UInt32::from_bytes([UInt8::BYTE_77, UInt8::BYTE_15, UInt8::BYTE_71, UInt8::BYTE_53]),
       UInt32::from_bytes([UInt8::BYTE_211, UInt8::BYTE_24, UInt8::BYTE_95, UInt8::BYTE_6]),
       UInt32::from_bytes([UInt8::BYTE_79, UInt8::BYTE_153, UInt8::BYTE_178, UInt8::BYTE_243])]
    }

  fn b3_w4_onto(w: UInt32::U32, tail: Bytes::Stream) -> Bytes::Stream {
      let w = UInt32::to_bytes(w);
      (&(Lists::Node::Cons(w[0], (&(Lists::Node::Cons(w[1], (&(Lists::Node::Cons(w[2],
      (&(Lists::Node::Cons(w[3], tail))))))))))))
    }

  inline fn b3_flatten_onto(h: [UInt32::U32; 8], tail: Bytes::Stream) -> Bytes::Stream {
      b3_w4_onto(h[0], b3_w4_onto(h[1], b3_w4_onto(h[2], b3_w4_onto(h[3],
      b3_w4_onto(h[4], b3_w4_onto(h[5], b3_w4_onto(h[6], b3_w4_onto(h[7], tail))))))))
    }

  inline fn b3_to_digest(h: [UInt32::U32; 8]) -> ProofDeserialize::Digest {
      let h = [UInt32::to_bytes(h[0]), UInt32::to_bytes(h[1]), UInt32::to_bytes(h[2]), UInt32::to_bytes(h[3]), UInt32::to_bytes(h[4]), UInt32::to_bytes(h[5]), UInt32::to_bytes(h[6]), UInt32::to_bytes(h[7])];
      [[h[0][0], h[0][1], h[0][2], h[0][3], h[1][0], h[1][1], h[1][2], h[1][3]],
       [h[2][0], h[2][1], h[2][2], h[2][3], h[3][0], h[3][1], h[3][2], h[3][3]],
       [h[4][0], h[4][1], h[4][2], h[4][3], h[5][0], h[5][1], h[5][2], h[5][3]],
       [h[6][0], h[6][1], h[6][2], h[6][3], h[7][0], h[7][1], h[7][2], h[7][3]]]
    }

  fn digest_eq(ap: ProofDeserialize::DigestP, bp: ProofDeserialize::DigestP) -> Field {
      let a = (*(ap));
      let b = (*(bp));
      UInt64::eq(a[0], b[0]) * UInt64::eq(a[1], b[1]) *
      UInt64::eq(a[2], b[2]) * UInt64::eq(a[3], b[3])
  }

  fn b3_dk_next_layer(key_cv: &[UInt32::U32; 8], layer: Blake3::Layer, digest: [UInt32::U32; 8], root: Field) -> (Blake3::MaybeDigest, Blake3::Layer) {
      match (*(layer)) {
        Blake3::LayerNode::Nil => { (Blake3::MaybeDigest::Some(digest), layer) } ,
        Blake3::LayerNode::Push(layer, other) => {
          let (last, new_layer) = b3_dk_next_layer(key_cv, layer, other, 0);
          match last {
            Blake3::MaybeDigest::None => { (Blake3::MaybeDigest::Some(digest), new_layer) } ,
            Blake3::MaybeDigest::Some(last) => {
              let [x0, x1, x2, x3, x4, x5, x6, x7] = last;
              let [x8, x9, x10, x11, x12, x13, x14, x15] = digest;
              let blocks = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15];
              match (*(new_layer)) {
                Blake3::LayerNode::Nil => {
                  let flags = 68 + 8 * root;
                  let digest = Blake3::compress_init((*(key_cv)), blocks, [UInt8::BYTE_0; 8], 64, flags);
                  (Blake3::MaybeDigest::None, (&(Blake3::LayerNode::Push(new_layer, digest)))) } ,
                _ => {
                  let digest = Blake3::compress_init((*(key_cv)), blocks, [UInt8::BYTE_0; 8], 64, 68);
                  (Blake3::MaybeDigest::None, (&(Blake3::LayerNode::Push(new_layer, digest)))) } ,
              } } ,
          } } ,
      }
    }

  fn b3_dk_compress_layer(key_cv: &[UInt32::U32; 8], layer: Blake3::Layer) -> [UInt32::U32; 8] {
      let Blake3::LayerNode::Push(rest, digest) = (*(layer));
      match (*(rest)) {
        Blake3::LayerNode::Nil => { digest } ,
        _ => {
          let (last, new_merkle) = b3_dk_next_layer(key_cv, rest, digest, 1);
          match last {
            Blake3::MaybeDigest::None => { b3_dk_compress_layer(key_cv, new_merkle) } ,
            Blake3::MaybeDigest::Some(last) => { b3_dk_compress_layer(key_cv, (&(Blake3::LayerNode::Push(new_merkle, last)))) } ,
          } } ,
      }
    }

  fn b3_dk_finish(
      byte_acc: Bytes::Stream,
      block_index: Field,
      chunk_index: Field,
      chunk_count: &UInt64::U64,
      block_digest: &[UInt32::U32; 8],
      layer: Blake3::Layer
  ) -> Blake3::Layer {
      match (block_index, chunk_index) {
        (0, 0) => {
          match (*(chunk_count)) {
            [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0] => {
              (&(Blake3::LayerNode::Push(layer, Blake3::compress_init((*(block_digest)), [UInt32::ZERO; 16], (*(chunk_count)), 0, 75)))) } ,
            _ => { layer } ,
          } } ,
        (0, _) => { (&(Blake3::LayerNode::Push(layer, (*(block_digest))))) } ,
        (_, _) => {
          let flags = 66 + UInt64::is_zero((*(chunk_count))) * 8 + Fields::is_zero(chunk_index - block_index);
          let block = Blake3::bytes_to_block(Blake3::pad_block(byte_acc, 64 - block_index));
          (&(Blake3::LayerNode::Push(layer, Blake3::compress_init((*(block_digest)), block, (*(chunk_count)), block_index, flags)))) } ,
      }
    }

  fn b3_dk_compress_chunks(
      input: Bytes::Stream,
      byte_acc: Bytes::Stream,
      block_index: Field,
      chunk_index: Field,
      chunk_count: &UInt64::U64,
      block_digest: &[UInt32::U32; 8],
      layer: Blake3::Layer
  ) -> Blake3::Layer {
      match (*(input)) {
        Lists::Node::Nil => {
          b3_dk_finish(byte_acc, block_index, chunk_index, chunk_count, block_digest, layer) } ,
        Lists::Node::Cons(head, rest) => {
          b3_dk_compress_chunks(rest, (&(Lists::Node::Cons(head, byte_acc))), block_index + 1, chunk_index + 1, chunk_count, block_digest, layer) } ,
      }
    }

  fn b3_dk_hash_blocks(key_cv: &[UInt32::U32; 8], input: Bytes::Stream, block_no: Field, chunk_count: &UInt64::U64, cv: &[UInt32::U32; 8], layer: Blake3::Layer) -> Blake3::Layer {
      match Blake3::take_block(input) {
        Blake3::BlockRead::Short => {
          b3_dk_compress_chunks(input, (&(Lists::Node::Nil)), 0, 64 * block_no, chunk_count, cv, layer) } ,
        Blake3::BlockRead::Full(block, rest) => {
          let empty = match (*(rest)) { Lists::Node::Nil => { 1 } , _ => { 0 } , };
          let at15 = Fields::is_zero(block_no - 15);
          let start_flag = Fields::is_zero(block_no);
          let end_flag = empty + at15 - empty * at15;
          let root_flag = empty * UInt64::is_zero((*(chunk_count)));
          let flags = 64 + start_flag + 2 * end_flag + 8 * root_flag;
          let digest = Blake3::compress_init((*(cv)), block, (*(chunk_count)), 64, flags);
          match (empty, at15) {
            (1, _) => { (&(Blake3::LayerNode::Push(layer, digest))) } ,
            (_, 1) => {
              b3_dk_hash_blocks(key_cv, rest, 0, (&(UInt64::wrapping_succ((*(chunk_count))))), key_cv, (&(Blake3::LayerNode::Push(layer, digest)))) } ,
            (_, _) => { b3_dk_hash_blocks(key_cv, rest, block_no + 1, chunk_count, (&(digest)), layer) } ,
          } } ,
      }
    }

  inline fn b3_dk_hash(key_cv: &[UInt32::U32; 8], input: Bytes::Stream) -> [UInt32::U32; 8] {
      b3_dk_compress_layer(key_cv, b3_dk_hash_blocks(key_cv, input, 0, (&([UInt8::BYTE_0; 8])), key_cv, (&(Blake3::LayerNode::Nil))))
    }

  fn b3_rows_chunks(cur: Lists::List<UInt64::U64>, rows: Lists::List<Lists::List<UInt64::U64>>, block_no: Field, chunk_count: &UInt64::U64, cv: &[UInt32::U32; 8], layer: Blake3::Layer) -> Blake3::Layer {
      let (l0, c1, r1, g0) = Pcs::rows_pop(cur, rows);
      match g0 {

        0 => {
          match UInt64::is_zero((*(chunk_count))) { 1 => {
              (&(Blake3::LayerNode::Push(layer, Blake3::compress_init((*(cv)), [UInt32::ZERO; 16], (*(chunk_count)), 0, 75)))) } ,
            _ => {  layer } ,
          } } ,
        _ => {
          let (l1, c2, r2, g1) = Pcs::rows_pop(c1, r1);
          let (l2, c3, r3, g2) = Pcs::rows_pop(c2, r2);
          let (l3, c4, r4, g3) = Pcs::rows_pop(c3, r3);
          let (l4, c5, r5, g4) = Pcs::rows_pop(c4, r4);
          let (l5, c6, r6, g5) = Pcs::rows_pop(c5, r5);
          let (l6, c7, r7, g6) = Pcs::rows_pop(c6, r6);
          let (l7, c8, r8, g7) = Pcs::rows_pop(c7, r7);
          let nbytes = 8 * (g0 + g1 + g2 + g3 + g4 + g5 + g6 + g7);
          let block = [
            UInt32::from_bytes([l0[0], l0[1], l0[2], l0[3]]), UInt32::from_bytes([l0[4], l0[5], l0[6], l0[7]]),
            UInt32::from_bytes([l1[0], l1[1], l1[2], l1[3]]), UInt32::from_bytes([l1[4], l1[5], l1[6], l1[7]]),
            UInt32::from_bytes([l2[0], l2[1], l2[2], l2[3]]), UInt32::from_bytes([l2[4], l2[5], l2[6], l2[7]]),
            UInt32::from_bytes([l3[0], l3[1], l3[2], l3[3]]), UInt32::from_bytes([l3[4], l3[5], l3[6], l3[7]]),
            UInt32::from_bytes([l4[0], l4[1], l4[2], l4[3]]), UInt32::from_bytes([l4[4], l4[5], l4[6], l4[7]]),
            UInt32::from_bytes([l5[0], l5[1], l5[2], l5[3]]), UInt32::from_bytes([l5[4], l5[5], l5[6], l5[7]]),
            UInt32::from_bytes([l6[0], l6[1], l6[2], l6[3]]), UInt32::from_bytes([l6[4], l6[5], l6[6], l6[7]]),
            UInt32::from_bytes([l7[0], l7[1], l7[2], l7[3]]), UInt32::from_bytes([l7[4], l7[5], l7[6], l7[7]])];
          let empty = match (*(c8)) {
            Lists::Node::Nil => {  match (*(r8)) { Lists::Node::Nil => {  1 } , _ => {  0 } , } } ,
            _ => {  0 } ,
          };
          let at15 = Fields::is_zero(block_no - 15);
          let start_flag = Fields::is_zero(block_no);
          let end_flag = empty + at15 - (empty * at15);
          let root_flag = empty * UInt64::is_zero((*(chunk_count)));
          let flags = 64 + start_flag + 2 * end_flag + 8 * root_flag;
          let digest = Blake3::compress_init((*(cv)), block, (*(chunk_count)), nbytes, flags);
          match (empty, at15) {
            (1, _) => {  (&(Blake3::LayerNode::Push(layer, digest))) } ,
            (_, 1) => {
              let leaf_cv = v6_merkle_leaf_cv();
              b3_rows_chunks(c8, r8, 0, (&(UInt64::wrapping_succ((*(chunk_count))))), (&(leaf_cv)), (&(Blake3::LayerNode::Push(layer, digest)))) } ,
            (_, _) => {  b3_rows_chunks(c8, r8, block_no + 1, chunk_count, (&(digest)), layer) } ,
          } } ,
      }
    }

  inline fn b3_rows(rows: Lists::List<Lists::List<UInt64::U64>>) -> [UInt32::U32; 8] {
      let leaf_cv = v6_merkle_leaf_cv();
      let leaf_cv_ref = (&(leaf_cv));
      b3_dk_compress_layer(leaf_cv_ref, b3_rows_chunks((&(Lists::Node::Nil)), rows, 0, (&([UInt8::BYTE_0; 8])), leaf_cv_ref, (&(Blake3::LayerNode::Nil))))
    }
}
⟧

end MultiStark.Source
