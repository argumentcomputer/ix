import Aiur.Library.U32
import Aiur.Library.U64
import Aiur.Library.List
import Aiur.Library.Field

/-! Shared Blake3 implementation, extracted from the audited IxVM port.
Inputs are finite lists of checked bytes. Ingress must establish finiteness for
untrusted memory; internally constructed lists preserve it. -/
namespace Aiur.Library.Blake3
open Aiur

def dependencies : Modules.Program Nat :=
  U32.templates.append U64.declarations |>.append List.declarations |>.append Field.declarations

def declarations : Modules.Program Nat := aiur_library% dependencies r#"
module Blake3 {
  type U8 = UInt8::U8;
  type U32 = UInt32::U32;
  type U64 = UInt64::U64;
  type ByteStream = Lists::List<U8>;
  type Digest = [U32; 8];
  enum LayerNode { Push(Layer, Digest), Nil }
  type Layer = &LayerNode;
  enum MaybeDigest { None, Some(Digest) }
  inline fn iv() -> [U32; 8] {
    [
      UInt32::from_bytes([UInt8::BYTE_103, UInt8::BYTE_230, UInt8::BYTE_9, UInt8::BYTE_106]),
      UInt32::from_bytes([UInt8::BYTE_133, UInt8::BYTE_174, UInt8::BYTE_103, UInt8::BYTE_187]),
      UInt32::from_bytes([UInt8::BYTE_114, UInt8::BYTE_243, UInt8::BYTE_110, UInt8::BYTE_60]),
      UInt32::from_bytes([UInt8::BYTE_58, UInt8::BYTE_245, UInt8::BYTE_79, UInt8::BYTE_165]),
      UInt32::from_bytes([UInt8::BYTE_127, UInt8::BYTE_82, UInt8::BYTE_14, UInt8::BYTE_81]),
      UInt32::from_bytes([UInt8::BYTE_140, UInt8::BYTE_104, UInt8::BYTE_5, UInt8::BYTE_155]),
      UInt32::from_bytes([UInt8::BYTE_171, UInt8::BYTE_217, UInt8::BYTE_131, UInt8::BYTE_31]),
      UInt32::from_bytes([UInt8::BYTE_25, UInt8::BYTE_205, UInt8::BYTE_224, UInt8::BYTE_91])
    ]
  }

  inline fn hash(input: ByteStream) -> [U32; 8] {
    let IV = iv();
    compress_layer(compress_chunks(input, &(Lists::Node::Nil), 0, 0, &([UInt8::BYTE_0; 8]), &(IV), &(LayerNode::Nil)))
  }

  fn verify_bytes_against(bytes: ByteStream, expected: [U8; 32]) -> () {
    let h = hash(bytes);
    assert_eq!(address_to_fields(
      digest_bytes(h)),
      address_to_fields(expected),
      "hash of the supplied bytes != the address they were fetched under");
  }

  fn bytes_to_addr(bytes: ByteStream) -> &[U8; 32] {
    let h = hash(bytes);
    &(digest_bytes(h))
  }

  fn next_layer(layer: Layer, digest: [U32; 8], root: Field) -> (MaybeDigest, Layer) {
    match *(layer) {
      LayerNode::Nil => { (MaybeDigest::Some(digest), layer) },
      LayerNode::Push(layer, other) => {
        let (last, new_layer) = next_layer(layer, other, 0);
        match last {
          MaybeDigest::None => { (MaybeDigest::Some(digest), new_layer) },
          MaybeDigest::Some(last) => {
            let PARENT = 4;
            let ROOT = 8;
            let IV = iv();
            let [x0, x1, x2, x3, x4, x5, x6, x7] = last;
            let [x8, x9, x10, x11, x12, x13, x14, x15] = digest;
            let blocks = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15];
            match *(new_layer) {
              LayerNode::Nil => {
                let flags = PARENT + ROOT * root;
                let digest = compress_init(IV, blocks, [UInt8::BYTE_0; 8], 64, flags);
                (MaybeDigest::None, &(LayerNode::Push(new_layer, digest))) },
              _ => {
                let flags = PARENT;
                let digest = compress_init(IV, blocks, [UInt8::BYTE_0; 8], 64, flags);
                (MaybeDigest::None, &(LayerNode::Push(new_layer, digest))) },
            } },
        } },
    }
  }

  fn compress_layer(layer: Layer) -> [U32; 8] {
    let LayerNode::Push(rest, digest) = *(layer);
    match *(rest) {
      LayerNode::Nil => { digest },
      _ => {
        let (last, new_merkle) = next_layer(rest, digest, 1);
        match last {
          MaybeDigest::None => { compress_layer(new_merkle) },
          MaybeDigest::Some(last) => { compress_layer(&(LayerNode::Push(new_merkle, last))) },
        } },
    }
  }

  fn compress_chunks(
    input: ByteStream,
    byte_acc: ByteStream,
    block_index: Field,
    chunk_index: Field,
    chunk_count: &U64,
    block_digest: &[U32; 8],
    layer: Layer
  ) -> Layer {
    match *(input) {

      Lists::Node::Nil => {
        finish(byte_acc, block_index, chunk_index, chunk_count, block_digest, layer) },
      Lists::Node::Cons(head, input) => {
        let byte_acc = &(Lists::Node::Cons(head, byte_acc));
        match block_index {
          63 => { compress_block(input, byte_acc, chunk_index, chunk_count, block_digest, layer) },
          _ => { compress_chunks(input, byte_acc, block_index + 1, chunk_index + 1, chunk_count, block_digest, layer) },
        } },
    }
  }

  fn bytes_to_block(byte_acc: ByteStream) -> [U32; 16] {
    let Lists::Node::Cons(b63, l) = *(byte_acc);
    let Lists::Node::Cons(b62, l) = *(l);
    let Lists::Node::Cons(b61, l) = *(l);
    let Lists::Node::Cons(b60, l) = *(l);
    let Lists::Node::Cons(b59, l) = *(l);
    let Lists::Node::Cons(b58, l) = *(l);
    let Lists::Node::Cons(b57, l) = *(l);
    let Lists::Node::Cons(b56, l) = *(l);
    let Lists::Node::Cons(b55, l) = *(l);
    let Lists::Node::Cons(b54, l) = *(l);
    let Lists::Node::Cons(b53, l) = *(l);
    let Lists::Node::Cons(b52, l) = *(l);
    let Lists::Node::Cons(b51, l) = *(l);
    let Lists::Node::Cons(b50, l) = *(l);
    let Lists::Node::Cons(b49, l) = *(l);
    let Lists::Node::Cons(b48, l) = *(l);
    let Lists::Node::Cons(b47, l) = *(l);
    let Lists::Node::Cons(b46, l) = *(l);
    let Lists::Node::Cons(b45, l) = *(l);
    let Lists::Node::Cons(b44, l) = *(l);
    let Lists::Node::Cons(b43, l) = *(l);
    let Lists::Node::Cons(b42, l) = *(l);
    let Lists::Node::Cons(b41, l) = *(l);
    let Lists::Node::Cons(b40, l) = *(l);
    let Lists::Node::Cons(b39, l) = *(l);
    let Lists::Node::Cons(b38, l) = *(l);
    let Lists::Node::Cons(b37, l) = *(l);
    let Lists::Node::Cons(b36, l) = *(l);
    let Lists::Node::Cons(b35, l) = *(l);
    let Lists::Node::Cons(b34, l) = *(l);
    let Lists::Node::Cons(b33, l) = *(l);
    let Lists::Node::Cons(b32, l) = *(l);
    let Lists::Node::Cons(b31, l) = *(l);
    let Lists::Node::Cons(b30, l) = *(l);
    let Lists::Node::Cons(b29, l) = *(l);
    let Lists::Node::Cons(b28, l) = *(l);
    let Lists::Node::Cons(b27, l) = *(l);
    let Lists::Node::Cons(b26, l) = *(l);
    let Lists::Node::Cons(b25, l) = *(l);
    let Lists::Node::Cons(b24, l) = *(l);
    let Lists::Node::Cons(b23, l) = *(l);
    let Lists::Node::Cons(b22, l) = *(l);
    let Lists::Node::Cons(b21, l) = *(l);
    let Lists::Node::Cons(b20, l) = *(l);
    let Lists::Node::Cons(b19, l) = *(l);
    let Lists::Node::Cons(b18, l) = *(l);
    let Lists::Node::Cons(b17, l) = *(l);
    let Lists::Node::Cons(b16, l) = *(l);
    let Lists::Node::Cons(b15, l) = *(l);
    let Lists::Node::Cons(b14, l) = *(l);
    let Lists::Node::Cons(b13, l) = *(l);
    let Lists::Node::Cons(b12, l) = *(l);
    let Lists::Node::Cons(b11, l) = *(l);
    let Lists::Node::Cons(b10, l) = *(l);
    let Lists::Node::Cons(b9, l) = *(l);
    let Lists::Node::Cons(b8, l) = *(l);
    let Lists::Node::Cons(b7, l) = *(l);
    let Lists::Node::Cons(b6, l) = *(l);
    let Lists::Node::Cons(b5, l) = *(l);
    let Lists::Node::Cons(b4, l) = *(l);
    let Lists::Node::Cons(b3, l) = *(l);
    let Lists::Node::Cons(b2, l) = *(l);
    let Lists::Node::Cons(b1, l) = *(l);
    let Lists::Node::Cons(b0, _) = *(l);
    [
      UInt32::from_bytes([b0, b1, b2, b3]), UInt32::from_bytes([b4, b5, b6, b7]), UInt32::from_bytes([b8, b9, b10, b11]), UInt32::from_bytes([b12, b13, b14, b15]),
      UInt32::from_bytes([b16, b17, b18, b19]), UInt32::from_bytes([b20, b21, b22, b23]), UInt32::from_bytes([b24, b25, b26, b27]), UInt32::from_bytes([b28, b29, b30, b31]),
      UInt32::from_bytes([b32, b33, b34, b35]), UInt32::from_bytes([b36, b37, b38, b39]), UInt32::from_bytes([b40, b41, b42, b43]), UInt32::from_bytes([b44, b45, b46, b47]),
      UInt32::from_bytes([b48, b49, b50, b51]), UInt32::from_bytes([b52, b53, b54, b55]), UInt32::from_bytes([b56, b57, b58, b59]), UInt32::from_bytes([b60, b61, b62, b63])
    ]
  }

  fn pad_block(acc: ByteStream, n: Field) -> ByteStream {
    match n {
      0 => { acc },
      _ => { pad_block(&(Lists::Node::Cons(UInt8::BYTE_0, acc)), n - 1) },
    }
  }

  fn finish(
    byte_acc: ByteStream,
    block_index: Field,
    chunk_index: Field,
    chunk_count: &U64,
    block_digest: &[U32; 8],
    layer: Layer
  ) -> Layer {
    let CHUNK_START = 1;
    let CHUNK_END = 2;
    let ROOT = 8;
    match (block_index, chunk_index) {
      (0, 0) => {
        match *(chunk_count) {
          [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0] => {
            let flags = ROOT + CHUNK_START + CHUNK_END;
            &(LayerNode::Push(layer, compress_init(*(block_digest), [UInt32::ZERO; 16], *(chunk_count), 0, flags))) },
          _ => { layer },
        } },
      (0, _) => { &(LayerNode::Push(layer, *(block_digest))) },
      (_, _) => {
        let flags = CHUNK_END + UInt64::is_zero(*(chunk_count)) * ROOT + Fields::is_zero(chunk_index - block_index) * CHUNK_START;
        let block = bytes_to_block(pad_block(byte_acc, 64 - block_index));
        &(LayerNode::Push(layer, compress_init(*(block_digest), block, *(chunk_count), block_index, flags))) },
    }
  }

  fn compress_block(
    input: ByteStream,
    byte_acc: ByteStream,
    chunk_index: Field,
    chunk_count: &U64,
    block_digest: &[U32; 8],
    layer: Layer
  ) -> Layer {
    let CHUNK_START = 1;
    let CHUNK_END = 2;
    let ROOT = 8;
    let block = bytes_to_block(byte_acc);
    match chunk_index {
      1023 => {
        let flags = ROOT * Lists::is_empty(input) * UInt64::is_zero(*(chunk_count)) + CHUNK_END;

        let IV = iv();
        let layer = &(LayerNode::Push(layer, compress_init(*(block_digest), block, *(chunk_count), 64, flags)));
        compress_chunks(input, &(Lists::Node::Nil), 0, 0, &(UInt64::wrapping_succ(*(chunk_count))), &(IV), layer) },
      _ => {
        let chunk_end_flag = Lists::is_empty(input) * CHUNK_END;
        let root_flag = Lists::is_empty(input) * UInt64::is_zero(*(chunk_count)) * ROOT;
        let chunk_start_flag = Fields::is_zero(chunk_index - 63) * CHUNK_START;
        let flags = chunk_end_flag + root_flag + chunk_start_flag;
        let block_digest = compress_init(*(block_digest), block, *(chunk_count), 64, flags);
        compress_chunks(input, &(Lists::Node::Nil), 0, chunk_index + 1, chunk_count, &(block_digest), layer) },
    }
  }

  inline fn g_function(
    a: U32,
    b: U32,
    c: U32,
    d: U32,
    x: U32,
    y: U32
  ) -> [U32; 4] {
    let a = UInt32::add3(a, b, x);
    let d = UInt32::rotr16(UInt32::xor(d, a));
    let c = UInt32::add(c, d);
    let b = UInt32::xor_rotr12(b, c);
    let a = UInt32::add3(a, b, y);
    let d = UInt32::rotr8(UInt32::xor(d, a));
    let c = UInt32::add(c, d);
    let b = UInt32::xor_rotr7(b, c);
    [a, b, c, d]
  }

  inline fn compress_inner_j(state: [U32; 32]) -> [U32; 32] {
    let [a, b, c, d] = g_function(
      state[0], state[4], state[8], state[12], state[16], state[17]
    );
    let state = (state with { [0] = a });
    let state = (state with { [4] = b });
    let state = (state with { [8] = c });
    let state = (state with { [12] = d });

    let [a, b, c, d] = g_function(
      state[1], state[5], state[9], state[13], state[18], state[19]
    );
    let state = (state with { [1] = a });
    let state = (state with { [5] = b });
    let state = (state with { [9] = c });
    let state = (state with { [13] = d });

    let [a, b, c, d] = g_function(
      state[2], state[6], state[10], state[14], state[20], state[21]
    );
    let state = (state with { [2] = a });
    let state = (state with { [6] = b });
    let state = (state with { [10] = c });
    let state = (state with { [14] = d });

    let [a, b, c, d] = g_function(
      state[3], state[7], state[11], state[15], state[22], state[23]
    );
    let state = (state with { [3] = a });
    let state = (state with { [7] = b });
    let state = (state with { [11] = c });
    let state = (state with { [15] = d });

    let [a, b, c, d] = g_function(
      state[0], state[5], state[10], state[15], state[24], state[25]
    );
    let state = (state with { [0] = a });
    let state = (state with { [5] = b });
    let state = (state with { [10] = c });
    let state = (state with { [15] = d });

    let [a, b, c, d] = g_function(
      state[1], state[6], state[11], state[12], state[26], state[27]
    );
    let state = (state with { [1] = a });
    let state = (state with { [6] = b });
    let state = (state with { [11] = c });
    let state = (state with { [12] = d });

    let [a, b, c, d] = g_function(
      state[2], state[7], state[8], state[13], state[28], state[29]
    );
    let state = (state with { [2] = a });
    let state = (state with { [7] = b });
    let state = (state with { [8] = c });
    let state = (state with { [13] = d });

    let [a, b, c, d] = g_function(
      state[3], state[4], state[9], state[14], state[30], state[31]
    );
    let state = (state with { [3] = a });
    let state = (state with { [4] = b });
    let state = (state with { [9] = c });
    let state = (state with { [14] = d });

    state
  }

  inline fn compress_init(
    chaining_value: [U32; 8],
    block_words: [U32; 16],
    counter: U64,
    block_len: Field,
    flags: Field
  ) -> [U32; 8] {
    let IV = iv();
    let IV0 = IV[0];
    let IV1 = IV[1];
    let IV2 = IV[2];
    let IV3 = IV[3];

    let counter_low = UInt32::from_bytes(counter[0 .. 4]);
    let counter_high = UInt32::from_bytes(counter[4 .. 8]);

    let block_len_u32 = UInt32::from_bytes([UInt8::from_field(block_len), UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]);
    let flags_u32 = UInt32::from_bytes([UInt8::from_field(flags), UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]);
    let state: [U32; 32] = [
      chaining_value[0], chaining_value[1], chaining_value[2], chaining_value[3],
      chaining_value[4], chaining_value[5], chaining_value[6], chaining_value[7],
                    IV0,               IV1,               IV2,               IV3,
            counter_low,      counter_high,     block_len_u32,         flags_u32,
         block_words[0],    block_words[1],    block_words[2],    block_words[3],
         block_words[4],    block_words[5],    block_words[6],    block_words[7],
         block_words[8],    block_words[9],   block_words[10],   block_words[11],
        block_words[12],   block_words[13],   block_words[14],   block_words[15]
    ];

    compress(0, state)
  }

  fn compress(
    stage: Field,
    state: [U32; 32]
  ) -> [U32; 8] {
    match stage {
      7 => {
        let output0 = UInt32::xor(state[0], state[8]);
        let output1 = UInt32::xor(state[1], state[9]);
        let output2 = UInt32::xor(state[2], state[10]);
        let output3 = UInt32::xor(state[3], state[11]);
        let output4 = UInt32::xor(state[4], state[12]);
        let output5 = UInt32::xor(state[5], state[13]);
        let output6 = UInt32::xor(state[6], state[14]);
        let output7 = UInt32::xor(state[7], state[15]);
        [output0, output1, output2, output3, output4, output5, output6, output7] },
      _ => {
        let new_state = compress_inner_j(state);

        let new_state = (new_state with { [16] = state[18] });
        let new_state = (new_state with { [17] = state[22] });
        let new_state = (new_state with { [18] = state[19] });
        let new_state = (new_state with { [19] = state[26] });
        let new_state = (new_state with { [20] = state[23] });
        let new_state = (new_state with { [21] = state[16] });
        let new_state = (new_state with { [22] = state[20] });
        let new_state = (new_state with { [23] = state[29] });
        let new_state = (new_state with { [24] = state[17] });
        let new_state = (new_state with { [25] = state[27] });
        let new_state = (new_state with { [26] = state[28] });
        let new_state = (new_state with { [27] = state[21] });
        let new_state = (new_state with { [28] = state[25] });
        let new_state = (new_state with { [29] = state[30] });
        let new_state = (new_state with { [30] = state[31] });
        let new_state = (new_state with { [31] = state[24] });
        compress(stage + 1, new_state) },
    }
  }

  inline fn digest_bytes(digest: [U32; 8]) -> [U8; 32] {
    let b0 = UInt32::to_bytes(digest[0]);
    let b1 = UInt32::to_bytes(digest[1]);
    let b2 = UInt32::to_bytes(digest[2]);
    let b3 = UInt32::to_bytes(digest[3]);
    let b4 = UInt32::to_bytes(digest[4]);
    let b5 = UInt32::to_bytes(digest[5]);
    let b6 = UInt32::to_bytes(digest[6]);
    let b7 = UInt32::to_bytes(digest[7]);
    [b0[0], b0[1], b0[2], b0[3], b1[0], b1[1], b1[2], b1[3],
     b2[0], b2[1], b2[2], b2[3], b3[0], b3[1], b3[2], b3[3],
     b4[0], b4[1], b4[2], b4[3], b5[0], b5[1], b5[2], b5[3],
     b6[0], b6[1], b6[2], b6[3], b7[0], b7[1], b7[2], b7[3]]
}

  inline fn address_to_fields(bytes: [U8; 32]) -> [Field; 32] {
    [UInt8::to_field(bytes[0]), UInt8::to_field(bytes[1]), UInt8::to_field(bytes[2]), UInt8::to_field(bytes[3]), UInt8::to_field(bytes[4]), UInt8::to_field(bytes[5]), UInt8::to_field(bytes[6]), UInt8::to_field(bytes[7]), UInt8::to_field(bytes[8]), UInt8::to_field(bytes[9]), UInt8::to_field(bytes[10]), UInt8::to_field(bytes[11]), UInt8::to_field(bytes[12]), UInt8::to_field(bytes[13]), UInt8::to_field(bytes[14]), UInt8::to_field(bytes[15]), UInt8::to_field(bytes[16]), UInt8::to_field(bytes[17]), UInt8::to_field(bytes[18]), UInt8::to_field(bytes[19]), UInt8::to_field(bytes[20]), UInt8::to_field(bytes[21]), UInt8::to_field(bytes[22]), UInt8::to_field(bytes[23]), UInt8::to_field(bytes[24]), UInt8::to_field(bytes[25]), UInt8::to_field(bytes[26]), UInt8::to_field(bytes[27]), UInt8::to_field(bytes[28]), UInt8::to_field(bytes[29]), UInt8::to_field(bytes[30]), UInt8::to_field(bytes[31])]
}

  inline fn address_from_fields(raw: [Field; 32]) -> [U8; 32] {
    let (b0, b1) = UInt8::from_fields(raw[0], raw[1]);
    let (b2, b3) = UInt8::from_fields(raw[2], raw[3]);
    let (b4, b5) = UInt8::from_fields(raw[4], raw[5]);
    let (b6, b7) = UInt8::from_fields(raw[6], raw[7]);
    let (b8, b9) = UInt8::from_fields(raw[8], raw[9]);
    let (b10, b11) = UInt8::from_fields(raw[10], raw[11]);
    let (b12, b13) = UInt8::from_fields(raw[12], raw[13]);
    let (b14, b15) = UInt8::from_fields(raw[14], raw[15]);
    let (b16, b17) = UInt8::from_fields(raw[16], raw[17]);
    let (b18, b19) = UInt8::from_fields(raw[18], raw[19]);
    let (b20, b21) = UInt8::from_fields(raw[20], raw[21]);
    let (b22, b23) = UInt8::from_fields(raw[22], raw[23]);
    let (b24, b25) = UInt8::from_fields(raw[24], raw[25]);
    let (b26, b27) = UInt8::from_fields(raw[26], raw[27]);
    let (b28, b29) = UInt8::from_fields(raw[28], raw[29]);
    let (b30, b31) = UInt8::from_fields(raw[30], raw[31]);
    [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]
}
}
"#

def templates : Modules.Program Nat :=
  dependencies.append declarations

def source : Modules.Program Nat :=
  U32.source.append U64.declarations |>.append List.declarations |>.append Field.declarations
    |>.append declarations

end Aiur.Library.Blake3
