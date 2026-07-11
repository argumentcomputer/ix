module
public import Ix.Aiur.Meta

public section

namespace IxVM

-- The unrolled message schedule + 64-round fold elaborate to one deeply
-- nested let chain; the default recursion budget is not enough.
set_option maxRecDepth 65536 in
def sha256 := ⟦
  /- # Test entrypoints -/

  pub fn sha256_test() -> [[U8; 4]; 8] {
    let (idx, len) = io_get_info(0, [0]);
    let byte_stream = #read_byte_stream(0, idx, len);
    sha256(byte_stream)
  }

  /- # Benchmark entrypoints -/

  pub fn sha256_bench(num_hashes: G) -> G {
    let num_hashes_pred = num_hashes - 1;
    let key = [num_hashes_pred];
    let (idx, len) = io_get_info(0, key);
    let byte_stream = #read_byte_stream(0, idx, len);
    sha256(byte_stream);
    match num_hashes_pred {
      0 => 0,
      _ => sha256_bench(num_hashes_pred),
    }
  }

  /- # Implementation -/

  fn sha256(stream: ByteStream) -> [[U8; 4]; 8] {
    let state = [
      [0x6au8, 0x09u8, 0xe6u8, 0x67u8],
      [0xbbu8, 0x67u8, 0xaeu8, 0x85u8],
      [0x3cu8, 0x6eu8, 0xf3u8, 0x72u8],
      [0xa5u8, 0x4fu8, 0xf5u8, 0x3au8],
      [0x51u8, 0x0eu8, 0x52u8, 0x7fu8],
      [0x9bu8, 0x05u8, 0x68u8, 0x8cu8],
      [0x1fu8, 0x83u8, 0xd9u8, 0xabu8],
      [0x5bu8, 0xe0u8, 0xcdu8, 0x19u8]
    ];
    sha256_aux(stream, [0u8; 8], state)
  }

  fn sha256_aux(stream: ByteStream, len_be: U64, state: [[U8; 4]; 8]) -> [[U8; 4]; 8] {
    let W = [[0u8; 4]; 16];
    match load(stream) {
      ListNode.Nil =>
        let W = set(W, 0, [0x80u8, 0u8, 0u8, 0u8]);
        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
        fill_W_and_run_rounds(W, state),
      ListNode.Cons(b0, tail) => match load(tail) {
        ListNode.Nil =>
          let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 8u8]);
          let W = set(W, 0, [b0, 0x80u8, 0u8, 0u8]);
          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
          fill_W_and_run_rounds(W, state),
        ListNode.Cons(b1, tail) => match load(tail) {
          ListNode.Nil =>
            let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 16u8]);
            let W = set(W, 0, [b0, b1, 0x80u8, 0u8]);
            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
            fill_W_and_run_rounds(W, state),
          ListNode.Cons(b2, tail) => match load(tail) {
            ListNode.Nil =>
              let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 24u8]);
              let W = set(W, 0, [b0, b1, b2, 0x80u8]);
              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
              fill_W_and_run_rounds(W, state),
            ListNode.Cons(b3, tail) =>
              let W = set(W, 0, [b0, b1, b2, b3]);
              match load(tail) {
              ListNode.Nil =>
                let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 32u8]);
                let W = set(W, 1, [0x80u8, 0u8, 0u8, 0u8]);
                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                fill_W_and_run_rounds(W, state),
              ListNode.Cons(b4, tail) => match load(tail) {
                ListNode.Nil =>
                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 40u8]);
                  let W = set(W, 1, [b4, 0x80u8, 0u8, 0u8]);
                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                  fill_W_and_run_rounds(W, state),
                ListNode.Cons(b5, tail) => match load(tail) {
                  ListNode.Nil =>
                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 48u8]);
                    let W = set(W, 1, [b4, b5, 0x80u8, 0u8]);
                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                    fill_W_and_run_rounds(W, state),
                  ListNode.Cons(b6, tail) => match load(tail) {
                    ListNode.Nil =>
                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 56u8]);
                      let W = set(W, 1, [b4, b5, b6, 0x80u8]);
                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                      fill_W_and_run_rounds(W, state),
                    ListNode.Cons(b7, tail) =>
                      let W = set(W, 1, [b4, b5, b6, b7]);
                      match load(tail) {
                      ListNode.Nil =>
                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 64u8]);
                        let W = set(W, 2, [0x80u8, 0u8, 0u8, 0u8]);
                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                        fill_W_and_run_rounds(W, state),
                      ListNode.Cons(b8, tail) => match load(tail) {
                        ListNode.Nil =>
                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 72u8]);
                          let W = set(W, 2, [b8, 0x80u8, 0u8, 0u8]);
                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                          fill_W_and_run_rounds(W, state),
                        ListNode.Cons(b9, tail) => match load(tail) {
                          ListNode.Nil =>
                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 80u8]);
                            let W = set(W, 2, [b8, b9, 0x80u8, 0u8]);
                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                            fill_W_and_run_rounds(W, state),
                          ListNode.Cons(b10, tail) => match load(tail) {
                            ListNode.Nil =>
                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 88u8]);
                              let W = set(W, 2, [b8, b9, b10, 0x80u8]);
                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                              fill_W_and_run_rounds(W, state),
                            ListNode.Cons(b11, tail) =>
                              let W = set(W, 2, [b8, b9, b10, b11]);
                              match load(tail) {
                              ListNode.Nil =>
                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 96u8]);
                                let W = set(W, 3, [0x80u8, 0u8, 0u8, 0u8]);
                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                fill_W_and_run_rounds(W, state),
                              ListNode.Cons(b12, tail) => match load(tail) {
                                ListNode.Nil =>
                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 104u8]);
                                  let W = set(W, 3, [b12, 0x80u8, 0u8, 0u8]);
                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                  fill_W_and_run_rounds(W, state),
                                ListNode.Cons(b13, tail) => match load(tail) {
                                  ListNode.Nil =>
                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 112u8]);
                                    let W = set(W, 3, [b12, b13, 0x80u8, 0u8]);
                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                    fill_W_and_run_rounds(W, state),
                                  ListNode.Cons(b14, tail) => match load(tail) {
                                    ListNode.Nil =>
                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 120u8]);
                                      let W = set(W, 3, [b12, b13, b14, 0x80u8]);
                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                      fill_W_and_run_rounds(W, state),
                                    ListNode.Cons(b15, tail) =>
                                      let W = set(W, 3, [b12, b13, b14, b15]);
                                      match load(tail) {
                                      ListNode.Nil =>
                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 128u8]);
                                        let W = set(W, 4, [0x80u8, 0u8, 0u8, 0u8]);
                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                        fill_W_and_run_rounds(W, state),
                                      ListNode.Cons(b16, tail) => match load(tail) {
                                        ListNode.Nil =>
                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 136u8]);
                                          let W = set(W, 4, [b16, 0x80u8, 0u8, 0u8]);
                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                          fill_W_and_run_rounds(W, state),
                                        ListNode.Cons(b17, tail) => match load(tail) {
                                          ListNode.Nil =>
                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 144u8]);
                                            let W = set(W, 4, [b16, b17, 0x80u8, 0u8]);
                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                            fill_W_and_run_rounds(W, state),
                                          ListNode.Cons(b18, tail) => match load(tail) {
                                            ListNode.Nil =>
                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 152u8]);
                                              let W = set(W, 4, [b16, b17, b18, 0x80u8]);
                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                              fill_W_and_run_rounds(W, state),
                                            ListNode.Cons(b19, tail) =>
                                              let W = set(W, 4, [b16, b17, b18, b19]);
                                              match load(tail) {
                                              ListNode.Nil =>
                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 160u8]);
                                                let W = set(W, 5, [0x80u8, 0u8, 0u8, 0u8]);
                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                fill_W_and_run_rounds(W, state),
                                              ListNode.Cons(b20, tail) => match load(tail) {
                                                ListNode.Nil =>
                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 168u8]);
                                                  let W = set(W, 5, [b20, 0x80u8, 0u8, 0u8]);
                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                  fill_W_and_run_rounds(W, state),
                                                ListNode.Cons(b21, tail) => match load(tail) {
                                                  ListNode.Nil =>
                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 176u8]);
                                                    let W = set(W, 5, [b20, b21, 0x80u8, 0u8]);
                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                    fill_W_and_run_rounds(W, state),
                                                  ListNode.Cons(b22, tail) => match load(tail) {
                                                    ListNode.Nil =>
                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 184u8]);
                                                      let W = set(W, 5, [b20, b21, b22, 0x80u8]);
                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                      fill_W_and_run_rounds(W, state),
                                                    ListNode.Cons(b23, tail) =>
                                                      let W = set(W, 5, [b20, b21, b22, b23]);
                                                      match load(tail) {
                                                      ListNode.Nil =>
                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 192u8]);
                                                        let W = set(W, 6, [0x80u8, 0u8, 0u8, 0u8]);
                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                        fill_W_and_run_rounds(W, state),
                                                      ListNode.Cons(b24, tail) => match load(tail) {
                                                        ListNode.Nil =>
                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 200u8]);
                                                          let W = set(W, 6, [b24, 0x80u8, 0u8, 0u8]);
                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                          fill_W_and_run_rounds(W, state),
                                                        ListNode.Cons(b25, tail) => match load(tail) {
                                                          ListNode.Nil =>
                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 208u8]);
                                                            let W = set(W, 6, [b24, b25, 0x80u8, 0u8]);
                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                            fill_W_and_run_rounds(W, state),
                                                          ListNode.Cons(b26, tail) => match load(tail) {
                                                            ListNode.Nil =>
                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 216u8]);
                                                              let W = set(W, 6, [b24, b25, b26, 0x80u8]);
                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                              fill_W_and_run_rounds(W, state),
                                                            ListNode.Cons(b27, tail) =>
                                                              let W = set(W, 6, [b24, b25, b26, b27]);
                                                              match load(tail) {
                                                              ListNode.Nil =>
                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 224u8]);
                                                                let W = set(W, 7, [0x80u8, 0u8, 0u8, 0u8]);
                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                fill_W_and_run_rounds(W, state),
                                                              ListNode.Cons(b28, tail) => match load(tail) {
                                                                ListNode.Nil =>
                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 232u8]);
                                                                  let W = set(W, 7, [b28, 0x80u8, 0u8, 0u8]);
                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                  fill_W_and_run_rounds(W, state),
                                                                ListNode.Cons(b29, tail) => match load(tail) {
                                                                  ListNode.Nil =>
                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 240u8]);
                                                                    let W = set(W, 7, [b28, b29, 0x80u8, 0u8]);
                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                    fill_W_and_run_rounds(W, state),
                                                                  ListNode.Cons(b30, tail) => match load(tail) {
                                                                    ListNode.Nil =>
                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [0u8, 248u8]);
                                                                      let W = set(W, 7, [b28, b29, b30, 0x80u8]);
                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                      fill_W_and_run_rounds(W, state),
                                                                    ListNode.Cons(b31, tail) =>
                                                                      let W = set(W, 7, [b28, b29, b30, b31]);
                                                                      match load(tail) {
                                                                      ListNode.Nil =>
                                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 0u8]);
                                                                        let W = set(W, 8, [0x80u8, 0u8, 0u8, 0u8]);
                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                        fill_W_and_run_rounds(W, state),
                                                                      ListNode.Cons(b32, tail) => match load(tail) {
                                                                        ListNode.Nil =>
                                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 8u8]);
                                                                          let W = set(W, 8, [b32, 0x80u8, 0u8, 0u8]);
                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                          fill_W_and_run_rounds(W, state),
                                                                        ListNode.Cons(b33, tail) => match load(tail) {
                                                                          ListNode.Nil =>
                                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 16u8]);
                                                                            let W = set(W, 8, [b32, b33, 0x80u8, 0u8]);
                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                            fill_W_and_run_rounds(W, state),
                                                                          ListNode.Cons(b34, tail) => match load(tail) {
                                                                            ListNode.Nil =>
                                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 24u8]);
                                                                              let W = set(W, 8, [b32, b33, b34, 0x80u8]);
                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                              fill_W_and_run_rounds(W, state),
                                                                            ListNode.Cons(b35, tail) =>
                                                                              let W = set(W, 8, [b32, b33, b34, b35]);
                                                                              match load(tail) {
                                                                              ListNode.Nil =>
                                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 32u8]);
                                                                                let W = set(W, 9, [0x80u8, 0u8, 0u8, 0u8]);
                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                fill_W_and_run_rounds(W, state),
                                                                              ListNode.Cons(b36, tail) => match load(tail) {
                                                                                ListNode.Nil =>
                                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 40u8]);
                                                                                  let W = set(W, 9, [b36, 0x80u8, 0u8, 0u8]);
                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                  fill_W_and_run_rounds(W, state),
                                                                                ListNode.Cons(b37, tail) => match load(tail) {
                                                                                  ListNode.Nil =>
                                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 48u8]);
                                                                                    let W = set(W, 9, [b36, b37, 0x80u8, 0u8]);
                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                    fill_W_and_run_rounds(W, state),
                                                                                  ListNode.Cons(b38, tail) => match load(tail) {
                                                                                    ListNode.Nil =>
                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 56u8]);
                                                                                      let W = set(W, 9, [b36, b37, b38, 0x80u8]);
                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                      fill_W_and_run_rounds(W, state),
                                                                                    ListNode.Cons(b39, tail) =>
                                                                                      let W = set(W, 9, [b36, b37, b38, b39]);
                                                                                      match load(tail) {
                                                                                      ListNode.Nil =>
                                                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 64u8]);
                                                                                        let W = set(W, 10, [0x80u8, 0u8, 0u8, 0u8]);
                                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                        fill_W_and_run_rounds(W, state),
                                                                                      ListNode.Cons(b40, tail) => match load(tail) {
                                                                                        ListNode.Nil =>
                                                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 72u8]);
                                                                                          let W = set(W, 10, [b40, 0x80u8, 0u8, 0u8]);
                                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                          fill_W_and_run_rounds(W, state),
                                                                                        ListNode.Cons(b41, tail) => match load(tail) {
                                                                                          ListNode.Nil =>
                                                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 80u8]);
                                                                                            let W = set(W, 10, [b40, b41, 0x80u8, 0u8]);
                                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                            fill_W_and_run_rounds(W, state),
                                                                                          ListNode.Cons(b42, tail) => match load(tail) {
                                                                                            ListNode.Nil =>
                                                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 88u8]);
                                                                                              let W = set(W, 10, [b40, b41, b42, 0x80u8]);
                                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                              fill_W_and_run_rounds(W, state),
                                                                                            ListNode.Cons(b43, tail) =>
                                                                                              let W = set(W, 10, [b40, b41, b42, b43]);
                                                                                              match load(tail) {
                                                                                              ListNode.Nil =>
                                                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 96u8]);
                                                                                                let W = set(W, 11, [0x80u8, 0u8, 0u8, 0u8]);
                                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                fill_W_and_run_rounds(W, state),
                                                                                              ListNode.Cons(b44, tail) => match load(tail) {
                                                                                                ListNode.Nil =>
                                                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 104u8]);
                                                                                                  let W = set(W, 11, [b44, 0x80u8, 0u8, 0u8]);
                                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                  fill_W_and_run_rounds(W, state),
                                                                                                ListNode.Cons(b45, tail) => match load(tail) {
                                                                                                  ListNode.Nil =>
                                                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 112u8]);
                                                                                                    let W = set(W, 11, [b44, b45, 0x80u8, 0u8]);
                                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                    fill_W_and_run_rounds(W, state),
                                                                                                  ListNode.Cons(b46, tail) => match load(tail) {
                                                                                                    ListNode.Nil =>
                                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 120u8]);
                                                                                                      let W = set(W, 11, [b44, b45, b46, 0x80u8]);
                                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                      fill_W_and_run_rounds(W, state),
                                                                                                    ListNode.Cons(b47, tail) =>
                                                                                                      let W = set(W, 11, [b44, b45, b46, b47]);
                                                                                                      match load(tail) {
                                                                                                      ListNode.Nil =>
                                                                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 128u8]);
                                                                                                        let W = set(W, 12, [0x80u8, 0u8, 0u8, 0u8]);
                                                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                        fill_W_and_run_rounds(W, state),
                                                                                                      ListNode.Cons(b48, tail) => match load(tail) {
                                                                                                        ListNode.Nil =>
                                                                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 136u8]);
                                                                                                          let W = set(W, 12, [b48, 0x80u8, 0u8, 0u8]);
                                                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                          fill_W_and_run_rounds(W, state),
                                                                                                        ListNode.Cons(b49, tail) => match load(tail) {
                                                                                                          ListNode.Nil =>
                                                                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 144u8]);
                                                                                                            let W = set(W, 12, [b48, b49, 0x80u8, 0u8]);
                                                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                            fill_W_and_run_rounds(W, state),
                                                                                                          ListNode.Cons(b50, tail) => match load(tail) {
                                                                                                            ListNode.Nil =>
                                                                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 152u8]);
                                                                                                              let W = set(W, 12, [b48, b49, b50, 0x80u8]);
                                                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                              fill_W_and_run_rounds(W, state),
                                                                                                            ListNode.Cons(b51, tail) =>
                                                                                                              let W = set(W, 12, [b48, b49, b50, b51]);
                                                                                                              match load(tail) {
                                                                                                              ListNode.Nil =>
                                                                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 160u8]);
                                                                                                                let W = set(W, 13, [0x80u8, 0u8, 0u8, 0u8]);
                                                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                fill_W_and_run_rounds(W, state),
                                                                                                              ListNode.Cons(b52, tail) => match load(tail) {
                                                                                                                ListNode.Nil =>
                                                                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 168u8]);
                                                                                                                  let W = set(W, 13, [b52, 0x80u8, 0u8, 0u8]);
                                                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                  fill_W_and_run_rounds(W, state),
                                                                                                                ListNode.Cons(b53, tail) => match load(tail) {
                                                                                                                  ListNode.Nil =>
                                                                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 176u8]);
                                                                                                                    let W = set(W, 13, [b52, b53, 0x80u8, 0u8]);
                                                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                    fill_W_and_run_rounds(W, state),
                                                                                                                  ListNode.Cons(b54, tail) => match load(tail) {
                                                                                                                    ListNode.Nil =>
                                                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 184u8]);
                                                                                                                      let W = set(W, 13, [b52, b53, b54, 0x80u8]);
                                                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                      fill_W_and_run_rounds(W, state),
                                                                                                                    ListNode.Cons(b55, tail) =>
                                                                                                                      let W = set(W, 13, [b52, b53, b54, b55]);
                                                                                                                      match load(tail) {
                                                                                                                      ListNode.Nil =>
                                                                                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 192u8]);
                                                                                                                        let W = set(W, 14, [0x80u8, 0u8, 0u8, 0u8]);
                                                                                                                        let state = fill_W_and_run_rounds(W, state);
                                                                                                                        fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                      ListNode.Cons(b56, tail) => match load(tail) {
                                                                                                                        ListNode.Nil =>
                                                                                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 200u8]);
                                                                                                                          let W = set(W, 14, [b56, 0x80u8, 0u8, 0u8]);
                                                                                                                          let state = fill_W_and_run_rounds(W, state);
                                                                                                                          fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                        ListNode.Cons(b57, tail) => match load(tail) {
                                                                                                                          ListNode.Nil =>
                                                                                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 208u8]);
                                                                                                                            let W = set(W, 14, [b56, b57, 0x80u8, 0u8]);
                                                                                                                            let state = fill_W_and_run_rounds(W, state);
                                                                                                                            fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                          ListNode.Cons(b58, tail) => match load(tail) {
                                                                                                                            ListNode.Nil =>
                                                                                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 216u8]);
                                                                                                                              let W = set(W, 14, [b56, b57, b58, 0x80u8]);
                                                                                                                              let state = fill_W_and_run_rounds(W, state);
                                                                                                                              fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                            ListNode.Cons(b59, tail) =>
                                                                                                                              let W = set(W, 14, [b56, b57, b58, b59]);
                                                                                                                              match load(tail) {
                                                                                                                              ListNode.Nil =>
                                                                                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 224u8]);
                                                                                                                                let W = set(W, 15, [0x80u8, 0u8, 0u8, 0u8]);
                                                                                                                                let state = fill_W_and_run_rounds(W, state);
                                                                                                                                fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                              ListNode.Cons(b60, tail) => match load(tail) {
                                                                                                                                ListNode.Nil =>
                                                                                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 232u8]);
                                                                                                                                  let W = set(W, 15, [b60, 0x80u8, 0u8, 0u8]);
                                                                                                                                  let state = fill_W_and_run_rounds(W, state);
                                                                                                                                  fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                                ListNode.Cons(b61, tail) => match load(tail) {
                                                                                                                                  ListNode.Nil =>
                                                                                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 240u8]);
                                                                                                                                    let W = set(W, 15, [b60, b61, 0x80u8, 0u8]);
                                                                                                                                    let state = fill_W_and_run_rounds(W, state);
                                                                                                                                    fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                                  ListNode.Cons(b62, tail) => match load(tail) {
                                                                                                                                    ListNode.Nil =>
                                                                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [1u8, 248u8]);
                                                                                                                                      let W = set(W, 15, [b60, b61, b62, 0x80u8]);
                                                                                                                                      let state = fill_W_and_run_rounds(W, state);
                                                                                                                                      fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                                    ListNode.Cons(b63, tail) =>
                                                                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [2u8, 0u8]);
                                                                                                                                      let W = set(W, 15, [b60, b61, b62, b63]);
                                                                                                                                      let state = fill_W_and_run_rounds(W, state);
                                                                                                                                      sha256_aux(tail, len_be, state),
                                                                                                                                  },
                                                                                                                                },
                                                                                                                              },
                                                                                                                            },
                                                                                                                          },
                                                                                                                        },
                                                                                                                      },
                                                                                                                    },
                                                                                                                  },
                                                                                                                },
                                                                                                              },
                                                                                                            },
                                                                                                          },
                                                                                                        },
                                                                                                      },
                                                                                                    },
                                                                                                  },
                                                                                                },
                                                                                              },
                                                                                            },
                                                                                          },
                                                                                        },
                                                                                      },
                                                                                    },
                                                                                  },
                                                                                },
                                                                              },
                                                                            },
                                                                          },
                                                                        },
                                                                      },
                                                                    },
                                                                  },
                                                                },
                                                              },
                                                            },
                                                          },
                                                        },
                                                      },
                                                    },
                                                  },
                                                },
                                              },
                                            },
                                          },
                                        },
                                      },
                                    },
                                  },
                                },
                              },
                            },
                          },
                        },
                      },
                    },
                  },
                },
              },
            },
          },
        },
      },
    }
  }

  fn fill_W_with_length_and_run_rounds(len_be: U64, state: [[U8; 4]; 8]) -> [[U8; 4]; 8] {
    let W = [[0u8; 4]; 16];
    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
    fill_W_and_run_rounds(W, state)
  }

  fn fill_W_and_run_rounds(W: [[U8; 4]; 16], state: [[U8; 4]; 8]) -> [[U8; 4]; 8] {
    let K = [
      [0x42u8, 0x8au8, 0x2fu8, 0x98u8], [0x71u8, 0x37u8, 0x44u8, 0x91u8], [0xb5u8, 0xc0u8, 0xfbu8, 0xcfu8], [0xe9u8, 0xb5u8, 0xdbu8, 0xa5u8],
      [0x39u8, 0x56u8, 0xc2u8, 0x5bu8], [0x59u8, 0xf1u8, 0x11u8, 0xf1u8], [0x92u8, 0x3fu8, 0x82u8, 0xa4u8], [0xabu8, 0x1cu8, 0x5eu8, 0xd5u8],
      [0xd8u8, 0x07u8, 0xaau8, 0x98u8], [0x12u8, 0x83u8, 0x5bu8, 0x01u8], [0x24u8, 0x31u8, 0x85u8, 0xbeu8], [0x55u8, 0x0cu8, 0x7du8, 0xc3u8],
      [0x72u8, 0xbeu8, 0x5du8, 0x74u8], [0x80u8, 0xdeu8, 0xb1u8, 0xfeu8], [0x9bu8, 0xdcu8, 0x06u8, 0xa7u8], [0xc1u8, 0x9bu8, 0xf1u8, 0x74u8],
      [0xe4u8, 0x9bu8, 0x69u8, 0xc1u8], [0xefu8, 0xbeu8, 0x47u8, 0x86u8], [0x0fu8, 0xc1u8, 0x9du8, 0xc6u8], [0x24u8, 0x0cu8, 0xa1u8, 0xccu8],
      [0x2du8, 0xe9u8, 0x2cu8, 0x6fu8], [0x4au8, 0x74u8, 0x84u8, 0xaau8], [0x5cu8, 0xb0u8, 0xa9u8, 0xdcu8], [0x76u8, 0xf9u8, 0x88u8, 0xdau8],
      [0x98u8, 0x3eu8, 0x51u8, 0x52u8], [0xa8u8, 0x31u8, 0xc6u8, 0x6du8], [0xb0u8, 0x03u8, 0x27u8, 0xc8u8], [0xbfu8, 0x59u8, 0x7fu8, 0xc7u8],
      [0xc6u8, 0xe0u8, 0x0bu8, 0xf3u8], [0xd5u8, 0xa7u8, 0x91u8, 0x47u8], [0x06u8, 0xcau8, 0x63u8, 0x51u8], [0x14u8, 0x29u8, 0x29u8, 0x67u8],
      [0x27u8, 0xb7u8, 0x0au8, 0x85u8], [0x2eu8, 0x1bu8, 0x21u8, 0x38u8], [0x4du8, 0x2cu8, 0x6du8, 0xfcu8], [0x53u8, 0x38u8, 0x0du8, 0x13u8],
      [0x65u8, 0x0au8, 0x73u8, 0x54u8], [0x76u8, 0x6au8, 0x0au8, 0xbbu8], [0x81u8, 0xc2u8, 0xc9u8, 0x2eu8], [0x92u8, 0x72u8, 0x2cu8, 0x85u8],
      [0xa2u8, 0xbfu8, 0xe8u8, 0xa1u8], [0xa8u8, 0x1au8, 0x66u8, 0x4bu8], [0xc2u8, 0x4bu8, 0x8bu8, 0x70u8], [0xc7u8, 0x6cu8, 0x51u8, 0xa3u8],
      [0xd1u8, 0x92u8, 0xe8u8, 0x19u8], [0xd6u8, 0x99u8, 0x06u8, 0x24u8], [0xf4u8, 0x0eu8, 0x35u8, 0x85u8], [0x10u8, 0x6au8, 0xa0u8, 0x70u8],
      [0x19u8, 0xa4u8, 0xc1u8, 0x16u8], [0x1eu8, 0x37u8, 0x6cu8, 0x08u8], [0x27u8, 0x48u8, 0x77u8, 0x4cu8], [0x34u8, 0xb0u8, 0xbcu8, 0xb5u8],
      [0x39u8, 0x1cu8, 0x0cu8, 0xb3u8], [0x4eu8, 0xd8u8, 0xaau8, 0x4au8], [0x5bu8, 0x9cu8, 0xcau8, 0x4fu8], [0x68u8, 0x2eu8, 0x6fu8, 0xf3u8],
      [0x74u8, 0x8fu8, 0x82u8, 0xeeu8], [0x78u8, 0xa5u8, 0x63u8, 0x6fu8], [0x84u8, 0xc8u8, 0x78u8, 0x14u8], [0x8cu8, 0xc7u8, 0x02u8, 0x08u8],
      [0x90u8, 0xbeu8, 0xffu8, 0xfau8], [0xa4u8, 0x50u8, 0x6cu8, 0xebu8], [0xbeu8, 0xf9u8, 0xa3u8, 0xf7u8], [0xc6u8, 0x71u8, 0x78u8, 0xf2u8]
    ];

    -- Message schedule, inlined (the old `define_W_i` helper's body): each
    -- call cost 4 output aux + 1 lookup here plus a 210-wide row per
    -- distinct input tuple in its own circuit — with the schedule in-block
    -- the work rides the block row that already exists.
    let Wx = [[0u8; 4]; 64];
    let Wx = fold(0 .. 16, Wx, |Wx, @j| set(Wx, @j, W[@j]));
    let Wx = fold(16 .. 64, Wx, |Wx, @i|
      let [w15_b3, w15_b2, w15_b1, w15_b0] = Wx[@i - 15];
      let [w15_b0_0, w15_b0_1, w15_b0_2, w15_b0_3, w15_b0_4, w15_b0_5, w15_b0_6, w15_b0_7] = u8_bit_decomposition(w15_b0);
      let [w15_b1_0, w15_b1_1, w15_b1_2, w15_b1_3, w15_b1_4, w15_b1_5, w15_b1_6, w15_b1_7] = u8_bit_decomposition(w15_b1);
      let [w15_b2_0, w15_b2_1, w15_b2_2, w15_b2_3, w15_b2_4, w15_b2_5, w15_b2_6, w15_b2_7] = u8_bit_decomposition(w15_b2);
      let [w15_b3_0, w15_b3_1, w15_b3_2, w15_b3_3, w15_b3_4, w15_b3_5, w15_b3_6, w15_b3_7] = u8_bit_decomposition(w15_b3);

      let w15_rotr7 = [
        u8_from_field_unsafe(w15_b3_7 + 2 * w15_b0_0 + 4 * w15_b0_1 + 8 * w15_b0_2 + 16 * w15_b0_3 + 32 * w15_b0_4 + 64 * w15_b0_5 + 128 * w15_b0_6),
        u8_from_field_unsafe(w15_b2_7 + 2 * w15_b3_0 + 4 * w15_b3_1 + 8 * w15_b3_2 + 16 * w15_b3_3 + 32 * w15_b3_4 + 64 * w15_b3_5 + 128 * w15_b3_6),
        u8_from_field_unsafe(w15_b1_7 + 2 * w15_b2_0 + 4 * w15_b2_1 + 8 * w15_b2_2 + 16 * w15_b2_3 + 32 * w15_b2_4 + 64 * w15_b2_5 + 128 * w15_b2_6),
        u8_from_field_unsafe(w15_b0_7 + 2 * w15_b1_0 + 4 * w15_b1_1 + 8 * w15_b1_2 + 16 * w15_b1_3 + 32 * w15_b1_4 + 64 * w15_b1_5 + 128 * w15_b1_6)
      ];

      let w15_rotr18 = [
        u8_from_field_unsafe(w15_b1_2 + 2 * w15_b1_3 + 4 * w15_b1_4 + 8 * w15_b1_5 + 16 * w15_b1_6 + 32 * w15_b1_7 + 64 * w15_b2_0 + 128 * w15_b2_1),
        u8_from_field_unsafe(w15_b0_2 + 2 * w15_b0_3 + 4 * w15_b0_4 + 8 * w15_b0_5 + 16 * w15_b0_6 + 32 * w15_b0_7 + 64 * w15_b1_0 + 128 * w15_b1_1),
        u8_from_field_unsafe(w15_b3_2 + 2 * w15_b3_3 + 4 * w15_b3_4 + 8 * w15_b3_5 + 16 * w15_b3_6 + 32 * w15_b3_7 + 64 * w15_b0_0 + 128 * w15_b0_1),
        u8_from_field_unsafe(w15_b2_2 + 2 * w15_b2_3 + 4 * w15_b2_4 + 8 * w15_b2_5 + 16 * w15_b2_6 + 32 * w15_b2_7 + 64 * w15_b3_0 + 128 * w15_b3_1)
      ];

      let w15_shr3 = [
        u8_from_field_unsafe(w15_b3_3 + 2 * w15_b3_4 + 4 * w15_b3_5 + 8 * w15_b3_6 + 16 * w15_b3_7),
        u8_from_field_unsafe(w15_b2_3 + 2 * w15_b2_4 + 4 * w15_b2_5 + 8 * w15_b2_6 + 16 * w15_b2_7 + 32 * w15_b3_0 + 64 * w15_b3_1 + 128 * w15_b3_2),
        u8_from_field_unsafe(w15_b1_3 + 2 * w15_b1_4 + 4 * w15_b1_5 + 8 * w15_b1_6 + 16 * w15_b1_7 + 32 * w15_b2_0 + 64 * w15_b2_1 + 128 * w15_b2_2),
        u8_from_field_unsafe(w15_b0_3 + 2 * w15_b0_4 + 4 * w15_b0_5 + 8 * w15_b0_6 + 16 * w15_b0_7 + 32 * w15_b1_0 + 64 * w15_b1_1 + 128 * w15_b1_2)
      ];

      let [w2_b3, w2_b2, w2_b1, w2_b0] = Wx[@i - 2];
      let [w2_b0_0, w2_b0_1, w2_b0_2, w2_b0_3, w2_b0_4, w2_b0_5, w2_b0_6, w2_b0_7] = u8_bit_decomposition(w2_b0);
      let [w2_b1_0, w2_b1_1, w2_b1_2, w2_b1_3, w2_b1_4, w2_b1_5, w2_b1_6, w2_b1_7] = u8_bit_decomposition(w2_b1);
      let [w2_b2_0, w2_b2_1, w2_b2_2, w2_b2_3, w2_b2_4, w2_b2_5, w2_b2_6, w2_b2_7] = u8_bit_decomposition(w2_b2);
      let [w2_b3_0, w2_b3_1, w2_b3_2, w2_b3_3, w2_b3_4, w2_b3_5, w2_b3_6, w2_b3_7] = u8_bit_decomposition(w2_b3);

      let w2_rotr17 = [
        u8_from_field_unsafe(w2_b1_1 + 2 * w2_b1_2 + 4 * w2_b1_3 + 8 * w2_b1_4 + 16 * w2_b1_5 + 32 * w2_b1_6 + 64 * w2_b1_7 + 128 * w2_b2_0),
        u8_from_field_unsafe(w2_b0_1 + 2 * w2_b0_2 + 4 * w2_b0_3 + 8 * w2_b0_4 + 16 * w2_b0_5 + 32 * w2_b0_6 + 64 * w2_b0_7 + 128 * w2_b1_0),
        u8_from_field_unsafe(w2_b3_1 + 2 * w2_b3_2 + 4 * w2_b3_3 + 8 * w2_b3_4 + 16 * w2_b3_5 + 32 * w2_b3_6 + 64 * w2_b3_7 + 128 * w2_b0_0),
        u8_from_field_unsafe(w2_b2_1 + 2 * w2_b2_2 + 4 * w2_b2_3 + 8 * w2_b2_4 + 16 * w2_b2_5 + 32 * w2_b2_6 + 64 * w2_b2_7 + 128 * w2_b3_0)
      ];

      let w2_rotr19 = [
        u8_from_field_unsafe(w2_b1_3 + 2 * w2_b1_4 + 4 * w2_b1_5 + 8 * w2_b1_6 + 16 * w2_b1_7 + 32 * w2_b2_0 + 64 * w2_b2_1 + 128 * w2_b2_2),
        u8_from_field_unsafe(w2_b0_3 + 2 * w2_b0_4 + 4 * w2_b0_5 + 8 * w2_b0_6 + 16 * w2_b0_7 + 32 * w2_b1_0 + 64 * w2_b1_1 + 128 * w2_b1_2),
        u8_from_field_unsafe(w2_b3_3 + 2 * w2_b3_4 + 4 * w2_b3_5 + 8 * w2_b3_6 + 16 * w2_b3_7 + 32 * w2_b0_0 + 64 * w2_b0_1 + 128 * w2_b0_2),
        u8_from_field_unsafe(w2_b2_3 + 2 * w2_b2_4 + 4 * w2_b2_5 + 8 * w2_b2_6 + 16 * w2_b2_7 + 32 * w2_b3_0 + 64 * w2_b3_1 + 128 * w2_b3_2)
      ];

      -- shr10's top byte is the constant 0; only the three live bytes are
      -- materialized, and s1's byte 0 xors two operands instead of three.
      let w2_shr10 = [
        u8_from_field_unsafe(w2_b3_2 + 2 * w2_b3_3 + 4 * w2_b3_4 + 8 * w2_b3_5 + 16 * w2_b3_6 + 32 * w2_b3_7),
        u8_from_field_unsafe(w2_b2_2 + 2 * w2_b2_3 + 4 * w2_b2_4 + 8 * w2_b2_5 + 16 * w2_b2_6 + 32 * w2_b2_7 + 64 * w2_b3_0 + 128 * w2_b3_1),
        u8_from_field_unsafe(w2_b1_2 + 2 * w2_b1_3 + 4 * w2_b1_4 + 8 * w2_b1_5 + 16 * w2_b1_6 + 32 * w2_b1_7 + 64 * w2_b2_0 + 128 * w2_b2_1)
      ];

      let ws0 = [
        u8_xor(w15_rotr7[0], u8_xor(w15_rotr18[0], w15_shr3[0])),
        u8_xor(w15_rotr7[1], u8_xor(w15_rotr18[1], w15_shr3[1])),
        u8_xor(w15_rotr7[2], u8_xor(w15_rotr18[2], w15_shr3[2])),
        u8_xor(w15_rotr7[3], u8_xor(w15_rotr18[3], w15_shr3[3]))
      ];
      let ws1 = [
        u8_xor(w2_rotr17[0], w2_rotr19[0]),
        u8_xor(w2_rotr17[1], u8_xor(w2_rotr19[1], w2_shr10[0])),
        u8_xor(w2_rotr17[2], u8_xor(w2_rotr19[2], w2_shr10[1])),
        u8_xor(w2_rotr17[3], u8_xor(w2_rotr19[3], w2_shr10[2]))
      ];

      -- W_i = W_i-16 ⊞ s0 ⊞ W_i-7 ⊞ s1 (big-endian u8_add carry chains).
      let (ss0, ssc1) = u8_add(ws0[3], ws1[3]);
      let (sst1, sso1) = u8_add(ws0[2], ws1[2]);
      let (ss1, ssc1a) = u8_add(sst1, ssc1);
      let ssc2 = u8_from_field_unsafe(to_field(sso1) + to_field(ssc1a));
      let (sst2, sso2) = u8_add(ws0[1], ws1[1]);
      let (ss2, ssc2a) = u8_add(sst2, ssc2);
      let ssc3 = u8_from_field_unsafe(to_field(sso2) + to_field(ssc2a));
      let (sst3, _x) = u8_add(ws0[0], ws1[0]);
      let (ss3, _x) = u8_add(sst3, ssc3);

      let w16 = Wx[@i - 16];
      let w7 = Wx[@i - 7];
      let (ww0, wwc1) = u8_add(w16[3], w7[3]);
      let (wwt1, wwo1) = u8_add(w16[2], w7[2]);
      let (ww1, wwc1a) = u8_add(wwt1, wwc1);
      let wwc2 = u8_from_field_unsafe(to_field(wwo1) + to_field(wwc1a));
      let (wwt2, wwo2) = u8_add(w16[1], w7[1]);
      let (ww2, wwc2a) = u8_add(wwt2, wwc2);
      let wwc3 = u8_from_field_unsafe(to_field(wwo2) + to_field(wwc2a));
      let (wwt3, _x) = u8_add(w16[0], w7[0]);
      let (ww3, _x) = u8_add(wwt3, wwc3);

      let (wi0, wic1) = u8_add(ss0, ww0);
      let (wit1, wio1) = u8_add(ss1, ww1);
      let (wi1, wic1a) = u8_add(wit1, wic1);
      let wic2 = u8_from_field_unsafe(to_field(wio1) + to_field(wic1a));
      let (wit2, wio2) = u8_add(ss2, ww2);
      let (wi2, wic2a) = u8_add(wit2, wic2);
      let wic3 = u8_from_field_unsafe(to_field(wio2) + to_field(wic2a));
      let (wit3, _x) = u8_add(ss3, ww3);
      let (wi3, _x) = u8_add(wit3, wic3);
      set(Wx, @i, [wi3, wi2, wi1, wi0])
    );
    let W = Wx;

    let state_new = fold(0 .. 64, state, |acc, @i|
      let e_0_bits = u8_bit_decomposition(acc[4][3]);
      let e_1_bits = u8_bit_decomposition(acc[4][2]);
      let e_2_bits = u8_bit_decomposition(acc[4][1]);
      let e_3_bits = u8_bit_decomposition(acc[4][0]);

      -- Each rotated/shifted byte is the weighted sum of 8 bits. Written
      -- inline: it is pure arithmetic, so it costs no aux column or lookup.
      let e_rotr6 = [
        u8_from_field_unsafe(e_3_bits[6] + 2 * e_3_bits[7] + 4 * e_0_bits[0] + 8 * e_0_bits[1] + 16 * e_0_bits[2] + 32 * e_0_bits[3] + 64 * e_0_bits[4] + 128 * e_0_bits[5]),
        u8_from_field_unsafe(e_2_bits[6] + 2 * e_2_bits[7] + 4 * e_3_bits[0] + 8 * e_3_bits[1] + 16 * e_3_bits[2] + 32 * e_3_bits[3] + 64 * e_3_bits[4] + 128 * e_3_bits[5]),
        u8_from_field_unsafe(e_1_bits[6] + 2 * e_1_bits[7] + 4 * e_2_bits[0] + 8 * e_2_bits[1] + 16 * e_2_bits[2] + 32 * e_2_bits[3] + 64 * e_2_bits[4] + 128 * e_2_bits[5]),
        u8_from_field_unsafe(e_0_bits[6] + 2 * e_0_bits[7] + 4 * e_1_bits[0] + 8 * e_1_bits[1] + 16 * e_1_bits[2] + 32 * e_1_bits[3] + 64 * e_1_bits[4] + 128 * e_1_bits[5])
      ];

      let e_rotr11 = [
        u8_from_field_unsafe(e_0_bits[3] + 2 * e_0_bits[4] + 4 * e_0_bits[5] + 8 * e_0_bits[6] + 16 * e_0_bits[7] + 32 * e_1_bits[0] + 64 * e_1_bits[1] + 128 * e_1_bits[2]),
        u8_from_field_unsafe(e_3_bits[3] + 2 * e_3_bits[4] + 4 * e_3_bits[5] + 8 * e_3_bits[6] + 16 * e_3_bits[7] + 32 * e_0_bits[0] + 64 * e_0_bits[1] + 128 * e_0_bits[2]),
        u8_from_field_unsafe(e_2_bits[3] + 2 * e_2_bits[4] + 4 * e_2_bits[5] + 8 * e_2_bits[6] + 16 * e_2_bits[7] + 32 * e_3_bits[0] + 64 * e_3_bits[1] + 128 * e_3_bits[2]),
        u8_from_field_unsafe(e_1_bits[3] + 2 * e_1_bits[4] + 4 * e_1_bits[5] + 8 * e_1_bits[6] + 16 * e_1_bits[7] + 32 * e_2_bits[0] + 64 * e_2_bits[1] + 128 * e_2_bits[2])
      ];

      let e_rotr25 = [
        u8_from_field_unsafe(e_2_bits[1] + 2 * e_2_bits[2] + 4 * e_2_bits[3] + 8 * e_2_bits[4] + 16 * e_2_bits[5] + 32 * e_2_bits[6] + 64 * e_2_bits[7] + 128 * e_3_bits[0]),
        u8_from_field_unsafe(e_1_bits[1] + 2 * e_1_bits[2] + 4 * e_1_bits[3] + 8 * e_1_bits[4] + 16 * e_1_bits[5] + 32 * e_1_bits[6] + 64 * e_1_bits[7] + 128 * e_2_bits[0]),
        u8_from_field_unsafe(e_0_bits[1] + 2 * e_0_bits[2] + 4 * e_0_bits[3] + 8 * e_0_bits[4] + 16 * e_0_bits[5] + 32 * e_0_bits[6] + 64 * e_0_bits[7] + 128 * e_1_bits[0]),
        u8_from_field_unsafe(e_3_bits[1] + 2 * e_3_bits[2] + 4 * e_3_bits[3] + 8 * e_3_bits[4] + 16 * e_3_bits[5] + 32 * e_3_bits[6] + 64 * e_3_bits[7] + 128 * e_0_bits[0])
      ];

      let e_not = [u8_from_field_unsafe(255 - to_field(acc[4][0])), u8_from_field_unsafe(255 - to_field(acc[4][1])), u8_from_field_unsafe(255 - to_field(acc[4][2])), u8_from_field_unsafe(255 - to_field(acc[4][3]))];

      -- Word ops inlined as byte ops (1 aux + 1 lookup each): a call to a
      -- u32_* helper costs 4 output aux + 1 lookup here PLUS a row in the
      -- helper's 26-35-wide circuit — the byte ops are less than half that.
      let s1 = [
        u8_xor(e_rotr6[0], u8_xor(e_rotr11[0], e_rotr25[0])),
        u8_xor(e_rotr6[1], u8_xor(e_rotr11[1], e_rotr25[1])),
        u8_xor(e_rotr6[2], u8_xor(e_rotr11[2], e_rotr25[2])),
        u8_xor(e_rotr6[3], u8_xor(e_rotr11[3], e_rotr25[3]))
      ];
      let ch = [
        u8_xor(u8_and(acc[4][0], acc[5][0]), u8_and(e_not[0], acc[6][0])),
        u8_xor(u8_and(acc[4][1], acc[5][1]), u8_and(e_not[1], acc[6][1])),
        u8_xor(u8_and(acc[4][2], acc[5][2]), u8_and(e_not[2], acc[6][2])),
        u8_xor(u8_and(acc[4][3], acc[5][3]), u8_and(e_not[3], acc[6][3]))
      ];
      -- temp1 = h ⊞ s1 ⊞ ch ⊞ K[i] ⊞ W[i], big-endian byte-carry chains
      -- (index 3 = LSB; carry folding mirrors `u32_be_add`).
      let kw = K[@i];
      let wi = W[@i];
      let (kw0, kwc1) = u8_add(kw[3], wi[3]);
      let (kwt1, kwo1) = u8_add(kw[2], wi[2]);
      let (kw1, kwc1a) = u8_add(kwt1, kwc1);
      let kwc2 = u8_from_field_unsafe(to_field(kwo1) + to_field(kwc1a));
      let (kwt2, kwo2) = u8_add(kw[1], wi[1]);
      let (kw2, kwc2a) = u8_add(kwt2, kwc2);
      let kwc3 = u8_from_field_unsafe(to_field(kwo2) + to_field(kwc2a));
      let (kwt3, _x) = u8_add(kw[0], wi[0]);
      let (kw3, _x) = u8_add(kwt3, kwc3);

      let (sc0, scc1) = u8_add(s1[3], ch[3]);
      let (sct1, sco1) = u8_add(s1[2], ch[2]);
      let (sc1, scc1a) = u8_add(sct1, scc1);
      let scc2 = u8_from_field_unsafe(to_field(sco1) + to_field(scc1a));
      let (sct2, sco2) = u8_add(s1[1], ch[1]);
      let (sc2, scc2a) = u8_add(sct2, scc2);
      let scc3 = u8_from_field_unsafe(to_field(sco2) + to_field(scc2a));
      let (sct3, _x) = u8_add(s1[0], ch[0]);
      let (sc3, _x) = u8_add(sct3, scc3);

      let (hs0, hsc1) = u8_add(acc[7][3], sc0);
      let (hst1, hso1) = u8_add(acc[7][2], sc1);
      let (hs1, hsc1a) = u8_add(hst1, hsc1);
      let hsc2 = u8_from_field_unsafe(to_field(hso1) + to_field(hsc1a));
      let (hst2, hso2) = u8_add(acc[7][1], sc2);
      let (hs2, hsc2a) = u8_add(hst2, hsc2);
      let hsc3 = u8_from_field_unsafe(to_field(hso2) + to_field(hsc2a));
      let (hst3, _x) = u8_add(acc[7][0], sc3);
      let (hs3, _x) = u8_add(hst3, hsc3);

      let (t10, t1c1) = u8_add(hs0, kw0);
      let (t1t1, t1o1) = u8_add(hs1, kw1);
      let (t11, t1c1a) = u8_add(t1t1, t1c1);
      let t1c2 = u8_from_field_unsafe(to_field(t1o1) + to_field(t1c1a));
      let (t1t2, t1o2) = u8_add(hs2, kw2);
      let (t12, t1c2a) = u8_add(t1t2, t1c2);
      let t1c3 = u8_from_field_unsafe(to_field(t1o2) + to_field(t1c2a));
      let (t1t3, _x) = u8_add(hs3, kw3);
      let (t13, _x) = u8_add(t1t3, t1c3);

      let a_0_bits = u8_bit_decomposition(acc[0][3]);
      let a_1_bits = u8_bit_decomposition(acc[0][2]);
      let a_2_bits = u8_bit_decomposition(acc[0][1]);
      let a_3_bits = u8_bit_decomposition(acc[0][0]);

      let a_rotr2 = [
        u8_from_field_unsafe(a_3_bits[2] + 2 * a_3_bits[3] + 4 * a_3_bits[4] + 8 * a_3_bits[5] + 16 * a_3_bits[6] + 32 * a_3_bits[7] + 64 * a_0_bits[0] + 128 * a_0_bits[1]),
        u8_from_field_unsafe(a_2_bits[2] + 2 * a_2_bits[3] + 4 * a_2_bits[4] + 8 * a_2_bits[5] + 16 * a_2_bits[6] + 32 * a_2_bits[7] + 64 * a_3_bits[0] + 128 * a_3_bits[1]),
        u8_from_field_unsafe(a_1_bits[2] + 2 * a_1_bits[3] + 4 * a_1_bits[4] + 8 * a_1_bits[5] + 16 * a_1_bits[6] + 32 * a_1_bits[7] + 64 * a_2_bits[0] + 128 * a_2_bits[1]),
        u8_from_field_unsafe(a_0_bits[2] + 2 * a_0_bits[3] + 4 * a_0_bits[4] + 8 * a_0_bits[5] + 16 * a_0_bits[6] + 32 * a_0_bits[7] + 64 * a_1_bits[0] + 128 * a_1_bits[1])
      ];

      let a_rotr13 = [
        u8_from_field_unsafe(a_0_bits[5] + 2 * a_0_bits[6] + 4 * a_0_bits[7] + 8 * a_1_bits[0] + 16 * a_1_bits[1] + 32 * a_1_bits[2] + 64 * a_1_bits[3] + 128 * a_1_bits[4]),
        u8_from_field_unsafe(a_3_bits[5] + 2 * a_3_bits[6] + 4 * a_3_bits[7] + 8 * a_0_bits[0] + 16 * a_0_bits[1] + 32 * a_0_bits[2] + 64 * a_0_bits[3] + 128 * a_0_bits[4]),
        u8_from_field_unsafe(a_2_bits[5] + 2 * a_2_bits[6] + 4 * a_2_bits[7] + 8 * a_3_bits[0] + 16 * a_3_bits[1] + 32 * a_3_bits[2] + 64 * a_3_bits[3] + 128 * a_3_bits[4]),
        u8_from_field_unsafe(a_1_bits[5] + 2 * a_1_bits[6] + 4 * a_1_bits[7] + 8 * a_2_bits[0] + 16 * a_2_bits[1] + 32 * a_2_bits[2] + 64 * a_2_bits[3] + 128 * a_2_bits[4])
      ];

      let a_rotr22 = [
        u8_from_field_unsafe(a_1_bits[6] + 2 * a_1_bits[7] + 4 * a_2_bits[0] + 8 * a_2_bits[1] + 16 * a_2_bits[2] + 32 * a_2_bits[3] + 64 * a_2_bits[4] + 128 * a_2_bits[5]),
        u8_from_field_unsafe(a_0_bits[6] + 2 * a_0_bits[7] + 4 * a_1_bits[0] + 8 * a_1_bits[1] + 16 * a_1_bits[2] + 32 * a_1_bits[3] + 64 * a_1_bits[4] + 128 * a_1_bits[5]),
        u8_from_field_unsafe(a_3_bits[6] + 2 * a_3_bits[7] + 4 * a_0_bits[0] + 8 * a_0_bits[1] + 16 * a_0_bits[2] + 32 * a_0_bits[3] + 64 * a_0_bits[4] + 128 * a_0_bits[5]),
        u8_from_field_unsafe(a_2_bits[6] + 2 * a_2_bits[7] + 4 * a_3_bits[0] + 8 * a_3_bits[1] + 16 * a_3_bits[2] + 32 * a_3_bits[3] + 64 * a_3_bits[4] + 128 * a_3_bits[5])
      ];

      let s0 = [
        u8_xor(a_rotr2[0], u8_xor(a_rotr13[0], a_rotr22[0])),
        u8_xor(a_rotr2[1], u8_xor(a_rotr13[1], a_rotr22[1])),
        u8_xor(a_rotr2[2], u8_xor(a_rotr13[2], a_rotr22[2])),
        u8_xor(a_rotr2[3], u8_xor(a_rotr13[3], a_rotr22[3]))
      ];
      let maj = [
        u8_xor(u8_and(acc[0][0], acc[1][0]), u8_xor(u8_and(acc[0][0], acc[2][0]), u8_and(acc[1][0], acc[2][0]))),
        u8_xor(u8_and(acc[0][1], acc[1][1]), u8_xor(u8_and(acc[0][1], acc[2][1]), u8_and(acc[1][1], acc[2][1]))),
        u8_xor(u8_and(acc[0][2], acc[1][2]), u8_xor(u8_and(acc[0][2], acc[2][2]), u8_and(acc[1][2], acc[2][2]))),
        u8_xor(u8_and(acc[0][3], acc[1][3]), u8_xor(u8_and(acc[0][3], acc[2][3]), u8_and(acc[1][3], acc[2][3])))
      ];
      -- temp2 = s0 ⊞ maj
      let (t20, t2c1) = u8_add(s0[3], maj[3]);
      let (t2t1, t2o1) = u8_add(s0[2], maj[2]);
      let (t21, t2c1a) = u8_add(t2t1, t2c1);
      let t2c2 = u8_from_field_unsafe(to_field(t2o1) + to_field(t2c1a));
      let (t2t2, t2o2) = u8_add(s0[1], maj[1]);
      let (t22, t2c2a) = u8_add(t2t2, t2c2);
      let t2c3 = u8_from_field_unsafe(to_field(t2o2) + to_field(t2c2a));
      let (t2t3, _x) = u8_add(s0[0], maj[0]);
      let (t23, _x) = u8_add(t2t3, t2c3);

      -- a' = temp1 ⊞ temp2
      let (na0, nac1) = u8_add(t10, t20);
      let (nat1, nao1) = u8_add(t11, t21);
      let (na1, nac1a) = u8_add(nat1, nac1);
      let nac2 = u8_from_field_unsafe(to_field(nao1) + to_field(nac1a));
      let (nat2, nao2) = u8_add(t12, t22);
      let (na2, nac2a) = u8_add(nat2, nac2);
      let nac3 = u8_from_field_unsafe(to_field(nao2) + to_field(nac2a));
      let (nat3, _x) = u8_add(t13, t23);
      let (na3, _x) = u8_add(nat3, nac3);

      -- e' = d ⊞ temp1
      let (ne0, nec1) = u8_add(acc[3][3], t10);
      let (net1, neo1) = u8_add(acc[3][2], t11);
      let (ne1, nec1a) = u8_add(net1, nec1);
      let nec2 = u8_from_field_unsafe(to_field(neo1) + to_field(nec1a));
      let (net2, neo2) = u8_add(acc[3][1], t12);
      let (ne2, nec2a) = u8_add(net2, nec2);
      let nec3 = u8_from_field_unsafe(to_field(neo2) + to_field(nec2a));
      let (net3, _x) = u8_add(acc[3][0], t13);
      let (ne3, _x) = u8_add(net3, nec3);

      [[na3, na2, na1, na0], acc[0], acc[1], acc[2], [ne3, ne2, ne1, ne0], acc[4], acc[5], acc[6]]
    );

    -- Final Davies-Meyer state addition, inlined per word via the same
    -- big-endian u8_add carry chains as the round body.
    let fs = fold(0 .. 8, [[0u8; 4]; 8], |fs, @j|
      let sw = state[@j];
      let nw = state_new[@j];
      let (f0, fc1) = u8_add(sw[3], nw[3]);
      let (ft1, fo1) = u8_add(sw[2], nw[2]);
      let (f1, fc1a) = u8_add(ft1, fc1);
      let fc2 = u8_from_field_unsafe(to_field(fo1) + to_field(fc1a));
      let (ft2, fo2) = u8_add(sw[1], nw[1]);
      let (f2, fc2a) = u8_add(ft2, fc2);
      let fc3 = u8_from_field_unsafe(to_field(fo2) + to_field(fc2a));
      let (ft3, _x) = u8_add(sw[0], nw[0]);
      let (f3, _x) = u8_add(ft3, fc3);
      set(fs, @j, [f3, f2, f1, f0])
    );
    fs
  }
⟧

end IxVM

end
