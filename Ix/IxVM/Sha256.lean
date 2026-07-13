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

  /- # Word-op helpers (all `@`-inlined into the round / schedule folds). -/

  -- Big-endian 32-bit add (index 3 = LSB); mutually-exclusive carries fold
  -- with a free field `+`.
  fn u32_be_add(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    let (s0, c1) = u8_add(a[3], b[3]);
    let (t1, o1) = u8_add(a[2], b[2]);
    let (s1, c1a) = u8_add(t1, c1);
    let c2 = u8_from_field_unsafe(to_field(o1) + to_field(c1a));
    let (t2, o2) = u8_add(a[1], b[1]);
    let (s2, c2a) = u8_add(t2, c2);
    let c3 = u8_from_field_unsafe(to_field(o2) + to_field(c2a));
    let (t3, _x) = u8_add(a[0], b[0]);
    let (s3, _x) = u8_add(t3, c3);
    [s3, s2, s1, s0]
  }

  -- Big-endian sum of four 32-bit words in one carry-propagation pass. Each
  -- byte column is accumulated with chained `u8_add` (running partial stays
  -- < 256); the 0/1 carry bits fold into the next column with a free field
  -- add. 15 `u8_add`s vs 21 for three chained `u32_be_add`s. The column carry
  -- is floor(column_sum / 256) <= 3 (< 256), so feeding it to `u8_add` is safe.
  fn u32_be_add4(a: [U8; 4], b: [U8; 4], c: [U8; 4], d: [U8; 4]) -> [U8; 4] {
    let (t, k1) = u8_add(a[3], b[3]);
    let (t, k2) = u8_add(t, c[3]);
    let (s0, k3) = u8_add(t, d[3]);
    let cy = u8_from_field_unsafe(to_field(k1) + to_field(k2) + to_field(k3));
    let (t, k1) = u8_add(a[2], b[2]);
    let (t, k2) = u8_add(t, c[2]);
    let (t, k3) = u8_add(t, d[2]);
    let (s1, k4) = u8_add(t, cy);
    let cy = u8_from_field_unsafe(to_field(k1) + to_field(k2) + to_field(k3) + to_field(k4));
    let (t, k1) = u8_add(a[1], b[1]);
    let (t, k2) = u8_add(t, c[1]);
    let (t, k3) = u8_add(t, d[1]);
    let (s2, k4) = u8_add(t, cy);
    let cy = u8_from_field_unsafe(to_field(k1) + to_field(k2) + to_field(k3) + to_field(k4));
    let (t, _x) = u8_add(a[0], b[0]);
    let (t, _x) = u8_add(t, c[0]);
    let (t, _x) = u8_add(t, d[0]);
    let (s3, _x) = u8_add(t, cy);
    [s3, s2, s1, s0]
  }

  -- Big-endian sum of five 32-bit words in one carry pass (as `u32_be_add4`).
  -- 19 `u8_add`s vs 28 for four chained `u32_be_add`s. Column carry is
  -- floor(column_sum / 256) <= 4 (< 256).
  fn u32_be_add5(a: [U8; 4], b: [U8; 4], c: [U8; 4], d: [U8; 4], e: [U8; 4]) -> [U8; 4] {
    let (t, k1) = u8_add(a[3], b[3]);
    let (t, k2) = u8_add(t, c[3]);
    let (t, k3) = u8_add(t, d[3]);
    let (s0, k4) = u8_add(t, e[3]);
    let cy = u8_from_field_unsafe(to_field(k1) + to_field(k2) + to_field(k3) + to_field(k4));
    let (t, k1) = u8_add(a[2], b[2]);
    let (t, k2) = u8_add(t, c[2]);
    let (t, k3) = u8_add(t, d[2]);
    let (t, k4) = u8_add(t, e[2]);
    let (s1, k5) = u8_add(t, cy);
    let cy = u8_from_field_unsafe(to_field(k1) + to_field(k2) + to_field(k3) + to_field(k4) + to_field(k5));
    let (t, k1) = u8_add(a[1], b[1]);
    let (t, k2) = u8_add(t, c[1]);
    let (t, k3) = u8_add(t, d[1]);
    let (t, k4) = u8_add(t, e[1]);
    let (s2, k5) = u8_add(t, cy);
    let cy = u8_from_field_unsafe(to_field(k1) + to_field(k2) + to_field(k3) + to_field(k4) + to_field(k5));
    let (t, _x) = u8_add(a[0], b[0]);
    let (t, _x) = u8_add(t, c[0]);
    let (t, _x) = u8_add(t, d[0]);
    let (t, _x) = u8_add(t, e[0]);
    let (s3, _x) = u8_add(t, cy);
    [s3, s2, s1, s0]
  }

  fn u32_xor(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    [u8_xor(a[0], b[0]), u8_xor(a[1], b[1]), u8_xor(a[2], b[2]), u8_xor(a[3], b[3])]
  }

  fn u32_and(a: [U8; 4], b: [U8; 4]) -> [U8; 4] {
    [u8_and(a[0], b[0]), u8_and(a[1], b[1]), u8_and(a[2], b[2]), u8_and(a[3], b[3])]
  }

  fn u32_not(a: [U8; 4]) -> [U8; 4] {
    [u8_from_field_unsafe(255 - to_field(a[0])), u8_from_field_unsafe(255 - to_field(a[1])),
     u8_from_field_unsafe(255 - to_field(a[2])), u8_from_field_unsafe(255 - to_field(a[3]))]
  }

  -- ch = (e & f) ^ (~e & g). The two ands are bitwise-disjoint (one needs the
  -- e bit set, the other clear), so the xor is a free field add (no lookup).
  fn ch(e: [U8; 4], f: [U8; 4], g: [U8; 4]) -> [U8; 4] {
    let ef = @u32_and(e, f);
    let neg = @u32_and(@u32_not(e), g);
    [u8_from_field_unsafe(to_field(ef[0]) + to_field(neg[0])),
     u8_from_field_unsafe(to_field(ef[1]) + to_field(neg[1])),
     u8_from_field_unsafe(to_field(ef[2]) + to_field(neg[2])),
     u8_from_field_unsafe(to_field(ef[3]) + to_field(neg[3]))]
  }

  -- maj = (a & b) ^ (a & c) ^ (b & c) = (a & b) + (c & (a ^ b)). `a ^ b` is the
  -- free recomposition (a + b) - 2·(a & b); the two final terms are disjoint
  -- (a = b ⇒ second is 0, a ≠ b ⇒ first is 0), so their xor is a free add too.
  -- Two ands instead of three ands + two xors.
  fn maj(a: [U8; 4], b: [U8; 4], c: [U8; 4]) -> [U8; 4] {
    let ab = @u32_and(a, b);
    let axb = [u8_from_field_unsafe((to_field(a[0]) + to_field(b[0])) - 2 * to_field(ab[0])),
               u8_from_field_unsafe((to_field(a[1]) + to_field(b[1])) - 2 * to_field(ab[1])),
               u8_from_field_unsafe((to_field(a[2]) + to_field(b[2])) - 2 * to_field(ab[2])),
               u8_from_field_unsafe((to_field(a[3]) + to_field(b[3])) - 2 * to_field(ab[3]))];
    let cx = @u32_and(c, axb);
    [u8_from_field_unsafe(to_field(ab[0]) + to_field(cx[0])),
     u8_from_field_unsafe(to_field(ab[1]) + to_field(cx[1])),
     u8_from_field_unsafe(to_field(ab[2]) + to_field(cx[2])),
     u8_from_field_unsafe(to_field(ab[3]) + to_field(cx[3]))]
  }

  -- The four SHA-256 sigmas. Each decomposes its word's bytes ONCE (b0 =
  -- LSB byte w[3] .. b3 = MSB byte w[0]) and recomposes the rotations as
  -- weighted bit sums (pure arithmetic: no aux/lookup), then xors them.

  -- Sigma1(e) = rotr6 ^ rotr11 ^ rotr25.
  fn big_sigma1(w: [U8; 4]) -> [U8; 4] {
    let b0 = u8_bit_decomposition(w[3]);
    let b1 = u8_bit_decomposition(w[2]);
    let b2 = u8_bit_decomposition(w[1]);
    let b3 = u8_bit_decomposition(w[0]);
    let r6 = [
      u8_from_field_unsafe(b3[6] + 2 * b3[7] + 4 * b0[0] + 8 * b0[1] + 16 * b0[2] + 32 * b0[3] + 64 * b0[4] + 128 * b0[5]),
      u8_from_field_unsafe(b2[6] + 2 * b2[7] + 4 * b3[0] + 8 * b3[1] + 16 * b3[2] + 32 * b3[3] + 64 * b3[4] + 128 * b3[5]),
      u8_from_field_unsafe(b1[6] + 2 * b1[7] + 4 * b2[0] + 8 * b2[1] + 16 * b2[2] + 32 * b2[3] + 64 * b2[4] + 128 * b2[5]),
      u8_from_field_unsafe(b0[6] + 2 * b0[7] + 4 * b1[0] + 8 * b1[1] + 16 * b1[2] + 32 * b1[3] + 64 * b1[4] + 128 * b1[5])
    ];
    let r11 = [
      u8_from_field_unsafe(b0[3] + 2 * b0[4] + 4 * b0[5] + 8 * b0[6] + 16 * b0[7] + 32 * b1[0] + 64 * b1[1] + 128 * b1[2]),
      u8_from_field_unsafe(b3[3] + 2 * b3[4] + 4 * b3[5] + 8 * b3[6] + 16 * b3[7] + 32 * b0[0] + 64 * b0[1] + 128 * b0[2]),
      u8_from_field_unsafe(b2[3] + 2 * b2[4] + 4 * b2[5] + 8 * b2[6] + 16 * b2[7] + 32 * b3[0] + 64 * b3[1] + 128 * b3[2]),
      u8_from_field_unsafe(b1[3] + 2 * b1[4] + 4 * b1[5] + 8 * b1[6] + 16 * b1[7] + 32 * b2[0] + 64 * b2[1] + 128 * b2[2])
    ];
    let r25 = [
      u8_from_field_unsafe(b2[1] + 2 * b2[2] + 4 * b2[3] + 8 * b2[4] + 16 * b2[5] + 32 * b2[6] + 64 * b2[7] + 128 * b3[0]),
      u8_from_field_unsafe(b1[1] + 2 * b1[2] + 4 * b1[3] + 8 * b1[4] + 16 * b1[5] + 32 * b1[6] + 64 * b1[7] + 128 * b2[0]),
      u8_from_field_unsafe(b0[1] + 2 * b0[2] + 4 * b0[3] + 8 * b0[4] + 16 * b0[5] + 32 * b0[6] + 64 * b0[7] + 128 * b1[0]),
      u8_from_field_unsafe(b3[1] + 2 * b3[2] + 4 * b3[3] + 8 * b3[4] + 16 * b3[5] + 32 * b3[6] + 64 * b3[7] + 128 * b0[0])
    ];
    @u32_xor(r6, @u32_xor(r11, r25))
  }

  -- Sigma0(a) = rotr2 ^ rotr13 ^ rotr22.
  fn big_sigma0(w: [U8; 4]) -> [U8; 4] {
    let b0 = u8_bit_decomposition(w[3]);
    let b1 = u8_bit_decomposition(w[2]);
    let b2 = u8_bit_decomposition(w[1]);
    let b3 = u8_bit_decomposition(w[0]);
    let r2 = [
      u8_from_field_unsafe(b3[2] + 2 * b3[3] + 4 * b3[4] + 8 * b3[5] + 16 * b3[6] + 32 * b3[7] + 64 * b0[0] + 128 * b0[1]),
      u8_from_field_unsafe(b2[2] + 2 * b2[3] + 4 * b2[4] + 8 * b2[5] + 16 * b2[6] + 32 * b2[7] + 64 * b3[0] + 128 * b3[1]),
      u8_from_field_unsafe(b1[2] + 2 * b1[3] + 4 * b1[4] + 8 * b1[5] + 16 * b1[6] + 32 * b1[7] + 64 * b2[0] + 128 * b2[1]),
      u8_from_field_unsafe(b0[2] + 2 * b0[3] + 4 * b0[4] + 8 * b0[5] + 16 * b0[6] + 32 * b0[7] + 64 * b1[0] + 128 * b1[1])
    ];
    let r13 = [
      u8_from_field_unsafe(b0[5] + 2 * b0[6] + 4 * b0[7] + 8 * b1[0] + 16 * b1[1] + 32 * b1[2] + 64 * b1[3] + 128 * b1[4]),
      u8_from_field_unsafe(b3[5] + 2 * b3[6] + 4 * b3[7] + 8 * b0[0] + 16 * b0[1] + 32 * b0[2] + 64 * b0[3] + 128 * b0[4]),
      u8_from_field_unsafe(b2[5] + 2 * b2[6] + 4 * b2[7] + 8 * b3[0] + 16 * b3[1] + 32 * b3[2] + 64 * b3[3] + 128 * b3[4]),
      u8_from_field_unsafe(b1[5] + 2 * b1[6] + 4 * b1[7] + 8 * b2[0] + 16 * b2[1] + 32 * b2[2] + 64 * b2[3] + 128 * b2[4])
    ];
    let r22 = [
      u8_from_field_unsafe(b1[6] + 2 * b1[7] + 4 * b2[0] + 8 * b2[1] + 16 * b2[2] + 32 * b2[3] + 64 * b2[4] + 128 * b2[5]),
      u8_from_field_unsafe(b0[6] + 2 * b0[7] + 4 * b1[0] + 8 * b1[1] + 16 * b1[2] + 32 * b1[3] + 64 * b1[4] + 128 * b1[5]),
      u8_from_field_unsafe(b3[6] + 2 * b3[7] + 4 * b0[0] + 8 * b0[1] + 16 * b0[2] + 32 * b0[3] + 64 * b0[4] + 128 * b0[5]),
      u8_from_field_unsafe(b2[6] + 2 * b2[7] + 4 * b3[0] + 8 * b3[1] + 16 * b3[2] + 32 * b3[3] + 64 * b3[4] + 128 * b3[5])
    ];
    @u32_xor(r2, @u32_xor(r13, r22))
  }

  -- sigma0(w) = rotr7 ^ rotr18 ^ shr3.
  fn small_sigma0(w: [U8; 4]) -> [U8; 4] {
    let b0 = u8_bit_decomposition(w[3]);
    let b1 = u8_bit_decomposition(w[2]);
    let b2 = u8_bit_decomposition(w[1]);
    let b3 = u8_bit_decomposition(w[0]);
    let r7 = [
      u8_from_field_unsafe(b3[7] + 2 * b0[0] + 4 * b0[1] + 8 * b0[2] + 16 * b0[3] + 32 * b0[4] + 64 * b0[5] + 128 * b0[6]),
      u8_from_field_unsafe(b2[7] + 2 * b3[0] + 4 * b3[1] + 8 * b3[2] + 16 * b3[3] + 32 * b3[4] + 64 * b3[5] + 128 * b3[6]),
      u8_from_field_unsafe(b1[7] + 2 * b2[0] + 4 * b2[1] + 8 * b2[2] + 16 * b2[3] + 32 * b2[4] + 64 * b2[5] + 128 * b2[6]),
      u8_from_field_unsafe(b0[7] + 2 * b1[0] + 4 * b1[1] + 8 * b1[2] + 16 * b1[3] + 32 * b1[4] + 64 * b1[5] + 128 * b1[6])
    ];
    let r18 = [
      u8_from_field_unsafe(b1[2] + 2 * b1[3] + 4 * b1[4] + 8 * b1[5] + 16 * b1[6] + 32 * b1[7] + 64 * b2[0] + 128 * b2[1]),
      u8_from_field_unsafe(b0[2] + 2 * b0[3] + 4 * b0[4] + 8 * b0[5] + 16 * b0[6] + 32 * b0[7] + 64 * b1[0] + 128 * b1[1]),
      u8_from_field_unsafe(b3[2] + 2 * b3[3] + 4 * b3[4] + 8 * b3[5] + 16 * b3[6] + 32 * b3[7] + 64 * b0[0] + 128 * b0[1]),
      u8_from_field_unsafe(b2[2] + 2 * b2[3] + 4 * b2[4] + 8 * b2[5] + 16 * b2[6] + 32 * b2[7] + 64 * b3[0] + 128 * b3[1])
    ];
    let s3 = [
      u8_from_field_unsafe(b3[3] + 2 * b3[4] + 4 * b3[5] + 8 * b3[6] + 16 * b3[7]),
      u8_from_field_unsafe(b2[3] + 2 * b2[4] + 4 * b2[5] + 8 * b2[6] + 16 * b2[7] + 32 * b3[0] + 64 * b3[1] + 128 * b3[2]),
      u8_from_field_unsafe(b1[3] + 2 * b1[4] + 4 * b1[5] + 8 * b1[6] + 16 * b1[7] + 32 * b2[0] + 64 * b2[1] + 128 * b2[2]),
      u8_from_field_unsafe(b0[3] + 2 * b0[4] + 4 * b0[5] + 8 * b0[6] + 16 * b0[7] + 32 * b1[0] + 64 * b1[1] + 128 * b1[2])
    ];
    @u32_xor(r7, @u32_xor(r18, s3))
  }

  -- sigma1(w) = rotr17 ^ rotr19 ^ shr10. shr10's top byte is the constant
  -- 0, so byte 0 of the result xors only two operands.
  fn small_sigma1(w: [U8; 4]) -> [U8; 4] {
    let b0 = u8_bit_decomposition(w[3]);
    let b1 = u8_bit_decomposition(w[2]);
    let b2 = u8_bit_decomposition(w[1]);
    let b3 = u8_bit_decomposition(w[0]);
    let r17 = [
      u8_from_field_unsafe(b1[1] + 2 * b1[2] + 4 * b1[3] + 8 * b1[4] + 16 * b1[5] + 32 * b1[6] + 64 * b1[7] + 128 * b2[0]),
      u8_from_field_unsafe(b0[1] + 2 * b0[2] + 4 * b0[3] + 8 * b0[4] + 16 * b0[5] + 32 * b0[6] + 64 * b0[7] + 128 * b1[0]),
      u8_from_field_unsafe(b3[1] + 2 * b3[2] + 4 * b3[3] + 8 * b3[4] + 16 * b3[5] + 32 * b3[6] + 64 * b3[7] + 128 * b0[0]),
      u8_from_field_unsafe(b2[1] + 2 * b2[2] + 4 * b2[3] + 8 * b2[4] + 16 * b2[5] + 32 * b2[6] + 64 * b2[7] + 128 * b3[0])
    ];
    let r19 = [
      u8_from_field_unsafe(b1[3] + 2 * b1[4] + 4 * b1[5] + 8 * b1[6] + 16 * b1[7] + 32 * b2[0] + 64 * b2[1] + 128 * b2[2]),
      u8_from_field_unsafe(b0[3] + 2 * b0[4] + 4 * b0[5] + 8 * b0[6] + 16 * b0[7] + 32 * b1[0] + 64 * b1[1] + 128 * b1[2]),
      u8_from_field_unsafe(b3[3] + 2 * b3[4] + 4 * b3[5] + 8 * b3[6] + 16 * b3[7] + 32 * b0[0] + 64 * b0[1] + 128 * b0[2]),
      u8_from_field_unsafe(b2[3] + 2 * b2[4] + 4 * b2[5] + 8 * b2[6] + 16 * b2[7] + 32 * b3[0] + 64 * b3[1] + 128 * b3[2])
    ];
    let s10 = [
      u8_from_field_unsafe(b3[2] + 2 * b3[3] + 4 * b3[4] + 8 * b3[5] + 16 * b3[6] + 32 * b3[7]),
      u8_from_field_unsafe(b2[2] + 2 * b2[3] + 4 * b2[4] + 8 * b2[5] + 16 * b2[6] + 32 * b2[7] + 64 * b3[0] + 128 * b3[1]),
      u8_from_field_unsafe(b1[2] + 2 * b1[3] + 4 * b1[4] + 8 * b1[5] + 16 * b1[6] + 32 * b1[7] + 64 * b2[0] + 128 * b2[1])
    ];
    [u8_xor(r17[0], r19[0]),
     u8_xor(r17[1], u8_xor(r19[1], s10[0])),
     u8_xor(r17[2], u8_xor(r19[2], s10[1])),
     u8_xor(r17[3], u8_xor(r19[3], s10[2]))]
  }

  -- One message-schedule word: W_i = W_16 + sigma0(W_15) + W_7 + sigma1(W_2).
  -- A call (not `@`-inlined) so the 48 schedule words share one circuit
  -- instead of widening the block circuit 48-fold.
  fn sha256_schedule(w16: [U8; 4], w15: [U8; 4], w7: [U8; 4], w2: [U8; 4]) -> [U8; 4] {
    let s0 = @small_sigma0(w15);
    let s1 = @small_sigma1(w2);
    @u32_be_add4(w16, s0, w7, s1)
  }

  -- One compression round. Called (not `@`-inlined) so the 64 rounds share
  -- one circuit run as 64 rows, keeping the block circuit narrow -- the
  -- sigma/ch/maj/add helpers stay inlined within this round.
  fn sha256_round(acc: [[U8; 4]; 8], ki: [U8; 4], wi: [U8; 4]) -> [[U8; 4]; 8] {
    let s1 = @big_sigma1(acc[4]);
    let ch_efg = @ch(acc[4], acc[5], acc[6]);
    let temp1 = @u32_be_add5(acc[7], s1, ch_efg, ki, wi);
    let s0 = @big_sigma0(acc[0]);
    let maj_abc = @maj(acc[0], acc[1], acc[2]);
    let temp2 = @u32_be_add(s0, maj_abc);
    [@u32_be_add(temp1, temp2), acc[0], acc[1], acc[2],
     @u32_be_add(acc[3], temp1), acc[4], acc[5], acc[6]]
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
      -- W_i = W_i-16 + sigma0(W_i-15) + W_i-7 + sigma1(W_i-2).
      let w15 = Wx[@i - 15];
      let w2 = Wx[@i - 2];
      let w16 = Wx[@i - 16];
      let w7 = Wx[@i - 7];
      set(Wx, @i, sha256_schedule(w16, w15, w7, w2))
    );
    let W = Wx;

    let state_new = fold(0 .. 64, state, |acc, @i|
      -- acc = [a,b,c,d,e,f,g,h]; K[i], W[i] are the round constant and word.
      let ki = K[@i];
      let wi = W[@i];
      sha256_round(acc, ki, wi)
    );

    let fs = fold(0 .. 8, [[0u8; 4]; 8], |fs, @j|
      let sw = state[@j];
      let nw = state_new[@j];
      set(fs, @j, @u32_be_add(sw, nw))
    );
    fs
  }
⟧

end IxVM

end
