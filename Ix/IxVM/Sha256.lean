module
public import Ix.Aiur.Meta

public section

namespace IxVM

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

    let W_16 = define_W_i(W[14], W[9],  W[1],  W[0]);
    let W_17 = define_W_i(W[15], W[10], W[2],  W[1]);
    let W_18 = define_W_i(W_16,  W[11], W[3],  W[2]);
    let W_19 = define_W_i(W_17,  W[12], W[4],  W[3]);
    let W_20 = define_W_i(W_18,  W[13], W[5],  W[4]);
    let W_21 = define_W_i(W_19,  W[14], W[6],  W[5]);
    let W_22 = define_W_i(W_20,  W[15], W[7],  W[6]);
    let W_23 = define_W_i(W_21,  W_16,  W[8],  W[7]);
    let W_24 = define_W_i(W_22,  W_17,  W[9],  W[8]);
    let W_25 = define_W_i(W_23,  W_18,  W[10], W[9]);
    let W_26 = define_W_i(W_24,  W_19,  W[11], W[10]);
    let W_27 = define_W_i(W_25,  W_20,  W[12], W[11]);
    let W_28 = define_W_i(W_26,  W_21,  W[13], W[12]);
    let W_29 = define_W_i(W_27,  W_22,  W[14], W[13]);
    let W_30 = define_W_i(W_28,  W_23,  W[15], W[14]);
    let W_31 = define_W_i(W_29,  W_24,  W_16,  W[15]);
    let W_32 = define_W_i(W_30,  W_25,  W_17,  W_16);
    let W_33 = define_W_i(W_31,  W_26,  W_18,  W_17);
    let W_34 = define_W_i(W_32,  W_27,  W_19,  W_18);
    let W_35 = define_W_i(W_33,  W_28,  W_20,  W_19);
    let W_36 = define_W_i(W_34,  W_29,  W_21,  W_20);
    let W_37 = define_W_i(W_35,  W_30,  W_22,  W_21);
    let W_38 = define_W_i(W_36,  W_31,  W_23,  W_22);
    let W_39 = define_W_i(W_37,  W_32,  W_24,  W_23);
    let W_40 = define_W_i(W_38,  W_33,  W_25,  W_24);
    let W_41 = define_W_i(W_39,  W_34,  W_26,  W_25);
    let W_42 = define_W_i(W_40,  W_35,  W_27,  W_26);
    let W_43 = define_W_i(W_41,  W_36,  W_28,  W_27);
    let W_44 = define_W_i(W_42,  W_37,  W_29,  W_28);
    let W_45 = define_W_i(W_43,  W_38,  W_30,  W_29);
    let W_46 = define_W_i(W_44,  W_39,  W_31,  W_30);
    let W_47 = define_W_i(W_45,  W_40,  W_32,  W_31);
    let W_48 = define_W_i(W_46,  W_41,  W_33,  W_32);
    let W_49 = define_W_i(W_47,  W_42,  W_34,  W_33);
    let W_50 = define_W_i(W_48,  W_43,  W_35,  W_34);
    let W_51 = define_W_i(W_49,  W_44,  W_36,  W_35);
    let W_52 = define_W_i(W_50,  W_45,  W_37,  W_36);
    let W_53 = define_W_i(W_51,  W_46,  W_38,  W_37);
    let W_54 = define_W_i(W_52,  W_47,  W_39,  W_38);
    let W_55 = define_W_i(W_53,  W_48,  W_40,  W_39);
    let W_56 = define_W_i(W_54,  W_49,  W_41,  W_40);
    let W_57 = define_W_i(W_55,  W_50,  W_42,  W_41);
    let W_58 = define_W_i(W_56,  W_51,  W_43,  W_42);
    let W_59 = define_W_i(W_57,  W_52,  W_44,  W_43);
    let W_60 = define_W_i(W_58,  W_53,  W_45,  W_44);
    let W_61 = define_W_i(W_59,  W_54,  W_46,  W_45);
    let W_62 = define_W_i(W_60,  W_55,  W_47,  W_46);
    let W_63 = define_W_i(W_61,  W_56,  W_48,  W_47);

    let W = [
      W[0], W[1], W[2],  W[3],  W[4],  W[5],  W[6],  W[7],
      W[8], W[9], W[10], W[11], W[12], W[13], W[14], W[15],
      W_16, W_17, W_18,  W_19,  W_20,  W_21,  W_22,  W_23,
      W_24, W_25, W_26,  W_27,  W_28,  W_29,  W_30,  W_31,
      W_32, W_33, W_34,  W_35,  W_36,  W_37,  W_38,  W_39,
      W_40, W_41, W_42,  W_43,  W_44,  W_45,  W_46,  W_47,
      W_48, W_49, W_50,  W_51,  W_52,  W_53,  W_54,  W_55,
      W_56, W_57, W_58,  W_59,  W_60,  W_61,  W_62,  W_63
    ];

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

      let s1 = u32_xor(e_rotr6, u32_xor(e_rotr11, e_rotr25));
      let ch = u32_xor(u32_and(acc[4], acc[5]), u32_and(e_not, acc[6]));
      let temp1 = u32_be_add(acc[7], u32_be_add(s1, u32_be_add(ch, u32_be_add(K[@i], W[@i]))));

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

      let s0 = u32_xor(a_rotr2, u32_xor(a_rotr13, a_rotr22));
      let maj = u32_xor(u32_and(acc[0], acc[1]), u32_xor(u32_and(acc[0], acc[2]), u32_and(acc[1], acc[2])));
      let temp2 = u32_be_add(s0, maj);

      [u32_be_add(temp1, temp2), acc[0], acc[1], acc[2], u32_be_add(acc[3], temp1), acc[4], acc[5], acc[6]]
    );

    [
      u32_be_add(state[0], state_new[0]),
      u32_be_add(state[1], state_new[1]),
      u32_be_add(state[2], state_new[2]),
      u32_be_add(state[3], state_new[3]),
      u32_be_add(state[4], state_new[4]),
      u32_be_add(state[5], state_new[5]),
      u32_be_add(state[6], state_new[6]),
      u32_be_add(state[7], state_new[7])
    ]
  }

  fn define_W_i(«W_i-2»: [U8; 4], «W_i-7»: [U8; 4], «W_i-15»: [U8; 4], «W_i-16»: [U8; 4]) -> [U8; 4] {
    let [«W_i-15_b3», «W_i-15_b2», «W_i-15_b1», «W_i-15_b0»] = «W_i-15»;
    let [«W_i-15_b0_0», «W_i-15_b0_1», «W_i-15_b0_2», «W_i-15_b0_3», «W_i-15_b0_4», «W_i-15_b0_5», «W_i-15_b0_6», «W_i-15_b0_7»] = u8_bit_decomposition(«W_i-15_b0»);
    let [«W_i-15_b1_0», «W_i-15_b1_1», «W_i-15_b1_2», «W_i-15_b1_3», «W_i-15_b1_4», «W_i-15_b1_5», «W_i-15_b1_6», «W_i-15_b1_7»] = u8_bit_decomposition(«W_i-15_b1»);
    let [«W_i-15_b2_0», «W_i-15_b2_1», «W_i-15_b2_2», «W_i-15_b2_3», «W_i-15_b2_4», «W_i-15_b2_5», «W_i-15_b2_6», «W_i-15_b2_7»] = u8_bit_decomposition(«W_i-15_b2»);
    let [«W_i-15_b3_0», «W_i-15_b3_1», «W_i-15_b3_2», «W_i-15_b3_3», «W_i-15_b3_4», «W_i-15_b3_5», «W_i-15_b3_6», «W_i-15_b3_7»] = u8_bit_decomposition(«W_i-15_b3»);

    let «W_i-15_rotr7» = [
      u8_from_field_unsafe(«W_i-15_b3_7» + 2 * «W_i-15_b0_0» + 4 * «W_i-15_b0_1» + 8 * «W_i-15_b0_2» + 16 * «W_i-15_b0_3» + 32 * «W_i-15_b0_4» + 64 * «W_i-15_b0_5» + 128 * «W_i-15_b0_6»),
      u8_from_field_unsafe(«W_i-15_b2_7» + 2 * «W_i-15_b3_0» + 4 * «W_i-15_b3_1» + 8 * «W_i-15_b3_2» + 16 * «W_i-15_b3_3» + 32 * «W_i-15_b3_4» + 64 * «W_i-15_b3_5» + 128 * «W_i-15_b3_6»),
      u8_from_field_unsafe(«W_i-15_b1_7» + 2 * «W_i-15_b2_0» + 4 * «W_i-15_b2_1» + 8 * «W_i-15_b2_2» + 16 * «W_i-15_b2_3» + 32 * «W_i-15_b2_4» + 64 * «W_i-15_b2_5» + 128 * «W_i-15_b2_6»),
      u8_from_field_unsafe(«W_i-15_b0_7» + 2 * «W_i-15_b1_0» + 4 * «W_i-15_b1_1» + 8 * «W_i-15_b1_2» + 16 * «W_i-15_b1_3» + 32 * «W_i-15_b1_4» + 64 * «W_i-15_b1_5» + 128 * «W_i-15_b1_6»)
    ];

    let «W_i-15_rotr18» = [
      u8_from_field_unsafe(«W_i-15_b1_2» + 2 * «W_i-15_b1_3» + 4 * «W_i-15_b1_4» + 8 * «W_i-15_b1_5» + 16 * «W_i-15_b1_6» + 32 * «W_i-15_b1_7» + 64 * «W_i-15_b2_0» + 128 * «W_i-15_b2_1»),
      u8_from_field_unsafe(«W_i-15_b0_2» + 2 * «W_i-15_b0_3» + 4 * «W_i-15_b0_4» + 8 * «W_i-15_b0_5» + 16 * «W_i-15_b0_6» + 32 * «W_i-15_b0_7» + 64 * «W_i-15_b1_0» + 128 * «W_i-15_b1_1»),
      u8_from_field_unsafe(«W_i-15_b3_2» + 2 * «W_i-15_b3_3» + 4 * «W_i-15_b3_4» + 8 * «W_i-15_b3_5» + 16 * «W_i-15_b3_6» + 32 * «W_i-15_b3_7» + 64 * «W_i-15_b0_0» + 128 * «W_i-15_b0_1»),
      u8_from_field_unsafe(«W_i-15_b2_2» + 2 * «W_i-15_b2_3» + 4 * «W_i-15_b2_4» + 8 * «W_i-15_b2_5» + 16 * «W_i-15_b2_6» + 32 * «W_i-15_b2_7» + 64 * «W_i-15_b3_0» + 128 * «W_i-15_b3_1»)
    ];

    let «W_i-15_shr3» = [
      u8_from_field_unsafe(«W_i-15_b3_3» + 2 * «W_i-15_b3_4» + 4 * «W_i-15_b3_5» + 8 * «W_i-15_b3_6» + 16 * «W_i-15_b3_7»),
      u8_from_field_unsafe(«W_i-15_b2_3» + 2 * «W_i-15_b2_4» + 4 * «W_i-15_b2_5» + 8 * «W_i-15_b2_6» + 16 * «W_i-15_b2_7» + 32 * «W_i-15_b3_0» + 64 * «W_i-15_b3_1» + 128 * «W_i-15_b3_2»),
      u8_from_field_unsafe(«W_i-15_b1_3» + 2 * «W_i-15_b1_4» + 4 * «W_i-15_b1_5» + 8 * «W_i-15_b1_6» + 16 * «W_i-15_b1_7» + 32 * «W_i-15_b2_0» + 64 * «W_i-15_b2_1» + 128 * «W_i-15_b2_2»),
      u8_from_field_unsafe(«W_i-15_b0_3» + 2 * «W_i-15_b0_4» + 4 * «W_i-15_b0_5» + 8 * «W_i-15_b0_6» + 16 * «W_i-15_b0_7» + 32 * «W_i-15_b1_0» + 64 * «W_i-15_b1_1» + 128 * «W_i-15_b1_2»)
    ];

    let [«W_i-2_b3», «W_i-2_b2», «W_i-2_b1», «W_i-2_b0»] = «W_i-2»;
    let [«W_i-2_b0_0», «W_i-2_b0_1», «W_i-2_b0_2», «W_i-2_b0_3», «W_i-2_b0_4», «W_i-2_b0_5», «W_i-2_b0_6», «W_i-2_b0_7»] = u8_bit_decomposition(«W_i-2_b0»);
    let [«W_i-2_b1_0», «W_i-2_b1_1», «W_i-2_b1_2», «W_i-2_b1_3», «W_i-2_b1_4», «W_i-2_b1_5», «W_i-2_b1_6», «W_i-2_b1_7»] = u8_bit_decomposition(«W_i-2_b1»);
    let [«W_i-2_b2_0», «W_i-2_b2_1», «W_i-2_b2_2», «W_i-2_b2_3», «W_i-2_b2_4», «W_i-2_b2_5», «W_i-2_b2_6», «W_i-2_b2_7»] = u8_bit_decomposition(«W_i-2_b2»);
    let [«W_i-2_b3_0», «W_i-2_b3_1», «W_i-2_b3_2», «W_i-2_b3_3», «W_i-2_b3_4», «W_i-2_b3_5», «W_i-2_b3_6», «W_i-2_b3_7»] = u8_bit_decomposition(«W_i-2_b3»);

    let «W_i-2_rotr17» = [
      u8_from_field_unsafe(«W_i-2_b1_1» + 2 * «W_i-2_b1_2» + 4 * «W_i-2_b1_3» + 8 * «W_i-2_b1_4» + 16 * «W_i-2_b1_5» + 32 * «W_i-2_b1_6» + 64 * «W_i-2_b1_7» + 128 * «W_i-2_b2_0»),
      u8_from_field_unsafe(«W_i-2_b0_1» + 2 * «W_i-2_b0_2» + 4 * «W_i-2_b0_3» + 8 * «W_i-2_b0_4» + 16 * «W_i-2_b0_5» + 32 * «W_i-2_b0_6» + 64 * «W_i-2_b0_7» + 128 * «W_i-2_b1_0»),
      u8_from_field_unsafe(«W_i-2_b3_1» + 2 * «W_i-2_b3_2» + 4 * «W_i-2_b3_3» + 8 * «W_i-2_b3_4» + 16 * «W_i-2_b3_5» + 32 * «W_i-2_b3_6» + 64 * «W_i-2_b3_7» + 128 * «W_i-2_b0_0»),
      u8_from_field_unsafe(«W_i-2_b2_1» + 2 * «W_i-2_b2_2» + 4 * «W_i-2_b2_3» + 8 * «W_i-2_b2_4» + 16 * «W_i-2_b2_5» + 32 * «W_i-2_b2_6» + 64 * «W_i-2_b2_7» + 128 * «W_i-2_b3_0»)
    ];

    let «W_i-2_rotr19» = [
      u8_from_field_unsafe(«W_i-2_b1_3» + 2 * «W_i-2_b1_4» + 4 * «W_i-2_b1_5» + 8 * «W_i-2_b1_6» + 16 * «W_i-2_b1_7» + 32 * «W_i-2_b2_0» + 64 * «W_i-2_b2_1» + 128 * «W_i-2_b2_2»),
      u8_from_field_unsafe(«W_i-2_b0_3» + 2 * «W_i-2_b0_4» + 4 * «W_i-2_b0_5» + 8 * «W_i-2_b0_6» + 16 * «W_i-2_b0_7» + 32 * «W_i-2_b1_0» + 64 * «W_i-2_b1_1» + 128 * «W_i-2_b1_2»),
      u8_from_field_unsafe(«W_i-2_b3_3» + 2 * «W_i-2_b3_4» + 4 * «W_i-2_b3_5» + 8 * «W_i-2_b3_6» + 16 * «W_i-2_b3_7» + 32 * «W_i-2_b0_0» + 64 * «W_i-2_b0_1» + 128 * «W_i-2_b0_2»),
      u8_from_field_unsafe(«W_i-2_b2_3» + 2 * «W_i-2_b2_4» + 4 * «W_i-2_b2_5» + 8 * «W_i-2_b2_6» + 16 * «W_i-2_b2_7» + 32 * «W_i-2_b3_0» + 64 * «W_i-2_b3_1» + 128 * «W_i-2_b3_2»)
    ];

    let «W_i-2_shr10» = [
      u8_from_field_unsafe(0),
      u8_from_field_unsafe(«W_i-2_b3_2» + 2 * «W_i-2_b3_3» + 4 * «W_i-2_b3_4» + 8 * «W_i-2_b3_5» + 16 * «W_i-2_b3_6» + 32 * «W_i-2_b3_7»),
      u8_from_field_unsafe(«W_i-2_b2_2» + 2 * «W_i-2_b2_3» + 4 * «W_i-2_b2_4» + 8 * «W_i-2_b2_5» + 16 * «W_i-2_b2_6» + 32 * «W_i-2_b2_7» + 64 * «W_i-2_b3_0» + 128 * «W_i-2_b3_1»),
      u8_from_field_unsafe(«W_i-2_b1_2» + 2 * «W_i-2_b1_3» + 4 * «W_i-2_b1_4» + 8 * «W_i-2_b1_5» + 16 * «W_i-2_b1_6» + 32 * «W_i-2_b1_7» + 64 * «W_i-2_b2_0» + 128 * «W_i-2_b2_1»)
    ];

    let «W_i_s0» = u32_xor(«W_i-15_rotr7», u32_xor(«W_i-15_rotr18», «W_i-15_shr3»));
    let «W_i_s1» = u32_xor(«W_i-2_rotr17», u32_xor(«W_i-2_rotr19», «W_i-2_shr10»));
    u32_be_add(«W_i-16», u32_be_add(«W_i_s0», u32_be_add(«W_i-7», «W_i_s1»)))
  }
⟧

end IxVM

end
