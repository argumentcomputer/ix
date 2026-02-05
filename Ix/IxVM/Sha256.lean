import Ix.Aiur.Meta

namespace IxVM
-- #exit

def sha256 := ⟦
  /- # Test entrypoints -/

  fn sha256_test() -> [[G; 4]; 8] {
    let (idx, len) = io_get_info([0]);
    let byte_stream = read_byte_stream(idx, len);
    sha256(byte_stream)
  }

  /- # Benchmark entrypoints -/

  fn sha256_bench(num_hashes: G) -> G {
    let num_hashes_pred = num_hashes - 1;
    let key = [num_hashes_pred];
    let (idx, len) = io_get_info(key);
    let byte_stream = read_byte_stream(idx, len);
    let _x = sha256(byte_stream);
    match num_hashes_pred {
      0 => 0,
      _ => sha256_bench(num_hashes_pred),
    }
  }

  /- # Implementation -/

  fn sha256(stream: ByteStream) -> [[G; 4]; 8] {
    let state = [
      [0x6a, 0x09, 0xe6, 0x67],
      [0xbb, 0x67, 0xae, 0x85],
      [0x3c, 0x6e, 0xf3, 0x72],
      [0xa5, 0x4f, 0xf5, 0x3a],
      [0x51, 0x0e, 0x52, 0x7f],
      [0x9b, 0x05, 0x68, 0x8c],
      [0x1f, 0x83, 0xd9, 0xab],
      [0x5b, 0xe0, 0xcd, 0x19]
    ];
    sha256_aux(stream, [0; 8], state)
  }

  fn sha256_aux(stream: ByteStream, len_be: [G; 8], state: [[G; 4]; 8]) -> [[G; 4]; 8] {
    let W = [[0; 4]; 16];
    match stream {
      ByteStream.Nil =>
        let W = set(W, 0, [0x80, 0, 0, 0]);
        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
        fill_W_and_run_rounds(W, state),
      ByteStream.Cons(b0, tail_ptr) => match load(tail_ptr) {
        ByteStream.Nil =>
          let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 8]);
          let W = set(W, 0, [b0, 0x80, 0, 0]);
          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
          fill_W_and_run_rounds(W, state),
        ByteStream.Cons(b1, tail_ptr) => match load(tail_ptr) {
          ByteStream.Nil =>
            let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 16]);
            let W = set(W, 0, [b0, b1, 0x80, 0]);
            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
            fill_W_and_run_rounds(W, state),
          ByteStream.Cons(b2, tail_ptr) => match load(tail_ptr) {
            ByteStream.Nil =>
              let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 24]);
              let W = set(W, 0, [b0, b1, b2, 0x80]);
              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
              fill_W_and_run_rounds(W, state),
            ByteStream.Cons(b3, tail_ptr) =>
              let W = set(W, 0, [b0, b1, b2, b3]);
              match load(tail_ptr) {
              ByteStream.Nil =>
                let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 32]);
                let W = set(W, 1, [0x80, 0, 0, 0]);
                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                fill_W_and_run_rounds(W, state),
              ByteStream.Cons(b4, tail_ptr) => match load(tail_ptr) {
                ByteStream.Nil =>
                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 40]);
                  let W = set(W, 1, [b4, 0x80, 0, 0]);
                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                  fill_W_and_run_rounds(W, state),
                ByteStream.Cons(b5, tail_ptr) => match load(tail_ptr) {
                  ByteStream.Nil =>
                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 48]);
                    let W = set(W, 1, [b4, b5, 0x80, 0]);
                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                    fill_W_and_run_rounds(W, state),
                  ByteStream.Cons(b6, tail_ptr) => match load(tail_ptr) {
                    ByteStream.Nil =>
                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 56]);
                      let W = set(W, 1, [b4, b5, b6, 0x80]);
                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                      fill_W_and_run_rounds(W, state),
                    ByteStream.Cons(b7, tail_ptr) =>
                      let W = set(W, 1, [b4, b5, b6, b7]);
                      match load(tail_ptr) {
                      ByteStream.Nil =>
                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 64]);
                        let W = set(W, 2, [0x80, 0, 0, 0]);
                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                        fill_W_and_run_rounds(W, state),
                      ByteStream.Cons(b8, tail_ptr) => match load(tail_ptr) {
                        ByteStream.Nil =>
                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 72]);
                          let W = set(W, 2, [b8, 0x80, 0, 0]);
                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                          fill_W_and_run_rounds(W, state),
                        ByteStream.Cons(b9, tail_ptr) => match load(tail_ptr) {
                          ByteStream.Nil =>
                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 80]);
                            let W = set(W, 2, [b8, b9, 0x80, 0]);
                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                            fill_W_and_run_rounds(W, state),
                          ByteStream.Cons(b10, tail_ptr) => match load(tail_ptr) {
                            ByteStream.Nil =>
                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 88]);
                              let W = set(W, 2, [b8, b9, b10, 0x80]);
                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                              fill_W_and_run_rounds(W, state),
                            ByteStream.Cons(b11, tail_ptr) =>
                              let W = set(W, 2, [b8, b9, b10, b11]);
                              match load(tail_ptr) {
                              ByteStream.Nil =>
                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 96]);
                                let W = set(W, 3, [0x80, 0, 0, 0]);
                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                fill_W_and_run_rounds(W, state),
                              ByteStream.Cons(b12, tail_ptr) => match load(tail_ptr) {
                                ByteStream.Nil =>
                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 104]);
                                  let W = set(W, 3, [b12, 0x80, 0, 0]);
                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                  fill_W_and_run_rounds(W, state),
                                ByteStream.Cons(b13, tail_ptr) => match load(tail_ptr) {
                                  ByteStream.Nil =>
                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 112]);
                                    let W = set(W, 3, [b12, b13, 0x80, 0]);
                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                    fill_W_and_run_rounds(W, state),
                                  ByteStream.Cons(b14, tail_ptr) => match load(tail_ptr) {
                                    ByteStream.Nil =>
                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 120]);
                                      let W = set(W, 3, [b12, b13, b14, 0x80]);
                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                      fill_W_and_run_rounds(W, state),
                                    ByteStream.Cons(b15, tail_ptr) =>
                                      let W = set(W, 3, [b12, b13, b14, b15]);
                                      match load(tail_ptr) {
                                      ByteStream.Nil =>
                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 128]);
                                        let W = set(W, 4, [0x80, 0, 0, 0]);
                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                        fill_W_and_run_rounds(W, state),
                                      ByteStream.Cons(b16, tail_ptr) => match load(tail_ptr) {
                                        ByteStream.Nil =>
                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 136]);
                                          let W = set(W, 4, [b16, 0x80, 0, 0]);
                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                          fill_W_and_run_rounds(W, state),
                                        ByteStream.Cons(b17, tail_ptr) => match load(tail_ptr) {
                                          ByteStream.Nil =>
                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 144]);
                                            let W = set(W, 4, [b16, b17, 0x80, 0]);
                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                            fill_W_and_run_rounds(W, state),
                                          ByteStream.Cons(b18, tail_ptr) => match load(tail_ptr) {
                                            ByteStream.Nil =>
                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 152]);
                                              let W = set(W, 4, [b16, b17, b18, 0x80]);
                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                              fill_W_and_run_rounds(W, state),
                                            ByteStream.Cons(b19, tail_ptr) =>
                                              let W = set(W, 4, [b16, b17, b18, b19]);
                                              match load(tail_ptr) {
                                              ByteStream.Nil =>
                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 160]);
                                                let W = set(W, 5, [0x80, 0, 0, 0]);
                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                fill_W_and_run_rounds(W, state),
                                              ByteStream.Cons(b20, tail_ptr) => match load(tail_ptr) {
                                                ByteStream.Nil =>
                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 168]);
                                                  let W = set(W, 5, [b20, 0x80, 0, 0]);
                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                  fill_W_and_run_rounds(W, state),
                                                ByteStream.Cons(b21, tail_ptr) => match load(tail_ptr) {
                                                  ByteStream.Nil =>
                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 176]);
                                                    let W = set(W, 5, [b20, b21, 0x80, 0]);
                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                    fill_W_and_run_rounds(W, state),
                                                  ByteStream.Cons(b22, tail_ptr) => match load(tail_ptr) {
                                                    ByteStream.Nil =>
                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 184]);
                                                      let W = set(W, 5, [b20, b21, b22, 0x80]);
                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                      fill_W_and_run_rounds(W, state),
                                                    ByteStream.Cons(b23, tail_ptr) =>
                                                      let W = set(W, 5, [b20, b21, b22, b23]);
                                                      match load(tail_ptr) {
                                                      ByteStream.Nil =>
                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 192]);
                                                        let W = set(W, 6, [0x80, 0, 0, 0]);
                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                        fill_W_and_run_rounds(W, state),
                                                      ByteStream.Cons(b24, tail_ptr) => match load(tail_ptr) {
                                                        ByteStream.Nil =>
                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 200]);
                                                          let W = set(W, 6, [b24, 0x80, 0, 0]);
                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                          fill_W_and_run_rounds(W, state),
                                                        ByteStream.Cons(b25, tail_ptr) => match load(tail_ptr) {
                                                          ByteStream.Nil =>
                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 208]);
                                                            let W = set(W, 6, [b24, b25, 0x80, 0]);
                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                            fill_W_and_run_rounds(W, state),
                                                          ByteStream.Cons(b26, tail_ptr) => match load(tail_ptr) {
                                                            ByteStream.Nil =>
                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 216]);
                                                              let W = set(W, 6, [b24, b25, b26, 0x80]);
                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                              fill_W_and_run_rounds(W, state),
                                                            ByteStream.Cons(b27, tail_ptr) =>
                                                              let W = set(W, 6, [b24, b25, b26, b27]);
                                                              match load(tail_ptr) {
                                                              ByteStream.Nil =>
                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 224]);
                                                                let W = set(W, 7, [0x80, 0, 0, 0]);
                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                fill_W_and_run_rounds(W, state),
                                                              ByteStream.Cons(b28, tail_ptr) => match load(tail_ptr) {
                                                                ByteStream.Nil =>
                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 232]);
                                                                  let W = set(W, 7, [b28, 0x80, 0, 0]);
                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                  fill_W_and_run_rounds(W, state),
                                                                ByteStream.Cons(b29, tail_ptr) => match load(tail_ptr) {
                                                                  ByteStream.Nil =>
                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 240]);
                                                                    let W = set(W, 7, [b28, b29, 0x80, 0]);
                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                    fill_W_and_run_rounds(W, state),
                                                                  ByteStream.Cons(b30, tail_ptr) => match load(tail_ptr) {
                                                                    ByteStream.Nil =>
                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [0, 248]);
                                                                      let W = set(W, 7, [b28, b29, b30, 0x80]);
                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                      fill_W_and_run_rounds(W, state),
                                                                    ByteStream.Cons(b31, tail_ptr) =>
                                                                      let W = set(W, 7, [b28, b29, b30, b31]);
                                                                      match load(tail_ptr) {
                                                                      ByteStream.Nil =>
                                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 0]);
                                                                        let W = set(W, 8, [0x80, 0, 0, 0]);
                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                        fill_W_and_run_rounds(W, state),
                                                                      ByteStream.Cons(b32, tail_ptr) => match load(tail_ptr) {
                                                                        ByteStream.Nil =>
                                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 8]);
                                                                          let W = set(W, 8, [b32, 0x80, 0, 0]);
                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                          fill_W_and_run_rounds(W, state),
                                                                        ByteStream.Cons(b33, tail_ptr) => match load(tail_ptr) {
                                                                          ByteStream.Nil =>
                                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 16]);
                                                                            let W = set(W, 8, [b32, b33, 0x80, 0]);
                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                            fill_W_and_run_rounds(W, state),
                                                                          ByteStream.Cons(b34, tail_ptr) => match load(tail_ptr) {
                                                                            ByteStream.Nil =>
                                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 24]);
                                                                              let W = set(W, 8, [b32, b33, b34, 0x80]);
                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                              fill_W_and_run_rounds(W, state),
                                                                            ByteStream.Cons(b35, tail_ptr) =>
                                                                              let W = set(W, 8, [b32, b33, b34, b35]);
                                                                              match load(tail_ptr) {
                                                                              ByteStream.Nil =>
                                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 32]);
                                                                                let W = set(W, 9, [0x80, 0, 0, 0]);
                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                fill_W_and_run_rounds(W, state),
                                                                              ByteStream.Cons(b36, tail_ptr) => match load(tail_ptr) {
                                                                                ByteStream.Nil =>
                                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 40]);
                                                                                  let W = set(W, 9, [b36, 0x80, 0, 0]);
                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                  fill_W_and_run_rounds(W, state),
                                                                                ByteStream.Cons(b37, tail_ptr) => match load(tail_ptr) {
                                                                                  ByteStream.Nil =>
                                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 48]);
                                                                                    let W = set(W, 9, [b36, b37, 0x80, 0]);
                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                    fill_W_and_run_rounds(W, state),
                                                                                  ByteStream.Cons(b38, tail_ptr) => match load(tail_ptr) {
                                                                                    ByteStream.Nil =>
                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 56]);
                                                                                      let W = set(W, 9, [b36, b37, b38, 0x80]);
                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                      fill_W_and_run_rounds(W, state),
                                                                                    ByteStream.Cons(b39, tail_ptr) =>
                                                                                      let W = set(W, 9, [b36, b37, b38, b39]);
                                                                                      match load(tail_ptr) {
                                                                                      ByteStream.Nil =>
                                                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 64]);
                                                                                        let W = set(W, 10, [0x80, 0, 0, 0]);
                                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                        fill_W_and_run_rounds(W, state),
                                                                                      ByteStream.Cons(b40, tail_ptr) => match load(tail_ptr) {
                                                                                        ByteStream.Nil =>
                                                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 72]);
                                                                                          let W = set(W, 10, [b40, 0x80, 0, 0]);
                                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                          fill_W_and_run_rounds(W, state),
                                                                                        ByteStream.Cons(b41, tail_ptr) => match load(tail_ptr) {
                                                                                          ByteStream.Nil =>
                                                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 80]);
                                                                                            let W = set(W, 10, [b40, b41, 0x80, 0]);
                                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                            fill_W_and_run_rounds(W, state),
                                                                                          ByteStream.Cons(b42, tail_ptr) => match load(tail_ptr) {
                                                                                            ByteStream.Nil =>
                                                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 88]);
                                                                                              let W = set(W, 10, [b40, b41, b42, 0x80]);
                                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                              fill_W_and_run_rounds(W, state),
                                                                                            ByteStream.Cons(b43, tail_ptr) =>
                                                                                              let W = set(W, 10, [b40, b41, b42, b43]);
                                                                                              match load(tail_ptr) {
                                                                                              ByteStream.Nil =>
                                                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 96]);
                                                                                                let W = set(W, 11, [0x80, 0, 0, 0]);
                                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                fill_W_and_run_rounds(W, state),
                                                                                              ByteStream.Cons(b44, tail_ptr) => match load(tail_ptr) {
                                                                                                ByteStream.Nil =>
                                                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 104]);
                                                                                                  let W = set(W, 11, [b44, 0x80, 0, 0]);
                                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                  fill_W_and_run_rounds(W, state),
                                                                                                ByteStream.Cons(b45, tail_ptr) => match load(tail_ptr) {
                                                                                                  ByteStream.Nil =>
                                                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 112]);
                                                                                                    let W = set(W, 11, [b44, b45, 0x80, 0]);
                                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                    fill_W_and_run_rounds(W, state),
                                                                                                  ByteStream.Cons(b46, tail_ptr) => match load(tail_ptr) {
                                                                                                    ByteStream.Nil =>
                                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 120]);
                                                                                                      let W = set(W, 11, [b44, b45, b46, 0x80]);
                                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                      fill_W_and_run_rounds(W, state),
                                                                                                    ByteStream.Cons(b47, tail_ptr) =>
                                                                                                      let W = set(W, 11, [b44, b45, b46, b47]);
                                                                                                      match load(tail_ptr) {
                                                                                                      ByteStream.Nil =>
                                                                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 128]);
                                                                                                        let W = set(W, 12, [0x80, 0, 0, 0]);
                                                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                        fill_W_and_run_rounds(W, state),
                                                                                                      ByteStream.Cons(b48, tail_ptr) => match load(tail_ptr) {
                                                                                                        ByteStream.Nil =>
                                                                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 136]);
                                                                                                          let W = set(W, 12, [b48, 0x80, 0, 0]);
                                                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                          fill_W_and_run_rounds(W, state),
                                                                                                        ByteStream.Cons(b49, tail_ptr) => match load(tail_ptr) {
                                                                                                          ByteStream.Nil =>
                                                                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 144]);
                                                                                                            let W = set(W, 12, [b48, b49, 0x80, 0]);
                                                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                            fill_W_and_run_rounds(W, state),
                                                                                                          ByteStream.Cons(b50, tail_ptr) => match load(tail_ptr) {
                                                                                                            ByteStream.Nil =>
                                                                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 152]);
                                                                                                              let W = set(W, 12, [b48, b49, b50, 0x80]);
                                                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                              fill_W_and_run_rounds(W, state),
                                                                                                            ByteStream.Cons(b51, tail_ptr) =>
                                                                                                              let W = set(W, 12, [b48, b49, b50, b51]);
                                                                                                              match load(tail_ptr) {
                                                                                                              ByteStream.Nil =>
                                                                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 160]);
                                                                                                                let W = set(W, 13, [0x80, 0, 0, 0]);
                                                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                fill_W_and_run_rounds(W, state),
                                                                                                              ByteStream.Cons(b52, tail_ptr) => match load(tail_ptr) {
                                                                                                                ByteStream.Nil =>
                                                                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 168]);
                                                                                                                  let W = set(W, 13, [b52, 0x80, 0, 0]);
                                                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                  fill_W_and_run_rounds(W, state),
                                                                                                                ByteStream.Cons(b53, tail_ptr) => match load(tail_ptr) {
                                                                                                                  ByteStream.Nil =>
                                                                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 176]);
                                                                                                                    let W = set(W, 13, [b52, b53, 0x80, 0]);
                                                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                    fill_W_and_run_rounds(W, state),
                                                                                                                  ByteStream.Cons(b54, tail_ptr) => match load(tail_ptr) {
                                                                                                                    ByteStream.Nil =>
                                                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 184]);
                                                                                                                      let W = set(W, 13, [b52, b53, b54, 0x80]);
                                                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                      fill_W_and_run_rounds(W, state),
                                                                                                                    ByteStream.Cons(b55, tail_ptr) =>
                                                                                                                      let W = set(W, 13, [b52, b53, b54, b55]);
                                                                                                                      match load(tail_ptr) {
                                                                                                                      ByteStream.Nil =>
                                                                                                                        let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 192]);
                                                                                                                        let W = set(W, 14, [0x80, 0, 0, 0]);
                                                                                                                        let state = fill_W_and_run_rounds(W, state);
                                                                                                                        fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                      ByteStream.Cons(b56, tail_ptr) => match load(tail_ptr) {
                                                                                                                        ByteStream.Nil =>
                                                                                                                          let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 200]);
                                                                                                                          let W = set(W, 14, [b56, 0x80, 0, 0]);
                                                                                                                          let state = fill_W_and_run_rounds(W, state);
                                                                                                                          fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                        ByteStream.Cons(b57, tail_ptr) => match load(tail_ptr) {
                                                                                                                          ByteStream.Nil =>
                                                                                                                            let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 208]);
                                                                                                                            let W = set(W, 14, [b56, b57, 0x80, 0]);
                                                                                                                            let state = fill_W_and_run_rounds(W, state);
                                                                                                                            fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                          ByteStream.Cons(b58, tail_ptr) => match load(tail_ptr) {
                                                                                                                            ByteStream.Nil =>
                                                                                                                              let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 216]);
                                                                                                                              let W = set(W, 14, [b56, b57, b58, 0x80]);
                                                                                                                              let state = fill_W_and_run_rounds(W, state);
                                                                                                                              fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                            ByteStream.Cons(b59, tail_ptr) =>
                                                                                                                              let W = set(W, 14, [b56, b57, b58, b59]);
                                                                                                                              match load(tail_ptr) {
                                                                                                                              ByteStream.Nil =>
                                                                                                                                let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 224]);
                                                                                                                                let W = set(W, 15, [0x80, 0, 0, 0]);
                                                                                                                                let state = fill_W_and_run_rounds(W, state);
                                                                                                                                fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                              ByteStream.Cons(b60, tail_ptr) => match load(tail_ptr) {
                                                                                                                                ByteStream.Nil =>
                                                                                                                                  let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 232]);
                                                                                                                                  let W = set(W, 15, [b60, 0x80, 0, 0]);
                                                                                                                                  let state = fill_W_and_run_rounds(W, state);
                                                                                                                                  fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                                ByteStream.Cons(b61, tail_ptr) => match load(tail_ptr) {
                                                                                                                                  ByteStream.Nil =>
                                                                                                                                    let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 240]);
                                                                                                                                    let W = set(W, 15, [b60, b61, 0x80, 0]);
                                                                                                                                    let state = fill_W_and_run_rounds(W, state);
                                                                                                                                    fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                                  ByteStream.Cons(b62, tail_ptr) => match load(tail_ptr) {
                                                                                                                                    ByteStream.Nil =>
                                                                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [1, 248]);
                                                                                                                                      let W = set(W, 15, [b60, b61, b62, 0x80]);
                                                                                                                                      let state = fill_W_and_run_rounds(W, state);
                                                                                                                                      fill_W_with_length_and_run_rounds(len_be, state),
                                                                                                                                    ByteStream.Cons(b63, tail_ptr) =>
                                                                                                                                      let len_be = relaxed_u64_be_add_2_bytes(len_be, [2, 0]);
                                                                                                                                      let W = set(W, 15, [b60, b61, b62, b63]);
                                                                                                                                      let state = fill_W_and_run_rounds(W, state);
                                                                                                                                      sha256_aux(load(tail_ptr), len_be, state),
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

  fn fill_W_with_length_and_run_rounds(len_be: [G; 8], state: [[G; 4]; 8]) -> [[G; 4]; 8] {
    let W = [[0; 4]; 16];
    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
    fill_W_and_run_rounds(W, state)
  }

  fn fill_W_and_run_rounds(W: [[G; 4]; 16], state: [[G; 4]; 8]) -> [[G; 4]; 8] {
    let K = [
      [0x42, 0x8a, 0x2f, 0x98], [0x71, 0x37, 0x44, 0x91], [0xb5, 0xc0, 0xfb, 0xcf], [0xe9, 0xb5, 0xdb, 0xa5],
      [0x39, 0x56, 0xc2, 0x5b], [0x59, 0xf1, 0x11, 0xf1], [0x92, 0x3f, 0x82, 0xa4], [0xab, 0x1c, 0x5e, 0xd5],
      [0xd8, 0x07, 0xaa, 0x98], [0x12, 0x83, 0x5b, 0x01], [0x24, 0x31, 0x85, 0xbe], [0x55, 0x0c, 0x7d, 0xc3],
      [0x72, 0xbe, 0x5d, 0x74], [0x80, 0xde, 0xb1, 0xfe], [0x9b, 0xdc, 0x06, 0xa7], [0xc1, 0x9b, 0xf1, 0x74],
      [0xe4, 0x9b, 0x69, 0xc1], [0xef, 0xbe, 0x47, 0x86], [0x0f, 0xc1, 0x9d, 0xc6], [0x24, 0x0c, 0xa1, 0xcc],
      [0x2d, 0xe9, 0x2c, 0x6f], [0x4a, 0x74, 0x84, 0xaa], [0x5c, 0xb0, 0xa9, 0xdc], [0x76, 0xf9, 0x88, 0xda],
      [0x98, 0x3e, 0x51, 0x52], [0xa8, 0x31, 0xc6, 0x6d], [0xb0, 0x03, 0x27, 0xc8], [0xbf, 0x59, 0x7f, 0xc7],
      [0xc6, 0xe0, 0x0b, 0xf3], [0xd5, 0xa7, 0x91, 0x47], [0x06, 0xca, 0x63, 0x51], [0x14, 0x29, 0x29, 0x67],
      [0x27, 0xb7, 0x0a, 0x85], [0x2e, 0x1b, 0x21, 0x38], [0x4d, 0x2c, 0x6d, 0xfc], [0x53, 0x38, 0x0d, 0x13],
      [0x65, 0x0a, 0x73, 0x54], [0x76, 0x6a, 0x0a, 0xbb], [0x81, 0xc2, 0xc9, 0x2e], [0x92, 0x72, 0x2c, 0x85],
      [0xa2, 0xbf, 0xe8, 0xa1], [0xa8, 0x1a, 0x66, 0x4b], [0xc2, 0x4b, 0x8b, 0x70], [0xc7, 0x6c, 0x51, 0xa3],
      [0xd1, 0x92, 0xe8, 0x19], [0xd6, 0x99, 0x06, 0x24], [0xf4, 0x0e, 0x35, 0x85], [0x10, 0x6a, 0xa0, 0x70],
      [0x19, 0xa4, 0xc1, 0x16], [0x1e, 0x37, 0x6c, 0x08], [0x27, 0x48, 0x77, 0x4c], [0x34, 0xb0, 0xbc, 0xb5],
      [0x39, 0x1c, 0x0c, 0xb3], [0x4e, 0xd8, 0xaa, 0x4a], [0x5b, 0x9c, 0xca, 0x4f], [0x68, 0x2e, 0x6f, 0xf3],
      [0x74, 0x8f, 0x82, 0xee], [0x78, 0xa5, 0x63, 0x6f], [0x84, 0xc8, 0x78, 0x14], [0x8c, 0xc7, 0x02, 0x08],
      [0x90, 0xbe, 0xff, 0xfa], [0xa4, 0x50, 0x6c, 0xeb], [0xbe, 0xf9, 0xa3, 0xf7], [0xc6, 0x71, 0x78, 0xf2]
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

      let e_rotr6 = [
        u8_recompose([e_3_bits[6], e_3_bits[7], e_0_bits[0], e_0_bits[1], e_0_bits[2], e_0_bits[3], e_0_bits[4], e_0_bits[5]]),
        u8_recompose([e_2_bits[6], e_2_bits[7], e_3_bits[0], e_3_bits[1], e_3_bits[2], e_3_bits[3], e_3_bits[4], e_3_bits[5]]),
        u8_recompose([e_1_bits[6], e_1_bits[7], e_2_bits[0], e_2_bits[1], e_2_bits[2], e_2_bits[3], e_2_bits[4], e_2_bits[5]]),
        u8_recompose([e_0_bits[6], e_0_bits[7], e_1_bits[0], e_1_bits[1], e_1_bits[2], e_1_bits[3], e_1_bits[4], e_1_bits[5]])
      ];

      let e_rotr11 = [
        u8_recompose([e_0_bits[3], e_0_bits[4], e_0_bits[5], e_0_bits[6], e_0_bits[7], e_1_bits[0], e_1_bits[1], e_1_bits[2]]),
        u8_recompose([e_3_bits[3], e_3_bits[4], e_3_bits[5], e_3_bits[6], e_3_bits[7], e_0_bits[0], e_0_bits[1], e_0_bits[2]]),
        u8_recompose([e_2_bits[3], e_2_bits[4], e_2_bits[5], e_2_bits[6], e_2_bits[7], e_3_bits[0], e_3_bits[1], e_3_bits[2]]),
        u8_recompose([e_1_bits[3], e_1_bits[4], e_1_bits[5], e_1_bits[6], e_1_bits[7], e_2_bits[0], e_2_bits[1], e_2_bits[2]])
      ];

      let e_rotr25 = [
        u8_recompose([e_2_bits[1], e_2_bits[2], e_2_bits[3], e_2_bits[4], e_2_bits[5], e_2_bits[6], e_2_bits[7], e_3_bits[0]]),
        u8_recompose([e_1_bits[1], e_1_bits[2], e_1_bits[3], e_1_bits[4], e_1_bits[5], e_1_bits[6], e_1_bits[7], e_2_bits[0]]),
        u8_recompose([e_0_bits[1], e_0_bits[2], e_0_bits[3], e_0_bits[4], e_0_bits[5], e_0_bits[6], e_0_bits[7], e_1_bits[0]]),
        u8_recompose([e_3_bits[1], e_3_bits[2], e_3_bits[3], e_3_bits[4], e_3_bits[5], e_3_bits[6], e_3_bits[7], e_0_bits[0]])
      ];

      let e_not = [255 - acc[4][0], 255 - acc[4][1], 255 - acc[4][2], 255 - acc[4][3]];

      let s1 = u32_xor(e_rotr6, u32_xor(e_rotr11, e_rotr25));
      let ch = u32_xor(u32_and(acc[4], acc[5]), u32_and(e_not, acc[6]));
      let temp1 = u32_be_add(acc[7], u32_be_add(s1, u32_be_add(ch, u32_be_add(K[@i], W[@i]))));

      let a_0_bits = u8_bit_decomposition(acc[0][3]);
      let a_1_bits = u8_bit_decomposition(acc[0][2]);
      let a_2_bits = u8_bit_decomposition(acc[0][1]);
      let a_3_bits = u8_bit_decomposition(acc[0][0]);

      let a_rotr2 = [
        u8_recompose([a_3_bits[2], a_3_bits[3], a_3_bits[4], a_3_bits[5], a_3_bits[6], a_3_bits[7], a_0_bits[0], a_0_bits[1]]),
        u8_recompose([a_2_bits[2], a_2_bits[3], a_2_bits[4], a_2_bits[5], a_2_bits[6], a_2_bits[7], a_3_bits[0], a_3_bits[1]]),
        u8_recompose([a_1_bits[2], a_1_bits[3], a_1_bits[4], a_1_bits[5], a_1_bits[6], a_1_bits[7], a_2_bits[0], a_2_bits[1]]),
        u8_recompose([a_0_bits[2], a_0_bits[3], a_0_bits[4], a_0_bits[5], a_0_bits[6], a_0_bits[7], a_1_bits[0], a_1_bits[1]])
      ];

      let a_rotr13 = [
        u8_recompose([a_0_bits[5], a_0_bits[6], a_0_bits[7], a_1_bits[0], a_1_bits[1], a_1_bits[2], a_1_bits[3], a_1_bits[4]]),
        u8_recompose([a_3_bits[5], a_3_bits[6], a_3_bits[7], a_0_bits[0], a_0_bits[1], a_0_bits[2], a_0_bits[3], a_0_bits[4]]),
        u8_recompose([a_2_bits[5], a_2_bits[6], a_2_bits[7], a_3_bits[0], a_3_bits[1], a_3_bits[2], a_3_bits[3], a_3_bits[4]]),
        u8_recompose([a_1_bits[5], a_1_bits[6], a_1_bits[7], a_2_bits[0], a_2_bits[1], a_2_bits[2], a_2_bits[3], a_2_bits[4]])
      ];

      let a_rotr22 = [
        u8_recompose([a_1_bits[6], a_1_bits[7], a_2_bits[0], a_2_bits[1], a_2_bits[2], a_2_bits[3], a_2_bits[4], a_2_bits[5]]),
        u8_recompose([a_0_bits[6], a_0_bits[7], a_1_bits[0], a_1_bits[1], a_1_bits[2], a_1_bits[3], a_1_bits[4], a_1_bits[5]]),
        u8_recompose([a_3_bits[6], a_3_bits[7], a_0_bits[0], a_0_bits[1], a_0_bits[2], a_0_bits[3], a_0_bits[4], a_0_bits[5]]),
        u8_recompose([a_2_bits[6], a_2_bits[7], a_3_bits[0], a_3_bits[1], a_3_bits[2], a_3_bits[3], a_3_bits[4], a_3_bits[5]])
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

  fn define_W_i(«W_i-2»: [G; 4], «W_i-7»: [G; 4], «W_i-15»: [G; 4], «W_i-16»: [G; 4]) -> [G; 4] {
    let [«W_i-15_b3», «W_i-15_b2», «W_i-15_b1», «W_i-15_b0»] = «W_i-15»;
    let [«W_i-15_b0_0», «W_i-15_b0_1», «W_i-15_b0_2», «W_i-15_b0_3», «W_i-15_b0_4», «W_i-15_b0_5», «W_i-15_b0_6», «W_i-15_b0_7»] = u8_bit_decomposition(«W_i-15_b0»);
    let [«W_i-15_b1_0», «W_i-15_b1_1», «W_i-15_b1_2», «W_i-15_b1_3», «W_i-15_b1_4», «W_i-15_b1_5», «W_i-15_b1_6», «W_i-15_b1_7»] = u8_bit_decomposition(«W_i-15_b1»);
    let [«W_i-15_b2_0», «W_i-15_b2_1», «W_i-15_b2_2», «W_i-15_b2_3», «W_i-15_b2_4», «W_i-15_b2_5», «W_i-15_b2_6», «W_i-15_b2_7»] = u8_bit_decomposition(«W_i-15_b2»);
    let [«W_i-15_b3_0», «W_i-15_b3_1», «W_i-15_b3_2», «W_i-15_b3_3», «W_i-15_b3_4», «W_i-15_b3_5», «W_i-15_b3_6», «W_i-15_b3_7»] = u8_bit_decomposition(«W_i-15_b3»);

    let «W_i-15_rotr7» = [
      u8_recompose([«W_i-15_b3_7», «W_i-15_b0_0», «W_i-15_b0_1», «W_i-15_b0_2», «W_i-15_b0_3», «W_i-15_b0_4», «W_i-15_b0_5», «W_i-15_b0_6»]),
      u8_recompose([«W_i-15_b2_7», «W_i-15_b3_0», «W_i-15_b3_1», «W_i-15_b3_2», «W_i-15_b3_3», «W_i-15_b3_4», «W_i-15_b3_5», «W_i-15_b3_6»]),
      u8_recompose([«W_i-15_b1_7», «W_i-15_b2_0», «W_i-15_b2_1», «W_i-15_b2_2», «W_i-15_b2_3», «W_i-15_b2_4», «W_i-15_b2_5», «W_i-15_b2_6»]),
      u8_recompose([«W_i-15_b0_7», «W_i-15_b1_0», «W_i-15_b1_1», «W_i-15_b1_2», «W_i-15_b1_3», «W_i-15_b1_4», «W_i-15_b1_5», «W_i-15_b1_6»])
    ];

    let «W_i-15_rotr18» = [
      u8_recompose([«W_i-15_b1_2», «W_i-15_b1_3», «W_i-15_b1_4», «W_i-15_b1_5», «W_i-15_b1_6», «W_i-15_b1_7», «W_i-15_b2_0», «W_i-15_b2_1»]),
      u8_recompose([«W_i-15_b0_2», «W_i-15_b0_3», «W_i-15_b0_4», «W_i-15_b0_5», «W_i-15_b0_6», «W_i-15_b0_7», «W_i-15_b1_0», «W_i-15_b1_1»]),
      u8_recompose([«W_i-15_b3_2», «W_i-15_b3_3», «W_i-15_b3_4», «W_i-15_b3_5», «W_i-15_b3_6», «W_i-15_b3_7», «W_i-15_b0_0», «W_i-15_b0_1»]),
      u8_recompose([«W_i-15_b2_2», «W_i-15_b2_3», «W_i-15_b2_4», «W_i-15_b2_5», «W_i-15_b2_6», «W_i-15_b2_7», «W_i-15_b3_0», «W_i-15_b3_1»])
    ];

    let «W_i-15_shr3» = [
      u8_recompose([«W_i-15_b3_3», «W_i-15_b3_4», «W_i-15_b3_5», «W_i-15_b3_6», «W_i-15_b3_7», 0,             0,             0]),
      u8_recompose([«W_i-15_b2_3», «W_i-15_b2_4», «W_i-15_b2_5», «W_i-15_b2_6», «W_i-15_b2_7», «W_i-15_b3_0», «W_i-15_b3_1», «W_i-15_b3_2»]),
      u8_recompose([«W_i-15_b1_3», «W_i-15_b1_4», «W_i-15_b1_5», «W_i-15_b1_6», «W_i-15_b1_7», «W_i-15_b2_0», «W_i-15_b2_1», «W_i-15_b2_2»]),
      u8_recompose([«W_i-15_b0_3», «W_i-15_b0_4», «W_i-15_b0_5», «W_i-15_b0_6», «W_i-15_b0_7», «W_i-15_b1_0», «W_i-15_b1_1», «W_i-15_b1_2»])
    ];

    let [«W_i-2_b3», «W_i-2_b2», «W_i-2_b1», «W_i-2_b0»] = «W_i-2»;
    let [«W_i-2_b0_0», «W_i-2_b0_1», «W_i-2_b0_2», «W_i-2_b0_3», «W_i-2_b0_4», «W_i-2_b0_5», «W_i-2_b0_6», «W_i-2_b0_7»] = u8_bit_decomposition(«W_i-2_b0»);
    let [«W_i-2_b1_0», «W_i-2_b1_1», «W_i-2_b1_2», «W_i-2_b1_3», «W_i-2_b1_4», «W_i-2_b1_5», «W_i-2_b1_6», «W_i-2_b1_7»] = u8_bit_decomposition(«W_i-2_b1»);
    let [«W_i-2_b2_0», «W_i-2_b2_1», «W_i-2_b2_2», «W_i-2_b2_3», «W_i-2_b2_4», «W_i-2_b2_5», «W_i-2_b2_6», «W_i-2_b2_7»] = u8_bit_decomposition(«W_i-2_b2»);
    let [«W_i-2_b3_0», «W_i-2_b3_1», «W_i-2_b3_2», «W_i-2_b3_3», «W_i-2_b3_4», «W_i-2_b3_5», «W_i-2_b3_6», «W_i-2_b3_7»] = u8_bit_decomposition(«W_i-2_b3»);

    let «W_i-2_rotr17» = [
      u8_recompose([«W_i-2_b1_1», «W_i-2_b1_2», «W_i-2_b1_3», «W_i-2_b1_4», «W_i-2_b1_5», «W_i-2_b1_6», «W_i-2_b1_7», «W_i-2_b2_0»]),
      u8_recompose([«W_i-2_b0_1», «W_i-2_b0_2», «W_i-2_b0_3», «W_i-2_b0_4», «W_i-2_b0_5», «W_i-2_b0_6», «W_i-2_b0_7», «W_i-2_b1_0»]),
      u8_recompose([«W_i-2_b3_1», «W_i-2_b3_2», «W_i-2_b3_3», «W_i-2_b3_4», «W_i-2_b3_5», «W_i-2_b3_6», «W_i-2_b3_7», «W_i-2_b0_0»]),
      u8_recompose([«W_i-2_b2_1», «W_i-2_b2_2», «W_i-2_b2_3», «W_i-2_b2_4», «W_i-2_b2_5», «W_i-2_b2_6», «W_i-2_b2_7», «W_i-2_b3_0»])
    ];

    let «W_i-2_rotr19» = [
      u8_recompose([«W_i-2_b1_3», «W_i-2_b1_4», «W_i-2_b1_5», «W_i-2_b1_6», «W_i-2_b1_7», «W_i-2_b2_0», «W_i-2_b2_1», «W_i-2_b2_2»]),
      u8_recompose([«W_i-2_b0_3», «W_i-2_b0_4», «W_i-2_b0_5», «W_i-2_b0_6», «W_i-2_b0_7», «W_i-2_b1_0», «W_i-2_b1_1», «W_i-2_b1_2»]),
      u8_recompose([«W_i-2_b3_3», «W_i-2_b3_4», «W_i-2_b3_5», «W_i-2_b3_6», «W_i-2_b3_7», «W_i-2_b0_0», «W_i-2_b0_1», «W_i-2_b0_2»]),
      u8_recompose([«W_i-2_b2_3», «W_i-2_b2_4», «W_i-2_b2_5», «W_i-2_b2_6», «W_i-2_b2_7», «W_i-2_b3_0», «W_i-2_b3_1», «W_i-2_b3_2»])
    ];

    let «W_i-2_shr10» = [
      u8_recompose([0; 8]),
      u8_recompose([«W_i-2_b3_2», «W_i-2_b3_3», «W_i-2_b3_4», «W_i-2_b3_5», «W_i-2_b3_6», «W_i-2_b3_7», 0,            0]),
      u8_recompose([«W_i-2_b2_2», «W_i-2_b2_3», «W_i-2_b2_4», «W_i-2_b2_5», «W_i-2_b2_6», «W_i-2_b2_7», «W_i-2_b3_0», «W_i-2_b3_1»]),
      u8_recompose([«W_i-2_b1_2», «W_i-2_b1_3», «W_i-2_b1_4», «W_i-2_b1_5», «W_i-2_b1_6», «W_i-2_b1_7», «W_i-2_b2_0», «W_i-2_b2_1»])
    ];

    let «W_i_s0» = u32_xor(«W_i-15_rotr7», u32_xor(«W_i-15_rotr18», «W_i-15_shr3»));
    let «W_i_s1» = u32_xor(«W_i-2_rotr17», u32_xor(«W_i-2_rotr19», «W_i-2_shr10»));
    u32_be_add(«W_i-16», u32_be_add(«W_i_s0», u32_be_add(«W_i-7», «W_i_s1»)))
  }
⟧
