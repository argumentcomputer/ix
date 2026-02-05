import Ix.Aiur.Meta

namespace IxVM

#exit

def sha256 := ⟦
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
          let len_be = u64_be_add_byte(len_be, 1);
          let W = set(W, 0, [b0, 0x80, 0, 0]);
          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
          fill_W_and_run_rounds(W, state),
        ByteStream.Cons(b1, tail_ptr) => match load(tail_ptr) {
          ByteStream.Nil =>
            let len_be = u64_be_add_byte(len_be, 2);
            let W = set(W, 0, [b0, b1, 0x80, 0]);
            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
            fill_W_and_run_rounds(W, state),
          ByteStream.Cons(b2, tail_ptr) => match load(tail_ptr) {
            ByteStream.Nil =>
              let len_be = u64_be_add_byte(len_be, 3);
              let W = set(W, 0, [b0, b1, b2, 0x80]);
              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
              fill_W_and_run_rounds(W, state),
            ByteStream.Cons(b3, tail_ptr) =>
              let W = set(W, 0, [b0, b1, b2, b3]);
              match load(tail_ptr) {
              ByteStream.Nil =>
                let len_be = u64_be_add_byte(len_be, 4);
                let W = set(W, 1, [0x80, 0, 0, 0]);
                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                fill_W_and_run_rounds(W, state),
              ByteStream.Cons(b4, tail_ptr) => match load(tail_ptr) {
                ByteStream.Nil =>
                  let len_be = u64_be_add_byte(len_be, 5);
                  let W = set(W, 1, [b4, 0x80, 0, 0]);
                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                  fill_W_and_run_rounds(W, state),
                ByteStream.Cons(b5, tail_ptr) => match load(tail_ptr) {
                  ByteStream.Nil =>
                    let len_be = u64_be_add_byte(len_be, 6);
                    let W = set(W, 1, [b4, b5, 0x80, 0]);
                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                    fill_W_and_run_rounds(W, state),
                  ByteStream.Cons(b6, tail_ptr) => match load(tail_ptr) {
                    ByteStream.Nil =>
                      let len_be = u64_be_add_byte(len_be, 7);
                      let W = set(W, 1, [b4, b5, b6, 0x80]);
                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                      fill_W_and_run_rounds(W, state),
                    ByteStream.Cons(b7, tail_ptr) =>
                      let W = set(W, 1, [b4, b5, b6, b7]);
                      match load(tail_ptr) {
                      ByteStream.Nil =>
                        let len_be = u64_be_add_byte(len_be, 8);
                        let W = set(W, 2, [0x80, 0, 0, 0]);
                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                        fill_W_and_run_rounds(W, state),
                      ByteStream.Cons(b8, tail_ptr) => match load(tail_ptr) {
                        ByteStream.Nil =>
                          let len_be = u64_be_add_byte(len_be, 9);
                          let W = set(W, 2, [b8, 0x80, 0, 0]);
                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                          fill_W_and_run_rounds(W, state),
                        ByteStream.Cons(b9, tail_ptr) => match load(tail_ptr) {
                          ByteStream.Nil =>
                            let len_be = u64_be_add_byte(len_be, 10);
                            let W = set(W, 2, [b8, b9, 0x80, 0]);
                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                            fill_W_and_run_rounds(W, state),
                          ByteStream.Cons(b10, tail_ptr) => match load(tail_ptr) {
                            ByteStream.Nil =>
                              let len_be = u64_be_add_byte(len_be, 11);
                              let W = set(W, 2, [b8, b9, b10, 0x80]);
                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                              fill_W_and_run_rounds(W, state),
                            ByteStream.Cons(b11, tail_ptr) =>
                              let W = set(W, 2, [b8, b9, b10, b11]);
                              match load(tail_ptr) {
                              ByteStream.Nil =>
                                let len_be = u64_be_add_byte(len_be, 12);
                                let W = set(W, 3, [0x80, 0, 0, 0]);
                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                fill_W_and_run_rounds(W, state),
                              ByteStream.Cons(b12, tail_ptr) => match load(tail_ptr) {
                                ByteStream.Nil =>
                                  let len_be = u64_be_add_byte(len_be, 13);
                                  let W = set(W, 3, [b12, 0x80, 0, 0]);
                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                  fill_W_and_run_rounds(W, state),
                                ByteStream.Cons(b13, tail_ptr) => match load(tail_ptr) {
                                  ByteStream.Nil =>
                                    let len_be = u64_be_add_byte(len_be, 14);
                                    let W = set(W, 3, [b12, b13, 0x80, 0]);
                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                    fill_W_and_run_rounds(W, state),
                                  ByteStream.Cons(b14, tail_ptr) => match load(tail_ptr) {
                                    ByteStream.Nil =>
                                      let len_be = u64_be_add_byte(len_be, 15);
                                      let W = set(W, 3, [b12, b13, b14, 0x80]);
                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                      fill_W_and_run_rounds(W, state),
                                    ByteStream.Cons(b15, tail_ptr) =>
                                      let W = set(W, 3, [b12, b13, b14, b15]);
                                      match load(tail_ptr) {
                                      ByteStream.Nil =>
                                        let len_be = u64_be_add_byte(len_be, 16);
                                        let W = set(W, 4, [0x80, 0, 0, 0]);
                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                        fill_W_and_run_rounds(W, state),
                                      ByteStream.Cons(b16, tail_ptr) => match load(tail_ptr) {
                                        ByteStream.Nil =>
                                          let len_be = u64_be_add_byte(len_be, 17);
                                          let W = set(W, 4, [b16, 0x80, 0, 0]);
                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                          fill_W_and_run_rounds(W, state),
                                        ByteStream.Cons(b17, tail_ptr) => match load(tail_ptr) {
                                          ByteStream.Nil =>
                                            let len_be = u64_be_add_byte(len_be, 18);
                                            let W = set(W, 4, [b16, b17, 0x80, 0]);
                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                            fill_W_and_run_rounds(W, state),
                                          ByteStream.Cons(b18, tail_ptr) => match load(tail_ptr) {
                                            ByteStream.Nil =>
                                              let len_be = u64_be_add_byte(len_be, 19);
                                              let W = set(W, 4, [b16, b17, b18, 0x80]);
                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                              fill_W_and_run_rounds(W, state),
                                            ByteStream.Cons(b19, tail_ptr) =>
                                              let W = set(W, 4, [b16, b17, b18, b19]);
                                              match load(tail_ptr) {
                                              ByteStream.Nil =>
                                                let len_be = u64_be_add_byte(len_be, 20);
                                                let W = set(W, 5, [0x80, 0, 0, 0]);
                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                fill_W_and_run_rounds(W, state),
                                              ByteStream.Cons(b20, tail_ptr) => match load(tail_ptr) {
                                                ByteStream.Nil =>
                                                  let len_be = u64_be_add_byte(len_be, 21);
                                                  let W = set(W, 5, [b20, 0x80, 0, 0]);
                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                  fill_W_and_run_rounds(W, state),
                                                ByteStream.Cons(b21, tail_ptr) => match load(tail_ptr) {
                                                  ByteStream.Nil =>
                                                    let len_be = u64_be_add_byte(len_be, 22);
                                                    let W = set(W, 5, [b20, b21, 0x80, 0]);
                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                    fill_W_and_run_rounds(W, state),
                                                  ByteStream.Cons(b22, tail_ptr) => match load(tail_ptr) {
                                                    ByteStream.Nil =>
                                                      let len_be = u64_be_add_byte(len_be, 23);
                                                      let W = set(W, 5, [b20, b21, b22, 0x80]);
                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                      fill_W_and_run_rounds(W, state),
                                                    ByteStream.Cons(b23, tail_ptr) =>
                                                      let W = set(W, 5, [b20, b21, b22, b23]);
                                                      match load(tail_ptr) {
                                                      ByteStream.Nil =>
                                                        let len_be = u64_be_add_byte(len_be, 24);
                                                        let W = set(W, 6, [0x80, 0, 0, 0]);
                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                        fill_W_and_run_rounds(W, state),
                                                      ByteStream.Cons(b24, tail_ptr) => match load(tail_ptr) {
                                                        ByteStream.Nil =>
                                                          let len_be = u64_be_add_byte(len_be, 25);
                                                          let W = set(W, 6, [b24, 0x80, 0, 0]);
                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                          fill_W_and_run_rounds(W, state),
                                                        ByteStream.Cons(b25, tail_ptr) => match load(tail_ptr) {
                                                          ByteStream.Nil =>
                                                            let len_be = u64_be_add_byte(len_be, 26);
                                                            let W = set(W, 6, [b24, b25, 0x80, 0]);
                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                            fill_W_and_run_rounds(W, state),
                                                          ByteStream.Cons(b26, tail_ptr) => match load(tail_ptr) {
                                                            ByteStream.Nil =>
                                                              let len_be = u64_be_add_byte(len_be, 27);
                                                              let W = set(W, 6, [b24, b25, b26, 0x80]);
                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                              fill_W_and_run_rounds(W, state),
                                                            ByteStream.Cons(b27, tail_ptr) =>
                                                              let W = set(W, 6, [b24, b25, b26, b27]);
                                                              match load(tail_ptr) {
                                                              ByteStream.Nil =>
                                                                let len_be = u64_be_add_byte(len_be, 28);
                                                                let W = set(W, 7, [0x80, 0, 0, 0]);
                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                fill_W_and_run_rounds(W, state),
                                                              ByteStream.Cons(b28, tail_ptr) => match load(tail_ptr) {
                                                                ByteStream.Nil =>
                                                                  let len_be = u64_be_add_byte(len_be, 29);
                                                                  let W = set(W, 7, [b28, 0x80, 0, 0]);
                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                  fill_W_and_run_rounds(W, state),
                                                                ByteStream.Cons(b29, tail_ptr) => match load(tail_ptr) {
                                                                  ByteStream.Nil =>
                                                                    let len_be = u64_be_add_byte(len_be, 30);
                                                                    let W = set(W, 7, [b28, b29, 0x80, 0]);
                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                    fill_W_and_run_rounds(W, state),
                                                                  ByteStream.Cons(b30, tail_ptr) => match load(tail_ptr) {
                                                                    ByteStream.Nil =>
                                                                      let len_be = u64_be_add_byte(len_be, 31);
                                                                      let W = set(W, 7, [b28, b29, b30, 0x80]);
                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                      fill_W_and_run_rounds(W, state),
                                                                    ByteStream.Cons(b31, tail_ptr) =>
                                                                      let W = set(W, 7, [b28, b29, b30, b31]);
                                                                      match load(tail_ptr) {
                                                                      ByteStream.Nil =>
                                                                        let len_be = u64_be_add_byte(len_be, 32);
                                                                        let W = set(W, 8, [0x80, 0, 0, 0]);
                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                        fill_W_and_run_rounds(W, state),
                                                                      ByteStream.Cons(b32, tail_ptr) => match load(tail_ptr) {
                                                                        ByteStream.Nil =>
                                                                          let len_be = u64_be_add_byte(len_be, 33);
                                                                          let W = set(W, 8, [b32, 0x80, 0, 0]);
                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                          fill_W_and_run_rounds(W, state),
                                                                        ByteStream.Cons(b33, tail_ptr) => match load(tail_ptr) {
                                                                          ByteStream.Nil =>
                                                                            let len_be = u64_be_add_byte(len_be, 34);
                                                                            let W = set(W, 8, [b32, b33, 0x80, 0]);
                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                            fill_W_and_run_rounds(W, state),
                                                                          ByteStream.Cons(b34, tail_ptr) => match load(tail_ptr) {
                                                                            ByteStream.Nil =>
                                                                              let len_be = u64_be_add_byte(len_be, 35);
                                                                              let W = set(W, 8, [b32, b33, b34, 0x80]);
                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                              fill_W_and_run_rounds(W, state),
                                                                            ByteStream.Cons(b35, tail_ptr) =>
                                                                              let W = set(W, 8, [b32, b33, b34, b35]);
                                                                              match load(tail_ptr) {
                                                                              ByteStream.Nil =>
                                                                                let len_be = u64_be_add_byte(len_be, 36);
                                                                                let W = set(W, 9, [0x80, 0, 0, 0]);
                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                fill_W_and_run_rounds(W, state),
                                                                              ByteStream.Cons(b36, tail_ptr) => match load(tail_ptr) {
                                                                                ByteStream.Nil =>
                                                                                  let len_be = u64_be_add_byte(len_be, 37);
                                                                                  let W = set(W, 9, [b36, 0x80, 0, 0]);
                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                  fill_W_and_run_rounds(W, state),
                                                                                ByteStream.Cons(b37, tail_ptr) => match load(tail_ptr) {
                                                                                  ByteStream.Nil =>
                                                                                    let len_be = u64_be_add_byte(len_be, 38);
                                                                                    let W = set(W, 9, [b36, b37, 0x80, 0]);
                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                    fill_W_and_run_rounds(W, state),
                                                                                  ByteStream.Cons(b38, tail_ptr) => match load(tail_ptr) {
                                                                                    ByteStream.Nil =>
                                                                                      let len_be = u64_be_add_byte(len_be, 39);
                                                                                      let W = set(W, 9, [b36, b37, b38, 0x80]);
                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                      fill_W_and_run_rounds(W, state),
                                                                                    ByteStream.Cons(b39, tail_ptr) =>
                                                                                      let W = set(W, 9, [b36, b37, b38, b39]);
                                                                                      match load(tail_ptr) {
                                                                                      ByteStream.Nil =>
                                                                                        let len_be = u64_be_add_byte(len_be, 40);
                                                                                        let W = set(W, 10, [0x80, 0, 0, 0]);
                                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                        fill_W_and_run_rounds(W, state),
                                                                                      ByteStream.Cons(b40, tail_ptr) => match load(tail_ptr) {
                                                                                        ByteStream.Nil =>
                                                                                          let len_be = u64_be_add_byte(len_be, 41);
                                                                                          let W = set(W, 10, [b40, 0x80, 0, 0]);
                                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                          fill_W_and_run_rounds(W, state),
                                                                                        ByteStream.Cons(b41, tail_ptr) => match load(tail_ptr) {
                                                                                          ByteStream.Nil =>
                                                                                            let len_be = u64_be_add_byte(len_be, 42);
                                                                                            let W = set(W, 10, [b40, b41, 0x80, 0]);
                                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                            fill_W_and_run_rounds(W, state),
                                                                                          ByteStream.Cons(b42, tail_ptr) => match load(tail_ptr) {
                                                                                            ByteStream.Nil =>
                                                                                              let len_be = u64_be_add_byte(len_be, 43);
                                                                                              let W = set(W, 10, [b40, b41, b42, 0x80]);
                                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                              fill_W_and_run_rounds(W, state),
                                                                                            ByteStream.Cons(b43, tail_ptr) =>
                                                                                              let W = set(W, 10, [b40, b41, b42, b43]);
                                                                                              match load(tail_ptr) {
                                                                                              ByteStream.Nil =>
                                                                                                let len_be = u64_be_add_byte(len_be, 44);
                                                                                                let W = set(W, 11, [0x80, 0, 0, 0]);
                                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                fill_W_and_run_rounds(W, state),
                                                                                              ByteStream.Cons(b44, tail_ptr) => match load(tail_ptr) {
                                                                                                ByteStream.Nil =>
                                                                                                  let len_be = u64_be_add_byte(len_be, 45);
                                                                                                  let W = set(W, 11, [b44, 0x80, 0, 0]);
                                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                  fill_W_and_run_rounds(W, state),
                                                                                                ByteStream.Cons(b45, tail_ptr) => match load(tail_ptr) {
                                                                                                  ByteStream.Nil =>
                                                                                                    let len_be = u64_be_add_byte(len_be, 46);
                                                                                                    let W = set(W, 11, [b44, b45, 0x80, 0]);
                                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                    fill_W_and_run_rounds(W, state),
                                                                                                  ByteStream.Cons(b46, tail_ptr) => match load(tail_ptr) {
                                                                                                    ByteStream.Nil =>
                                                                                                      let len_be = u64_be_add_byte(len_be, 47);
                                                                                                      let W = set(W, 11, [b44, b45, b46, 0x80]);
                                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                      fill_W_and_run_rounds(W, state),
                                                                                                    ByteStream.Cons(b47, tail_ptr) =>
                                                                                                      let W = set(W, 11, [b44, b45, b46, b47]);
                                                                                                      match load(tail_ptr) {
                                                                                                      ByteStream.Nil =>
                                                                                                        let len_be = u64_be_add_byte(len_be, 48);
                                                                                                        let W = set(W, 12, [0x80, 0, 0, 0]);
                                                                                                        let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                        let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                        fill_W_and_run_rounds(W, state),
                                                                                                      ByteStream.Cons(b48, tail_ptr) => match load(tail_ptr) {
                                                                                                        ByteStream.Nil =>
                                                                                                          let len_be = u64_be_add_byte(len_be, 49);
                                                                                                          let W = set(W, 12, [b48, 0x80, 0, 0]);
                                                                                                          let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                          let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                          fill_W_and_run_rounds(W, state),
                                                                                                        ByteStream.Cons(b49, tail_ptr) => match load(tail_ptr) {
                                                                                                          ByteStream.Nil =>
                                                                                                            let len_be = u64_be_add_byte(len_be, 50);
                                                                                                            let W = set(W, 12, [b48, b49, 0x80, 0]);
                                                                                                            let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                            let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                            fill_W_and_run_rounds(W, state),
                                                                                                          ByteStream.Cons(b50, tail_ptr) => match load(tail_ptr) {
                                                                                                            ByteStream.Nil =>
                                                                                                              let len_be = u64_be_add_byte(len_be, 51);
                                                                                                              let W = set(W, 12, [b48, b49, b50, 0x80]);
                                                                                                              let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                              let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                              fill_W_and_run_rounds(W, state),
                                                                                                            ByteStream.Cons(b51, tail_ptr) =>
                                                                                                              let W = set(W, 12, [b48, b49, b50, b51]);
                                                                                                              match load(tail_ptr) {
                                                                                                              ByteStream.Nil =>
                                                                                                                let len_be = u64_be_add_byte(len_be, 52);
                                                                                                                let W = set(W, 13, [0x80, 0, 0, 0]);
                                                                                                                let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                fill_W_and_run_rounds(W, state),
                                                                                                              ByteStream.Cons(b52, tail_ptr) => match load(tail_ptr) {
                                                                                                                ByteStream.Nil =>
                                                                                                                  let len_be = u64_be_add_byte(len_be, 53);
                                                                                                                  let W = set(W, 13, [b52, 0x80, 0, 0]);
                                                                                                                  let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                  let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                  fill_W_and_run_rounds(W, state),
                                                                                                                ByteStream.Cons(b53, tail_ptr) => match load(tail_ptr) {
                                                                                                                  ByteStream.Nil =>
                                                                                                                    let len_be = u64_be_add_byte(len_be, 54);
                                                                                                                    let W = set(W, 13, [b52, b53, 0x80, 0]);
                                                                                                                    let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                    let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                    fill_W_and_run_rounds(W, state),
                                                                                                                  ByteStream.Cons(b54, tail_ptr) => match load(tail_ptr) {
                                                                                                                    ByteStream.Nil =>
                                                                                                                      let len_be = u64_be_add_byte(len_be, 55);
                                                                                                                      let W = set(W, 13, [b52, b53, b54, 0x80]);
                                                                                                                      let W = set(W, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                      let W = set(W, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                      fill_W_and_run_rounds(W, state),
                                                                                                                    ByteStream.Cons(b55, tail_ptr) =>
                                                                                                                      let W = set(W, 13, [b52, b53, b54, b55]);
                                                                                                                      match load(tail_ptr) {
                                                                                                                      ByteStream.Nil =>
                                                                                                                        let len_be = u64_be_add_byte(len_be, 56);
                                                                                                                        let W = set(W, 14, [0x80, 0, 0, 0]);
                                                                                                                        let W2 = [[0; 4]; 16];
                                                                                                                        let W2 = set(W2, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                        let W2 = set(W2, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                        let state = fill_W_and_run_rounds(W, state);
                                                                                                                        fill_W_and_run_rounds(W2, state),
                                                                                                                      ByteStream.Cons(b56, tail_ptr) => match load(tail_ptr) {
                                                                                                                        ByteStream.Nil =>
                                                                                                                          let len_be = u64_be_add_byte(len_be, 57);
                                                                                                                          let W = set(W, 14, [b56, 0x80, 0, 0]);
                                                                                                                          let W2 = [[0; 4]; 16];
                                                                                                                          let W2 = set(W2, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                          let W2 = set(W2, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                          let state = fill_W_and_run_rounds(W, state);
                                                                                                                          fill_W_and_run_rounds(W2, state),
                                                                                                                        ByteStream.Cons(b57, tail_ptr) => match load(tail_ptr) {
                                                                                                                          ByteStream.Nil =>
                                                                                                                            let len_be = u64_be_add_byte(len_be, 58);
                                                                                                                            let W = set(W, 14, [b56, b57, 0x80, 0]);
                                                                                                                            let W2 = [[0; 4]; 16];
                                                                                                                            let W2 = set(W2, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                            let W2 = set(W2, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                            let state = fill_W_and_run_rounds(W, state);
                                                                                                                            fill_W_and_run_rounds(W2, state),
                                                                                                                          ByteStream.Cons(b58, tail_ptr) => match load(tail_ptr) {
                                                                                                                            ByteStream.Nil =>
                                                                                                                              let len_be = u64_be_add_byte(len_be, 59);
                                                                                                                              let W = set(W, 14, [b56, b57, b58, 0x80]);
                                                                                                                              let W2 = [[0; 4]; 16];
                                                                                                                              let W2 = set(W2, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                              let W2 = set(W2, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                              let state = fill_W_and_run_rounds(W, state);
                                                                                                                              fill_W_and_run_rounds(W2, state),
                                                                                                                            ByteStream.Cons(b59, tail_ptr) =>
                                                                                                                              let W = set(W, 14, [b56, b57, b58, b59]);
                                                                                                                              match load(tail_ptr) {
                                                                                                                              ByteStream.Nil =>
                                                                                                                                let len_be = u64_be_add_byte(len_be, 60);
                                                                                                                                let W = set(W, 15, [0x80, 0, 0, 0]);
                                                                                                                                let W2 = [[0; 4]; 16];
                                                                                                                                let W2 = set(W2, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                                let W2 = set(W2, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                                let state = fill_W_and_run_rounds(W, state);
                                                                                                                                fill_W_and_run_rounds(W2, state),
                                                                                                                              ByteStream.Cons(b60, tail_ptr) => match load(tail_ptr) {
                                                                                                                                ByteStream.Nil =>
                                                                                                                                  let len_be = u64_be_add_byte(len_be, 61);
                                                                                                                                  let W = set(W, 15, [b60, 0x80, 0, 0]);
                                                                                                                                  let W2 = [[0; 4]; 16];
                                                                                                                                  let W2 = set(W2, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                                  let W2 = set(W2, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                                  let state = fill_W_and_run_rounds(W, state);
                                                                                                                                  fill_W_and_run_rounds(W2, state),
                                                                                                                                ByteStream.Cons(b61, tail_ptr) => match load(tail_ptr) {
                                                                                                                                  ByteStream.Nil =>
                                                                                                                                    let len_be = u64_be_add_byte(len_be, 62);
                                                                                                                                    let W = set(W, 15, [b60, b61, 0x80, 0]);
                                                                                                                                    let W2 = [[0; 4]; 16];
                                                                                                                                    let W2 = set(W2, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                                    let W2 = set(W2, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                                    let state = fill_W_and_run_rounds(W, state);
                                                                                                                                    fill_W_and_run_rounds(W2, state),
                                                                                                                                  ByteStream.Cons(b62, tail_ptr) => match load(tail_ptr) {
                                                                                                                                    ByteStream.Nil =>
                                                                                                                                      let len_be = u64_be_add_byte(len_be, 63);
                                                                                                                                      let W = set(W, 15, [b60, b61, b62, 0x80]);
                                                                                                                                      let W2 = [[0; 4]; 16];
                                                                                                                                      let W2 = set(W2, 14, [len_be[0], len_be[1], len_be[2], len_be[3]]);
                                                                                                                                      let W2 = set(W2, 15, [len_be[4], len_be[5], len_be[6], len_be[7]]);
                                                                                                                                      let state = fill_W_and_run_rounds(W, state);
                                                                                                                                      fill_W_and_run_rounds(W2, state),
                                                                                                                                    ByteStream.Cons(b63, tail_ptr) =>
                                                                                                                                      let len_be = u64_be_add_byte(len_be, 64);
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

    -- Define W_16

    let [W_1_b3, W_1_b2, W_1_b1, W_1_b0] = W[1];
    let [W_1_b0_0, W_1_b0_1, W_1_b0_2, W_1_b0_3, W_1_b0_4, W_1_b0_5, W_1_b0_6, W_1_b0_7] = u8_bit_decomposition(W_1_b0);
    let [W_1_b1_0, W_1_b1_1, W_1_b1_2, W_1_b1_3, W_1_b1_4, W_1_b1_5, W_1_b1_6, W_1_b1_7] = u8_bit_decomposition(W_1_b1);
    let [W_1_b2_0, W_1_b2_1, W_1_b2_2, W_1_b2_3, W_1_b2_4, W_1_b2_5, W_1_b2_6, W_1_b2_7] = u8_bit_decomposition(W_1_b2);
    let [W_1_b3_0, W_1_b3_1, W_1_b3_2, W_1_b3_3, W_1_b3_4, W_1_b3_5, W_1_b3_6, W_1_b3_7] = u8_bit_decomposition(W_1_b3);

    let W_1_rotr7 = [
      u8_recompose([W_1_b3_7, W_1_b0_0, W_1_b0_1, W_1_b0_2, W_1_b0_3, W_1_b0_4, W_1_b0_5, W_1_b0_6]),
      u8_recompose([W_1_b2_7, W_1_b3_0, W_1_b3_1, W_1_b3_2, W_1_b3_3, W_1_b3_4, W_1_b3_5, W_1_b3_6]),
      u8_recompose([W_1_b1_7, W_1_b2_0, W_1_b2_1, W_1_b2_2, W_1_b2_3, W_1_b2_4, W_1_b2_5, W_1_b2_6]),
      u8_recompose([W_1_b0_7, W_1_b1_0, W_1_b1_1, W_1_b1_2, W_1_b1_3, W_1_b1_4, W_1_b1_5, W_1_b1_6])
    ];

    let W_1_rotr18 = [
      u8_recompose([W_1_b1_2, W_1_b1_3, W_1_b1_4, W_1_b1_5, W_1_b1_6, W_1_b1_7, W_1_b2_0, W_1_b2_1]),
      u8_recompose([W_1_b0_2, W_1_b0_3, W_1_b0_4, W_1_b0_5, W_1_b0_6, W_1_b0_7, W_1_b1_0, W_1_b1_1]),
      u8_recompose([W_1_b3_2, W_1_b3_3, W_1_b3_4, W_1_b3_5, W_1_b3_6, W_1_b3_7, W_1_b0_0, W_1_b0_1]),
      u8_recompose([W_1_b2_2, W_1_b2_3, W_1_b2_4, W_1_b2_5, W_1_b2_6, W_1_b2_7, W_1_b3_0, W_1_b3_1])
    ];

    let W_1_shr3 = [
      u8_recompose([W_1_b3_3, W_1_b3_4, W_1_b3_5, W_1_b3_6, W_1_b3_7, 0,        0,        0]),
      u8_recompose([W_1_b2_3, W_1_b2_4, W_1_b2_5, W_1_b2_6, W_1_b2_7, W_1_b3_0, W_1_b3_1, W_1_b3_2]),
      u8_recompose([W_1_b1_3, W_1_b1_4, W_1_b1_5, W_1_b1_6, W_1_b1_7, W_1_b2_0, W_1_b2_1, W_1_b2_2]),
      u8_recompose([W_1_b0_3, W_1_b0_4, W_1_b0_5, W_1_b0_6, W_1_b0_7, W_1_b1_0, W_1_b1_1, W_1_b1_2])
    ];

    let [W_14_b3, W_14_b2, W_14_b1, W_14_b0] = W[14];
    let [W_14_b0_0, W_14_b0_1, W_14_b0_2, W_14_b0_3, W_14_b0_4, W_14_b0_5, W_14_b0_6, W_14_b0_7] = u8_bit_decomposition(W_14_b0);
    let [W_14_b1_0, W_14_b1_1, W_14_b1_2, W_14_b1_3, W_14_b1_4, W_14_b1_5, W_14_b1_6, W_14_b1_7] = u8_bit_decomposition(W_14_b1);
    let [W_14_b2_0, W_14_b2_1, W_14_b2_2, W_14_b2_3, W_14_b2_4, W_14_b2_5, W_14_b2_6, W_14_b2_7] = u8_bit_decomposition(W_14_b2);
    let [W_14_b3_0, W_14_b3_1, W_14_b3_2, W_14_b3_3, W_14_b3_4, W_14_b3_5, W_14_b3_6, W_14_b3_7] = u8_bit_decomposition(W_14_b3);

    let W_14_rotr17 = [
      u8_recompose([W_14_b1_1, W_14_b1_2, W_14_b1_3, W_14_b1_4, W_14_b1_5, W_14_b1_6, W_14_b1_7, W_14_b2_0]),
      u8_recompose([W_14_b0_1, W_14_b0_2, W_14_b0_3, W_14_b0_4, W_14_b0_5, W_14_b0_6, W_14_b0_7, W_14_b1_0]),
      u8_recompose([W_14_b3_1, W_14_b3_2, W_14_b3_3, W_14_b3_4, W_14_b3_5, W_14_b3_6, W_14_b3_7, W_14_b0_0]),
      u8_recompose([W_14_b2_1, W_14_b2_2, W_14_b2_3, W_14_b2_4, W_14_b2_5, W_14_b2_6, W_14_b2_7, W_14_b3_0])
    ];

    let W_14_rotr19 = [
      u8_recompose([W_14_b1_3, W_14_b1_4, W_14_b1_5, W_14_b1_6, W_14_b1_7, W_14_b2_0, W_14_b2_1, W_14_b2_2]),
      u8_recompose([W_14_b0_3, W_14_b0_4, W_14_b0_5, W_14_b0_6, W_14_b0_7, W_14_b1_0, W_14_b1_1, W_14_b1_2]),
      u8_recompose([W_14_b3_3, W_14_b3_4, W_14_b3_5, W_14_b3_6, W_14_b3_7, W_14_b0_0, W_14_b0_1, W_14_b0_2]),
      u8_recompose([W_14_b2_3, W_14_b2_4, W_14_b2_5, W_14_b2_6, W_14_b2_7, W_14_b3_0, W_14_b3_1, W_14_b3_2])
    ];

    let W_14_shr10 = [
      u8_recompose([0; 8]),
      u8_recompose([W_14_b3_2, W_14_b3_3, W_14_b3_4, W_14_b3_5, W_14_b3_6, W_14_b3_7, 0,         0]),
      u8_recompose([W_14_b2_2, W_14_b2_3, W_14_b2_4, W_14_b2_5, W_14_b2_6, W_14_b2_7, W_14_b3_0, W_14_b3_1]),
      u8_recompose([W_14_b1_2, W_14_b1_3, W_14_b1_4, W_14_b1_5, W_14_b1_6, W_14_b1_7, W_14_b2_0, W_14_b2_1])
    ];

    let W_16_s0 = u32_xor(W_1_rotr7, u32_xor(W_1_rotr18, W_1_shr3));
    let W_16_s1 = u32_xor(W_14_rotr17, u32_xor(W_14_rotr19, W_14_shr10));
    let W_16 = u32_be_add(W[0], u32_be_add(W_16_s0, u32_be_add(W[9], W_16_s1)));

    -- Define W_17

    let [W_2_b3, W_2_b2, W_2_b1, W_2_b0] = W[2];
    let [W_2_b0_0, W_2_b0_1, W_2_b0_2, W_2_b0_3, W_2_b0_4, W_2_b0_5, W_2_b0_6, W_2_b0_7] = u8_bit_decomposition(W_2_b0);
    let [W_2_b1_0, W_2_b1_1, W_2_b1_2, W_2_b1_3, W_2_b1_4, W_2_b1_5, W_2_b1_6, W_2_b1_7] = u8_bit_decomposition(W_2_b1);
    let [W_2_b2_0, W_2_b2_1, W_2_b2_2, W_2_b2_3, W_2_b2_4, W_2_b2_5, W_2_b2_6, W_2_b2_7] = u8_bit_decomposition(W_2_b2);
    let [W_2_b3_0, W_2_b3_1, W_2_b3_2, W_2_b3_3, W_2_b3_4, W_2_b3_5, W_2_b3_6, W_2_b3_7] = u8_bit_decomposition(W_2_b3);

    let W_2_rotr7 = [
      u8_recompose([W_2_b3_7, W_2_b0_0, W_2_b0_1, W_2_b0_2, W_2_b0_3, W_2_b0_4, W_2_b0_5, W_2_b0_6]),
      u8_recompose([W_2_b2_7, W_2_b3_0, W_2_b3_1, W_2_b3_2, W_2_b3_3, W_2_b3_4, W_2_b3_5, W_2_b3_6]),
      u8_recompose([W_2_b1_7, W_2_b2_0, W_2_b2_1, W_2_b2_2, W_2_b2_3, W_2_b2_4, W_2_b2_5, W_2_b2_6]),
      u8_recompose([W_2_b0_7, W_2_b1_0, W_2_b1_1, W_2_b1_2, W_2_b1_3, W_2_b1_4, W_2_b1_5, W_2_b1_6])
    ];

    let W_2_rotr18 = [
      u8_recompose([W_2_b1_2, W_2_b1_3, W_2_b1_4, W_2_b1_5, W_2_b1_6, W_2_b1_7, W_2_b2_0, W_2_b2_1]),
      u8_recompose([W_2_b0_2, W_2_b0_3, W_2_b0_4, W_2_b0_5, W_2_b0_6, W_2_b0_7, W_2_b1_0, W_2_b1_1]),
      u8_recompose([W_2_b3_2, W_2_b3_3, W_2_b3_4, W_2_b3_5, W_2_b3_6, W_2_b3_7, W_2_b0_0, W_2_b0_1]),
      u8_recompose([W_2_b2_2, W_2_b2_3, W_2_b2_4, W_2_b2_5, W_2_b2_6, W_2_b2_7, W_2_b3_0, W_2_b3_1])
    ];

    let W_2_shr3 = [
      u8_recompose([W_2_b3_3, W_2_b3_4, W_2_b3_5, W_2_b3_6, W_2_b3_7, 0,        0,        0]),
      u8_recompose([W_2_b2_3, W_2_b2_4, W_2_b2_5, W_2_b2_6, W_2_b2_7, W_2_b3_0, W_2_b3_1, W_2_b3_2]),
      u8_recompose([W_2_b1_3, W_2_b1_4, W_2_b1_5, W_2_b1_6, W_2_b1_7, W_2_b2_0, W_2_b2_1, W_2_b2_2]),
      u8_recompose([W_2_b0_3, W_2_b0_4, W_2_b0_5, W_2_b0_6, W_2_b0_7, W_2_b1_0, W_2_b1_1, W_2_b1_2])
    ];

    let [W_15_b3, W_15_b2, W_15_b1, W_15_b0] = W[15];
    let [W_15_b0_0, W_15_b0_1, W_15_b0_2, W_15_b0_3, W_15_b0_4, W_15_b0_5, W_15_b0_6, W_15_b0_7] = u8_bit_decomposition(W_15_b0);
    let [W_15_b1_0, W_15_b1_1, W_15_b1_2, W_15_b1_3, W_15_b1_4, W_15_b1_5, W_15_b1_6, W_15_b1_7] = u8_bit_decomposition(W_15_b1);
    let [W_15_b2_0, W_15_b2_1, W_15_b2_2, W_15_b2_3, W_15_b2_4, W_15_b2_5, W_15_b2_6, W_15_b2_7] = u8_bit_decomposition(W_15_b2);
    let [W_15_b3_0, W_15_b3_1, W_15_b3_2, W_15_b3_3, W_15_b3_4, W_15_b3_5, W_15_b3_6, W_15_b3_7] = u8_bit_decomposition(W_15_b3);

    let W_15_rotr17 = [
      u8_recompose([W_15_b1_1, W_15_b1_2, W_15_b1_3, W_15_b1_4, W_15_b1_5, W_15_b1_6, W_15_b1_7, W_15_b2_0]),
      u8_recompose([W_15_b0_1, W_15_b0_2, W_15_b0_3, W_15_b0_4, W_15_b0_5, W_15_b0_6, W_15_b0_7, W_15_b1_0]),
      u8_recompose([W_15_b3_1, W_15_b3_2, W_15_b3_3, W_15_b3_4, W_15_b3_5, W_15_b3_6, W_15_b3_7, W_15_b0_0]),
      u8_recompose([W_15_b2_1, W_15_b2_2, W_15_b2_3, W_15_b2_4, W_15_b2_5, W_15_b2_6, W_15_b2_7, W_15_b3_0])
    ];

    let W_15_rotr19 = [
      u8_recompose([W_15_b1_3, W_15_b1_4, W_15_b1_5, W_15_b1_6, W_15_b1_7, W_15_b2_0, W_15_b2_1, W_15_b2_2]),
      u8_recompose([W_15_b0_3, W_15_b0_4, W_15_b0_5, W_15_b0_6, W_15_b0_7, W_15_b1_0, W_15_b1_1, W_15_b1_2]),
      u8_recompose([W_15_b3_3, W_15_b3_4, W_15_b3_5, W_15_b3_6, W_15_b3_7, W_15_b0_0, W_15_b0_1, W_15_b0_2]),
      u8_recompose([W_15_b2_3, W_15_b2_4, W_15_b2_5, W_15_b2_6, W_15_b2_7, W_15_b3_0, W_15_b3_1, W_15_b3_2])
    ];

    let W_15_shr10 = [
      u8_recompose([0; 8]),
      u8_recompose([W_15_b3_2, W_15_b3_3, W_15_b3_4, W_15_b3_5, W_15_b3_6, W_15_b3_7, 0,         0]),
      u8_recompose([W_15_b2_2, W_15_b2_3, W_15_b2_4, W_15_b2_5, W_15_b2_6, W_15_b2_7, W_15_b3_0, W_15_b3_1]),
      u8_recompose([W_15_b1_2, W_15_b1_3, W_15_b1_4, W_15_b1_5, W_15_b1_6, W_15_b1_7, W_15_b2_0, W_15_b2_1])
    ];

    let W_17_s0 = u32_xor(W_2_rotr7, u32_xor(W_2_rotr18, W_2_shr3));
    let W_17_s1 = u32_xor(W_15_rotr17, u32_xor(W_15_rotr19, W_15_shr10));
    let W_17 = u32_be_add(W[1], u32_be_add(W_17_s0, u32_be_add(W[10], W_17_s1)));

    -- Define W_18

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
    let [a, b, c, d, e, f, g, h] = fold(0 .. 64, state, |[a, b, c, d, e, f, g, h], @i|
      let [e_b3, e_b2, e_b1, e_b0] = e;
      let [e_b0_0, e_b0_1, e_b0_2, e_b0_3, e_b0_4, e_b0_5, e_b0_6, e_b0_7] = u8_bit_decomposition(e_b0);
      let [e_b1_0, e_b1_1, e_b1_2, e_b1_3, e_b1_4, e_b1_5, e_b1_6, e_b1_7] = u8_bit_decomposition(e_b1);
      let [e_b2_0, e_b2_1, e_b2_2, e_b2_3, e_b2_4, e_b2_5, e_b2_6, e_b2_7] = u8_bit_decomposition(e_b2);
      let [e_b3_0, e_b3_1, e_b3_2, e_b3_3, e_b3_4, e_b3_5, e_b3_6, e_b3_7] = u8_bit_decomposition(e_b3);

      let e_rotr6 = [
        u8_recompose([e_b3_6, e_b3_7, e_b0_0, e_b0_1, e_b0_2, e_b0_3, e_b0_4, e_b0_5]),
        u8_recompose([e_b2_6, e_b2_7, e_b3_0, e_b3_1, e_b3_2, e_b3_3, e_b3_4, e_b3_5]),
        u8_recompose([e_b1_6, e_b1_7, e_b2_0, e_b2_1, e_b2_2, e_b2_3, e_b2_4, e_b2_5]),
        u8_recompose([e_b0_6, e_b0_7, e_b1_0, e_b1_1, e_b1_2, e_b1_3, e_b1_4, e_b1_5])
      ];

      let e_rotr11 = [
        u8_recompose([e_b3_6, e_b3_7, e_b0_0, e_b0_1, e_b0_2, e_b0_3, e_b0_4, e_b0_5]),
        u8_recompose([e_b2_6, e_b2_7, e_b3_0, e_b3_1, e_b3_2, e_b3_3, e_b3_4, e_b3_5]),
        u8_recompose([e_b1_6, e_b1_7, e_b2_0, e_b2_1, e_b2_2, e_b2_3, e_b2_4, e_b2_5]),
        u8_recompose([e_b0_6, e_b0_7, e_b1_0, e_b1_1, e_b1_2, e_b1_3, e_b1_4, e_b1_5])
      ];

      let e_rotr25 = [
        u8_recompose([e_b2_1, e_b2_2, e_b2_3, e_b2_4, e_b2_5, e_b2_6, e_b2_7, e_b3_0]),
        u8_recompose([e_b1_1, e_b1_2, e_b1_3, e_b1_4, e_b1_5, e_b1_6, e_b1_7, e_b2_0]),
        u8_recompose([e_b0_1, e_b0_2, e_b0_3, e_b0_4, e_b0_5, e_b0_6, e_b0_7, e_b1_0]),
        u8_recompose([e_b3_1, e_b3_2, e_b3_3, e_b3_4, e_b3_5, e_b3_6, e_b3_7, e_b0_0])
      ];

      todo
    );
    [
      u32_be_add(state[0], a),
      u32_be_add(state[1], b),
      u32_be_add(state[2], c),
      u32_be_add(state[3], d),
      u32_be_add(state[4], e),
      u32_be_add(state[5], f),
      u32_be_add(state[6], g),
      u32_be_add(state[7], h)
    ]
  }

  fn u32_be_add(a: [G; 4], b: [G; 4]) -> [G; 4] {
    let [a3, a2, a1, a0] = a;
    let [b3, b2, b1, b0] = b;

    -- Byte 0, no initial carry
    let (sum0, carry1) = u8_add(a0, b0);

    -- Byte 1
    let (sum1, overflow1) = u8_add(a1, b1);
    let (sum1_with_carry, carry1a) = u8_add(sum1, carry1);
    let carry2 = u8_xor(overflow1, carry1a);

    -- Byte 2
    let (sum2, overflow2) = u8_add(a2, b2);
    let (sum2_with_carry, carry2a) = u8_add(sum2, carry2);
    let carry3 = u8_xor(overflow2, carry2a);

    -- Byte 3
    let (sum3, _x) = u8_add(a3, b3);
    let (sum3_with_carry, _x) = u8_add(sum3, carry3);

    [sum3_with_carry, sum2_with_carry, sum1_with_carry, sum0]
  }

  fn u64_be_add_byte(a: [G; 8], b: G) -> [G; 8] {
    let [a7, a6, a5, a4, a3, a2, a1, a0] = a;
    let (sum0, carry1) = u8_add(a0, b);
    let (sum1, carry2) = u8_add(a1, carry1);
    let (sum2, carry3) = u8_add(a2, carry2);
    let (sum3, carry4) = u8_add(a3, carry3);
    let (sum4, carry5) = u8_add(a4, carry4);
    let (sum5, carry6) = u8_add(a5, carry5);
    let (sum6, carry7) = u8_add(a6, carry6);
    let (sum7, _carry8) = u8_add(a7, carry7);
    [sum7, sum6, sum5, sum4, sum3, sum2, sum1, sum0]
  }

  fn u32_and(a: [G; 4], b: [G; 4]) -> [G; 4] {
    let [a0, a1, a2, a3] = a;
    let [b0, b1, b2, b3] = b;
    let c0 = u8_and(a0, b0);
    let c1 = u8_and(a1, b1);
    let c2 = u8_and(a2, b2);
    let c3 = u8_and(a3, b3);
    [c0, c1, c2, c3]
  }

  -- -- Computes the successor of an `u64` assumed to be properly represented in
  -- -- big-endian bytes. If that's not the case, this implementation has UB.
  -- fn relaxed_u64_be_succ(bytes: [G; 8]) -> [G; 8] {
  --   let [b7, b6, b5, b4, b3, b2, b1, b0] = bytes;
  --   match b0 {
  --     255 => match b1 {
  --       255 => match b2 {
  --         255 => match b3 {
  --           255 => match b4 {
  --             255 => match b5 {
  --               255 => match b6 {
  --                 255 => match b7 {
  --                   255 => [0, 0, 0, 0, 0, 0, 0, 0],
  --                   _ => [b7 + 1, 0, 0, 0, 0, 0, 0, 0],
  --                 },
  --                 _ => [b7, b6 + 1, 0, 0, 0, 0, 0, 0],
  --               },
  --               _ => [b7, b6, b5 + 1, 0, 0, 0, 0, 0],
  --             },
  --             _ => [b7, b6, b5, b4 + 1, 0, 0, 0, 0],
  --           },
  --           _ => [b7, b6, b5, b4, b3 + 1, 0, 0, 0],
  --         },
  --         _ => [b7, b6, b5, b4, b3, b2 + 1, 0, 0],
  --       },
  --       _ => [b7, b6, b5, b4, b3, b2, b1 + 1, 0],
  --     },
  --     _ => [b7, b6, b5, b4, b3, b2, b1, b0 + 1],
  --   }
  -- }
⟧
