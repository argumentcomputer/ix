import Ix.Aiur.Meta

namespace IxVM

def poseidon2 := ⟦
  fn poseidon2_permute(state: [G; 16]) -> [G; 16] {
    -- First half full rounds
    let round_constants = [
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    ];
    let state = fold(0 .. 4, state, |state, @r|
      -- Add constants + S-box on all elements
      let state = fold(0 .. 16, state, |state, @i|
        let x = state[@i] + round_constants[@r][@i];
        let x2 = x * x;
        let x4 = x2 * x2;
        set(state, @i, x4 * x2 * x)
      );
      external_linear_layer(state)
    );

    -- Partial rounds
    let round_constants = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    let state = fold(0 .. 22, state, |state, @r|
      -- Constant + S-box only on first element
      let x = state[0] + round_constants[@r];
      let x2 = x * x;
      let x4 = x2 * x2;
      let state = set(state, 0, x4 * x2 * x);
      internal_linear_layer(state)
    );

    -- Final full rounds
    let round_constants = [
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    ];
    fold(0 .. 4, state, |state, @r|
      let state = fold(0 .. 16, state, |state, @i|
        let x = state[@i] + round_constants[@r][@i];
        let x2 = x * x;
        let x4 = x2 * x2;
        set(state, @i, x4 * x2 * x)
      );
      external_linear_layer(state)
    )
  }

  fn external_linear_layer(state: [G; 16]) -> [G; 16] {
    let m = [
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    ];

    fold(0 .. 16, [0; 16], |new_state, @i|
      let row = m[@i];
      let dot_prod = fold(0 .. 16, 0, |acc, @j|
        acc + row[@j] * state[@j]
      );
      set(new_state, @i, dot_prod)
    )
  }

  fn internal_linear_layer(state: [G; 16]) -> [G; 16] {
    let sum =
      state[0]  + state[1]  + state[2]  + state[3]  +
      state[4]  + state[5]  + state[6]  + state[7]  +
      state[8]  + state[9]  + state[10] + state[11] +
      state[12] + state[13] + state[14] + state[15];

    let diag = [
      0xde9b91a467d6afc0,
      0xc5f16b9c76a9be17,
      0x0ab0fef2d540ac55,
      0x3001d27009d05773,
      0xed23b1f906d3d9eb,
      0x5ce73743cba97054,
      0x1c3bab944af4ba24,
      0x2faa105854dbafae,
      0x53ffb3ae6d421a10,
      0xbcda9df8884ba396,
      0xfc1273e4a31807bb,
      0xc77952573d5142c0,
      0x56683339a819b85e,
      0x328fcbd8f0ddc8eb,
      0xb5101e303fce9cb7,
      0x774487b8c40089bb
    ];
    let sum_coeffs = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];

    fold(0 .. 16, [0; 16], |new_state, @i|
      set(new_state, @i, diag[@i] * state[@i] + sum_coeffs[@i] * sum)
    )
  }

  fn poseidon2(input: ByteStream) -> [G; 4] {
    poseidon2_aux(input, [0; 16])[0..4]
  }

  fn poseidon2_aux(input: ByteStream, state: [G; 16]) -> [G; 16] {
    match input {
      ByteStream.Nil =>
        let state = set(state, 8, state[8] + 1);
        poseidon2_permute(state),
      ByteStream.Cons(x0, tail_ptr) => match load(tail_ptr) {
        ByteStream.Nil =>
          let state = set(state, 0, state[0] + x0);
          let state = set(state, 8, state[8] + 1);
          poseidon2_permute(state),
        ByteStream.Cons(x1, tail_ptr) => match load(tail_ptr) {
          ByteStream.Nil =>
            let state = set(state, 0, state[0] + x0);
            let state = set(state, 1, state[1] + x1);
            let state = set(state, 8, state[8] + 1);
          poseidon2_permute(state),
          ByteStream.Cons(x2, tail_ptr) => match load(tail_ptr) {
            ByteStream.Nil =>
              let state = set(state, 0, state[0] + x0);
              let state = set(state, 1, state[1] + x1);
              let state = set(state, 2, state[2] + x2);
              let state = set(state, 8, state[8] + 1);
              poseidon2_permute(state),
            ByteStream.Cons(x3, tail_ptr) => match load(tail_ptr) {
              ByteStream.Nil =>
                let state = set(state, 0, state[0] + x0);
                let state = set(state, 1, state[1] + x1);
                let state = set(state, 2, state[2] + x2);
                let state = set(state, 3, state[3] + x3);
                let state = set(state, 8, state[8] + 1);
              poseidon2_permute(state),
              ByteStream.Cons(x4, tail_ptr) => match load(tail_ptr) {
                ByteStream.Nil =>
                  let state = set(state, 0, state[0] + x0);
                  let state = set(state, 1, state[1] + x1);
                  let state = set(state, 2, state[2] + x2);
                  let state = set(state, 3, state[3] + x3);
                  let state = set(state, 4, state[4] + x4);
                  let state = set(state, 8, state[8] + 1);
                poseidon2_permute(state),
                ByteStream.Cons(x5, tail_ptr) => match load(tail_ptr) {
                  ByteStream.Nil =>
                    let state = set(state, 0, state[0] + x0);
                    let state = set(state, 1, state[1] + x1);
                    let state = set(state, 2, state[2] + x2);
                    let state = set(state, 3, state[3] + x3);
                    let state = set(state, 4, state[4] + x4);
                    let state = set(state, 5, state[5] + x5);
                    let state = set(state, 8, state[8] + 1);
                    poseidon2_permute(state),
                  ByteStream.Cons(x6, tail_ptr) =>
                    let state = set(state, 0, state[0] + x0);
                    let state = set(state, 1, state[1] + x1);
                    let state = set(state, 2, state[2] + x2);
                    let state = set(state, 3, state[3] + x3);
                    let state = set(state, 4, state[4] + x4);
                    let state = set(state, 5, state[5] + x5);
                    match load(tail_ptr) {
                      ByteStream.Nil =>
                        let state = set(state, 6, state[6] + x6);
                        let state = set(state, 8, state[8] + 1);
                        poseidon2_permute(state),
                      ByteStream.Cons(x7, tail_ptr) =>
                        let state = set(state, 6, state[6] + x6);
                        let state = set(state, 7, state[7] + x7);
                        let state = poseidon2_permute(state);
                        poseidon2_aux(load(tail_ptr), state),
                    },
                },
              },
            },
          },
        },
      },
    }
  }
⟧

end IxVM
