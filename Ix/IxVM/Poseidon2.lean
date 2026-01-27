import Ix.Aiur.Meta

namespace IxVM

def poseidon2 := ⟦
  fn poseidon2_24_permute(state: [G; 24]) -> [G; 24] {
    -- First half full rounds
    let round_constants = [
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    ];
    let state = fold(0 .. 4, state, |state, @r|
      -- Add constants + S-box on all elements
      let state = fold(0 .. 24, state, |state, @i|
        let x = state[@i] + round_constants[@r][@i];
        let x2 = x * x;
        set(state, @i, x2 * x2 * x)
      );
      external_linear_layer(state)
    );

    -- Partial rounds
    let round_constants = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    let state = fold(0 .. 20, state, |state, @r|
      -- Constant + S-box only on first element
      let x = state[0] + round_constants[@r];
      let x2 = x * x;
      let state = set(state, 0, x2 * x2 * x);
      internal_linear_layer(state)
    );

    -- Final full rounds
    let round_constants = [
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    ];
    fold(0 .. 4, state, |state, @r|
      let state = fold(0 .. 24, state, |state, @i|
        let x = state[@i] + round_constants[@r][@i];
        let x2 = x * x;
        set(state, @i, x2 * x2 * x)
      );
      external_linear_layer(state)
    )
  }

  fn external_linear_layer(state: [G; 24]) -> [G; 24] {
    let m = [
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
    ];

    fold(0 .. 24, [0; 24], |new_state, @i|
      let row = m[@i];
      let dot_prod = fold(0 .. 24, 0, |acc, @j|
        acc + row[@j] * state[@j]
      );
      set(new_state, @i, dot_prod)
    )
  }

  fn internal_linear_layer(state: [G; 24]) -> [G; 24] {
    let sum =
      state[0]  + state[1]  + state[2]  + state[3]  + state[4]  + state[5]  +
      state[6]  + state[7]  + state[8]  + state[9]  + state[10] + state[11] +
      state[12] + state[13] + state[14] + state[15] + state[16] + state[17] +
      state[18] + state[19] + state[20] + state[21] + state[22] + state[23];

    let diag = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    let sum_coeffs = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1];

    fold(0 .. 24, [0; 24], |new_state, @i|
      set(new_state, @i, diag[@i] * state[@i] + sum_coeffs[@i] * sum)
    )
  }

  fn poseidon2_24(input: ByteStream) -> [G; 4] {
    poseidon2_24_aux(input, [0; 24])[0..4]
  }

  fn poseidon2_24_aux(input: ByteStream, state: [G; 24]) -> [G; 24] {
    match input {
      ByteStream.Nil =>
        let state = set(state, 8, state[8] + 1);
        poseidon2_24_permute(state),
      ByteStream.Cons(x0, tail_ptr) => match load(tail_ptr) {
        ByteStream.Nil =>
          let state = set(state, 0, state[0] + x0);
          let state = set(state, 8, state[8] + 1);
          poseidon2_24_permute(state),
        ByteStream.Cons(x1, tail_ptr) => match load(tail_ptr) {
          ByteStream.Nil =>
            let state = set(state, 0, state[0] + x0);
            let state = set(state, 1, state[1] + x1);
            let state = set(state, 8, state[8] + 1);
          poseidon2_24_permute(state),
          ByteStream.Cons(x2, tail_ptr) => match load(tail_ptr) {
            ByteStream.Nil =>
              let state = set(state, 0, state[0] + x0);
              let state = set(state, 1, state[1] + x1);
              let state = set(state, 2, state[2] + x2);
              let state = set(state, 8, state[8] + 1);
              poseidon2_24_permute(state),
            ByteStream.Cons(x3, tail_ptr) => match load(tail_ptr) {
              ByteStream.Nil =>
                let state = set(state, 0, state[0] + x0);
                let state = set(state, 1, state[1] + x1);
                let state = set(state, 2, state[2] + x2);
                let state = set(state, 3, state[3] + x3);
                let state = set(state, 8, state[8] + 1);
              poseidon2_24_permute(state),
              ByteStream.Cons(x4, tail_ptr) => match load(tail_ptr) {
                ByteStream.Nil =>
                  let state = set(state, 0, state[0] + x0);
                  let state = set(state, 1, state[1] + x1);
                  let state = set(state, 2, state[2] + x2);
                  let state = set(state, 3, state[3] + x3);
                  let state = set(state, 4, state[4] + x4);
                  let state = set(state, 8, state[8] + 1);
                poseidon2_24_permute(state),
                ByteStream.Cons(x5, tail_ptr) => match load(tail_ptr) {
                  ByteStream.Nil =>
                    let state = set(state, 0, state[0] + x0);
                    let state = set(state, 1, state[1] + x1);
                    let state = set(state, 2, state[2] + x2);
                    let state = set(state, 3, state[3] + x3);
                    let state = set(state, 4, state[4] + x4);
                    let state = set(state, 5, state[5] + x5);
                    let state = set(state, 8, state[8] + 1);
                    poseidon2_24_permute(state),
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
                        poseidon2_24_permute(state),
                      ByteStream.Cons(x7, tail_ptr) =>
                        let state = set(state, 6, state[6] + x6);
                        let state = set(state, 7, state[7] + x7);
                        let state = poseidon2_24_permute(state);
                        poseidon2_24_aux(load(tail_ptr), state),
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
