import Ix.Aiur.Meta

namespace IxVM

def u64 := ⟦
  -- Computes the successor of an `u64` assumed to be properly represented in
  -- little-endian bytes. If that's not the case, this implementation has UB.
  fn relaxed_u64_succ(bytes: [G; 8]) -> [G; 8] {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bytes;
    match b0 {
      255 => match b1 {
        255 => match b2 {
          255 => match b3 {
            255 => match b4 {
              255 => match b5 {
                255 => match b6 {
                  255 => match b7 {
                    255 => [0, 0, 0, 0, 0, 0, 0, 0],
                    _ => [0, 0, 0, 0, 0, 0, 0, b7 + 1],
                  },
                  _ => [0, 0, 0, 0, 0, 0, b6 + 1, b7],
                },
                _ => [0, 0, 0, 0, 0, b5 + 1, b6, b7],
              },
              _ => [0, 0, 0, 0, b4 + 1, b5, b6, b7],
            },
            _ => [0, 0, 0, b3 + 1, b4, b5, b6, b7],
          },
          _ => [0, 0, b2 + 1, b3, b4, b5, b6, b7],
        },
        _ => [0, b1 + 1, b2, b3, b4, b5, b6, b7],
      },
      _ => [b0 + 1, b1, b2, b3, b4, b5, b6, b7],
    }
  }

  -- TODO remove this function
  fn u64_is_zero(x: [G; 8]) -> G {
    eq_zero(x[0])
      * eq_zero(x[1])
      * eq_zero(x[2])
      * eq_zero(x[3])
      * eq_zero(x[4])
      * eq_zero(x[5])
      * eq_zero(x[6])
      * eq_zero(x[7])
  }
⟧

end IxVM
