#[cfg(test)]
pub mod tests {
  use quickcheck::{Arbitrary, Gen};
  use std::ops::Range;

  pub fn gen_range(g: &mut Gen, range: Range<usize>) -> usize {
    let res: usize = Arbitrary::arbitrary(g);
    if range.is_empty() {
      0
    } else {
      (res % (range.end - range.start)) + range.start
    }
  }

  pub fn next_case<A: Copy>(g: &mut Gen, gens: &Vec<(usize, A)>) -> A {
    let sum: usize = gens.iter().map(|x| x.0).sum();
    let mut weight: usize = gen_range(g, 1..sum);
    for (n, case) in gens {
      if *n == 0 {
        continue;
      } else {
        match weight.checked_sub(*n) {
          None | Some(0) => {
            return *case;
          },
          _ => {
            weight -= *n;
          },
        }
      }
    }
    unreachable!()
  }
}
