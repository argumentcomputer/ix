use super::{synthesis::*, *};
use crate::sizing::CountedGate;
pub(super) fn canonical(
  b: &mut Builder,
  at: usize,
  n: usize,
  stride: usize,
) -> Bits {
  (0..n)
    .map(|i| {
      let live = flag(b, at + i * stride);
      let absent = b.not(live);
      for j in 1..stride {
        b.require_zero(absent, &word(at + i * stride + j));
      }
      live
    })
    .collect()
}
pub(super) fn capture(b: &mut Builder, g: &BodyGate) {
  let c = g.capacity;
  let r = c.block_words();
  let live = canonical(b, 2, 1, r)[0];
  let absent = b.not(live);
  b.require_zero(absent, &word(0));
  b.require_zero(absent, &word(1));
  let bank = 2 + r;
  let old = canonical(b, bank, c.blocks(), r);
  let mut flags = Vec::new();
  for f in 0..c.registry.functions() {
    for block in 0..c.registry.blocks_per_function() {
      let index = f * c.registry.blocks_per_function() + block;
      let at = bank + index * r;
      let owner = eqc(b, &word(0), f as u64);
      let ordinal = eqc(b, &word(1), block as u64);
      let matched = b.b.and(owner, ordinal);
      let insert = b.b.and(live, matched);
      flags.push(insert);
      b.require_zero(insert, &[old[index]]);
      if block > 0 {
        b.require(insert, old[index - 1]);
        same(b, insert, &word(at - r + SPAN)[64..], &word(2 + SPAN)[..64]);
      }
      for j in 0..r {
        let w = choose(b, insert, &word(2 + j), &word(at + j));
        b.write(g.input_count() + index * r + j, &w);
      }
    }
  }
  let selected = b.any(&flags);
  b.require(live, selected);
}
