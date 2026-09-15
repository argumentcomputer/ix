use super::{synthesis::*, *};
use crate::sizing::CountedGate;

pub(super) fn build(b: &mut Builder, g: &ValueGate) {
  let (commit, tags) = events(b, 0, 1);
  let value = b.b.and(commit, tags[9]);
  let kinds: Vec<_> = (0..4).map(|i| eqc(b, &word(2), i)).collect();
  let valid = b.any(&kinds);
  b.require(value, valid);
  let ctor = b.b.and(value, kinds[1]);
  let pap = b.b.and(value, kinds[2]);
  let refs = b.any(&[ctor, pap]);
  let leaf = b.any(&[kinds[0], kinds[3]]);
  let leaf = b.b.and(value, leaf);
  for i in 3..8 {
    b.require_zero(leaf, &word(i));
  }
  for i in 4..7 {
    b.require_zero(pap, &word(i));
  }
  for i in 8..LINK_BANK {
    b.require_zero(value, &word(i));
  }
  let cap = g.config.registry;
  let mut selections = Vec::new();
  for (constructors, count, stride, offset) in [
    (true, cap.constructors(), 7, 0),
    (false, cap.functions(), 5, cap.constructors() * 7),
  ] {
    for i in 0..count {
      let at = LINK_BANK + offset + i * stride;
      let live = flag(b, at);
      let absent = b.not(live);
      for j in 1..stride {
        b.require_zero(absent, &word(at + j));
      }
      let matches = if constructors {
        let left: Bits = (3..7).flat_map(word).collect();
        let right: Bits = (at + 1..at + 5).flat_map(word).collect();
        b.equal(&left, &right)
      } else {
        eqc(b, &word(3), i as u64)
      };
      let enabled = b.b.and(if constructors { ctor } else { pap }, live);
      let selected = b.b.and(enabled, matches);
      if constructors {
        same(b, selected, &word(7), &word(at + 5));
      } else {
        let partial = lt(b, &word(7), &word(at + 1));
        b.require(selected, partial);
      }
      selections.push((selected, b.constant(128, i as u64)));
    }
  }
  let flags: Vec<_> = selections.iter().map(|(flag, _)| *flag).collect();
  let found = b.any(&flags);
  b.require(refs, found);
  for i in 0..flags.len() {
    for j in i + 1..flags.len() {
      b.require_zero(flags[i], &[flags[j]]);
    }
  }
  let index = select(b, &selections, 128);
  b.write(g.input_count(), &index);
}
