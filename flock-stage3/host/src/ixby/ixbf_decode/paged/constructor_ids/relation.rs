use super::*;
use crate::boolean::BooleanR1csPlan;
pub(super) fn build(kind: ConstructorIdKind) -> BooleanR1csPlan {
  let mut builder = Builder::new(kind.inputs(), kind.outputs(), 1 << 14);
  let b = &mut builder;
  match kind {
    ConstructorIdKind::Source => {
      bound(b, b.one, &word(0), 256);
      bound(b, b.one, &word(1), 255);
      let enabled = lt(b, &word(1)[..9], &word(0)[..9]);
      let disabled = b.not(enabled);
      b.write(6, &[enabled]);
      for i in 0..4 {
        b.require_zero(disabled, &word(2 + i));
        b.write(7 + i, &word(2 + i));
      }
    },
    ConstructorIdKind::Audit => {
      for at in [0, 5, 10] {
        b.require_zero(b.one, &word(at)[1..]);
      }
      let previous = word(0)[0];
      let current = word(5)[0];
      let first = word(10)[0];
      let disabled = b.not(previous);
      let inactive = b.not(current);
      for i in 1..5 {
        b.require_zero(disabled, &word(i));
        b.require_zero(inactive, &word(5 + i));
        b.require_zero(first, &word(i));
      }
      b.require_zero(first, &[previous]);
      let allowed = b.any(&[previous, first]);
      b.require(current, allowed);
      let both = b.b.and(previous, current);
      let left = (1..5).rev().flat_map(word).collect::<Vec<_>>();
      let right = (6..10).rev().flat_map(word).collect::<Vec<_>>();
      let less = lt(b, &left, &right);
      b.require(both, less);
    },
  }
  builder.finish(kind.inputs() + kind.outputs() - 1)
}
