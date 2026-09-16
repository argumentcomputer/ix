use super::*;
use crate::ixby::ixbf_decode::source::{file_bits, require_index};
pub(super) fn plan(
  domain: ArtifactDomain,
  op: CommitmentBridgeOp,
) -> crate::boolean::BooleanR1csPlan {
  let ni = op.inputs();
  let no = op.outputs();
  let mut builder = Builder::new(
    ni,
    no,
    if op == CommitmentBridgeOp::Control { 1 << 13 } else { 1 << 16 },
  );
  let b = &mut builder;
  match op {
    CommitmentBridgeOp::Control => {
      bound(b, b.one, &word(0), 1 << 24);
      b.require_zero(b.one, &word(1)[64..]);
      let length = word(0)[..64].to_vec();
      let index = word(1)[..64].to_vec();
      let raw = file_bits(b, &length, RAW_DEPTH);
      let total = plus(b, b.one, &length, &b.constant(64, 48));
      let prefixed = file_bits(b, &total, PREFIXED_DEPTH);
      require_index(b, &index, &prefixed.last);
      let first = eqc(b, &index, 0);
      let later = b.not(first);
      let prior = minus(b, later, &index, &b.constant(64, 1));
      let prior = mask(b, later, &prior);
      let after = lt(b, &raw.last, &index);
      let has_next = b.not(after);
      let next = choose(b, after, &raw.last, &index);
      let end = plus(b, b.one, &index, &b.constant(64, 1));
      for (i, v) in
        [prior, next, raw.last, total, end, vec![has_next], prefixed.last]
          .into_iter()
          .enumerate()
      {
        b.write(ni + i, &v);
      }
    },
    CommitmentBridgeOp::Copy => {
      // index, parent2, has_next, raw preceding chunk64, raw next chunk64.
      b.require_zero(b.one, &word(0)[15..]);
      b.require_zero(b.one, &word(3)[1..]);
      let first = eqc(b, &word(0), 0);
      let has_next = word(3)[0];
      let prefix = domain.prefix();
      let p = prefix
        .into_iter()
        .flat_map(|v| b.constant(8, v as u64))
        .collect::<Vec<_>>();
      for i in 0..64 {
        let start = match i {
          0 => p.clone(),
          1 => word(1),
          2 => word(2),
          _ => word(4 + i - 3),
        };
        let rest = if i < 3 {
          word(4 + 61 + i)
        } else {
          mask(b, has_next, &word(68 + i - 3))
        };
        let value = choose(b, first, &start, &rest);
        b.write(ni + i, &value);
      }
    },
  }
  builder.finish(ni + no - 1)
}
