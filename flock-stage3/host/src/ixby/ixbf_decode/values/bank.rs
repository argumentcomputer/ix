use super::{super::grammar, synthesis::*, *};
use crate::sizing::CountedGate;

/// Presence and all absent words are canonical even in inactive rows.
fn canonical(
  b: &mut Builder,
  offset: usize,
  nodes: usize,
  stride: usize,
) -> Bits {
  (0..nodes)
    .map(|i| {
      let at = offset + i * stride;
      let live = flag(b, at);
      let absent = b.not(live);
      for j in 1..stride {
        b.require_zero(absent, &word(at + j));
      }
      live
    })
    .collect()
}
fn prefix(b: &mut Builder, count: usize, live: &[usize]) {
  le(b, b.one, &word(count), &b.constant(128, live.len() as u64));
  for (i, on) in live.iter().enumerate() {
    let expected = lt(b, &b.constant(128, i as u64), &word(count));
    same(b, b.one, &[*on], &[expected]);
  }
}
pub(super) fn capture(b: &mut Builder, g: &ValueGate) {
  let a = g.config.arena;
  let r = a.record_words();
  let bank = 2 + r;
  let emit = canonical(b, 2, 1, r)[0];
  let inactive = b.not(emit);
  b.require_zero(inactive, &word(1));
  let live = canonical(b, bank, a.nodes, r);
  prefix(b, 0, &live);
  same(b, emit, &word(1), &word(0));
  let room = lt(b, &word(0), &b.constant(128, a.nodes as u64));
  b.require(emit, room);
  let increment = [vec![emit], vec![b.zero; 127]].concat();
  let count = plus(b, b.one, &word(0), &increment);
  b.write(g.input_count(), &count);
  for (i, present) in live.iter().enumerate() {
    let matches = eqc(b, &word(1), i as u64);
    let insert = b.b.and(emit, matches);
    b.require_zero(insert, &[*present]);
    for j in 0..r {
      let cell = choose(b, insert, &word(2 + j), &word(bank + i * r + j));
      b.write(g.input_count() + 1 + i * r + j, &cell);
    }
  }
}

pub(super) fn finish(b: &mut Builder, g: &ValueGate) {
  let a = g.config.arena;
  let r = a.record_words();
  let stride = a.finished_record_words();
  let bank = 28 + ACC_WORDS + 1;
  let count = bank - 1;
  let live = canonical(b, bank, a.nodes, r);
  prefix(b, count, &live);
  same(b, b.one, &word(count), &word(grammar::SEEN));
  b.require_zero(b.one, &word(1)[40..]);
  let done = eqc(b, &word(1)[..8], grammar::Phase::Done as u64);
  b.require(b.one, done);
  let cursor = word(0);
  same(b, b.one, &cursor[..64], &cursor[64..]);
  for at in [
    grammar::CTORS_LEFT,
    grammar::FUNCTIONS_LEFT,
    grammar::BLOCKS_LEFT,
    grammar::ITEMS,
    grammar::PAYLOAD,
    grammar::PENDING,
    28,
    29,
    30,
  ] {
    b.require_zero(b.one, &word(at));
  }
  b.require_zero(b.one, &word(31)[64..]);
  le(b, b.one, &word(31)[..64], &cursor[..64]);
  let body = b.any(&word(31));
  b.require(b.one, body);
  let empty = eqc(b, &word(count), 0);
  same(b, empty, &word(31)[..64], &cursor[..64]);
  for (i, on) in live.iter().copied().enumerate() {
    let at = bank + i * r;
    let span = word(at + SPAN);
    let payload = word(at + PAYLOAD);
    let nonempty = lt(b, &span[..64], &span[64..]);
    b.require(on, nonempty);
    le(b, on, &span[64..], &cursor[..64]);
    let previous = if i == 0 {
      word(31)[..64].to_vec()
    } else {
      word(at - r + SPAN)[64..].to_vec()
    };
    same(b, on, &span[..64], &previous);
    let last = if i + 1 == a.nodes {
      on
    } else {
      let absent = b.not(live[i + 1]);
      b.b.and(on, absent)
    };
    same(b, last, &span[64..], &cursor[..64]);
    let kinds: Vec<_> = (0..5).map(|k| eqc(b, &word(at + KIND), k)).collect();
    let valid = b.any(&kinds);
    b.require(on, valid);
    let scalar = b.b.and(on, kinds[0]);
    let not_scalar = b.not(scalar);
    b.require_zero(not_scalar, &word(at + SCALAR));
    let refs = b.any(&[kinds[1], kinds[2]]);
    let refs = b.b.and(on, refs);
    let no_ref = b.not(refs);
    b.require_zero(no_ref, &word(at + REFERENCE));
    let aggregate = b.any(&[kinds[1], kinds[2], kinds[4]]);
    let aggregate = b.b.and(on, aggregate);
    let leaf = b.not(aggregate);
    b.require_zero(leaf, &word(at + CHILDREN));
    for (kind, cap) in [
      (1, g.config.registry.constructors()),
      (2, g.config.registry.functions()),
    ] {
      let enabled = b.b.and(on, kinds[kind]);
      let bounded = lt(b, &word(at + REFERENCE), &b.constant(128, cap as u64));
      b.require(enabled, bounded);
    }
    le(b, on, &word(at + CHILDREN), &b.constant(128, a.nodes as u64));
    let tags: Vec<_> = (0..7).map(|k| eqc(b, &word(at + SCALAR), k)).collect();
    let valid = b.any(&tags);
    b.require(scalar, valid);
    let active: Vec<_> = tags.iter().map(|tag| b.b.and(scalar, *tag)).collect();
    let nat = active[0];
    let payload_scalar = b.any(&[nat, active[1], active[6]]);
    let no_payload = b.not(payload_scalar);
    b.require_zero(no_payload, &payload);
    let starts = lt(b, &span[..64], &payload[..64]);
    b.require(payload_scalar, starts);
    let end = plus(b, payload_scalar, &payload[..64], &payload[64..]);
    same(b, payload_scalar, &end, &span[64..]);
    let nonzero = b.any(&payload[64..]);
    b.require(nat, nonzero);
    le(
      b,
      nat,
      &payload[64..],
      &b.constant(64, a.natural.encoded_bytes() as u64),
    );
    let fixed = b.any(&active[2..6]);
    let not_fixed = b.not(fixed);
    b.require_zero(not_fixed, &word(at + FIXED));
    b.require_zero(active[2], &word(at + FIXED)[1..]);
    b.require_zero(active[3], &word(at + FIXED)[32..]);
    b.require_zero(active[4], &word(at + FIXED)[64..]);
    let gold = b.any(&[active[4], active[5]]);
    let p = b.constant(64, 0xffff_ffff_0000_0001);
    let canonical = lt(b, &word(at + FIXED)[..64], &p);
    b.require(gold, canonical);
    let canonical = lt(b, &word(at + FIXED)[64..], &p);
    b.require(active[5], canonical);
    let not_nat = b.not(nat);
    for j in 0..a.natural.magnitude_words() {
      let limb = word(at + MAGNITUDE + j);
      b.require_zero(not_nat, &limb);
      let used = a.natural.bits().saturating_sub(j * 128).min(128);
      b.require_zero(b.one, &limb[used..]);
    }
  }
  // Derive each subtree from preorder child counts, with no stack advice.
  let mut ends = Vec::new();
  let mut span_ends = Vec::new();
  for i in 0..a.nodes {
    let mut pending = [vec![live[i]], vec![b.zero; 7]].concat();
    let mut choices = Vec::new();
    let mut spans = Vec::new();
    for (j, on) in live.iter().copied().enumerate().skip(i) {
      let take = b.any(&pending);
      b.require(take, on);
      let sum = plus(b, take, &pending, &word(bank + j * r + CHILDREN)[..8]);
      let next = minus(b, take, &sum, &b.constant(8, 1));
      let zero = eqc(b, &next, 0);
      let stop = b.b.and(take, zero);
      choices.push((stop, b.constant(8, (j + 1) as u64)));
      spans.push((stop, word(bank + j * r + SPAN)[64..].to_vec()));
      pending = choose(b, take, &next, &pending);
    }
    b.require_zero(b.one, &pending);
    ends.push(select(b, &choices, 8));
    span_ends.push(select(b, &spans, 64));
  }
  let mut parents = Vec::new();
  let mut depths = Vec::new();
  let mut max_depth = b.constant(8, 0);
  let mut roots = b.constant(8, 0);
  for (i, on) in live.iter().copied().enumerate() {
    let mut parent = b.constant(8, 0);
    let mut depth = [vec![on], vec![b.zero; 7]].concat();
    for (j, end) in ends.iter().enumerate().take(i) {
      let inside = lt(b, &b.constant(8, i as u64), end);
      let ancestor = b.b.and(on, inside);
      parent = choose(b, ancestor, &b.constant(8, (j + 1) as u64), &parent);
      depth =
        plus(b, b.one, &depth, &[vec![ancestor], vec![b.zero; 7]].concat());
    }
    le(b, on, &depth, &b.constant(8, a.depth as u64));
    let deeper = lt(b, &max_depth, &depth);
    max_depth = choose(b, deeper, &depth, &max_depth);
    let root = eqc(b, &parent, 0);
    let root = b.b.and(on, root);
    roots = plus(b, b.one, &roots, &[vec![root], vec![b.zero; 7]].concat());
    parents.push(parent);
    depths.push(depth);
  }
  let roots_wide = [roots.clone(), vec![b.zero; 120]].concat();
  let expected = if g.config.kind == GrammarKind::Input {
    word(grammar::ENTRY_ARITY)
  } else {
    b.constant(128, 1)
  };
  same(b, b.one, &roots_wide, &expected);
  b.write(g.input_count(), &word(count));
  b.write(g.input_count() + 1, &roots);
  b.write(g.input_count() + 2, &max_depth);
  for (i, on) in live.iter().copied().enumerate() {
    let mut ordinal = b.constant(8, 0);
    let mut children = b.constant(8, 0);
    for (j, parent) in parents.iter().enumerate() {
      if j < i {
        let equal = b.equal(parent, &parents[i]);
        let earlier = b.b.and(live[j], equal);
        let earlier = b.b.and(on, earlier);
        ordinal =
          plus(b, b.one, &ordinal, &[vec![earlier], vec![b.zero; 7]].concat());
      }
      let owns = eqc(b, parent, (i + 1) as u64);
      let child = b.b.and(live[j], owns);
      children =
        plus(b, b.one, &children, &[vec![child], vec![b.zero; 7]].concat());
    }
    same(
      b,
      on,
      &word(bank + i * r + CHILDREN),
      &[children, vec![b.zero; 120]].concat(),
    );
    let dest = g.input_count() + 3 + i * stride;
    for j in 0..r {
      b.write(dest + j, &word(bank + i * r + j));
    }
    for (j, bits) in
      [&parents[i], &ordinal, &ends[i], &depths[i]].iter().enumerate()
    {
      b.write(dest + r + j, bits);
    }
    b.write(
      dest + r + 4,
      &[word(bank + i * r + SPAN)[..64].to_vec(), span_ends[i].clone()]
        .concat(),
    );
  }
}

pub(super) fn read(b: &mut Builder, g: &ValueGate) {
  let a = g.config.arena;
  let stride = a.finished_record_words();
  let r = a.record_words();
  let enabled = flag(b, 0);
  let disabled = b.not(enabled);
  b.require_zero(disabled, &word(1));
  b.require_zero(disabled, &word(2));
  if g.op != ValueOp::ReadChild {
    b.require_zero(b.one, &word(2));
  }
  let owner = plus(b, enabled, &word(2), &b.constant(128, 1));
  if g.op == ValueOp::ReadChild {
    let bounded = lt(b, &word(2), &b.constant(128, a.nodes as u64));
    b.require(enabled, bounded);
  }
  let live = canonical(b, 3, a.nodes, stride);
  let mut flags = Vec::new();
  for (i, on) in live.iter().copied().enumerate() {
    let at = 3 + i * stride;
    let matches = if g.op == ValueOp::ReadNode {
      eqc(b, &word(1), i as u64)
    } else {
      let parent = if g.op == ValueOp::ReadRoot {
        b.constant(128, 0)
      } else {
        owner.clone()
      };
      let p = b.equal(&word(at + r), &parent);
      let o = b.equal(&word(at + r + 1), &word(1));
      b.b.and(p, o)
    };
    let selected = b.b.and(enabled, on);
    flags.push(b.b.and(selected, matches));
  }
  let found = b.any(&flags);
  b.require(enabled, found);
  for i in 0..flags.len() {
    for j in i + 1..flags.len() {
      b.require_zero(flags[i], &[flags[j]]);
    }
  }
  let choices: Vec<_> = flags
    .iter()
    .enumerate()
    .map(|(i, on)| (*on, b.constant(128, i as u64)))
    .collect();
  let index = select(b, &choices, 128);
  b.write(g.input_count(), &index);
  for j in 0..stride {
    let choices: Vec<_> = flags
      .iter()
      .enumerate()
      .map(|(i, on)| (*on, word(3 + i * stride + j)))
      .collect();
    let selected = select(b, &choices, 128);
    b.write(g.input_count() + 1 + j, &selected);
  }
}
