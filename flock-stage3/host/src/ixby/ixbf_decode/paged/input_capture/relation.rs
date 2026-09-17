use super::*;
use crate::{
  boolean::BooleanR1csPlan,
  ixby::{
    paged_code::{CONSTRUCTORS, FUNCTIONS},
    paged_frame::{HEAP as HEAP_BANK, LOCALS},
    paged_value::INPUT_BYTES,
  },
};
fn field(i: usize) -> Bits {
  word(FIELDS + i)
}
fn function(b: &mut Builder, on: usize, x: &[usize]) {
  b.require_zero(on, &x[32..]);
  bound(b, on, &x[..8], 64);
  bound(b, on, &x[16..32], 256);
  let mut entry = x[8..16].to_vec();
  entry.resize(16, b.zero);
  let good = lt(b, &entry, &x[16..32]);
  b.require(on, good);
}
fn span(b: &mut Builder, on: usize, x: &[usize], heap: &[usize]) -> usize {
  b.require_zero(on, &x[40..64]);
  bound(b, on, &x[64..], 65536);
  let nonempty = b.any(&x[64..]);
  let live = b.b.and(on, nonempty);
  let empty = b.not(nonempty);
  let empty = b.b.and(on, empty);
  b.require_zero(empty, x);
  let local = eqc(b, &x[36..40], LOCALS >> 36);
  let allocated = eqc(b, &x[36..40], HEAP_BANK >> 36);
  let valid = b.any(&[local, allocated]);
  b.require(live, valid);
  let mut offset = x[..36].to_vec();
  offset.resize(64, b.zero);
  let end = plus(b, live, &offset, &x[64..]);
  let local = b.b.and(live, local);
  bound(b, local, &end, 64);
  let allocated = b.b.and(live, allocated);
  le(b, allocated, &end, &heap[..64]);
  live
}
fn access(
  b: &mut Builder,
  index: usize,
  address: &Bits,
  write: usize,
  value: &[Bits; 2],
) {
  let at = INPUTS + STATE_WORDS + 4 * index;
  b.write(at, address);
  b.write(at + 1, &[write]);
  b.write(at + 2, &value[0]);
  b.write(at + 3, &value[1]);
}
pub(super) fn plan() -> BooleanR1csPlan {
  let mut builder = Builder::new(INPUTS, OUTPUTS, 1 << 17);
  let b = &mut builder;
  let commit = word(COMMITTED)[0];
  b.require_zero(b.one, &word(COMMITTED)[1..]);
  let tags = (0..18).map(|i| eqc(b, &word(TAG), i)).collect::<Vec<_>>();
  let valid = b.any(&tags);
  b.require(b.one, valid);
  let optional = b.any(&[tags[15], tags[17]]);
  let mandatory = b.not(optional);
  b.require(mandatory, commit);
  b.require_zero(tags[17], &[commit]);
  let active = b.not(tags[17]);
  b.require_zero(b.one, &word(1)[40..]);
  let phases =
    [0, 19, 13, 14, 15, 16, 17, 18, 20].map(|v| eqc(b, &word(1)[..8], v));
  let valid = b.any(&phases);
  b.require(b.one, valid);
  let on = phases.map(|p| b.b.and(active, p));
  for (&p, tag) in on.iter().zip([7, 9, 11, 14, 1, 15, 1, 16, 17]) {
    b.require(p, tags[tag]);
  }
  let header = on[0];
  let value = on[1];
  bound(b, b.one, &word(2), 256);
  bound(b, b.one, &word(3), 1024);
  let entry_ok = lt(b, &word(6), &word(3));
  b.require(b.one, entry_ok);
  bound(b, b.one, &word(7), 64);
  bound(b, b.one, &word(5), 65536);
  let room = lt(b, &word(5), &b.constant(128, 65536));
  b.require(value, room);
  bound(b, b.one, &word(HEAP), 1 << 36);
  bound(b, b.one, &word(DEPTH), 65536);
  bound(b, b.one, &word(SCALAR), 4);
  let live = span(b, b.one, &word(SPAN), &word(HEAP));
  let empty = b.not(live);
  b.require_zero(empty, &word(DEPTH));
  let pending = b.any(&word(SCALAR));
  b.require(pending, live);
  for i in STATE..STATE + STATE_WORDS {
    b.require_zero(phases[0], &word(i));
  }
  let started = b.not(phases[0]);
  function(b, started, &word(ENTRY));
  for i in [SPAN, DEPTH, SCALAR] {
    b.require_zero(phases[8], &word(i));
  }
  b.require_zero(phases[1], &word(SCALAR));
  let kinds = [0, 1, 2, 3, 4].map(|i| eqc(b, &field(0), i));
  let valid = b.any(&kinds);
  b.require(value, valid);
  b.require(value, live);
  let begin = b.b.and(value, kinds[0]);
  let ctor = b.b.and(value, kinds[1]);
  let pap = b.b.and(value, kinds[2]);
  let erased = b.b.and(value, kinds[3]);
  let array = b.b.and(value, kinds[4]);
  let object = b.any(&[ctor, pap]);
  let aggregate = b.any(&[object, array]);
  let notctor = b.not(ctor);
  b.require_zero(notctor, &word(RESOLVED));
  let good = lt(b, &word(RESOLVED), &word(2));
  b.require(ctor, good);
  let good = lt(b, &field(1), &word(3));
  b.require(pap, good);
  bound(b, object, &field(5), 64);
  bound(b, array, &field(5), 65536);
  let reply = std::array::from_fn::<_, 4, _>(|i| {
    [word(REPLIES + 2 * i), word(REPLIES + 2 * i + 1)]
  });
  for i in 0..4 {
    same(b, ctor, &field(1 + i), &reply[i / 2][i % 2]);
  }
  same(b, ctor, &field(5), &reply[2][0]);
  b.require_zero(ctor, &reply[2][1]);
  let fnread = b.any(&[header, pap]);
  function(b, fnread, &reply[0][0]);
  b.require_zero(fnread, &reply[0][1]);
  let mut arity = reply[0][0][..8].to_vec();
  arity.resize(128, b.zero);
  same(b, header, &arity, &word(7));
  same(b, header, &field(0), &word(7));
  let under = lt(b, &field(5), &arity);
  b.require(pap, under);
  let (pending, scalar_emit, scalar_cell) = scalar_value(b, &on, commit, begin);
  let emit = b.any(&[aggregate, erased, scalar_emit]);
  b.require(emit, live);
  let children = mask(b, aggregate, &field(5));
  let has_children = b.any(&children);
  let descend = b.b.and(emit, has_children);
  let next_heap = plus(b, aggregate, &word(HEAP), &children);
  bound(b, aggregate, &next_heap, 1 << 36);
  let mut pointer = word(HEAP)[..64].to_vec();
  pointer[36] = b.one;
  pointer[37] = b.one;
  pointer[38] = b.one;
  let pointer = mask(b, has_children, &pointer);
  let object_payload = [pointer.clone(), children[..64].to_vec()].concat();
  let mut ctor_header = b.constant(128, 7);
  ctor_header[64..].copy_from_slice(&word(RESOLVED)[..64]);
  let mut pap_header = b.constant(128, 9);
  pap_header[64..].copy_from_slice(&field(1)[..64]);
  let mut array_header = b.constant(128, 11);
  array_header[64..].copy_from_slice(&children[..64]);
  let mut array_payload = [pointer.clone(), b.constant(64, 0)].concat();
  array_payload[40] = has_children;
  let cell = [
    select(
      b,
      &[
        (ctor, ctor_header),
        (pap, pap_header),
        (array, array_header),
        (erased, b.constant(128, 5)),
        (scalar_emit, scalar_cell[0].clone()),
      ],
      128,
    ),
    select(
      b,
      &[
        (object, object_payload.clone()),
        (array, array_payload),
        (scalar_emit, scalar_cell[1].clone()),
      ],
      128,
    ),
  ];
  let remaining = minus(b, emit, &word(SPAN)[64..], &b.constant(64, 1));
  let has_remaining = b.any(&remaining);
  let next_pointer = plus(b, emit, &word(SPAN)[..64], &b.constant(64, 1));
  let siblings = [next_pointer, remaining].concat();
  let push = b.b.and(descend, has_remaining);
  let nochildren = b.not(has_children);
  let leaf = b.b.and(emit, nochildren);
  let has_stack = b.any(&word(DEPTH));
  let last = b.not(has_remaining);
  let finished = b.b.and(leaf, last);
  let pop = b.b.and(finished, has_stack);
  let popped_live = span(b, pop, &reply[3][0], &word(HEAP));
  b.require(pop, popped_live);
  b.require_zero(pop, &reply[3][1]);
  let deeper = plus(b, push, &word(DEPTH), &b.constant(128, 1));
  bound(b, push, &deeper, 65536);
  let shallower = minus(b, pop, &word(DEPTH), &b.constant(128, 1));
  let mut new_depth = choose(b, push, &deeper, &word(DEPTH));
  new_depth = choose(b, pop, &shallower, &new_depth);
  let keep = b.b.and(leaf, has_remaining);
  let after = select(
    b,
    &[
      (descend, object_payload),
      (keep, siblings.clone()),
      (pop, reply[3][0].clone()),
    ],
    128,
  );
  let mut next_span = choose(b, emit, &after, &word(SPAN));
  let roots = b.any(&field(0));
  let root_pointer = mask(b, roots, &b.constant(64, LOCALS));
  let root_span = [root_pointer, field(0)[..64].to_vec()].concat();
  next_span = choose(b, header, &root_span, &next_span);
  let next_entry = choose(b, header, &reply[0][0], &word(ENTRY));
  for (i, v) in
    [next_span, next_heap, new_depth, pending, next_entry].iter().enumerate()
  {
    b.write(INPUTS + i, v);
  }
  let mut entry_address = b.constant(128, FUNCTIONS);
  entry_address[..16].copy_from_slice(&word(6)[..16]);
  let mut pap_address = b.constant(128, FUNCTIONS);
  pap_address[..16].copy_from_slice(&field(1)[..16]);
  let index = word(RESOLVED)[..16].to_vec();
  let twice = plus(b, ctor, &index, &index);
  let triple = plus(b, ctor, &index, &twice);
  let mut ctor_address = b.constant(128, CONSTRUCTORS);
  ctor_address[..16].copy_from_slice(&triple);
  let ctor_one = plus(b, ctor, &ctor_address, &b.constant(128, 1));
  let ctor_two = plus(b, ctor, &ctor_address, &b.constant(128, 2));
  let ref_choices = [
    vec![(header, entry_address), (pap, pap_address), (ctor, ctor_address)],
    vec![(ctor, ctor_one)],
    vec![(ctor, ctor_two)],
  ];
  for i in 0..3 {
    let enabled =
      b.any(&ref_choices[i].iter().map(|(e, _)| *e).collect::<Vec<_>>());
    let disabled = b.not(enabled);
    for v in &reply[i] {
      b.require_zero(disabled, v);
    }
    let address = select(b, &ref_choices[i], 128);
    access(b, i, &address, b.zero, &reply[i]);
  }
  let no_pop = b.not(pop);
  for v in &reply[3] {
    b.require_zero(no_pop, v);
  }
  let read_address = plus(b, pop, &shallower, &b.constant(128, STACK));
  let read_address = mask(b, pop, &read_address);
  access(b, 3, &read_address, b.zero, &reply[3]);
  let write_address = plus(b, push, &word(DEPTH), &b.constant(128, STACK));
  let address = select(b, &[(push, write_address), (pop, read_address)], 128);
  let write = b.any(&[push, pop]);
  let saved = mask(b, push, &siblings);
  access(b, 4, &address, write, &[saved, b.constant(128, 0)]);
  let mut target = word(SPAN)[..64].to_vec();
  target.resize(128, b.zero);
  let target = mask(b, emit, &target);
  access(b, 5, &target, emit, &cell);
  builder.finish(INPUTS + OUTPUTS - 1)
}
fn scalar_value(
  b: &mut Builder,
  on: &[usize; 9],
  commit: usize,
  begin: usize,
) -> (Bits, usize, [Bits; 2]) {
  let scalar = on[2];
  let natural = on[3];
  let unset = eqc(b, &word(SCALAR), 1);
  b.require(scalar, unset);
  for (phase, tag) in [(3, 2), (4, 3), (5, 3), (6, 4), (7, 4)] {
    let valid = eqc(b, &word(SCALAR), tag);
    b.require(on[phase], valid);
  }
  let tags = std::array::from_fn::<_, 7, _>(|i| eqc(b, &field(0), i as u64));
  let valid = b.any(&tags);
  b.require(scalar, valid);
  let fixed = b.any(&tags[2..6]);
  let fixed = b.b.and(scalar, fixed);
  let nat = b.b.and(scalar, tags[0]);
  let string = b.b.and(scalar, tags[1]);
  let bytes = b.b.and(scalar, tags[6]);
  let count = b.any(&[on[4], on[6]]);
  let empty = eqc(b, &field(0), 0);
  let empty = b.b.and(count, empty);
  let str_done = b.b.and(on[5], commit);
  let payload = b.any(&[str_done, on[7]]);
  let done = b.any(&[fixed, natural, empty, payload]);
  let mut pending = choose(b, begin, &b.constant(128, 1), &word(SCALAR));
  for (on, tag) in [(nat, 2), (string, 3), (bytes, 4)] {
    pending = choose(b, on, &b.constant(128, tag), &pending);
  }
  let keep = b.not(done);
  pending = mask(b, keep, &pending);
  let bool_ = b.b.and(scalar, tags[2]);
  let word_ = b.b.and(scalar, tags[3]);
  let gold = b.b.and(scalar, tags[4]);
  let ext = b.b.and(scalar, tags[5]);
  let str_value = b.any(&[on[4], str_done]);
  let str_value = b.b.and(done, str_value);
  let byte_value = b.any(&[on[6], on[7]]);
  let byte_value = b.b.and(done, byte_value);
  let tag = select(
    b,
    &[
      (bool_, b.constant(128, 1)),
      (word_, b.constant(128, 2)),
      (gold, b.constant(128, 3)),
      (ext, b.constant(128, 4)),
      (natural, b.constant(128, 8)),
      (str_value, b.constant(128, 10)),
      (byte_value, b.constant(128, 6)),
    ],
    128,
  );
  let range = word(RANGE);
  same(b, payload, &range[..64], &word(0)[..64]);
  let mut length = range[64..].to_vec();
  length.resize(128, b.zero);
  same(b, payload, &length, &word(4));
  b.require_zero(payload, &range[41..64]);
  b.require_zero(payload, &range[100..]);
  let end = plus(b, payload, &range[..64], &range[64..]);
  same(b, payload, &end, &word(NEXT)[..64]);
  le(b, payload, &end, &word(0)[64..]);
  bound(b, payload, &end, 1 << 41);
  let pointer =
    plus(b, payload, &range[..64], &b.constant(64, INPUT_BYTES << 5));
  let pointer = [pointer, range[64..].to_vec()].concat();
  let value = select(
    b,
    &[(fixed, field(1)), (natural, word(NATURAL)), (payload, pointer)],
    128,
  );
  (pending, done, [tag, value])
}
