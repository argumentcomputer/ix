//! Persistent arrays and immutable byte builders in authenticated memory.
//! Array updates copy a binary-tree path. Flat input spans remain shared.
//! Builders prepend immutable chunk records; freeze copies each byte once.
use super::objects::{Bits, S};
use super::*;
use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  ixby::paged_frame::{ActionKind, HEAP, Phase, SCRATCH},
  ixby::paged_value::{ARRAY_TAG, BUILDER_TAG, DYNAMIC_BYTES},
};

pub(super) const ARRAY_DOWN: u64 = 11;
pub(super) const ARRAY_UP: u64 = 12;
pub(super) const FINISH: u64 = 13;
pub(super) const BUILDER_NODE: u64 = 14;
pub(super) const BUILDER_COPY: u64 = 15;
pub(super) const BUILDER_EMIT: u64 = 16;
pub(super) const STACK: u64 = SCRATCH + 192;
const RESULT: usize = 10;
const LENGTH: usize = 12;
const INDEX: usize = 13;
const CAPACITY: usize = 14;
const POINTER: usize = 15;
const DEPTH: usize = 16;
const ELEMENT: usize = 17;
const OLD_HEAP: usize = 19;
const OFFSET: usize = 20;
// Builder microstates reuse registers belonging to the inactive array engine.
const BUILDER: usize = 12;
const CHUNK: usize = 14;
const REMAIN: usize = 15;
const END: usize = 16;
const BUILDER_HEAP: usize = 17;
const OLD_BYTES: usize = 18;
const BUFFER: usize = 19;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CollectionKind {
  Start,
  ArrayRequest,
  ArrayStep,
  AscendRequest,
  Ascend,
  Finish,
  BuilderRequest,
  BuilderNode,
  CopyRequest,
  Copy,
  Emit,
}
impl CollectionKind {
  pub(super) fn extra_inputs(self) -> usize {
    match self {
      Self::Start => 7,
      Self::ArrayStep | Self::Ascend => 2,
      Self::BuilderNode | Self::Copy => 4,
      _ => 0,
    }
  }
  pub(super) fn outputs(self) -> usize {
    match self {
      Self::ArrayRequest | Self::AscendRequest => 1,
      Self::BuilderRequest | Self::CopyRequest => 2,
      Self::Finish => 5,
      Self::Start | Self::ArrayStep => STATE_WORDS + 8,
      Self::Ascend | Self::Emit => STATE_WORDS + 4,
      _ => STATE_WORDS,
    }
  }
}
pub(super) fn is_collection(op: u8) -> bool {
  (49..=57).contains(&op)
}
fn word(i: usize) -> Bits {
  (128 * i..128 * (i + 1)).collect()
}
fn op(s: &mut S, state: &[Bits], n: u64) -> usize {
  s.eqc(&state[HEADER][24..32], n)
}
fn pick(s: &mut S, n: usize, choices: &[(usize, Bits)]) -> Bits {
  (0..n)
    .map(|i| {
      let terms = choices
        .iter()
        .map(|(f, v)| s.and(*f, v.get(i).copied().unwrap_or(s.zero)))
        .collect::<Vec<_>>();
      s.b.xor(&terms, s.one)
    })
    .collect()
}
fn record(
  s: &mut S,
  enabled: usize,
  address: &[usize],
  value: &[Bits; 2],
) -> Vec<Bits> {
  vec![
    s.mask(enabled, &s.wide(address, 128)),
    s.wide(&[enabled], 128),
    s.mask(enabled, &value[0]),
    s.mask(enabled, &value[1]),
  ]
}
fn tagged(s: &S, tag: u64, length: &[usize], pointer: &[usize]) -> [Bits; 2] {
  [[s.c(64, tag), s.wide(length, 64)].concat(), s.wide(pointer, 128)]
}
fn canonical_heap(
  s: &mut S,
  e: usize,
  pointer: &[usize],
  count: &[usize],
  allocated: &[usize],
) {
  s.zeros(e, &pointer[40..]);
  s.is(e, &pointer[36..40], HEAP >> 36);
  let end = s.add(&s.wide(&pointer[..36], 64), &s.wide(count, 64));
  s.le(e, &end, &s.wide(allocated, 64));
}
fn reserve(
  s: &mut S,
  e: usize,
  heap: &[usize],
  count: &[usize],
) -> (Bits, Bits) {
  let next = s.add(&heap[..64], &s.wide(count, 64));
  s.bound(e, &next, 1 << 36);
  let address = s.add(&heap[..64], &s.c(64, HEAP));
  (s.wide(&next, 128), address)
}
fn capacity(s: &mut S, len: &[usize]) -> Bits {
  // ceil(log2(length)), with capacity 1 for an empty array.
  let empty = s.eqc(len, 0);
  let predecessor = s.sub(&s.wide(len, 64), &s.c(64, 1));
  let predecessor = s.choose(empty, &s.c(64, 0), &predecessor);
  let flags = (0..32).map(|i| s.any(&predecessor[i..32])).collect::<Vec<_>>();
  let mut result = vec![s.inv(flags[0])];
  for i in 1..32 {
    result.push(s.b.xor(&[flags[i - 1], flags[i]], s.one));
  }
  result.push(flags[31]);
  s.wide(&result, 64)
}
fn basic(s: &mut S, e: usize, state: &[Bits]) {
  s.is(e, &state[0][..8], Phase::Eval as u64);
  s.is(e, &state[HEADER][8..16], 0);
  s.is(e, &state[HEADER][16..24], 1);
  s.bound(e, &state[HEAP_COUNT], 1 << 36);
  s.bound(e, &state[BYTE_COUNT], 1 << 36);
}
fn start(s: &mut S, e: usize, state: &[Bits], args: &[Bits]) -> Vec<Bits> {
  s.instruction(e, state, 0, 1);
  s.zeros(e, &state[10..].concat());
  let flags = (49..=57).map(|i| op(s, state, i)).collect::<Vec<_>>();
  let valid = s.any(&flags);
  s.need(e, valid);
  let f = |n: usize| flags[n - 49];
  let empty = s.any(&[f(49), f(54)]);
  let first = s.inv(empty);
  let second = s.any(&[f(51), f(52), f(53), f(55)]);
  let uses = [first, second, f(52)];
  let mut types = Vec::new();
  for (i, used) in uses.into_iter().enumerate() {
    let enabled = s.and(e, used);
    types.push(s.value(enabled, &args[2 * i..2 * i + 2].concat()));
    let bytes = s.and(enabled, types[i][5]);
    s.le(bytes, &args[2 * i + 1][64..], &args[6][64..]);
  }
  let arrays = s.any(&flags[1..5]);
  let builders = s.any(&flags[6..]);
  let array = s.and(e, arrays);
  let builder = s.and(e, builders);
  s.need(array, types[0][10]);
  s.need(builder, types[0][11]);
  let indexed = s.any(&[f(51), f(52)]);
  let indexed = s.and(e, indexed);
  s.need(indexed, types[1][7]);
  let append = s.and(e, f(55));
  s.need(append, types[1][5]);
  bytes::byte_span(s, append, &args[3], &state[BYTE_COUNT]);
  // Each used argument contributes one, not its positional mask.
  let a1 = s.wide(&[first], 8);
  let a2 = s.wide(&[second], 8);
  let a3 = s.wide(&[f(52)], 8);
  let count = s.add(&a1, &a2);
  let count = s.add(&count, &a3);
  s.same(e, &state[HEADER][32..40], &count);
  s.same(e, &state[HEADER][40..48], &count);
  let length = &args[0][64..];
  let idx = s.choose(f(53), length, &args[3][..64]);
  let in_bounds = s.lt(&args[3], &s.wide(length, 128));
  s.need(indexed, in_bounds);
  let pushed = s.add(length, &s.c(64, 1));
  let push = s.and(e, f(53));
  s.bound(push, &pushed, u64::from(u32::MAX));
  let array_len = s.choose(f(53), &pushed, length);
  let cap = capacity(s, length);
  let nonempty = s.any(length);
  let full = s.eq(length, &cap);
  let growing = s.and(full, nonempty);
  let growing = s.and(growing, f(53));
  let active_array = s.any(&[f(51), f(52), f(53)]);
  let changing = s.any(&[f(52), f(53)]);
  let element =
    [s.choose(f(52), &args[4], &args[2]), s.choose(f(52), &args[5], &args[3])];
  let mut after = state.to_vec();
  for value in &mut after[10..] {
    *value = s.c(128, 0);
  }
  after[CONTROL] =
    s.choose(active_array, &s.c(128, ARRAY_DOWN), &s.c(128, FINISH));
  after[LENGTH] = s.mask(active_array, &s.wide(length, 128));
  let index = s.choose(growing, &s.c(64, 0), &idx);
  after[INDEX] = s.mask(active_array, &s.wide(&index, 128));
  after[CAPACITY] = s.mask(active_array, &s.wide(&cap, 128));
  let pointer = s.choose(growing, &s.c(128, 0), &args[1]);
  after[POINTER] = s.mask(active_array, &pointer);
  after[DEPTH] = s.wide(&[growing], 128);
  after[ELEMENT] = s.mask(changing, &element[0]);
  after[ELEMENT + 1] = s.mask(changing, &element[1]);
  after[OLD_HEAP] = s.mask(active_array, &state[HEAP_COUNT]);
  after[OFFSET] = s.mask(growing, &s.wide(length, 128));
  let array_result = tagged(s, ARRAY_TAG, &array_len, &s.c(64, 0));
  after[RESULT] = pick(
    s,
    128,
    &[
      (f(49), s.c(128, ARRAY_TAG)),
      (changing, array_result[0].clone()),
      (f(50), s.c(128, 8)),
      (f(54), s.c(128, BUILDER_TAG)),
      (f(57), s.c(128, 8)),
    ],
  );
  let length_result = s.any(&[f(50), f(57)]);
  after[RESULT + 1] = s.mask(length_result, &s.wide(length, 128));

  // Builder append stores the old builder and one immutable byte descriptor.
  let chunk_len = &args[3][64..];
  let chunk_live = s.any(chunk_len);
  let allocation = s.and(f(55), chunk_live);
  let allocated = s.and(e, allocation);
  let total = s.add(length, chunk_len);
  s.bound(append, &total, (1 << 36) - 1);
  s.le(builder, length, &args[6][64..]);
  s.le(append, &total, &args[6][64..]);
  let (heap, address) = reserve(s, allocated, &state[HEAP_COUNT], &s.c(64, 2));
  after[HEAP_COUNT] = s.choose(allocation, &heap, &state[HEAP_COUNT]);
  let head = s.choose(allocation, &s.wide(&address, 128), &args[1]);
  let result = tagged(s, BUILDER_TAG, &total, &head);
  for i in 0..2 {
    after[RESULT + i] = s.choose(f(55), &result[i], &after[RESULT + i]);
  }

  // Freeze reserves a contiguous result exactly once, then fills it backwards.
  let freeze = s.and(e, f(56));
  let rounded = s.add(length, &s.c(64, 31));
  let cells = s.wide(&rounded[5..], 64);
  let reserved = s.add(&state[BYTE_COUNT][..64], &cells);
  s.bound(freeze, &reserved, 1 << 36);
  let target = s.add(&state[BYTE_COUNT][..64], &s.c(64, DYNAMIC_BYTES));
  let pointer = [s.c(5, 0), target[..59].to_vec()].concat();
  let pointer = s.mask(nonempty, &pointer);
  let result = [s.c(128, 6), [pointer, length.to_vec()].concat()];
  for i in 0..2 {
    after[RESULT + i] = s.choose(f(56), &result[i], &after[RESULT + i]);
  }
  let phase = s.choose(nonempty, &s.c(128, BUILDER_NODE), &s.c(128, FINISH));
  after[CONTROL] = s.choose(f(56), &phase, &after[CONTROL]);
  after[BYTE_COUNT] =
    s.choose(f(56), &s.wide(&reserved, 128), &after[BYTE_COUNT]);
  for (at, value) in [
    (BUILDER, &args[0]),
    (BUILDER + 1, &args[1]),
    (BUILDER_HEAP, &state[HEAP_COUNT]),
    (OLD_BYTES, &state[BYTE_COUNT]),
  ] {
    after[at] = s.choose(f(56), value, &after[at]);
  }
  after[END] = s.choose(f(56), &s.wide(length, 128), &after[END]);
  let grow = s.and(e, growing);
  let grow_value = [[args[1][..64].to_vec(), s.c(64, 1)].concat(), s.c(128, 0)];
  let mut first = record(s, grow, &s.c(64, STACK), &grow_value);
  let prev =
    record(s, allocated, &address, &[args[0].clone(), args[1].clone()]);
  for (a, b) in first.iter_mut().zip(prev) {
    *a = a.iter().zip(b).map(|(&a, b)| s.b.xor(&[a, b], s.one)).collect();
  }
  after.extend(first);
  let next_address = s.add(&address, &s.c(64, 1));
  after.extend(record(
    s,
    allocated,
    &next_address,
    &[args[2].clone(), args[3].clone()],
  ));
  after
}

fn array_context(
  s: &mut S,
  e: usize,
  state: &[Bits],
  phase: u64,
) -> (usize, usize) {
  s.phase(e, state, phase, Phase::Eval);
  let get = op(s, state, 51);
  let set = op(s, state, 52);
  let push = op(s, state, 53);
  let valid = s.any(&[get, set, push]);
  s.need(e, valid);
  s.bound(e, &state[LENGTH], u64::from(u32::MAX));
  s.bound(e, &state[INDEX], (1 << 32) - 1);
  s.bound(e, &state[OFFSET], (1 << 32) - 1);
  s.bound(e, &state[CAPACITY], 1 << 32);
  s.bound(e, &state[DEPTH], 32);
  s.bound(e, &state[OLD_HEAP], 1 << 36);
  s.le(e, &state[OLD_HEAP], &state[HEAP_COUNT]);
  s.zeros(e, &state[21..].concat());
  let cap = &state[CAPACITY][..64];
  let nonzero = s.any(cap);
  s.need(e, nonzero);
  let predecessor = s.sub(cap, &s.c(64, 1));
  let multiple =
    cap.iter().zip(predecessor).map(|(&a, b)| s.and(a, b)).collect::<Bits>();
  s.zeros(e, &multiple);
  let inside = s.lt(&state[INDEX], &state[CAPACITY]);
  s.need(e, inside);
  let leaf = s.eqc(cap, 1);
  (get, leaf)
}
fn down_request(s: &mut S, e: usize, state: &[Bits]) -> Bits {
  let (get, leaf) = array_context(s, e, state, ARRAY_DOWN);
  let pointer = &state[POINTER];
  s.zeros(e, &pointer[41..]);
  let flat = pointer[40];
  let exists = s.lt(&state[OFFSET], &state[LENGTH]);
  let absent = s.inv(exists);
  let absent = s.and(e, absent);
  s.zeros(absent, pointer);
  let existing = s.and(e, exists);
  let remainder = s.sub(&state[LENGTH][..64], &state[OFFSET][..64]);
  let short = s.lt(&remainder, &state[CAPACITY][..64]);
  let count = s.choose(short, &remainder, &state[CAPACITY][..64]);
  let count = s.choose(flat, &count, &s.c(64, 1));
  canonical_heap(
    s,
    existing,
    &s.wide(&pointer[..40], 64),
    &count,
    &state[OLD_HEAP][..64],
  );
  let branch = s.inv(leaf);
  let nonflat = s.inv(flat);
  let branch = s.and(branch, nonflat);
  let terminal = s.and(leaf, get);
  let read = s.any(&[branch, terminal]);
  let read = s.and(read, exists);
  s.mask(read, &s.wide(&pointer[..40], 128))
}
fn down(s: &mut S, e: usize, state: &[Bits], reply: &[Bits]) -> Vec<Bits> {
  let request = down_request(s, e, state);
  let unused = s.eqc(&request, 0);
  s.zeros(unused, &reply.concat());
  let get = op(s, state, 51);
  let leaf = s.eqc(&state[CAPACITY], 1);
  let branch = s.inv(leaf);
  let changing = s.inv(get);
  let write_leaf = s.and(leaf, changing);
  let get_leaf = s.and(leaf, get);
  let checked_leaf = s.and(e, get_leaf);
  let masked = s.mask(checked_leaf, &reply.concat());
  s.value(checked_leaf, &masked);
  let flat = state[POINTER][40];
  let existing = s.any(&state[POINTER][..40]);
  let nonflat = s.inv(flat);
  let stored = s.and(existing, nonflat);
  let stored = s.and(stored, branch);
  let stored = s.and(e, stored);
  s.zeros(stored, &reply[1]);
  s.zeros(stored, &reply[0][41..64]);
  s.zeros(stored, &reply[0][105..]);
  let half = s.wide(&state[CAPACITY][1..64], 64);
  let right_offset = s.add(&state[OFFSET][..64], &half);
  let right_exists = s.lt(&right_offset, &state[LENGTH][..64]);
  let raw = s.wide(&state[POINTER][..40], 64);
  let right_pointer = s.add(&raw, &half);
  let mut right_flat = right_pointer;
  right_flat[40] = s.one;
  let right_flat = s.mask(right_exists, &right_flat);
  let left = s.choose(flat, &state[POINTER][..64], &reply[0][..64]);
  let right = s.choose(flat, &right_flat, &reply[0][64..]);
  let go_left = s.lt(&state[INDEX][..64], &half);
  let go_right = s.inv(go_left);
  let child = s.choose(go_left, &left, &right);
  let sibling = s.choose(go_left, &right, &left);
  let reduced_index = s.sub(&state[INDEX][..64], &half);
  let index = s.choose(go_left, &state[INDEX][..64], &reduced_index);
  let offset = s.choose(go_left, &state[OFFSET][..64], &right_offset);
  let depth = s.add(&state[DEPTH][..64], &s.c(64, 1));
  let branch_on = s.and(e, branch);
  s.bound(branch_on, &depth, 32);
  let stack = s.add(&state[DEPTH][..64], &s.c(64, STACK));
  let saved = [[sibling, s.wide(&[go_right], 64)].concat(), s.c(128, 0)];
  let write = s.and(e, write_leaf);
  let (heap, address) = reserve(s, write, &state[HEAP_COUNT], &s.c(64, 1));
  let mut after = state.to_vec();
  after[HEAP_COUNT] = s.choose(write_leaf, &heap, &state[HEAP_COUNT]);
  after[POINTER] =
    s.choose(branch, &s.wide(&child, 128), &s.wide(&address, 128));
  after[CAPACITY] = s.choose(branch, &s.wide(&half, 128), &state[CAPACITY]);
  after[INDEX] = s.choose(branch, &s.wide(&index, 128), &state[INDEX]);
  after[OFFSET] = s.choose(branch, &s.wide(&offset, 128), &state[OFFSET]);
  after[DEPTH] = s.choose(branch, &s.wide(&depth, 128), &state[DEPTH]);
  let has_parent = s.any(&state[DEPTH]);
  let ascend = s.and(write_leaf, has_parent);
  let phase = s.choose(ascend, &s.c(128, ARRAY_UP), &s.c(128, FINISH));
  after[CONTROL] = s.choose(branch, &s.c(128, ARRAY_DOWN), &phase);
  for i in 0..2 {
    after[RESULT + i] = s.choose(get_leaf, &reply[i], &after[RESULT + i]);
  }
  let no_parent = s.inv(has_parent);
  let root_leaf = s.and(write_leaf, no_parent);
  after[RESULT + 1] =
    s.choose(root_leaf, &s.wide(&address, 128), &after[RESULT + 1]);
  let save = s.and(branch_on, changing);
  after.extend(record(s, save, &stack, &saved));
  let write = s.and(e, write_leaf);
  after.extend(record(
    s,
    write,
    &address,
    &[state[ELEMENT].clone(), state[ELEMENT + 1].clone()],
  ));
  after
}
fn up_request(s: &mut S, e: usize, state: &[Bits]) -> Bits {
  let (get, _) = array_context(s, e, state, ARRAY_UP);
  s.zeros(e, &[get]);
  let present = s.any(&state[DEPTH]);
  s.need(e, present);
  let previous = s.sub(&state[DEPTH][..64], &s.c(64, 1));
  let address = s.add(&previous, &s.c(64, STACK));
  s.wide(&address, 128)
}
fn up(s: &mut S, e: usize, state: &[Bits], reply: &[Bits]) -> Vec<Bits> {
  up_request(s, e, state);
  s.zeros(e, &reply[1]);
  s.zeros(e, &reply[0][41..64]);
  s.zeros(e, &reply[0][65..]);
  canonical_heap(
    s,
    e,
    &state[POINTER][..64],
    &s.c(64, 1),
    &state[HEAP_COUNT][..64],
  );
  let right = reply[0][64];
  let left_pointer = s.choose(right, &reply[0][..64], &state[POINTER][..64]);
  let right_pointer = s.choose(right, &state[POINTER][..64], &reply[0][..64]);
  let value = [[left_pointer, right_pointer].concat(), s.c(128, 0)];
  let (heap, address) = reserve(s, e, &state[HEAP_COUNT], &s.c(64, 1));
  let depth = s.sub(&state[DEPTH][..64], &s.c(64, 1));
  let root = s.eqc(&depth, 0);
  let mut after = state.to_vec();
  after[HEAP_COUNT] = heap;
  after[POINTER] = s.wide(&address, 128);
  after[DEPTH] = s.wide(&depth, 128);
  after[CAPACITY] = [s.c(1, 0), state[CAPACITY][..127].to_vec()].concat();
  after[RESULT + 1] =
    s.choose(root, &s.wide(&address, 128), &after[RESULT + 1]);
  after[CONTROL] = s.choose(root, &s.c(128, FINISH), &s.c(128, ARRAY_UP));
  after.extend(record(s, e, &address, &value));
  after
}

fn builder_context(s: &mut S, e: usize, state: &[Bits], phase: u64) {
  s.phase(e, state, phase, Phase::Eval);
  s.is(e, &state[HEADER][24..32], 56);
  s.value(e, &state[BUILDER..BUILDER + 2].concat());
  s.is(e, &state[BUILDER][..64], BUILDER_TAG);
  s.is(e, &state[RESULT], 6);
  s.bound(e, &state[BUILDER_HEAP], 1 << 36);
  s.same(e, &state[HEAP_COUNT], &state[BUILDER_HEAP]);
  s.bound(e, &state[OLD_BYTES], 1 << 36);
  s.bound(e, &state[END], (1 << 36) - 1);
  s.bound(e, &state[REMAIN], (1 << 36) - 1);
  s.zeros(e, &state[21..].concat());
  let total = &state[RESULT + 1][64..];
  s.bound(e, total, (1 << 36) - 1);
  s.le(e, &state[END][..64], total);
  let rounded = s.add(total, &s.c(64, 31));
  let reserved = s.add(&state[OLD_BYTES][..64], &s.wide(&rounded[5..], 64));
  s.same(e, &state[BYTE_COUNT], &s.wide(&reserved, 128));
  let base = s.add(&state[OLD_BYTES][..64], &s.c(64, DYNAMIC_BYTES));
  let pointer = [s.c(5, 0), base[..59].to_vec()].concat();
  s.same(e, &state[RESULT + 1][..64], &pointer);
}
fn node_request(s: &mut S, e: usize, state: &[Bits]) -> Vec<Bits> {
  builder_context(s, e, state, BUILDER_NODE);
  s.zeros(e, &state[CHUNK]);
  s.zeros(e, &state[REMAIN]);
  s.same(e, &state[END][..64], &state[BUILDER][64..]);
  let live = s.any(&state[END]);
  s.need(e, live);
  canonical_heap(
    s,
    e,
    &state[BUILDER + 1][..64],
    &s.c(64, 2),
    &state[BUILDER_HEAP][..64],
  );
  let next = s.add(&state[BUILDER + 1][..64], &s.c(64, 1));
  vec![state[BUILDER + 1].clone(), s.wide(&next, 128)]
}
fn node(s: &mut S, e: usize, state: &[Bits], reply: &[Bits]) -> Vec<Bits> {
  node_request(s, e, state);
  let previous = s.value(e, &reply[..2].concat());
  let chunk = s.value(e, &reply[2..].concat());
  s.need(e, previous[11]);
  s.need(e, chunk[5]);
  let nonempty = s.any(&reply[3][64..]);
  s.need(e, nonempty);
  let total = s.add(&reply[0][64..], &reply[3][64..]);
  s.same(e, &total, &state[BUILDER][64..]);
  // No forward/self-reference can introduce a cycle or read the new output.
  let older = s.lt(&reply[1][..64], &state[BUILDER + 1][..64]);
  s.need(e, older);
  bytes::byte_span(s, e, &reply[3], &state[OLD_BYTES]);
  let mut after = state.to_vec();
  after[BUILDER] = reply[0].clone();
  after[BUILDER + 1] = reply[1].clone();
  after[CHUNK] = reply[3].clone();
  after[REMAIN] = s.wide(&reply[3][64..], 128);
  after[CONTROL] = s.c(128, BUILDER_COPY);
  after
}
fn copy_request(s: &mut S, e: usize, state: &[Bits]) -> Vec<Bits> {
  builder_context(s, e, state, BUILDER_COPY);
  let live = s.any(&state[REMAIN]);
  s.need(e, live);
  s.le(e, &state[REMAIN][..64], &state[CHUNK][64..]);
  let total = s.add(&state[BUILDER][64..], &state[REMAIN][..64]);
  s.same(e, &state[END], &s.wide(&total, 128));
  bytes::byte_span(s, e, &state[CHUNK], &state[OLD_BYTES]);
  let aligned = s.eqc(&state[END][..5], 0);
  let tail = s.wide(&state[END][..5], 64);
  let room = s.choose(aligned, &s.c(64, 32), &tail);
  let short = s.lt(&state[REMAIN][..64], &room);
  let count = s.choose(short, &state[REMAIN][..64], &room);
  let start = s.sub(&state[REMAIN][..64], &count);
  let pointer = s.add(&state[CHUNK][..64], &start);
  vec![s.wide(&pointer, 128), s.wide(&count, 128)]
}
fn copy(s: &mut S, e: usize, state: &[Bits], data: &[Bits]) -> Vec<Bits> {
  let request = copy_request(s, e, state);
  s.zeros(e, &data[2..].concat());
  let end = s.sub(&state[END][..64], &request[1][..64]);
  let remain = s.sub(&state[REMAIN][..64], &request[1][..64]);
  let mut shifted = data[..2].concat();
  for (i, &bit) in end.iter().take(5).enumerate() {
    let shift = 8 << i;
    let alternate = (0..256)
      .map(|j| if j < shift { s.zero } else { shifted[j - shift] })
      .collect::<Bits>();
    shifted = s.choose(bit, &alternate, &shifted);
  }
  let buffered = state[BUFFER..BUFFER + 2].concat();
  let overlap =
    buffered.iter().zip(&shifted).map(|(&a, &b)| s.and(a, b)).collect::<Bits>();
  s.zeros(e, &overlap);
  let output = buffered
    .iter()
    .zip(&shifted)
    .map(|(&a, &b)| s.b.xor(&[a, b], s.one))
    .collect::<Bits>();
  let aligned = s.eqc(&end[..5], 0);
  let more = s.any(&remain);
  let next = s.choose(more, &s.c(128, BUILDER_COPY), &s.c(128, BUILDER_NODE));
  let mut after = state.to_vec();
  after[END] = s.wide(&end, 128);
  after[REMAIN] = s.wide(&remain, 128);
  after[CHUNK] = s.mask(more, &state[CHUNK]);
  after[BUFFER] = output[..128].to_vec();
  after[BUFFER + 1] = output[128..].to_vec();
  after[CONTROL] = s.choose(aligned, &s.c(128, BUILDER_EMIT), &next);
  after
}
fn emit(s: &mut S, e: usize, state: &[Bits]) -> Vec<Bits> {
  builder_context(s, e, state, BUILDER_EMIT);
  s.zeros(e, &state[END][..5]);
  let total = s.add(&state[BUILDER][64..], &state[REMAIN][..64]);
  s.same(e, &state[END], &s.wide(&total, 128));
  let remaining = s.any(&state[END]);
  let chunk = s.any(&state[REMAIN]);
  let phase = s.choose(chunk, &s.c(128, BUILDER_COPY), &s.c(128, BUILDER_NODE));
  let offset = s.add(&state[OLD_BYTES][..64], &s.wide(&state[END][5..64], 64));
  let address = s.add(&offset, &s.c(64, DYNAMIC_BYTES));
  let mut after = state.to_vec();
  after[BUFFER] = s.c(128, 0);
  after[BUFFER + 1] = s.c(128, 0);
  after[CONTROL] = s.choose(remaining, &phase, &s.c(128, FINISH));
  after.extend(record(
    s,
    e,
    &address,
    &[state[BUFFER].clone(), state[BUFFER + 1].clone()],
  ));
  after
}
pub(super) fn build(kind: CollectionKind) -> BooleanR1csPlan {
  let ni = 1 + STATE_WORDS + kind.extra_inputs();
  let no = kind.outputs() + 1;
  let mut b = BooleanR1csBuilder::new(16, (ni + no) * 128);
  for i in 0..ni * 128 {
    b.free_boolean_at(i);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut s = S { b, one, zero, bad: Vec::new() };
  let e = 0;
  s.zeros(one, &(1..128).collect::<Bits>());
  let state = (1..1 + STATE_WORDS).map(word).collect::<Vec<_>>();
  let extra = (1 + STATE_WORDS..ni).map(word).collect::<Vec<_>>();
  basic(&mut s, e, &state);
  let mut output = match kind {
    CollectionKind::Start => start(&mut s, e, &state, &extra),
    CollectionKind::ArrayRequest => vec![down_request(&mut s, e, &state)],
    CollectionKind::ArrayStep => down(&mut s, e, &state, &extra),
    CollectionKind::AscendRequest => vec![up_request(&mut s, e, &state)],
    CollectionKind::Ascend => up(&mut s, e, &state, &extra),
    CollectionKind::BuilderRequest => node_request(&mut s, e, &state),
    CollectionKind::BuilderNode => node(&mut s, e, &state, &extra),
    CollectionKind::CopyRequest => copy_request(&mut s, e, &state),
    CollectionKind::Copy => copy(&mut s, e, &state, &extra),
    CollectionKind::Emit => emit(&mut s, e, &state),
    CollectionKind::Finish => {
      s.phase(e, &state, FINISH, Phase::Eval);
      let valid = (49..=57).map(|i| op(&mut s, &state, i)).collect::<Vec<_>>();
      let valid = s.any(&valid);
      s.need(e, valid);
      s.value(e, &state[RESULT..RESULT + 2].concat());
      let mut action = s.action(ActionKind::Bind, &state[HEADER][80..88]);
      action[2] = state[RESULT].clone();
      action[3] = state[RESULT + 1].clone();
      action
    },
  };
  assert_eq!(output.len(), kind.outputs());
  for value in &mut output {
    *value = s.mask(e, &s.wide(value, 128));
  }
  let bad = s.any(&s.bad.clone());
  output.push(s.wide(&[bad], 128));
  for (i, value) in output.iter().enumerate() {
    for (j, &bit) in value.iter().enumerate() {
      s.b.write_xor((ni + i) * 128 + j, &[bit], one);
    }
  }
  s.b.finish()
}
