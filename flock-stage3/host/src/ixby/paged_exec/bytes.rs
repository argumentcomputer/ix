//! Byte ranges, incremental copies and the standard BLAKE3 chunk/tree state.
//! All data words come from the same authenticated memory as execution.
use super::objects::{Bits, S};
use super::*;
use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  hash::{CHUNK_END, CHUNK_START, IV, PARENT, ROOT, pack_params, pack8},
  ixby::{
    paged_frame::{ActionKind, Phase, SCRATCH},
    paged_value::{DYNAMIC_BYTES, INPUT_BYTES, PROGRAM_BYTES},
  },
};

pub(super) const RESULT: usize = 10;
pub(super) const A: usize = 12;
pub(super) const B: usize = 13;
pub(super) const POSITION: usize = 14;
pub(super) const OLD_BYTES: usize = 16;
pub(super) const CV: usize = 17;
pub(super) const MERGE_MASK: usize = 19;
pub(super) const MERGE_CONTROL: usize = 20;
pub(super) const HASH_STACK: u64 = SCRATCH + 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteKind {
  Start,
  ReadRequest,
  ReadFinish,
  AppendRequest,
  AppendFinish,
  EqRequest,
  EqFinish,
  Finish,
  Emit,
  Window,
  HashRequest,
  HashFinish,
  HashMergeRequest,
  HashMergeFinish,
  HashPush,
  HashSkip,
}
impl ByteKind {
  pub(super) fn extra_inputs(self) -> usize {
    match self {
      Self::Start => 7,
      Self::ReadFinish => 4,
      Self::AppendFinish | Self::EqFinish | Self::Window => 8,
      Self::HashFinish | Self::HashMergeFinish => 2,
      _ => 0,
    }
  }
  pub(super) fn outputs(self) -> usize {
    match self {
      Self::ReadRequest | Self::HashMergeRequest => 2,
      Self::AppendRequest | Self::EqRequest => 4,
      Self::HashRequest => 5,
      Self::Finish => 5,
      Self::Window => 16,
      Self::AppendFinish | Self::Emit | Self::HashPush => STATE_WORDS + 4,
      _ => STATE_WORDS,
    }
  }
}
pub(super) fn is_byte(opcode: u8) -> bool {
  matches!(opcode, 21 | 22 | 29 | 30 | 39..=44)
}
fn word(at: usize) -> Bits {
  (at * 128..(at + 1) * 128).collect()
}
fn fw(s: &S, value: F128) -> Bits {
  let mut out = s.c(64, value.lo);
  out.extend(s.c(64, value.hi));
  out
}
fn pick(s: &mut S, n: usize, choices: &[(usize, Bits)]) -> Bits {
  (0..n)
    .map(|i| {
      let terms = choices
        .iter()
        .map(|(flag, bits)| {
          s.and(*flag, bits.get(i).copied().unwrap_or(s.zero))
        })
        .collect::<Vec<_>>();
      s.b.xor(&terms, s.one)
    })
    .collect()
}
fn opcode(s: &mut S, state: &[Bits], code: u64) -> usize {
  s.eqc(&state[HEADER][24..32], code)
}
fn byte_vector(s: &mut S, pointer: &[usize], length: &[usize]) -> Bits {
  let empty = s.eqc(length, 0);
  let live = s.inv(empty);
  let mut out = s.c(128, 0);
  out[..64].copy_from_slice(&s.mask(live, &s.wide(pointer, 64)));
  out[64..100].copy_from_slice(&s.wide(length, 36));
  out
}
fn length(s: &S, v: &[usize]) -> Bits {
  s.wide(&v[64..100], 64)
}
fn byte_span(s: &mut S, e: usize, v: &[usize], allocated: &[usize]) {
  s.zeros(e, &v[45..64]);
  s.zeros(e, &v[100..]);
  let empty = s.eqc(&v[64..100], 0);
  let empty_e = s.and(e, empty);
  s.zeros(empty_e, &v[..64]);
  let nonempty = s.inv(empty);
  let live = s.and(e, nonempty);
  let banks = [PROGRAM_BYTES, INPUT_BYTES, DYNAMIC_BYTES]
    .map(|bank| s.eqc(&v[41..45], bank >> 36));
  let valid = s.any(&banks);
  s.need(live, valid);
  let end = s.add(&s.wide(&v[..41], 42), &s.wide(&v[64..100], 42));
  s.bound(live, &end, 1 << 41);
  let dynamic = s.and(live, banks[2]);
  let mut bound = s.c(5, 0);
  bound.extend_from_slice(&allocated[..37]);
  s.le(dynamic, &end, &bound);
}
fn cells(s: &mut S, len: &[usize]) -> Bits {
  let rounded = s.add(&s.wide(len, 64), &s.c(64, 31));
  s.wide(&rounded[5..], 64)
}
fn min(s: &mut S, a: &[usize], b: &[usize]) -> Bits {
  let below = s.lt(a, b);
  s.choose(below, a, b)
}
fn read_pointer(
  s: &mut S,
  base: &[usize],
  position: &[usize],
  count: &[usize],
) -> Bits {
  let pointer = s.add(&base[..64], &s.wide(position, 64));
  let empty = s.eqc(count, 0);
  let live = s.inv(empty);
  let pointer = s.mask(live, &pointer);
  s.wide(&pointer, 128)
}
fn context(s: &mut S, e: usize, state: &[Bits]) {
  s.zeros(e, &state[15]);
  s.zeros(e, &state[21..].concat());
  s.zeros(e, &state[POSITION][64..]);
  s.bound(e, &state[POSITION], (1 << 36) - 1);
  s.bound(e, &state[OLD_BYTES], 1 << 36);
  let a_used = [22, 30, 39, 40, 41, 42, 43, 44].map(|p| opcode(s, state, p));
  let a_used = s.any(&a_used);
  let a_live = s.and(e, a_used);
  byte_span(s, a_live, &state[A], &state[OLD_BYTES]);
  let a_unused = s.inv(a_used);
  let a_unused = s.and(e, a_unused);
  s.zeros(a_unused, &state[A]);
  let append = opcode(s, state, 41);
  let eq = opcode(s, state, 43);
  let two = s.any(&[append, eq]);
  let b_live = s.and(e, two);
  byte_span(s, b_live, &state[B], &state[OLD_BYTES]);
  let b_unused = s.inv(two);
  let b_unused = s.and(e, b_unused);
  s.zeros(b_unused, &state[B]);
  let allocates = [21, 29, 41, 44].map(|p| opcode(s, state, p));
  let allocates = s.any(&allocates);
  let count = cells(s, &length(s, &state[RESULT + 1]));
  let count = s.mask(allocates, &count);
  let expected = s.add(&state[OLD_BYTES][..64], &count);
  s.same(e, &state[BYTE_COUNT], &s.wide(&expected, 128));
  let dynamic = s.add(&state[OLD_BYTES][..64], &s.c(64, DYNAMIC_BYTES));
  let mut pointer = s.c(5, 0);
  pointer.extend_from_slice(&dynamic[..59]);
  let expected = byte_vector(s, &pointer, &state[RESULT + 1][64..100]);
  let allocated = s.and(e, allocates);
  s.same(allocated, &state[RESULT + 1], &expected);
  let hash = opcode(s, state, 44);
  let nonhash = s.inv(hash);
  let nonhash = s.and(e, nonhash);
  s.zeros(nonhash, &state[MERGE_MASK..MERGE_CONTROL + 1].concat());
  let raw = [21, 29, 44].map(|p| opcode(s, state, p));
  let raw = s.any(&raw);
  let noraw = s.inv(raw);
  let noraw = s.and(e, noraw);
  s.zeros(noraw, &state[CV..CV + 2].concat());
}
fn start(s: &mut S, e: usize, state: &[Bits], extra: &[Bits]) -> Vec<Bits> {
  s.instruction(e, state, 0, 1);
  s.zeros(e, &state[10..].concat());
  let codes = [21u64, 22, 29, 30, 39, 40, 41, 42, 43, 44];
  let flags = codes.map(|p| opcode(s, state, p));
  let allowed = s.any(&flags);
  s.need(e, allowed);
  let f = |p| flags[codes.iter().position(|&x| x == p).unwrap()];
  let to = s.any(&[f(21), f(29)]);
  let from = s.any(&[f(22), f(30)]);
  let byte_a = s.inv(to);
  let two_bytes = s.any(&[f(41), f(43)]);
  let index = s.any(&[f(40), f(42)]);
  let second_used = s.any(&[two_bytes, index]);
  let uses = [s.one, second_used, f(42)];
  for (i, used) in uses.into_iter().enumerate() {
    let used = s.and(e, used);
    let tags = s.value(used, &extra[2 * i..2 * i + 2].concat());
    if i == 0 {
      for (flag, tag) in [(f(21), 1), (f(29), 2), (byte_a, 5)] {
        let check = s.and(e, flag);
        s.need(check, tags[tag]);
      }
    } else if i == 1 {
      for (flag, tag) in [(two_bytes, 5), (index, 1)] {
        let check = s.and(e, flag);
        s.need(check, tags[tag]);
      }
    } else {
      s.need(used, tags[1]);
    }
  }
  let one_arg = s.inv(second_used);
  let two_arg = s.b.product_of_parities(&[second_used], &[f(42), s.one]);
  let arity = pick(
    s,
    8,
    &[(one_arg, s.c(8, 1)), (two_arg, s.c(8, 2)), (f(42), s.c(8, 3))],
  );
  s.same(e, &state[HEADER][32..40], &arity);
  s.same(e, &state[HEADER][40..48], &arity);
  let a = &extra[1];
  let b = &extra[3];
  let len_a = length(s, a);
  let len_b = length(s, b);
  let byte_a_live = s.and(e, byte_a);
  byte_span(s, byte_a_live, a, &state[BYTE_COUNT]);
  let two_live = s.and(e, two_bytes);
  byte_span(s, two_live, b, &state[BYTE_COUNT]);
  let limit = &extra[6][64..];
  s.le(byte_a_live, &len_a, limit);
  s.le(two_live, &len_b, limit);
  for (flag, n) in [(f(22), 4), (f(30), 8)] {
    let flag = s.and(e, flag);
    s.is(flag, &len_a, n);
  }
  let get = s.and(e, f(40));
  let in_range = s.lt(&extra[3][..64], &len_a);
  s.need(get, in_range);
  let sliced_end = s.add(&extra[3][..64], &extra[5][..64]);
  let slice = s.and(e, f(42));
  s.le(slice, &sliced_end, &len_a);
  let len_check = s.and(e, f(39));
  s.bound(len_check, &len_a, u64::from(u32::MAX));
  let total = s.add(&len_a, &len_b);
  let allocated_len = pick(
    s,
    64,
    &[
      (f(21), s.c(64, 4)),
      (f(29), s.c(64, 8)),
      (f(41), total.clone()),
      (f(44), s.c(64, 32)),
    ],
  );
  let allocate = s.any(&[to, f(41), f(44)]);
  let allocated = s.and(e, allocate);
  s.bound(allocated, &allocated_len, (1 << 36) - 1);
  s.le(allocated, &allocated_len, limit);
  let count = cells(s, &allocated_len);
  let reserved = s.add(&state[BYTE_COUNT][..64], &count);
  s.bound(e, &reserved, 1 << 36);
  let address = s.add(&state[BYTE_COUNT][..64], &s.c(64, DYNAMIC_BYTES));
  let mut pointer = s.c(5, 0);
  pointer.extend_from_slice(&address[..59]);
  let result_bytes = byte_vector(s, &pointer, &allocated_len);
  let slice_pointer = s.add(&a[..64], &extra[3][..64]);
  let slice_vector = byte_vector(s, &slice_pointer, &extra[5][..32]);
  let same_len = s.eq(&len_a, &len_b);
  let empty_a = s.eqc(&len_a, 0);
  let nonempty_a = s.inv(empty_a);
  let scanning_eq = s.and(same_len, nonempty_a);
  let scanning_eq = s.and(f(43), scanning_eq);
  let empty_result = s.eqc(&allocated_len, 0);
  let nonempty_result = s.inv(empty_result);
  let copying = s.and(f(41), nonempty_result);
  let reading = s.any(&[from, f(40)]);
  let pending = s.any(&[to, copying, reading, scanning_eq, f(44)]);
  let immediate = s.inv(pending);
  let phase = pick(
    s,
    128,
    &[
      (to, s.c(128, BYTE_EMIT)),
      (copying, s.c(128, BYTE_APPEND)),
      (reading, s.c(128, BYTE_READ)),
      (scanning_eq, s.c(128, BYTE_EQ)),
      (f(44), s.c(128, HASH_BLOCK)),
      (immediate, s.c(128, BYTE_FINISH)),
    ],
  );
  let bytes_result = s.any(&[allocate, f(42)]);
  let word_result = s.any(&[f(22), f(39), f(40)]);
  let result_header = pick(
    s,
    128,
    &[
      (bytes_result, s.c(128, 6)),
      (word_result, s.c(128, 2)),
      (f(30), s.c(128, 3)),
      (f(43), s.c(128, 1)),
    ],
  );
  let eq_result = s.wide(&[same_len], 128);
  let payload = pick(
    s,
    128,
    &[
      (allocate, result_bytes),
      (f(42), slice_vector),
      (f(39), s.wide(&len_a, 128)),
      (f(43), eq_result),
    ],
  );
  let mut after = state.to_vec();
  for w in &mut after[10..] {
    *w = s.c(128, 0);
  }
  after[CONTROL] = phase;
  after[BYTE_COUNT] = s.wide(&reserved, 128);
  after[RESULT] = result_header;
  after[RESULT + 1] = payload;
  after[A] = s.mask(byte_a, a);
  after[B] = s.mask(two_bytes, b);
  after[POSITION] = s.mask(f(40), &extra[3]);
  after[OLD_BYTES] = state[BYTE_COUNT].clone();
  let iv = pack8(&IV);
  after[CV] = pick(s, 128, &[(to, extra[1].clone()), (f(44), fw(s, iv[0]))]);
  after[CV + 1] = s.mask(f(44), &fw(s, iv[1]));
  after
}

// Operation implementations are below; each returns actual state/access words.
fn window(s: &mut S, e: usize, extra: &[Bits]) -> Vec<Bits> {
  let pointer = &extra[0];
  let count = &extra[1];
  let disabled = s.inv(e);
  s.zeros(disabled, &extra.concat());
  s.zeros(e, &pointer[45..]);
  s.bound(e, count, 64);
  let empty = s.eqc(count, 0);
  let empty_e = s.and(e, empty);
  s.zeros(empty_e, pointer);
  let nonempty = s.inv(empty);
  let live = s.and(e, nonempty);
  let banks = [PROGRAM_BYTES, INPUT_BYTES, DYNAMIC_BYTES]
    .map(|v| s.eqc(&pointer[41..45], v >> 36));
  let valid = s.any(&banks);
  s.need(live, valid);
  let end = s.add(&s.wide(&pointer[..41], 42), &s.wide(&count[..7], 42));
  s.bound(live, &end, 1 << 41);
  let size = s.add(&s.wide(&pointer[..5], 8), &s.wide(&count[..7], 8));
  let rounded = s.add(&size, &s.c(8, 31));
  let ncells = &rounded[5..8];
  let mut records = Vec::new();
  for i in 0..3 {
    let used = s.lt(&s.c(3, i), ncells);
    let used = s.and(e, used);
    let unused = s.inv(used);
    s.zeros(unused, &extra[2 + 2 * i as usize..4 + 2 * i as usize].concat());
    let base = s.wide(&pointer[5..45], 64);
    let address = s.add(&base, &s.c(64, i));
    let address = s.mask(used, &address);
    records.extend([
      s.wide(&address, 128),
      s.c(128, 0),
      extra[2 + 2 * i as usize].clone(),
      extra[3 + 2 * i as usize].clone(),
    ]);
  }
  let mut shifted = extra[2..].concat();
  for (i, &flag) in pointer.iter().take(5).enumerate() {
    let alternate = (0..768)
      .map(|j| shifted.get(j + (8 << i)).copied().unwrap_or(s.zero))
      .collect::<Bits>();
    shifted = s.choose(flag, &alternate, &shifted);
  }
  let mut data = Vec::new();
  for i in 0..64 {
    let used = s.lt(&s.c(7, i as u64), &count[..7]);
    data.extend(s.mask(used, &shifted[8 * i..8 * i + 8]));
  }
  let mut out =
    data.as_chunks::<128>().0.iter().map(|w| w.to_vec()).collect::<Vec<_>>();
  out.extend(records);
  out
}
fn read_request(s: &mut S, e: usize, state: &[Bits]) -> Vec<Bits> {
  s.is(e, &state[CONTROL], BYTE_READ);
  let word = opcode(s, state, 22);
  let field = opcode(s, state, 30);
  let get = opcode(s, state, 40);
  let valid = s.any(&[word, field, get]);
  s.need(e, valid);
  let count =
    pick(s, 64, &[(word, s.c(64, 4)), (field, s.c(64, 8)), (get, s.c(64, 1))]);
  let from = s.any(&[word, field]);
  let from = s.and(e, from);
  s.zeros(from, &state[POSITION]);
  s.same(from, &length(s, &state[A]), &count);
  let get = s.and(e, get);
  s.bound(get, &state[POSITION], u64::from(u32::MAX));
  let end = s.add(&state[POSITION][..64], &count);
  s.le(e, &end, &length(s, &state[A]));
  let pointer = read_pointer(s, &state[A], &state[POSITION][..64], &count);
  vec![pointer, s.wide(&count, 128)]
}
fn append_request(s: &mut S, e: usize, state: &[Bits]) -> Vec<Bits> {
  s.is(e, &state[CONTROL], BYTE_APPEND);
  s.is(e, &state[HEADER][24..32], 41);
  let position = &state[POSITION][..64];
  s.zeros(e, &position[..5]);
  let la = length(s, &state[A]);
  let lb = length(s, &state[B]);
  let total = s.add(&la, &lb);
  s.same(e, &length(s, &state[RESULT + 1]), &total);
  let valid = s.lt(position, &total);
  s.need(e, valid);
  let inside_a = s.lt(position, &la);
  let outside_a = s.inv(inside_a);
  let remaining_a = s.sub(&la, position);
  let remaining_a = s.mask(inside_a, &remaining_a);
  let count_a = min(s, &remaining_a, &s.c(64, 32));
  let position_b = s.sub(position, &la);
  let position_b = s.mask(outside_a, &position_b);
  let remaining_b = s.sub(&lb, &position_b);
  let available = s.sub(&s.c(64, 32), &count_a);
  let count_b = min(s, &remaining_b, &available);
  vec![
    read_pointer(s, &state[A], position, &count_a),
    s.wide(&count_a, 128),
    read_pointer(s, &state[B], &position_b, &count_b),
    s.wide(&count_b, 128),
  ]
}
fn eq_request(s: &mut S, e: usize, state: &[Bits]) -> Vec<Bits> {
  s.is(e, &state[CONTROL], BYTE_EQ);
  s.is(e, &state[HEADER][24..32], 43);
  let la = length(s, &state[A]);
  let lb = length(s, &state[B]);
  s.same(e, &la, &lb);
  let position = &state[POSITION][..64];
  s.zeros(e, &position[..5]);
  let valid = s.lt(position, &la);
  s.need(e, valid);
  s.is(e, &state[RESULT], 1);
  s.is(e, &state[RESULT + 1], 1);
  let remaining = s.sub(&la, position);
  let count = min(s, &remaining, &s.c(64, 32));
  vec![
    read_pointer(s, &state[A], position, &count),
    s.wide(&count, 128),
    read_pointer(s, &state[B], position, &count),
    s.wide(&count, 128),
  ]
}
fn append_finish(
  s: &mut S,
  e: usize,
  state: &[Bits],
  extra: &[Bits],
) -> Vec<Bits> {
  let request = append_request(s, e, state);
  s.zeros(e, &extra[2..4].concat());
  s.zeros(e, &extra[6..8].concat());
  let mut second = extra[4..6].concat();
  for (i, &flag) in request[1].iter().take(6).enumerate() {
    let alternate = (0usize..256)
      .map(|j| j.checked_sub(8 << i).map(|at| second[at]).unwrap_or(s.zero))
      .collect::<Bits>();
    second = s.choose(flag, &alternate, &second);
  }
  let combined = extra[..2]
    .concat()
    .iter()
    .zip(second)
    .map(|(&a, b)| s.b.xor(&[a, b], s.one))
    .collect::<Bits>();
  let amount = s.add(&request[1][..64], &request[3][..64]);
  let next = s.add(&state[POSITION][..64], &amount);
  let done = s.eq(&next, &length(s, &state[RESULT + 1]));
  let address = s.add(
    &s.wide(&state[RESULT + 1][5..45], 64),
    &s.wide(&state[POSITION][5..64], 64),
  );
  let mut out = state.to_vec();
  out[POSITION] = s.wide(&next, 128);
  out[CONTROL] = s.choose(done, &s.c(128, BYTE_FINISH), &s.c(128, BYTE_APPEND));
  out.extend([
    s.wide(&address, 128),
    s.c(128, 1),
    combined[..128].to_vec(),
    combined[128..].to_vec(),
  ]);
  out
}
fn eq_finish(s: &mut S, e: usize, state: &[Bits], extra: &[Bits]) -> Vec<Bits> {
  let request = eq_request(s, e, state);
  s.zeros(e, &extra[2..4].concat());
  s.zeros(e, &extra[6..8].concat());
  let same = s.eq(&extra[..2].concat(), &extra[4..6].concat());
  let next = s.add(&state[POSITION][..64], &request[1][..64]);
  let complete = s.eq(&next, &length(s, &state[A]));
  let different = s.inv(same);
  let done = s.any(&[complete, different]);
  let mut out = state.to_vec();
  out[POSITION] = s.wide(&next, 128);
  out[RESULT + 1] = s.wide(&[same], 128);
  out[CONTROL] = s.choose(done, &s.c(128, BYTE_FINISH), &s.c(128, BYTE_EQ));
  out
}

struct HashInfo {
  count: Bits,
  counter: Bits,
  last: usize,
  end: usize,
  root: usize,
  next: Bits,
  params: Bits,
}
fn hash_info(s: &mut S, e: usize, state: &[Bits]) -> HashInfo {
  s.is(e, &state[CONTROL], HASH_BLOCK);
  s.is(e, &state[HEADER][24..32], 44);
  s.zeros(e, &state[MERGE_MASK..MERGE_CONTROL + 1].concat());
  let position = &state[POSITION][..64];
  s.zeros(e, &position[..6]);
  let len = length(s, &state[A]);
  let in_range = s.lt(position, &len);
  let empty = s.eqc(&len, 0);
  let first = s.eqc(position, 0);
  let empty_first = s.and(empty, first);
  let valid = s.any(&[in_range, empty_first]);
  s.need(e, valid);
  let remaining = s.sub(&len, position);
  let count = min(s, &remaining, &s.c(64, 64));
  let more = s.lt(&s.c(64, 64), &remaining);
  let last = s.inv(more);
  let chunk_end = s.eqc(&position[6..10], 15);
  let end = s.any(&[chunk_end, last]);
  let start = s.eqc(&position[6..10], 0);
  let counter = s.wide(&position[10..], 64);
  let first_chunk = s.eqc(&counter, 0);
  let root = s.and(first_chunk, last);
  let start_e = s.and(e, start);
  for (i, iv) in pack8(&IV).into_iter().enumerate() {
    s.same(start_e, &state[CV + i], &fw(s, iv));
  }
  let mut params = counter.clone();
  params.extend_from_slice(&count[..32]);
  params.extend(pick(
    s,
    32,
    &[
      (start, s.c(32, u64::from(CHUNK_START))),
      (end, s.c(32, u64::from(CHUNK_END))),
      (root, s.c(32, u64::from(ROOT))),
    ],
  ));
  let next = s.add(position, &count);
  HashInfo { count, counter, last, end, root, next, params }
}
fn hash_finish(
  s: &mut S,
  e: usize,
  state: &[Bits],
  extra: &[Bits],
) -> Vec<Bits> {
  let h = hash_info(s, e, state);
  let mut out = state.to_vec();
  out[POSITION] = s.wide(&h.next, 128);
  out[CV..CV + 2].clone_from_slice(extra);
  let not_root = s.inv(h.root);
  let merge = s.and(h.end, not_root);
  let block = s.inv(h.end);
  out[CONTROL] = pick(
    s,
    128,
    &[
      (h.root, s.c(128, BYTE_EMIT)),
      (merge, s.c(128, HASH_MERGE)),
      (block, s.c(128, HASH_BLOCK)),
    ],
  );
  out[MERGE_MASK] = s.mask(merge, &s.wide(&h.counter, 128));
  out[MERGE_CONTROL] = s.c(128, 0);
  out[MERGE_CONTROL][64] = s.and(merge, h.last);
  out
}
struct MergeInfo {
  bit: usize,
  final_chunk: usize,
  cleared: Bits,
  next_level: Bits,
  root: usize,
  address: Bits,
  params: Bits,
}
fn merge_info(s: &mut S, e: usize, state: &[Bits]) -> MergeInfo {
  s.is(e, &state[CONTROL], HASH_MERGE);
  s.is(e, &state[HEADER][24..32], 44);
  s.zeros(e, &state[MERGE_CONTROL][8..64]);
  s.zeros(e, &state[MERGE_CONTROL][65..]);
  let level = &state[MERGE_CONTROL][..8];
  s.bound(e, level, 26);
  s.bound(e, &state[MERGE_MASK], (1 << 26) - 1);
  let selectors = (0..27).map(|i| s.eqc(level, i)).collect::<Vec<_>>();
  let selected = selectors
    .iter()
    .zip(&state[MERGE_MASK][..27])
    .map(|(&a, &b)| s.and(a, b))
    .collect::<Vec<_>>();
  let bit = s.any(&selected);
  let mut cleared = state[MERGE_MASK].clone();
  for i in 0..27 {
    cleared[i] = s.b.xor(&[cleared[i], selectors[i]], s.one);
  }
  let final_chunk = state[MERGE_CONTROL][64];
  let empty = s.eqc(&cleared, 0);
  let root = s.and(final_chunk, empty);
  let mut params = fw(s, pack_params(0, 64, PARENT));
  params[96 + ROOT.trailing_zeros() as usize] = root;
  let next_level = s.add(level, &s.c(8, 1));
  let address = s.add(&s.wide(level, 64), &s.c(64, HASH_STACK));
  MergeInfo {
    bit,
    final_chunk,
    cleared,
    next_level,
    root,
    address: s.wide(&address, 128),
    params,
  }
}
fn merge_finish(
  s: &mut S,
  e: usize,
  state: &[Bits],
  extra: &[Bits],
) -> Vec<Bits> {
  let m = merge_info(s, e, state);
  s.need(e, m.bit);
  let mut out = state.to_vec();
  out[CV..CV + 2].clone_from_slice(extra);
  out[MERGE_MASK] = m.cleared;
  out[MERGE_CONTROL][..8].copy_from_slice(&m.next_level);
  out[CONTROL] = s.choose(m.root, &s.c(128, BYTE_EMIT), &s.c(128, HASH_MERGE));
  out
}

pub(super) fn build(kind: ByteKind) -> BooleanR1csPlan {
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
  for at in [HEAP_COUNT, BYTE_COUNT] {
    s.bound(e, &state[at], 1 << 36);
  }
  if !matches!(kind, ByteKind::Window | ByteKind::Start) {
    s.is(e, &state[0][..8], Phase::Eval as u64);
    s.is(e, &state[HEADER][8..16], 0);
    s.is(e, &state[HEADER][16..24], 1);
    let allowed = [21, 22, 29, 30, 39, 40, 41, 42, 43, 44]
      .map(|p| opcode(&mut s, &state, p));
    let allowed = s.any(&allowed);
    s.need(e, allowed);
    context(&mut s, e, &state);
  }
  let mut out = match kind {
    ByteKind::Start => start(&mut s, e, &state, &extra),
    ByteKind::Window => window(&mut s, e, &extra),
    ByteKind::ReadRequest => read_request(&mut s, e, &state),
    ByteKind::ReadFinish => {
      read_request(&mut s, e, &state);
      s.zeros(e, &extra[1..].concat());
      let field = opcode(&mut s, &state, 30);
      let tag = s.choose(field, &s.c(128, 3), &s.c(128, 2));
      s.same(e, &state[RESULT], &tag);
      let tagged = [s.mask(e, &tag), extra[0].clone()].concat();
      s.value(e, &tagged);
      let mut after = state.clone();
      after[RESULT + 1] = extra[0].clone();
      after[CONTROL] = s.c(128, BYTE_FINISH);
      after
    },
    ByteKind::AppendRequest => append_request(&mut s, e, &state),
    ByteKind::AppendFinish => append_finish(&mut s, e, &state, &extra),
    ByteKind::EqRequest => eq_request(&mut s, e, &state),
    ByteKind::EqFinish => eq_finish(&mut s, e, &state, &extra),
    ByteKind::Finish => {
      s.is(e, &state[CONTROL], BYTE_FINISH);
      s.value(e, &state[RESULT..RESULT + 2].concat());
      let mut action = s.action(ActionKind::Bind, &state[HEADER][80..88]);
      action[2] = state[RESULT].clone();
      action[3] = state[RESULT + 1].clone();
      action
    },
    ByteKind::Emit => {
      s.is(e, &state[CONTROL], BYTE_EMIT);
      let w = opcode(&mut s, &state, 21);
      let f = opcode(&mut s, &state, 29);
      let h = opcode(&mut s, &state, 44);
      let allowed = s.any(&[w, f, h]);
      s.need(e, allowed);
      let choices = [(w, s.c(64, 4)), (f, s.c(64, 8)), (h, s.c(64, 32))];
      let expected = pick(&mut s, 64, &choices);
      s.same(e, &length(&s, &state[RESULT + 1]), &expected);
      let word = s.and(e, w);
      let scalar = s.any(&[w, f]);
      let scalar = s.and(e, scalar);
      s.zeros(word, &state[CV][32..]);
      s.zeros(scalar, &state[CV][64..]);
      s.zeros(scalar, &state[CV + 1]);
      let address = s.add(&state[OLD_BYTES][..64], &s.c(64, DYNAMIC_BYTES));
      let mut after = state.clone();
      after[CONTROL] = s.c(128, BYTE_FINISH);
      after.extend([
        s.wide(&address, 128),
        s.c(128, 1),
        state[CV].clone(),
        state[CV + 1].clone(),
      ]);
      after
    },
    ByteKind::HashRequest => {
      let h = hash_info(&mut s, e, &state);
      vec![
        read_pointer(&mut s, &state[A], &state[POSITION][..64], &h.count),
        s.wide(&h.count, 128),
        state[CV].clone(),
        state[CV + 1].clone(),
        h.params,
      ]
    },
    ByteKind::HashFinish => hash_finish(&mut s, e, &state, &extra),
    ByteKind::HashMergeRequest => {
      let m = merge_info(&mut s, e, &state);
      s.need(e, m.bit);
      vec![m.address, m.params]
    },
    ByteKind::HashMergeFinish => merge_finish(&mut s, e, &state, &extra),
    ByteKind::HashPush | ByteKind::HashSkip => {
      let m = merge_info(&mut s, e, &state);
      let clear = s.inv(m.bit);
      s.need(e, clear);
      let mut after = state.clone();
      if kind == ByteKind::HashSkip {
        s.need(e, m.final_chunk);
        let empty = s.eqc(&state[MERGE_MASK], 0);
        let nonempty = s.inv(empty);
        s.need(e, nonempty);
        s.bound(e, &state[MERGE_CONTROL][..8], 25);
        after[MERGE_CONTROL][..8].copy_from_slice(&m.next_level);
      } else {
        let continuing = s.inv(m.final_chunk);
        s.need(e, continuing);
        s.zeros(e, &state[POSITION][..10]);
        let more = s.lt(&state[POSITION][..64], &length(&s, &state[A]));
        s.need(e, more);
        let first = s.eqc(&state[POSITION], 0);
        let advanced = s.inv(first);
        s.need(e, advanced);
        after[CONTROL] = s.c(128, HASH_BLOCK);
        for (i, iv) in pack8(&IV).into_iter().enumerate() {
          after[CV + i] = fw(&s, iv);
        }
        after[MERGE_MASK] = s.c(128, 0);
        after[MERGE_CONTROL] = s.c(128, 0);
        after.extend([
          m.address,
          s.c(128, 1),
          state[CV].clone(),
          state[CV + 1].clone(),
        ]);
      }
      after
    },
  };
  assert_eq!(out.len(), kind.outputs());
  for value in &mut out {
    *value = s.mask(e, &s.wide(value, 128));
  }
  let bad = s.any(&s.bad.clone());
  out.push(s.wide(&[bad], 128));
  for (i, value) in out.iter().enumerate() {
    for (j, &bit) in value.iter().enumerate() {
      s.b.write_xor((ni + i) * 128 + j, &[bit], one);
    }
  }
  s.b.finish()
}
