use super::model::{CONTINUATIONS, HEAP, LOCALS, SCRATCH};
use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  ixby::bits::{
    add, any, equal, equal_constant, not, require, require_zero, subtract,
  },
};

type Bits = Vec<usize>;
struct S {
  b: BooleanR1csBuilder,
  one: usize,
  zero: usize,
  bad: Vec<usize>,
}
impl S {
  fn new() -> Self {
    let mut b = BooleanR1csBuilder::new(17, 32 * 128);
    for bit in 0..13 * 128 {
      b.free_boolean_at(bit);
    }
    let one = b.alloc_constant_one();
    let zero = b.xor(&[one, one], one);
    Self { b, one, zero, bad: Vec::new() }
  }
  fn c(&self, n: usize, value: u64) -> Bits {
    (0..n)
      .map(|i| {
        if i < 64 && value & (1u64 << i) != 0 { self.one } else { self.zero }
      })
      .collect()
  }
  fn and(&mut self, a: usize, b: usize) -> usize {
    self.b.and(a, b)
  }
  fn inv(&mut self, a: usize) -> usize {
    not(&mut self.b, self.one, a)
  }
  fn sum(&mut self, a: &[usize]) -> usize {
    self.b.xor(a, self.one)
  }
  fn eqc(&mut self, a: &[usize], value: u64) -> usize {
    equal_constant(&mut self.b, self.one, a, value)
  }
  fn eq(&mut self, a: &[usize], b: &[usize]) -> usize {
    equal(&mut self.b, self.one, a, b)
  }
  fn need(&mut self, enabled: usize, good: usize) {
    require(&mut self.b, self.one, &mut self.bad, enabled, good);
  }
  fn zeros(&mut self, enabled: usize, bits: &[usize]) {
    require_zero(&mut self.b, self.one, &mut self.bad, enabled, bits);
  }
  fn unused(&mut self, used: usize, bits: &[usize]) {
    let disabled = self.inv(used);
    self.zeros(disabled, bits);
  }
  fn add(&mut self, a: &[usize], b: &[usize]) -> (Bits, usize) {
    add(&mut self.b, self.one, self.zero, a, b)
  }
  fn sub(&mut self, a: &[usize], b: &[usize]) -> (Bits, usize) {
    subtract(&mut self.b, self.one, self.zero, a, b)
  }
  fn bound(&mut self, enabled: usize, a: &[usize], inclusive: u64) {
    let mut wide = a.to_vec();
    wide.resize(64, self.zero);
    let limit = self.c(64, inclusive + 1);
    let fits = self.sub(&wide, &limit).1;
    self.need(enabled, fits);
  }
  fn at_most(&mut self, enabled: usize, a: &[usize], limit: &[usize]) {
    let mut wide = a.to_vec();
    wide.resize(limit.len(), self.zero);
    let too_large = self.sub(limit, &wide).1;
    let bad = self.and(enabled, too_large);
    self.bad.push(bad);
  }
  fn choose(&mut self, n: usize, choices: &[(usize, &[usize])]) -> Bits {
    (0..n)
      .map(|i| {
        let products = choices
          .iter()
          .map(|(flag, bits)| {
            assert_eq!(bits.len(), n);
            self.b.and(*flag, bits[i])
          })
          .collect::<Vec<_>>();
        self.b.xor(&products, self.one)
      })
      .collect()
  }
  fn mask(&mut self, enabled: usize, bits: &[usize]) -> Bits {
    bits.iter().map(|&bit| self.and(enabled, bit)).collect()
  }
  fn vector(&mut self, enabled: usize, descriptor: &[usize], persistent: bool) {
    assert_eq!(descriptor.len(), 128);
    self.unused(enabled, descriptor);
    self.zeros(enabled, &descriptor[40..64]);
    self.zeros(enabled, &descriptor[72..]);
    let count = &descriptor[64..72];
    self.bound(enabled, count, 64);
    let empty = self.eqc(count, 0);
    let nonempty = self.inv(empty);
    let used = self.and(enabled, nonempty);
    let absent = self.and(enabled, empty);
    self.zeros(absent, &descriptor[..40]);
    let heap = self.eqc(&descriptor[36..40], HEAP >> 36);
    let permitted = if persistent {
      heap
    } else {
      let scratch = self.eqc(&descriptor[..40], SCRATCH);
      self.sum(&[heap, scratch])
    };
    self.need(used, permitted);
    let mut length = count.to_vec();
    length.resize(37, self.zero);
    let mut base = descriptor[..36].to_vec();
    base.push(self.zero);
    let end = self.add(&base, &length).0;
    // The exclusive end may equal 2^36, but cannot cross it.
    let low = any(&mut self.b, self.one, &end[..36]);
    let overflow = self.and(end[36], low);
    let bad = self.and(used, overflow);
    self.bad.push(bad);
  }
  fn frame(
    &self,
    phase: &[usize],
    function: &[usize],
    block: &[usize],
    locals: &[usize],
    depth: &[usize],
  ) -> Bits {
    let mut bits = self.c(128, 0);
    bits[..8].copy_from_slice(phase);
    bits[8..24].copy_from_slice(function);
    bits[24..32].copy_from_slice(block);
    bits[32..40].copy_from_slice(locals);
    bits[48..64].copy_from_slice(depth);
    bits
  }
  fn local_address(&self, depth: &[usize], index: &[usize]) -> Bits {
    let mut out = self.c(128, LOCALS);
    out[..7].copy_from_slice(&index[..7]);
    out[7..23].copy_from_slice(depth);
    out
  }
  fn continuation_address(&self, depth: &[usize]) -> Bits {
    let mut out = self.c(128, CONTINUATIONS);
    out[..16].copy_from_slice(depth);
    out
  }
}
fn bits(start: usize, length: usize) -> Bits {
  (start..start + length).collect()
}

pub(super) fn build() -> BooleanR1csPlan {
  let mut s = S::new();
  let one = s.one;
  let phase = bits(0, 8);
  let function = bits(8, 16);
  let block = bits(24, 8);
  let locals = bits(32, 8);
  let depth = bits(48, 16);
  let index = bits(64, 8);
  let count = bits(72, 8);
  let base = bits(80, 8);
  let copy_pointer = bits(128, 128);
  let value = bits(256, 256);
  let arguments = bits(512, 128);
  let phases = (0..5).map(|i| s.eqc(&phase, i)).collect::<Vec<_>>();
  let [eval, ret, halt, apply, copying]: [usize; 5] =
    phases.clone().try_into().unwrap();
  let valid = s.sum(&phases);
  s.need(one, valid);
  s.zeros(one, &bits(40, 8));
  s.zeros(one, &bits(88, 40));
  s.bound(one, &function, 1023);
  s.bound(one, &locals, 128);
  s.bound(one, &depth, 1024);
  s.at_most(one, &locals, &bits(1536, 64));
  s.at_most(one, &depth, &bits(1600, 64));
  let framed = s.sum(&[eval, copying]);
  s.unused(framed, &bits(8, 32));
  s.unused(copying, &bits(64, 24));
  s.unused(copying, &copy_pointer);
  let valued = s.sum(&[ret, halt, apply]);
  s.unused(valued, &value);
  s.vector(apply, &arguments, true);
  s.zeros(halt, &depth);
  s.zeros(copying, &copy_pointer[40..]);
  s.bound(copying, &count, 64);
  let valid_index = s.sub(&index, &count).1;
  s.need(copying, valid_index);
  let (total_locals, total_carry) = s.add(&base, &count);
  let bad = s.and(copying, total_carry);
  s.bad.push(bad);
  let total_matches = s.eq(&total_locals, &locals);
  s.need(copying, total_matches);
  let mut copy_vector = copy_pointer.clone();
  copy_vector[64..72].copy_from_slice(&count);
  s.vector(copying, &copy_vector, false);

  let mode = bits(640, 8);
  let target = bits(648, 8);
  let callee = bits(656, 16);
  let entry = bits(672, 8);
  let arity = bits(680, 8);
  let args = bits(768, 128);
  let args_count = bits(832, 8);
  let result = bits(896, 256);
  let rest = bits(1152, 128);
  let rest_count = bits(1216, 8);
  let mut selected = vec![s.zero];
  for i in 1..=10 {
    let equal = s.eqc(&mode, i);
    selected.push(s.and(if i <= 8 { eval } else { apply }, equal));
  }
  let [
    bind,
    call,
    tail,
    returning,
    jump,
    append,
    start_apply,
    tail_apply,
    apply_return,
    apply_enter,
  ]: [usize; 10] = selected[1..].try_into().unwrap();
  let command_used = s.sum(&[eval, apply]);
  let command_valid = s.sum(&selected[1..]);
  s.need(command_used, command_valid);
  s.unused(command_used, &bits(640, 640));
  s.zeros(one, &bits(688, 80));
  let targeted = s.sum(&[bind, call, jump, append, start_apply]);
  s.unused(targeted, &target);
  let entering = s.sum(&[call, tail, apply_enter]);
  s.unused(entering, &bits(656, 32));
  s.bound(entering, &callee, 1023);
  s.bound(entering, &arity, 64);
  let same_arity = s.eq(&arity, &args_count);
  s.need(entering, same_arity);
  let uses_args = s.sum(&[entering, append, start_apply, tail_apply]);
  s.vector(uses_args, &args, false);
  // Apply arguments survive calls and must refer to the immutable heap.
  let persistent = s.sum(&[start_apply, tail_apply]);
  let persistent_args = s.mask(persistent, &args);
  s.vector(persistent, &persistent_args, true);
  let uses_result =
    s.sum(&[bind, returning, start_apply, tail_apply, apply_return]);
  s.unused(uses_result, &result);
  s.vector(apply_enter, &rest, true);
  let rest_empty = s.eqc(&rest_count, 0);
  let rest_nonempty = s.inv(rest_empty);
  let save_apply = s.and(apply_enter, rest_nonempty);
  let save_resume = s.sum(&[call, start_apply]);
  let push = s.sum(&[save_resume, save_apply]);
  let (deeper, depth_carry) = s.add(&depth, &s.c(16, 1));
  let bad = s.and(push, depth_carry);
  s.bad.push(bad);
  s.bound(push, &deeper, 1024);
  s.at_most(push, &deeper, &bits(1600, 64));

  let empty_stack = s.eqc(&depth, 0);
  let nonempty_stack = s.inv(empty_stack);
  let pop = s.and(ret, nonempty_stack);
  let terminal = s.and(ret, empty_stack);
  let (shallower, _) = s.sub(&depth, &s.c(16, 1));
  let reply = bits(1280, 256);
  let read_used = s.sum(&[pop, copying]);
  s.unused(read_used, &reply);
  let saved_kind = bits(1280, 8);
  let saved_function = bits(1288, 16);
  let saved_block = bits(1304, 8);
  let saved_locals = bits(1312, 8);
  let resume_kind = s.eqc(&saved_kind, 1);
  let apply_kind = s.eqc(&saved_kind, 2);
  let resume = s.and(pop, resume_kind);
  let pop_apply = s.and(pop, apply_kind);
  let saved_valid = s.sum(&[resume_kind, apply_kind]);
  s.need(pop, saved_valid);
  s.zeros(pop, &bits(1320, 88));
  s.zeros(pop_apply, &bits(1288, 32));
  s.bound(resume, &saved_function, 1023);
  let saved_args = bits(1408, 128);
  s.zeros(resume, &saved_args);
  let pop_args = s.mask(pop_apply, &saved_args);
  s.vector(pop_apply, &pop_args, true);
  let saved_empty = s.eqc(&saved_args[64..72], 0);
  let saved_nonempty = s.inv(saved_empty);
  s.need(pop_apply, saved_nonempty);

  let (bound_locals, bound_carry) = s.add(&locals, &s.c(8, 1));
  let bad = s.and(bind, bound_carry);
  s.bad.push(bad);
  s.bound(bind, &bound_locals, 128);
  s.at_most(bind, &bound_locals, &bits(1536, 64));
  let (resumed_locals, resumed_carry) = s.add(&saved_locals, &s.c(8, 1));
  let bad = s.and(resume, resumed_carry);
  s.bad.push(bad);
  s.bound(resume, &resumed_locals, 128);
  s.at_most(resume, &resumed_locals, &bits(1536, 64));
  let (appended_locals, appended_carry) = s.add(&locals, &args_count);
  let bad = s.and(append, appended_carry);
  s.bad.push(bad);
  s.bound(append, &appended_locals, 128);
  s.at_most(append, &appended_locals, &bits(1536, 64));
  s.at_most(entering, &args_count, &bits(1536, 64));

  let args_empty = s.eqc(&args_count, 0);
  let args_nonempty = s.inv(args_empty);
  let transfer = s.sum(&[entering, append]);
  let start_copy = s.and(transfer, args_nonempty);
  let (next_index, _) = s.add(&index, &s.c(8, 1));
  let copy_done = s.eq(&next_index, &count);
  let copy_more = s.inv(copy_done);
  let keep_copying = s.and(copying, copy_more);

  let zero8 = s.c(8, 0);
  let zero16 = s.c(16, 0);
  let apply_enter_without_push = s.and(apply_enter, rest_empty);
  let entry_depth = s.choose(
    16,
    &[(push, &deeper), (tail, &depth), (apply_enter_without_push, &depth)],
  );
  let transfer_phase = s.choose(8, &[(args_nonempty, &s.c(8, 4))]);
  let mut entered =
    s.frame(&transfer_phase, &callee, &entry, &args_count, &entry_depth);
  let mut appended =
    s.frame(&transfer_phase, &function, &target, &appended_locals, &depth);
  let bind_header = s.frame(&zero8, &function, &target, &bound_locals, &depth);
  let jump_header = s.frame(&zero8, &function, &target, &locals, &depth);
  let return_header = s.frame(&s.c(8, 1), &zero16, &zero8, &zero8, &depth);
  let start_apply_header =
    s.frame(&s.c(8, 3), &zero16, &zero8, &zero8, &deeper);
  let tail_apply_header = s.frame(&s.c(8, 3), &zero16, &zero8, &zero8, &depth);
  let resume_header =
    s.frame(&zero8, &saved_function, &saved_block, &resumed_locals, &shallower);
  let pop_apply_header =
    s.frame(&s.c(8, 3), &zero16, &zero8, &zero8, &shallower);
  let final_header = s.c(128, 2);
  let after_copy_phase = s.choose(8, &[(copy_more, &s.c(8, 4))]);
  let mut after_copy =
    s.frame(&after_copy_phase, &function, &block, &locals, &depth);
  let initial_count = s.mask(args_nonempty, &args_count);
  entered[72..80].copy_from_slice(&initial_count);
  appended[72..80].copy_from_slice(&initial_count);
  appended[80..88].copy_from_slice(&s.mask(args_nonempty, &locals));
  after_copy[64..72].copy_from_slice(&s.mask(copy_more, &next_index));
  after_copy[72..80].copy_from_slice(&s.mask(copy_more, &count));
  after_copy[80..88].copy_from_slice(&s.mask(copy_more, &base));
  let return_commands = s.sum(&[returning, apply_return]);
  let final_flags = s.sum(&[terminal, halt]);
  let next_header = s.choose(
    128,
    &[
      (bind, &bind_header),
      (entering, &entered),
      (return_commands, &return_header),
      (jump, &jump_header),
      (append, &appended),
      (start_apply, &start_apply_header),
      (tail_apply, &tail_apply_header),
      (resume, &resume_header),
      (pop_apply, &pop_apply_header),
      (final_flags, &final_header),
      (copying, &after_copy),
    ],
  );
  let next_pointer =
    s.choose(128, &[(start_copy, &args), (keep_copying, &copy_pointer)]);
  // The source vector's count is kept in the frame header, not pointer.hi.
  let mut next_pointer = next_pointer;
  next_pointer[40..].fill(s.zero);
  let result_commands = s.sum(&[return_commands, start_apply, tail_apply]);
  let value_retained = s.sum(&[pop_apply, final_flags]);
  let next_value =
    s.choose(256, &[(result_commands, &result), (value_retained, &value)]);
  let next_args =
    s.choose(128, &[(persistent, &args), (pop_apply, &saved_args)]);

  let mut read_pointer = copy_pointer[..40].to_vec();
  let mut wide_index = index.clone();
  wide_index.resize(40, s.zero);
  read_pointer = s.add(&read_pointer, &wide_index).0;
  read_pointer.resize(128, s.zero);
  let read_address = s.choose(
    128,
    &[(copying, &read_pointer), (pop, &s.continuation_address(&shallower))],
  );
  let saved_header = s.frame(&s.c(8, 1), &function, &target, &locals, &zero16);
  let next_cont_header =
    s.choose(128, &[(save_resume, &saved_header), (save_apply, &s.c(128, 2))]);
  let next_cont_args = s.mask(save_apply, &rest);
  let write_cont_address = s.mask(push, &s.continuation_address(&depth));
  let (copy_slot, _) = s.add(&base, &index);
  let write_local_address = s.choose(
    128,
    &[
      (bind, &s.local_address(&depth, &locals)),
      (resume, &s.local_address(&shallower, &saved_locals)),
      (copying, &s.local_address(&depth, &copy_slot)),
    ],
  );
  let write_local_value =
    s.choose(256, &[(bind, &result), (resume, &value), (copying, &reply)]);
  let local_write = s.sum(&[bind, resume, copying]);
  let mut push_word = s.c(128, 0);
  push_word[0] = push;
  let mut local_write_word = s.c(128, 0);
  local_write_word[0] = local_write;
  let inactive_fuel = s.sum(&[halt, copying]);
  let mut fuel_control = s.c(128, 0);
  fuel_control[0] = s.sum(&[ret, apply]);
  fuel_control[1] = s.sum(&[apply, inactive_fuel]);
  let mut out = next_header;
  out.extend(next_pointer);
  out.extend(next_value);
  out.extend(next_args);
  out.extend(read_address);
  out.extend(s.c(128, 0));
  out.extend(reply);
  out.extend(write_cont_address);
  out.extend(push_word);
  out.extend(next_cont_header);
  out.extend(next_cont_args);
  out.extend(write_local_address);
  out.extend(local_write_word);
  out.extend(write_local_value);
  out.extend(fuel_control);
  let violation = any(&mut s.b, s.one, &s.bad);
  let mut residual = s.c(128, 0);
  residual[0] = violation;
  out.extend(residual);
  assert_eq!(out.len(), 19 * 128);
  for (i, bit) in out.into_iter().enumerate() {
    s.b.write_xor(13 * 128 + i, &[bit], s.one);
  }
  s.b.finish()
}
