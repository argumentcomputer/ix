use super::ControlCapacities;
use crate::boolean::{BooleanR1csBuilder, BooleanR1csPlan};
use crate::ixby::{
  bits::{add, any, constant_bits, equal_constant, not, subtract},
  value::BOOL_TAG,
};

fn bits(start: usize, count: usize) -> Vec<usize> {
  (start..start + count).collect()
}

fn parity(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  terms: &[usize],
) -> usize {
  if terms.is_empty() { zero } else { b.xor(terms, one) }
}

fn matches(
  b: &mut BooleanR1csBuilder,
  one: usize,
  word: &[usize],
  maximum: usize,
) -> Vec<usize> {
  (0..=maximum)
    .map(|value| equal_constant(b, one, word, value as u64))
    .collect()
}

fn unused(
  b: &mut BooleanR1csBuilder,
  one: usize,
  used: usize,
  columns: &[usize],
  violations: &mut Vec<usize>,
) {
  let nonzero = any(b, one, columns);
  let disabled = not(b, one, used);
  violations.push(b.and(disabled, nonzero));
}

fn prefix(
  b: &mut BooleanR1csBuilder,
  one: usize,
  length: &[usize],
  cells: usize,
  count: usize,
  violations: &mut Vec<usize>,
) -> Vec<usize> {
  let equal = matches(b, one, length, count);
  let valid = b.xor(&equal, one);
  violations.push(not(b, one, valid));
  for index in 0..count {
    let live = b.xor(&equal[index + 1..], one);
    unused(b, one, live, &bits(cells + index * 256, 256), violations);
  }
  equal
}

fn write_sum(
  b: &mut BooleanR1csBuilder,
  one: usize,
  output: usize,
  terms: &[(usize, usize)],
) {
  let products: Vec<_> =
    terms.iter().map(|(select, source)| b.and(*select, *source)).collect();
  b.write_xor(output, &products, one);
}

pub(super) fn build(c: ControlCapacities) -> BooleanR1csPlan {
  let state_bits = c.state_words() * 128;
  let action = state_bits;
  let input_bits = (c.state_words() + c.action_words()) * 128;
  let output = input_bits;
  let violation_word = output + state_bits;
  let reserved = violation_word + 128;
  // Conservative capacity-only bound: metadata comparisons, live-prefix
  // padding, one bounded stack-top selection, stack updates and next frame.
  // It is not a guest- or trace-dependent choice of table width.
  let columns = reserved
    + (c.continuations + 1) * (32 * (c.locals + 1) + 270 * c.locals + 132)
    + (c.continuations + 1) * 128 * c.frame_words()
    + 256 * c.continuations * c.frame_words()
    + 128 * (12 * c.locals + 10)
    + 8192;
  let mut b = BooleanR1csBuilder::new(
    columns.next_power_of_two().ilog2() as usize,
    reserved,
  );
  for bit in 0..input_bits {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let constant_one = constant_bits(one, zero, 1);
  let kind = bits(0, 32);
  let fuel = bits(32, 32);
  let depth = bits(64, 32);
  let mode = bits(action, 32);
  let eval = equal_constant(&mut b, one, &kind, 0);
  let returning = equal_constant(&mut b, one, &kind, 1);
  let halted = equal_constant(&mut b, one, &kind, 2);
  let kind_valid = b.xor(&[eval, returning, halted], one);
  let active = b.xor(&[eval, returning], one);
  let action_modes: Vec<_> = (1..=5)
    .map(|mode_value| equal_constant(&mut b, one, &mode, mode_value))
    .collect();
  let flags: Vec<_> =
    action_modes.iter().map(|matched| b.and(eval, *matched)).collect();
  let [bind, call, ret, tail, branch]: [usize; 5] = flags.try_into().unwrap();
  let entering = b.xor(&[call, tail], one);
  let same_frame = b.xor(&[bind, branch], one);
  let depth_matches = matches(&mut b, one, &depth, c.continuations);
  let depth_valid = b.xor(&depth_matches, one);
  let nonempty = not(&mut b, one, depth_matches[0]);
  let resume = b.and(returning, nonempty);
  let terminal = b.and(returning, depth_matches[0]);
  let keep_result = b.xor(&[terminal, halted], one);
  let mut violations: Vec<_> =
    (96..128).chain(action + 224..action + 256).collect();
  violations.push(not(&mut b, one, kind_valid));
  violations.push(not(&mut b, one, depth_valid));
  let fuel_empty = equal_constant(&mut b, one, &fuel, 0);
  violations.push(b.and(active, fuel_empty));
  violations.push(b.and(halted, nonempty));
  let action_valid = b.xor(&action_modes, one);
  let action_invalid = not(&mut b, one, action_valid);
  violations.push(b.and(eval, action_invalid));
  unused(
    &mut b,
    one,
    eval,
    &bits(action, c.action_words() * 128),
    &mut violations,
  );
  let return_value = c.value_word() * 128;
  let return_nonzero = any(&mut b, one, &bits(return_value, 256));
  violations.push(b.and(eval, return_nonzero));

  let mut frame_lengths = Vec::new();
  for index in 0..=c.continuations {
    let frame = if index == 0 { 128 } else { c.stack_word(index - 1) * 128 };
    violations.extend(frame + 96..frame + 128);
    let lengths = prefix(
      &mut b,
      one,
      &bits(frame + 64, 32),
      frame + 128,
      c.locals,
      &mut violations,
    );
    frame_lengths.push(lengths);
    let live =
      if index == 0 { eval } else { b.xor(&depth_matches[index..], one) };
    // An inactive zero header has length zero, so prefix checks above also
    // force its entire value bank to zero; no inactive body can escape.
    unused(&mut b, one, live, &bits(frame, 128), &mut violations);
  }

  let arg_length = bits(action + 192, 32);
  prefix(&mut b, one, &arg_length, action + 512, c.arguments, &mut violations);
  let target_used = b.xor(&[bind, call, branch], one);
  unused(&mut b, one, target_used, &bits(action + 32, 32), &mut violations);
  unused(&mut b, one, branch, &bits(action + 64, 32), &mut violations);
  let callee_fields: Vec<_> =
    (action + 96..action + 128).chain(action + 128..action + 224).collect();
  unused(&mut b, one, entering, &callee_fields, &mut violations);
  let value_used = b.xor(&[bind, ret, branch], one);
  unused(&mut b, one, value_used, &bits(action + 256, 256), &mut violations);
  let mut arity_equal = one;
  for (arity, arg) in bits(action + 160, 32).iter().zip(&arg_length) {
    arity_equal = b.product_of_parities(&[arity_equal], &[*arity, *arg, one]);
  }
  let wrong_arity = not(&mut b, one, arity_equal);
  violations.push(b.and(entering, wrong_arity));
  let tag_equal =
    equal_constant(&mut b, one, &bits(action + 256, 64), BOOL_TAG);
  let mut bad_bool = vec![not(&mut b, one, tag_equal)];
  bad_bool.extend(action + 320..action + 384);
  bad_bool.extend(action + 385..action + 512);
  let bad_bool = any(&mut b, one, &bad_bool);
  violations.push(b.and(branch, bad_bool));
  let branch_yes = b.and(branch, action + 384);
  let condition_false = not(&mut b, one, action + 384);
  let branch_no = b.and(branch, condition_false);
  let stack_room = parity(&mut b, one, zero, &depth_matches[..c.continuations]);
  let no_stack_room = not(&mut b, one, stack_room);
  violations.push(b.and(call, no_stack_room));
  let current_room = b.xor(&frame_lengths[0][..c.locals], one);
  let no_current_room = not(&mut b, one, current_room);
  violations.push(b.and(bind, no_current_room));

  // One-hot selection is derived from the full constrained depth, not supplied
  // by the witness. The empty/invalid-depth top record is all zero.
  let mut top = Vec::with_capacity(c.frame_words() * 128);
  for bit in 0..c.frame_words() * 128 {
    let products: Vec<_> = (0..c.continuations)
      .map(|index| {
        b.and(depth_matches[index + 1], c.stack_word(index) * 128 + bit)
      })
      .collect();
    top.push(parity(&mut b, one, zero, &products));
  }
  let top_lengths = matches(&mut b, one, &top[64..96], c.locals);
  let top_room = b.xor(&top_lengths[..c.locals], one);
  let no_top_room = not(&mut b, one, top_room);
  violations.push(b.and(resume, no_top_room));

  let (fuel_less, _) = subtract(&mut b, one, zero, &fuel, &constant_one);
  let (depth_more, _) = add(&mut b, one, zero, &depth, &constant_one);
  let (depth_less, _) = subtract(&mut b, one, zero, &depth, &constant_one);
  let current_length = bits(192, 32);
  let (current_more, _) =
    add(&mut b, one, zero, &current_length, &constant_one);
  let (top_more, _) = add(&mut b, one, zero, &top[64..96], &constant_one);
  b.write_xor(output, &[ret], one);
  b.write_xor(output + 1, &[keep_result], one);
  for bit in 0..32 {
    let fuel_delta =
      b.product_of_parities(&[active], &[fuel[bit], fuel_less[bit]]);
    b.write_xor(output + 32 + bit, &[fuel[bit], fuel_delta], one);
    let pushed = b.product_of_parities(&[call], &[depth[bit], depth_more[bit]]);
    let popped =
      b.product_of_parities(&[resume], &[depth[bit], depth_less[bit]]);
    b.write_xor(output + 64 + bit, &[depth[bit], pushed, popped], one);
    write_sum(
      &mut b,
      one,
      output + 128 + bit,
      &[
        (same_frame, 128 + bit),
        (entering, action + 96 + bit),
        (resume, top[bit]),
      ],
    );
    write_sum(
      &mut b,
      one,
      output + 160 + bit,
      &[
        (bind, action + 32 + bit),
        (branch_yes, action + 32 + bit),
        (branch_no, action + 64 + bit),
        (entering, action + 128 + bit),
        (resume, top[32 + bit]),
      ],
    );
    write_sum(
      &mut b,
      one,
      output + 192 + bit,
      &[
        (bind, current_more[bit]),
        (branch, current_length[bit]),
        (entering, arg_length[bit]),
        (resume, top_more[bit]),
      ],
    );
  }
  for local in 0..c.locals {
    let appended = b.and(bind, frame_lengths[0][local]);
    let restored = b.and(resume, top_lengths[local]);
    for bit in 0..256 {
      let cell = 256 + local * 256 + bit;
      let mut terms = vec![
        (same_frame, cell),
        (appended, action + 256 + bit),
        (resume, top[128 + local * 256 + bit]),
        (restored, return_value + bit),
      ];
      if local < c.arguments {
        terms.push((entering, action + 512 + local * 256 + bit));
      }
      write_sum(&mut b, one, output + cell, &terms);
    }
  }
  for bit in 0..256 {
    write_sum(
      &mut b,
      one,
      output + return_value + bit,
      &[(ret, action + 256 + bit), (keep_result, return_value + bit)],
    );
  }
  for index in 0..c.continuations {
    let pushed = b.and(call, depth_matches[index]);
    let popped = b.and(resume, depth_matches[index + 1]);
    let kept = b.xor(&[one, pushed, popped], one);
    let frame = c.stack_word(index) * 128;
    for bit in 0..c.frame_words() * 128 {
      let saved =
        if (32..64).contains(&bit) { action + bit } else { 128 + bit };
      write_sum(
        &mut b,
        one,
        output + frame + bit,
        &[(kept, frame + bit), (pushed, saved)],
      );
    }
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(violation_word, &[violation], one);
  b.finish()
}
