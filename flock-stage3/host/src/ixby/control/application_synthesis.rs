//! Application-capable CEK transport. Apply is its own fuel-consuming state;
//! stack records distinguish resume frames from nonempty apply-rest vectors.
//! Action modes 6/7 start let/tail applications, 8 returns a resolved value,
//! and 9 enters a saturated callee, optionally pushing its remaining arguments.
use super::{
  ControlCapacities,
  synthesis::{bits, matches, parity, prefix, unused, write_sum},
};
use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  ixby::{
    bits::{
      add, any, constant_bits, equal, equal_constant, not, require,
      require_zero, subtract,
    },
    value::BOOL_TAG,
  },
};

#[cfg(test)]
#[path = "application_tests.rs"]
mod tests;

pub(super) fn build(c: ControlCapacities) -> BooleanR1csPlan {
  let state_bits = 128 * c.state_words();
  let action = state_bits;
  let action_words = c.application_action_words();
  let input_bits = state_bits + 128 * action_words;
  let output = input_bits;
  let reserved = output + state_bits + 128;
  let columns =
    reserved + 65536 + 4096 * (c.continuations + 2) * (c.locals + 2);
  let mut b = BooleanR1csBuilder::new(
    columns.next_power_of_two().ilog2() as usize,
    reserved,
  );
  for bit in 0..input_bits {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let one32 = constant_bits(one, zero, 1);
  let kind = bits(0, 32);
  let fuel = bits(32, 32);
  let depth = bits(64, 32);
  let flags = matches(&mut b, one, &kind, 3);
  let [eval, returning, halted, applying]: [usize; 4] =
    flags.try_into().unwrap();
  let valid_kind = b.xor(&[eval, returning, halted, applying], one);
  let active = b.xor(&[eval, returning, applying], one);
  let acting = b.xor(&[eval, applying], one);
  let modes = matches(&mut b, one, &bits(action, 32), 9);
  let mode: Vec<_> = modes
    .iter()
    .enumerate()
    .map(|(i, flag)| b.and(if i <= 7 { eval } else { applying }, *flag))
    .collect();
  let [
    bind,
    call,
    ret,
    tail,
    branch,
    let_apply,
    tail_apply,
    apply_ret,
    apply_enter,
  ]: [usize; 9] = mode[1..].try_into().unwrap();
  let starting = b.xor(&[let_apply, tail_apply], one);
  let entering = b.xor(&[call, tail, apply_enter], one);
  let same_frame = b.xor(&[bind, branch], one);
  let returning_value = b.xor(&[ret, apply_ret], one);
  let argument_used = b.xor(&[entering, starting], one);
  let target_used = b.xor(&[bind, call, branch, let_apply], one);
  let value_used = b.xor(&[bind, ret, branch, starting, apply_ret], one);
  let depth_matches = matches(&mut b, one, &depth, c.continuations);
  let valid_depth = b.xor(&depth_matches, one);
  let nonempty = not(&mut b, one, depth_matches[0]);
  let popping = b.and(returning, nonempty);
  let terminal = b.and(returning, depth_matches[0]);
  let keep_result = b.xor(&[terminal, halted], one);
  let mut violations = Vec::new();
  require(&mut b, one, &mut violations, one, valid_kind);
  require(&mut b, one, &mut violations, one, valid_depth);
  require_zero(&mut b, one, &mut violations, one, &bits(96, 32));
  let no_fuel = equal_constant(&mut b, one, &fuel, 0);
  violations.push(b.and(active, no_fuel));
  violations.push(b.and(halted, nonempty));
  let valid_action = b.xor(&mode[1..], one);
  require(&mut b, one, &mut violations, acting, valid_action);
  unused(
    &mut b,
    one,
    acting,
    &bits(action, action_words * 128),
    &mut violations,
  );
  let value = 128 * c.value_word();
  require_zero(&mut b, one, &mut violations, eval, &bits(value, 256));

  let mut frame_lengths = Vec::new();
  for index in 0..=c.continuations {
    let frame = if index == 0 { 128 } else { 128 * c.stack_word(index - 1) };
    let live =
      if index == 0 { acting } else { b.xor(&depth_matches[index..], one) };
    unused(&mut b, one, live, &bits(frame, 128), &mut violations);
    let lengths = prefix(
      &mut b,
      one,
      &bits(frame + 64, 32),
      frame + 128,
      c.locals,
      &mut violations,
    );
    frame_lengths.push(lengths);
    let rest = if index == 0 {
      require_zero(&mut b, one, &mut violations, one, &bits(frame + 96, 32));
      applying
    } else {
      require_zero(&mut b, one, &mut violations, one, &bits(frame + 97, 31));
      frame + 96
    };
    require_zero(&mut b, one, &mut violations, rest, &bits(frame, 64));
    let small = b.xor(&frame_lengths[index][..=c.arguments], one);
    require(&mut b, one, &mut violations, rest, small);
    if index != 0 {
      violations.push(b.and(rest, frame_lengths[index][0]));
    }
  }
  let arg_length = bits(action + 192, 32);
  prefix(&mut b, one, &arg_length, action + 512, c.arguments, &mut violations);
  unused(&mut b, one, argument_used, &arg_length, &mut violations);
  unused(&mut b, one, entering, &bits(action + 96, 96), &mut violations);
  unused(&mut b, one, target_used, &bits(action + 32, 32), &mut violations);
  unused(&mut b, one, branch, &bits(action + 64, 32), &mut violations);
  unused(&mut b, one, value_used, &bits(action + 256, 256), &mut violations);
  require_zero(&mut b, one, &mut violations, one, &bits(action + 224, 32));
  let same_arity = equal(&mut b, one, &bits(action + 160, 32), &arg_length);
  require(&mut b, one, &mut violations, entering, same_arity);
  let rest_base = action + 128 * c.action_words();
  require_zero(&mut b, one, &mut violations, one, &bits(rest_base + 32, 96));
  let rest_length = bits(rest_base, 32);
  let rest_lengths = prefix(
    &mut b,
    one,
    &rest_length,
    rest_base + 128,
    c.arguments,
    &mut violations,
  );
  unused(&mut b, one, apply_enter, &rest_length, &mut violations);
  let has_rest = not(&mut b, one, rest_lengths[0]);
  let push_rest = b.and(apply_enter, has_rest);
  let push_resume = b.xor(&[call, let_apply], one);
  let pushing = b.xor(&[push_resume, push_rest], one);
  violations.push(b.and(pushing, depth_matches[c.continuations]));
  violations.push(b.and(bind, frame_lengths[0][c.locals]));
  let boolean = equal_constant(&mut b, one, &bits(action + 256, 64), BOOL_TAG);
  require(&mut b, one, &mut violations, branch, boolean);
  require_zero(&mut b, one, &mut violations, branch, &bits(action + 320, 64));
  require_zero(&mut b, one, &mut violations, branch, &bits(action + 385, 127));
  let branch_yes = b.and(branch, action + 384);
  let false_condition = not(&mut b, one, action + 384);
  let branch_no = b.and(branch, false_condition);

  let mut top = Vec::with_capacity(128 * c.frame_words());
  for bit in 0..128 * c.frame_words() {
    let products: Vec<_> = (0..c.continuations)
      .map(|index| {
        b.and(depth_matches[index + 1], 128 * c.stack_word(index) + bit)
      })
      .collect();
    top.push(parity(&mut b, one, zero, &products));
  }
  let top_resume = not(&mut b, one, top[96]);
  let resume = b.and(popping, top_resume);
  let resume_apply = b.and(popping, top[96]);
  let next_apply = b.xor(&[starting, resume_apply], one);
  let top_lengths = matches(&mut b, one, &top[64..96], c.locals);
  violations.push(b.and(resume, top_lengths[c.locals]));
  let (fuel_less, _) = subtract(&mut b, one, zero, &fuel, &one32);
  let (depth_more, _) = add(&mut b, one, zero, &depth, &one32);
  let (depth_less, _) = subtract(&mut b, one, zero, &depth, &one32);
  let current_length = bits(192, 32);
  let (current_more, _) = add(&mut b, one, zero, &current_length, &one32);
  let (top_more, _) = add(&mut b, one, zero, &top[64..96], &one32);
  b.write_xor(output, &[returning_value, next_apply], one);
  b.write_xor(output + 1, &[keep_result, next_apply], one);
  for bit in 0..32 {
    let fuel_delta =
      b.product_of_parities(&[active], &[fuel[bit], fuel_less[bit]]);
    b.write_xor(output + 32 + bit, &[fuel[bit], fuel_delta], one);
    let pushed =
      b.product_of_parities(&[pushing], &[depth[bit], depth_more[bit]]);
    let popped =
      b.product_of_parities(&[popping], &[depth[bit], depth_less[bit]]);
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
        (starting, arg_length[bit]),
        (resume, top_more[bit]),
        (resume_apply, top[64 + bit]),
      ],
    );
  }
  let top_kept = b.xor(&[resume, resume_apply], one);
  let args_copied = b.xor(&[entering, starting], one);
  for local in 0..c.locals {
    let appended = b.and(bind, frame_lengths[0][local]);
    let restored = b.and(resume, top_lengths[local]);
    for bit in 0..256 {
      let cell = 256 + 256 * local + bit;
      let mut terms = vec![
        (same_frame, cell),
        (appended, action + 256 + bit),
        (top_kept, top[128 + 256 * local + bit]),
        (restored, value + bit),
      ];
      if local < c.arguments {
        terms.push((args_copied, action + 512 + 256 * local + bit));
      }
      write_sum(&mut b, one, output + cell, &terms);
    }
  }
  let result_from_action = b.xor(&[returning_value, starting], one);
  let result_from_state = b.xor(&[keep_result, resume_apply], one);
  for bit in 0..256 {
    write_sum(
      &mut b,
      one,
      output + value + bit,
      &[
        (result_from_action, action + 256 + bit),
        (result_from_state, value + bit),
      ],
    );
  }
  for index in 0..c.continuations {
    let saved_resume = b.and(push_resume, depth_matches[index]);
    let saved_rest = b.and(push_rest, depth_matches[index]);
    let popped = b.and(popping, depth_matches[index + 1]);
    let kept = b.xor(&[one, saved_resume, saved_rest, popped], one);
    let frame = 128 * c.stack_word(index);
    for bit in 0..128 * c.frame_words() {
      let resume_source =
        if (32..64).contains(&bit) { action + bit } else { 128 + bit };
      let rest_source = match bit {
        64..96 => rest_base + bit - 64,
        96 => one,
        128.. if bit < 128 + 256 * c.arguments => rest_base + bit,
        _ => zero,
      };
      write_sum(
        &mut b,
        one,
        output + frame + bit,
        &[
          (kept, frame + bit),
          (saved_resume, resume_source),
          (saved_rest, rest_source),
        ],
      );
    }
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(output + state_bits, &[violation], one);
  b.finish()
}
