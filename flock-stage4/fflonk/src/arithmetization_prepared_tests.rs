use super::*;
use ix_terminal_circuit::{
  R1csBuilder, alloc_f128_private, constrain_f128_multiply,
  constrain_f128_multiply_prepared, prepare_f128_operand,
};

fn census(
  prepared: bool,
  cache_capacity: Option<usize>,
  shape_only: bool,
  pairs: &[(usize, usize)],
) -> PlonkGateCensusV1 {
  let projection = PlonkGateProjectionV1::new();
  let mut builder = if shape_only {
    R1csBuilder::new_shape_projection_observed(projection.observer())
  } else {
    R1csBuilder::new_projection_observed(projection.observer())
  };
  if let Some(capacity) = cache_capacity {
    builder.enable_f128_preparation_cache(capacity).unwrap();
  }
  let phase = ConstraintPhase::Pcs;
  let count = pairs.iter().flat_map(|&(a, b)| [a, b]).max().unwrap() + 1;
  let inputs = (0..count)
    .map(|index| {
      let value = if shape_only {
        0
      } else {
        0x9912_6710_acea_fe49_25d1_ef6c_049a_0827u128
          .wrapping_mul(index as u128 + 3)
      };
      alloc_f128_private(&mut builder, value.to_le_bytes(), phase).unwrap()
    })
    .collect::<Vec<_>>();
  if prepared {
    let operands = inputs
      .iter()
      .map(|input| prepare_f128_operand(&mut builder, input, phase).unwrap())
      .collect::<Vec<_>>();
    for &(a, b) in pairs {
      let output = constrain_f128_multiply_prepared(
        &mut builder,
        &operands[a],
        &operands[b],
        phase,
      )
      .unwrap();
      if !shape_only {
        assert_eq!(
          *output.value(),
          oracle(*inputs[a].value(), *inputs[b].value())
        );
      }
    }
  } else {
    for &(a, b) in pairs {
      constrain_f128_multiply(&mut builder, &inputs[a], &inputs[b], phase)
        .unwrap();
    }
  }
  projection.finish(&builder.finish_projection().unwrap()).unwrap()
}

fn oracle(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
  let mut a = u128::from_le_bytes(a);
  let mut b = u128::from_le_bytes(b);
  let mut out = 0;
  for _ in 0..128 {
    if b & 1 != 0 {
      out ^= a;
    }
    let carry = a >> 127;
    a <<= 1;
    if carry != 0 {
      a ^= 0x87;
    }
    b >>= 1;
  }
  out.to_le_bytes()
}

#[test]
fn prepared_f128_operands_preserve_single_use_cost_and_save_repeated_packs() {
  for (name, pairs, reused_preparations) in [
    ("single", vec![(0, 1)], 0),
    ("one common operand", vec![(0, 1), (0, 2), (0, 3), (0, 4)], 3),
    ("two by two grid", vec![(0, 2), (0, 3), (1, 2), (1, 3)], 4),
    ("both repeated", vec![(0, 1); 4], 6),
  ] {
    let plain = census(false, None, true, &pairs);
    let prepared = census(true, None, true, &pairs);
    let assigned = census(true, None, false, &pairs);
    let cached = census(false, Some(8), true, &pairs);
    let cached_assigned = census(false, Some(8), false, &pairs);
    assert_eq!(prepared, assigned);
    assert_eq!(cached, cached_assigned);
    assert_eq!(prepared.constraint_rows, cached.constraint_rows);
    // Capacity one can retain only the right operand of these distinct-pair
    // products. Every next left lookup evicts it: no preparation is reused.
    assert_eq!(
      census(false, Some(1), true, &pairs).constraint_rows,
      plain.constraint_rows
    );
    // Each reused preparation eliminates 304 bit-XOR rows and 27*15
    // affine-packing rows. Inputs and product/reduction checks remain.
    assert_eq!(
      plain.constraint_rows - prepared.constraint_rows,
      reused_preparations * 709
    );
    eprintln!(
      "prepared F128 {name}: baseline={} prepared={} PLONK constraint rows; saving={}; complete COMPONENT counts only",
      plain.constraint_rows,
      prepared.constraint_rows,
      plain.constraint_rows - prepared.constraint_rows
    );
  }
}
