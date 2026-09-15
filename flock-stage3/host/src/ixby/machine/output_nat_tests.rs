use super::*;
use crate::ixby::{
  decode::test_support::{Value as V, meta, output},
  nat_value::NatCapacity,
  value::NAT_TAG,
};

fn setup(bound: usize, bytes: usize) -> OutputEncodeGate {
  OutputEncodeGate::new(
    3,
    ControlCapacities { locals: 2, continuations: 1, arguments: 1 },
    bytes,
  )
  .unwrap()
  .with_byte_values(ByteCapacity::new(17).unwrap(), 4)
  .unwrap()
  .with_nat_values(NatCapacity::new(bound).unwrap())
  .unwrap()
}
fn input(g: &OutputEncodeGate, data: &[u8]) -> Vec<F128> {
  let mut input = vec![F128::ZERO; g.input_count()];
  input[0] = meta(2, 0, 0, 0);
  let value = 1 + g.control.frame_words();
  input[value] = F128::new(NAT_TAG, 0);
  input[value + 1] = F128::new(3, 0);
  let buffer = g.control.state_words();
  input[buffer] = F128::new(data.len() as u64, 0);
  let mut padded = [0u8; 32];
  padded[..data.len()].copy_from_slice(data);
  input[buffer + 1] = crate::hash::pack_bytes(&padded[..16]);
  input[buffer + 2] = crate::hash::pack_bytes(&padded[16..]);
  input
}
fn check(
  g: &OutputEncodeGate,
  r1cs: &BlockR1cs,
  input: &[F128],
  good: bool,
) -> Vec<F128> {
  let mut bits = vec![false; r1cs.n()];
  g.plan().fill_row(&mut bits[..g.plan().k()], |bits| fill_words(input, bits));
  let residual = 128 * (g.input_count() + g.output_count() - 1);
  assert_eq!(bits[residual], !good);
  assert!(r1cs.satisfies(&bits));
  bits[residual] ^= true;
  assert!(!r1cs.satisfies(&bits));
  evaluate_words(g.plan(), input, g.output_count())
}
#[test]
fn nat_output_derives_revision_one_minimal_magnitudes_and_rejects_false_encodings()
 {
  let g = setup(129, 64);
  let r1cs = g.r1cs();
  for data in [vec![], vec![1], vec![255, 1], [vec![0; 16], vec![1]].concat()] {
    let result = check(&g, &r1cs, &input(&g, &data), true);
    let mut expected = output(&V::Nat(data));
    expected[4] = 1;
    assert_eq!(result[0], F128::new(expected.len() as u64, 0));
    let actual: Vec<_> = result[1..1 + g.data_words()]
      .iter()
      .flat_map(|word| {
        word.lo.to_le_bytes().into_iter().chain(word.hi.to_le_bytes())
      })
      .collect();
    assert_eq!(&actual[..expected.len()], expected);
    assert!(actual[expected.len()..].iter().all(|byte| *byte == 0));
  }
  for data in [vec![0], vec![1, 0], [vec![0; 16], vec![2]].concat()] {
    check(&g, &r1cs, &input(&g, &data), false);
  }
  let good = input(&g, &[255, 1]);
  let mut bad = good.clone();
  bad[g.control.state_words()].lo = 1;
  check(&g, &r1cs, &bad, false);
  let mut bad = good.clone();
  bad[1 + g.control.frame_words() + 1].hi = 1;
  check(&g, &r1cs, &bad, false);
  let small = setup(9, 15);
  check(&small, &small.r1cs(), &input(&small, &[255, 1]), false);
  let zero = setup(0, 64);
  check(&zero, &zero.r1cs(), &input(&zero, &[]), true);
  check(&zero, &zero.r1cs(), &input(&zero, &[1]), false);
  let mut witness = vec![false; r1cs.n()];
  g.plan()
    .fill_row(&mut witness[..g.plan().k()], |bits| fill_words(&good, bits));
  for word in 0..g.output_count() {
    for bit in [0, 7, 31, 32, 63, 64, 127] {
      let column = 128 * (g.input_count() + word) + bit;
      witness[column] ^= true;
      assert!(!r1cs.satisfies(&witness));
      witness[column] ^= true;
    }
  }
}
