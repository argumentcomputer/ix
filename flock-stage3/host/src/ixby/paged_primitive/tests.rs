use super::*;
use crate::{
  ixby::{
    bits::{fill_words, read_words},
    io::LayoutEmitter,
    ixbf::Primitive,
    paged_code::Header,
    paged_value::PROGRAM_BYTES,
    value::{bool_words, word32_words},
  },
  sizing::{CircuitEmitter, CountingEmitter},
};
use flock_prover::circuit::builder::{GateType, ShapeBuilder};

fn request(p: Primitive, values: &[[F128; 2]]) -> Vec<F128> {
  let h = Header {
    locals: 73,
    operation: 1,
    primitive: p.opcode(),
    arguments: p.arity() as u8,
    operands: p.arity() as u8,
    target: 184,
    ..Header::default()
  };
  let mut input = vec![F128::ONE, h.words()[0]];
  input.extend(values.iter().flatten());
  input.resize(8, F128::ZERO);
  input
}
fn checked(gate: &PrimitiveRouteGate, input: &[F128]) -> Vec<F128> {
  let mut bits = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut bits, |bits| fill_words(input, bits));
  let out = read_words(&bits, 8, 20);
  let table = gate.r1cs();
  bits.resize(table.n(), false);
  assert!(table.satisfies(&bits));
  let mut native = Vec::new();
  gate.eval(input, &(), &mut native);
  assert_eq!(native, out);
  out
}
#[test]
fn routing_uses_functional_tags_and_exact_arity_without_truncating_nat() {
  let gate = PrimitiveRouteGate::new(3).unwrap();
  let nat = [F128::new(8, 0), F128::new(0, 1)];
  let input = request(Primitive::NatDiv, &[nat, nat]);
  let out = checked(&gate, &input);
  assert_eq!(out[19], F128::ZERO);
  assert_eq!(
    &out[..6],
    &[F128::ONE, F128::new(4, 0), nat[0], nat[1], nat[0], nat[1]]
  );
  assert_eq!(&out[6..19], &[F128::ZERO; 13]);
  for p in Primitive::ALL {
    let values = vec![bool_words(true); p.arity()];
    let out = checked(&gate, &request(p, &values));
    if (7..=9).contains(&p.opcode()) {
      assert_eq!(out[19], F128::ONE);
      continue;
    }
    assert_eq!(out[19], F128::ZERO);
    if p.opcode() < 7 {
      assert_eq!(out[1], F128::new(u64::from(p.opcode() + 1), 0));
    } else if gate::numeric(p) {
      assert_eq!(out[6], F128::new(2 << 32, 0));
      assert_eq!(
        out[7],
        F128::new(
          u64::from(p.native_opcode().unwrap()) << 32,
          p.arity() as u64
        )
      );
      assert_eq!(out[12], F128::ZERO);
    } else {
      assert_eq!(out[12], F128::new(u64::from(p.opcode() + 1), 0));
      assert_eq!(
        &out[13..13 + 2 * p.arity()],
        &values.into_iter().flatten().collect::<Vec<_>>()
      );
    }
  }
  for (at, bits) in [
    (0, F128::new(2, 0)),
    (0, F128::new(0, 1)),
    (1, F128::new(1 << 8, 0)),
    (1, F128::new(1 << 16, 0)),
    (1, F128::new(1 << 32, 0)),
    (1, F128::new(1 << 40, 0)),
    (6, F128::ONE),
    (7, F128::ONE),
  ] {
    let mut changed = input.clone();
    changed[at] += bits;
    assert_eq!(checked(&gate, &changed)[19], F128::ONE);
  }
  assert_eq!(checked(&gate, &[F128::ZERO; 8]), [F128::ZERO; 20]);
}

fn emit(
  b: &mut impl CircuitEmitter,
) -> (NumericSlots, crate::ixby::io::InputLayout, crate::ixby::io::PublicLayout)
{
  let mut b = LayoutEmitter::new(b);
  let slots = NumericSlots::declare(&mut b, 8).unwrap();
  let input = (0..8).map(|_| b.input()).collect::<Vec<_>>();
  let result =
    slots.evaluate(&mut b, input[0], input[1], input[2..].try_into().unwrap());
  for word in result
    .value
    .into_iter()
    .chain([result.byte_code])
    .chain(result.byte_arguments)
  {
    b.publish(word);
  }
  slots.finish_canonical(&mut b);
  let (inputs, public) = b.finish();
  (slots, inputs, public)
}
#[test]
fn numeric_primitive_wires_match_nat_word_and_field_oracles() {
  let mut b = ShapeBuilder::new(8);
  let (_, inputs, public) = emit(&mut b);
  let shape = b.finish().unwrap();
  let mut counted = CountingEmitter::new();
  emit(&mut counted);
  counted.ensure_matches(&shape).unwrap();
  for p in Primitive::ALL.into_iter().filter(|p| gate::numeric(*p)) {
    let (args, value) = if p.opcode() < 7 {
      let a = (1u128 << 32) + 1;
      let c = 37u128;
      let magnitude = match p {
        Primitive::NatAdd => a + c,
        Primitive::NatSub => a - c,
        Primitive::NatMul => a * c,
        Primitive::NatDiv => a / c,
        Primitive::NatMod => a % c,
        Primitive::NatEq => u128::from(a == c),
        Primitive::NatLt => u128::from(a < c),
        _ => unreachable!(),
      };
      let nat =
        |n: u128| [F128::new(8, 0), F128::new(n as u64, (n >> 64) as u64)];
      let expected = if p.opcode() >= 5 {
        bool_words(magnitude != 0)
      } else {
        nat(magnitude)
      };
      (vec![nat(a), nat(c)], expected)
    } else {
      let code = p.native_opcode().unwrap();
      let (a, c) = (0xffff_ffffu32, 37u32);
      if matches!(code, 1 | 2 | 6 | 7 | 8) {
        let expected = match code {
          1 => a.wrapping_sub(c),
          2 => a.wrapping_mul(c),
          6 => {
            if c < 32 {
              a << c
            } else {
              0
            }
          },
          7 => {
            if c < 32 {
              a >> c
            } else {
              0
            }
          },
          8 => a.rotate_right(c % 32),
          _ => unreachable!(),
        };
        (vec![word32_words(a), word32_words(c)], word32_words(expected))
      } else {
        crate::ixby::primitive::tests::oracle(
          code,
          a,
          c,
          0xffffffff00000000,
          37,
        )
      }
    };
    let input = request(p, &args);
    let mut expected = value.to_vec();
    expected.resize(9, F128::ZERO);
    let witness = shape.run(&inputs.assign(&input).unwrap(), &[]);
    assert_eq!(witness.public, public.instantiate(&expected).unwrap(), "{p:?}");
    let bad = request(p, &vec![bool_words(true); p.arity()]);
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || shape.run(&inputs.assign(&bad).unwrap(), &[])
      ))
      .is_err(),
      "accepted wrong {p:?} type"
    );
  }
  let bytes = [F128::new(6, 0), F128::new(PROGRAM_BYTES << 5, 16)];
  let input = request(Primitive::Blake3, &[bytes]);
  let mut expected =
    vec![F128::ZERO, F128::ZERO, F128::new(45, 0), bytes[0], bytes[1]];
  expected.resize(9, F128::ZERO);
  let witness = shape.run(&inputs.assign(&input).unwrap(), &[]);
  assert_eq!(witness.public, public.instantiate(&expected).unwrap());
}
