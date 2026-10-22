use aiur::{
  bytecode::{Entry, Function, Instruction, Program, Type, VERSION},
  field::{FieldBackend, NativeField, PrimeField},
  hints::HintChannels,
  value::IoType,
};
use multi_stark::p3_goldilocks::Goldilocks;

fn exercise<B: FieldBackend>(field: B) {
  for (channel, words) in [("u32.add", 2), ("u32.add3", 3)] {
    let width = words * 4;
    let bytes = Type::Tuple { items: vec![Type::Field; 4] };
    let p = Program {
      version: VERSION,
      modulus: field.modulus(),
      enums: vec![],
      tables: vec![],
      maps: vec![],
      functions: vec![Function {
        name: "sum".into(),
        params: vec![Type::Field; width],
        result: bytes.clone(),
        registers: width + 4,
        code: vec![
          Instruction::Hint {
            channel: channel.into(),
            key_type: Type::Tuple { items: vec![bytes; words] },
            r#type: Type::Tuple { items: vec![Type::Field; 4] },
            key: (0..width).collect(),
            dest: (width..width + 4).collect(),
          },
          Instruction::Ret { value: (width..width + 4).collect() },
        ],
      }],
      entries: vec![Entry {
        name: "sum".into(),
        function: 0,
        inputs: vec![IoType::Field; width],
        output: None,
      }],
    }
    .check_with(field)
    .unwrap();
    let mut channels = HintChannels::new();
    aiur::library::u32::register(&mut channels, field).unwrap();
    let prepared = p.prepare_hint_channels(&[], &channels).unwrap();
    // Overflow, carry propagation through each byte, and distinct limbs.
    for operands in [
      [0, 0, 0],
      [u32::MAX, 1, u32::MAX],
      [0x00ff_ffff, 1, 0x0100_0000],
      [0x0123_4567, 0x89ab_cdef, 0x7654_3210],
    ] {
      let input: Vec<_> = operands[..words]
        .iter()
        .flat_map(|word| word.to_le_bytes())
        .map(|b| field.from_u64(u64::from(b)))
        .collect();
      let result = prepared.execute("sum", input).unwrap();
      let expected =
        operands[..words].iter().fold(0u32, |a, b| a.wrapping_add(*b));
      assert_eq!(
        result.output,
        expected.to_le_bytes().map(|b| field.from_u64(u64::from(b)))
      );
    }
    for index in 0..width {
      for invalid in [256, 1 << 32, field.modulus() - 1] {
        let mut input = vec![field.zero(); width];
        input[index] = field.from_u64(invalid);
        let error = prepared.execute("sum", input).unwrap_err();
        assert_eq!(error.instruction, 0);
        assert_eq!(error.message, "non-byte u32 sum operand");
      }
    }
  }
}

#[test]
fn sum_hints_wrap_correctly_and_reject_every_invalid_limb() {
  exercise(PrimeField::new(0xffff_ffff_0000_0001).unwrap());
  exercise(NativeField::<Goldilocks>::new());
}
