use super::*;
use num_bigint::BigUint;

fn n(value: u64) -> BigUint {
  BigUint::from(value)
}
fn local(value: u64) -> Operand<'static> {
  Operand::Local(n(value))
}
fn block(locals: u64, instruction: Instruction<'static>) -> Block<'static> {
  Block { locals: n(locals), instruction, encoded: 0..0 }
}

fn modified(change: impl FnOnce(&mut Artifact<'static>)) -> Vec<u8> {
  let mut artifact = decode_program(IDENTITY, DecodeLimits::default()).unwrap();
  change(&mut artifact);
  artifact.encode()
}

fn scalar_input(value: Scalar<'_>) -> Vec<u8> {
  Input {
    source: &[],
    values: ValueForest {
      nodes: vec![ValueNode {
        kind: ValueKind::Scalar(value),
        children: vec![],
      }],
      roots: vec![0],
      depth: 1,
    },
  }
  .encode()
}

fn reject_program(bytes: &[u8]) {
  assert!(
    decode_program(bytes, DecodeLimits::default()).is_err(),
    "unexpected admission: {bytes:?}"
  );
}

fn rich_program() -> Vec<u8> {
  modified(|artifact| {
    artifact.limits.functions = n(2);
    artifact.limits.constructors = n(2);
    artifact.limits.blocks = n(8);
    artifact.limits.locals = n(8);
    artifact.limits.operands = n(4);
    artifact.limits.input_nodes = n(32);
    artifact.constructors = vec![
      ConstructorDeclaration {
        id: ConstructorId { block: [0; 32], member: n(0), tag: n(0) },
        fields: n(1),
      },
      ConstructorDeclaration {
        id: ConstructorId {
          block: [255; 32],
          member: n(1) << 80,
          tag: n(1) << 65,
        },
        fields: n(2),
      },
    ];
    artifact.functions.push(Function {
      arity: n(3),
      entry: 0,
      blocks: vec![block(3, Instruction::Return(Operand::Erased))],
    });
  })
}

// Independently hand-encoded identity program. Functional format 1, semantics
// 0; one function, arity 1, one block, return local 0. Not IXBY profile bytes.
const IDENTITY: &[u8] = &[
  b'I', b'X', b'B', b'F', 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 8, 0x80,
  0x20, 64, 64, 24, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0,
];

#[test]
fn independently_encoded_identity_roundtrips_with_original_ranges() {
  let artifact = decode_program(IDENTITY, DecodeLimits::default()).unwrap();
  assert_eq!(artifact.encode(), IDENTITY);
  assert_eq!(artifact.entry(), 0);
  assert_eq!(artifact.max_steps().to_string(), "24");
  assert_eq!(artifact.functions()[0].blocks[0].encoded, 30..34);
  assert_eq!(artifact.inventory().instructions, [0, 1, 0, 0, 0, 0, 0, 0]);
}

#[test]
fn functional_opcode_names_map_explicitly_without_aliases() {
  let mut native = std::collections::BTreeSet::new();
  for (opcode, primitive) in Primitive::ALL.into_iter().enumerate() {
    assert_eq!(usize::from(primitive.opcode()), opcode);
    assert_eq!(Primitive::from_opcode(opcode as u8), Some(primitive));
    match primitive.native_opcode() {
      Some(opcode) => {
        assert!(native.insert(opcode));
        assert_eq!(
          super::super::decode::primitive_arity(opcode),
          Some(primitive.arity())
        );
      },
      None => assert!((7..=9).contains(&primitive.opcode())),
    }
  }
  assert_eq!(
    native.into_iter().collect::<Vec<_>>(),
    (0..42).collect::<Vec<_>>()
  );
  for opcode in 45..=u8::MAX {
    assert_eq!(Primitive::from_opcode(opcode), None);
  }
}

#[test]
fn every_truncated_program_prefix_wrong_domain_and_version_rejects() {
  for end in 0..IDENTITY.len() {
    reject_program(&IDENTITY[..end]);
  }
  for offset in [0, 3, 4, 7, 8, 11] {
    let mut bytes = IDENTITY.to_vec();
    bytes[offset] ^= 1;
    reject_program(&bytes);
  }
  let mut bytes = IDENTITY.to_vec();
  bytes.extend([0, 0]);
  reject_program(&bytes);
  let mut bytes = IDENTITY.to_vec();
  bytes[..4].copy_from_slice(b"IXBY");
  reject_program(&bytes);
}

#[test]
fn natural_metadata_above_u64_and_u32_is_preserved_exactly() {
  let big: BigUint = (n(1) << 100usize) + n(129);
  let bytes = modified(|artifact| {
    artifact.max_steps = big.clone();
    artifact.limits.continuations = big.clone();
    artifact.limits.functions = big.clone();
  });
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  assert_eq!(artifact.max_steps(), &big);
  assert_eq!(artifact.limits().continuations, big);
  assert_eq!(artifact.encode(), bytes);
  let bytes = modified(|artifact| artifact.max_steps = n(16_000_000_000));
  assert_eq!(
    decode_program(&bytes, DecodeLimits::default()).unwrap().max_steps(),
    &n(16_000_000_000)
  );
}

#[test]
fn nonminimal_unterminated_and_hostile_large_counts_reject() {
  let mut bytes = IDENTITY.to_vec();
  bytes.splice(12..13, [0x81, 0]);
  reject_program(&bytes);
  let mut bytes = IDENTITY.to_vec();
  bytes.splice(12..13, [0x80, 0]);
  reject_program(&bytes);
  let mut bytes = IDENTITY[..12].to_vec();
  bytes.extend([0x80; 17]);
  reject_program(&bytes);
  let bytes = modified(|artifact| artifact.limits.functions = n(u64::MAX));
  // Metadata itself is allowed; the vector count still must fit the file.
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  assert_eq!(artifact.functions().len(), 1);
  let mut hostile = IDENTITY.to_vec();
  hostile.splice(26..27, [0xff, 0xff, 0xff, 0xff, 0x0f]);
  reject_program(&hostile);
}

#[test]
fn all_host_loader_budgets_fail_closed() {
  for loader in [
    DecodeLimits { bytes: IDENTITY.len() - 1, ..DecodeLimits::default() },
    DecodeLimits { integer_bytes: 1, ..DecodeLimits::default() },
    DecodeLimits { syntax_nodes: 3, ..DecodeLimits::default() },
  ] {
    assert!(decode_program(IDENTITY, loader).is_err());
  }
  let artifact = decode_program(IDENTITY, DecodeLimits::default()).unwrap();
  let bytes = scalar_input(Scalar::Nat(n(0)));
  for loader in [
    DecodeLimits { value_nodes: 0, ..DecodeLimits::default() },
    DecodeLimits { value_depth: 0, ..DecodeLimits::default() },
    DecodeLimits { bytes: bytes.len() - 1, ..DecodeLimits::default() },
  ] {
    assert!(decode_input(&artifact, &bytes, loader).is_err());
  }
}

#[test]
fn every_scalar_kind_roundtrips_and_payloads_remain_distinct() {
  let artifact = decode_program(IDENTITY, DecodeLimits::default()).unwrap();
  let values = [
    Scalar::Nat((n(1) << 255) + n(17)),
    Scalar::String("λ\0🦀"),
    Scalar::Bool(true),
    Scalar::Word32(u32::MAX),
    Scalar::Goldilocks(0xffff_ffff_0000_0000),
    Scalar::Extension([0, 0xffff_ffff_0000_0000]),
    Scalar::Bytes(&[0, 255, 128]),
  ];
  for (tag, value) in values.into_iter().enumerate() {
    let bytes = scalar_input(value.clone());
    assert_eq!(bytes[14], tag as u8);
    let input =
      decode_input(&artifact, &bytes, DecodeLimits::default()).unwrap();
    assert_eq!(input.encode(), bytes);
    assert_eq!(input.values().nodes()[0].kind, ValueKind::Scalar(value));
    for end in 0..bytes.len() {
      assert!(
        decode_input(&artifact, &bytes[..end], DecodeLimits::default())
          .is_err()
      );
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(
      decode_input(&artifact, &trailing, DecodeLimits::default()).is_err()
    );
  }
}

#[test]
fn noncanonical_scalars_and_invalid_utf8_reject() {
  let artifact = decode_program(IDENTITY, DecodeLimits::default()).unwrap();
  let mut bad_bool = scalar_input(Scalar::Bool(true));
  bad_bool[15] = 2;
  let mut bad_field = scalar_input(Scalar::Goldilocks(0));
  bad_field[15..23].copy_from_slice(&0xffff_ffff_0000_0001u64.to_le_bytes());
  let mut bad_extension = scalar_input(Scalar::Extension([0, 0]));
  bad_extension[23..31].copy_from_slice(&u64::MAX.to_le_bytes());
  let mut bad_string = scalar_input(Scalar::String("ab"));
  bad_string[16..18].copy_from_slice(&[0xc0, 0xaf]);
  let mut bad_nat = scalar_input(Scalar::Nat(n(0)));
  bad_nat.splice(15..16, [0x80, 0]);
  let mut bad_tag = scalar_input(Scalar::Nat(n(0)));
  bad_tag[14] = 7;
  for bytes in
    [bad_bool, bad_field, bad_extension, bad_string, bad_nat, bad_tag]
  {
    assert!(decode_input(&artifact, &bytes, DecodeLimits::default()).is_err());
  }
}

#[test]
fn scalar_capacity_and_nat_zero_boundary_follow_reference() {
  let program = modified(|artifact| artifact.limits.nat_bits = n(0));
  let artifact = decode_program(&program, DecodeLimits::default()).unwrap();
  let zero = scalar_input(Scalar::Nat(n(0)));
  assert!(decode_input(&artifact, &zero, DecodeLimits::default()).is_ok());
  let one = scalar_input(Scalar::Nat(n(1)));
  assert!(decode_input(&artifact, &one, DecodeLimits::default()).is_err());
  let word = scalar_input(Scalar::Word32(u32::MAX));
  assert!(decode_input(&artifact, &word, DecodeLimits::default()).is_ok());
  let bytes = scalar_input(Scalar::Bytes(&[0; 65]));
  assert!(decode_input(&artifact, &bytes, DecodeLimits::default()).is_err());
  let program = modified(|artifact| artifact.limits.nat_bits = n(65));
  let artifact = decode_program(&program, DecodeLimits::default()).unwrap();
  for (bits, accepted) in [(64, true), (65, false)] {
    let bytes = scalar_input(Scalar::Nat(n(1) << bits));
    assert_eq!(
      decode_input(&artifact, &bytes, DecodeLimits::default()).is_ok(),
      accepted
    );
  }
}

fn changed<'a>(
  bytes: &'a [u8],
  change: impl FnOnce(&mut Artifact<'a>),
) -> Vec<u8> {
  let mut artifact = decode_program(bytes, DecodeLimits::default()).unwrap();
  change(&mut artifact);
  artifact.encode()
}

#[test]
fn whole_image_validation_includes_dead_code_and_unique_identities() {
  let bytes = rich_program();
  let malformed = [
    changed(&bytes, |a| a.entry = 2),
    changed(&bytes, |a| a.functions[1].entry = 7),
    changed(&bytes, |a| a.functions[1].arity = n(4)),
    changed(&bytes, |a| a.functions[1].blocks[0].locals = n(9)),
    changed(&bytes, |a| {
      a.functions[1].blocks[0].instruction = Instruction::Return(local(3))
    }),
    changed(&bytes, |a| {
      a.functions[1].blocks.push(block(0, Instruction::Return(local(0))))
    }),
    changed(&bytes, |a| a.constructors[1].id = a.constructors[0].id.clone()),
    changed(&bytes, |a| a.constructors[1].fields = n(5)),
    changed(&bytes, |a| a.limits.functions = n(1)),
    changed(&bytes, |a| a.limits.constructors = n(1)),
  ];
  for bytes in malformed {
    reject_program(&bytes);
  }
}

#[test]
fn all_operation_forms_and_primitive_arities_admit_structurally() {
  let base = rich_program();
  let mut operations = vec![
    Operation::Copy(local(0)),
    Operation::Construct(1, vec![local(0), Operand::Erased]),
    Operation::Project(local(0), n(1) << 100),
    Operation::Closure(1, vec![local(0), Operand::Erased]),
    Operation::Call(1, vec![local(0), Operand::Erased, Operand::Erased]),
    Operation::CallSelf(vec![local(0)]),
    Operation::Apply(Operand::Erased, vec![]),
  ];
  for primitive in Primitive::ALL {
    operations.push(Operation::Primitive(
      primitive,
      vec![Operand::Erased; primitive.arity()],
    ));
  }
  for operation in operations {
    let bytes = changed(&base, |a| {
      a.functions[0].blocks = vec![
        block(1, Instruction::Let(operation, 1)),
        block(2, Instruction::Return(local(1))),
      ]
    });
    let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
    assert_eq!(artifact.encode(), bytes);
    assert_eq!(artifact.inventory().instructions, [1, 2, 0, 0, 0, 0, 0, 0]);
  }
}

#[test]
fn wrong_calls_closures_primitive_arities_and_resume_frames_reject() {
  let base = rich_program();
  for operation in [
    Operation::Primitive(Primitive::BytesSlice, vec![Operand::Erased; 2]),
    Operation::Primitive(Primitive::NatAdd, vec![Operand::Erased; 3]),
    Operation::Construct(0, vec![]),
    Operation::Construct(2, vec![Operand::Erased]),
    Operation::Closure(1, vec![Operand::Erased; 3]),
    Operation::Closure(2, vec![]),
    Operation::Call(1, vec![Operand::Erased; 2]),
    Operation::Call(2, vec![]),
    Operation::CallSelf(vec![]),
    Operation::Apply(local(1), vec![]),
    Operation::Apply(Operand::Erased, vec![Operand::Erased; 5]),
  ] {
    let bytes = changed(&base, |a| {
      a.functions[0].blocks = vec![
        block(1, Instruction::Let(operation, 1)),
        block(2, Instruction::Return(local(1))),
      ]
    });
    reject_program(&bytes);
  }
  for (next, target_locals) in [(1, 1), (2, 2)] {
    let bytes = changed(&base, |a| {
      a.functions[0].blocks = vec![
        block(1, Instruction::Let(Operation::Copy(local(0)), next)),
        block(target_locals, Instruction::Return(Operand::Erased)),
      ]
    });
    reject_program(&bytes);
  }
}

#[test]
fn tail_forms_and_arbitrary_precision_local_contracts_are_preserved() {
  let base = rich_program();
  for instruction in [
    Instruction::TailCall(1, vec![Operand::Erased; 3]),
    Instruction::TailCallSelf(vec![local(0)]),
    Instruction::TailApply(Operand::Erased, vec![local(0)]),
  ] {
    let bytes =
      changed(&base, |a| a.functions[0].blocks = vec![block(1, instruction)]);
    assert_eq!(
      decode_program(&bytes, DecodeLimits::default()).unwrap().encode(),
      bytes
    );
  }
  let large: BigUint = n(1) << 80usize;
  let bytes = modified(|a| {
    a.limits.operands = large.clone();
    a.limits.locals = &large + 1u8;
    a.limits.blocks = n(2);
    a.functions[0].arity = large.clone();
    a.functions[0].blocks = vec![
      Block {
        locals: large.clone(),
        instruction: Instruction::Let(
          Operation::Copy(Operand::Local(&large - 1u8)),
          1,
        ),
        encoded: 0..0,
      },
      Block {
        locals: &large + 1u8,
        instruction: Instruction::Return(Operand::Local(large.clone())),
        encoded: 0..0,
      },
    ];
  });
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  assert_eq!(artifact.inventory().maximum_frame_locals, &large + 1u8);
  assert_eq!(artifact.encode(), bytes);
}

#[test]
fn case_nat_and_branch_have_distinct_tags_and_frame_contracts() {
  let base = rich_program();
  let bytes = changed(&base, |a| {
    a.functions[0].blocks = vec![
      block(1, Instruction::CaseNat(local(0), 1, 2)),
      block(1, Instruction::Return(local(0))),
      block(2, Instruction::Return(local(1))),
    ]
  });
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  let tag_offset = artifact.functions()[0].blocks[0].encoded.start + 1;
  assert_eq!(bytes[tag_offset], 6);
  let mut swapped = bytes.clone();
  swapped[tag_offset] = 7;
  reject_program(&swapped);
  let bytes = changed(&base, |a| {
    a.functions[0].blocks = vec![
      block(1, Instruction::Branch(local(0), 1, 2)),
      block(1, Instruction::Return(local(0))),
      block(1, Instruction::Return(Operand::Erased)),
    ]
  });
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  let tag_offset = artifact.functions()[0].blocks[0].encoded.start + 1;
  assert_eq!(bytes[tag_offset], 7);
  let mut swapped = bytes.clone();
  swapped[tag_offset] = 6;
  reject_program(&swapped);
}

#[test]
fn constructor_cases_check_all_alternatives_and_appended_fields() {
  let base = rich_program();
  let bytes = changed(&base, |a| {
    a.functions[0].blocks = vec![
      block(
        1,
        Instruction::CaseConstructor(
          local(0),
          vec![
            Alternative { constructor: 0, target: 1 },
            Alternative { constructor: 1, target: 2 },
          ],
        ),
      ),
      block(2, Instruction::Return(local(1))),
      block(3, Instruction::Return(local(2))),
    ]
  });
  assert!(decode_program(&bytes, DecodeLimits::default()).is_ok());
  for alternatives in [
    vec![
      Alternative { constructor: 0, target: 1 },
      Alternative { constructor: 0, target: 1 },
    ],
    vec![Alternative { constructor: 2, target: 1 }],
    vec![Alternative { constructor: 1, target: 1 }],
    vec![Alternative { constructor: 0, target: 7 }],
  ] {
    let bad = changed(&bytes, |a| {
      a.functions[0].blocks[0].instruction =
        Instruction::CaseConstructor(local(0), alternatives)
    });
    reject_program(&bad);
  }
}

#[test]
fn nested_constructor_and_pap_forest_roundtrips_without_recursive_ownership() {
  let bytes = rich_program();
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  let input = Input {
    source: &[],
    values: ValueForest {
      nodes: vec![
        ValueNode {
          kind: ValueKind::Constructor(artifact.constructors()[1].id.clone()),
          children: vec![1, 2],
        },
        ValueNode {
          kind: ValueKind::Scalar(Scalar::String("λ")),
          children: vec![],
        },
        ValueNode { kind: ValueKind::PartialApplication(1), children: vec![3] },
        ValueNode {
          kind: ValueKind::Scalar(Scalar::Nat(n(1) << 90)),
          children: vec![],
        },
      ],
      roots: vec![0],
      depth: 3,
    },
  };
  let encoded = input.encode();
  let decoded =
    decode_input(&artifact, &encoded, DecodeLimits::default()).unwrap();
  assert_eq!(decoded.values().nodes(), input.values().nodes());
  assert_eq!(decoded.values().depth(), 3);
  assert_eq!(decoded.values().roots(), [0]);
  assert_eq!(decoded.encode(), encoded);
  let output = Output { source: &[], values: input.values };
  let encoded = output.encode();
  let decoded =
    decode_output(&artifact, &encoded, DecodeLimits::default()).unwrap();
  assert_eq!(decoded.values().nodes(), output.values().nodes());
  assert_eq!(decoded.encode(), encoded);
  for end in 0..encoded.len() {
    assert!(
      decode_output(&artifact, &encoded[..end], DecodeLimits::default())
        .is_err()
    );
  }
}

#[test]
fn unread_paps_and_constructor_values_are_still_validated() {
  let bytes = rich_program();
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  let id = artifact.constructors()[0].id.clone();
  let mut unknown = id.clone();
  unknown.tag += 1u8;
  for (kind, child_count) in [
    (ValueKind::Constructor(id), 0),
    (ValueKind::Constructor(unknown), 1),
    (ValueKind::PartialApplication(1), 3),
    (ValueKind::PartialApplication(2), 0),
  ] {
    let mut nodes =
      vec![ValueNode { kind, children: (1..=child_count).collect() }];
    nodes.extend(
      (0..child_count)
        .map(|_| ValueNode { kind: ValueKind::Erased, children: vec![] }),
    );
    let encoded = Input {
      source: &[],
      values: ValueForest { nodes, roots: vec![0], depth: 2 },
    }
    .encode();
    assert!(
      decode_input(&artifact, &encoded, DecodeLimits::default()).is_err()
    );
  }
}

#[test]
fn node_fuel_is_shared_across_all_roots_and_children() {
  let base = rich_program();
  let bytes = changed(&base, |a| {
    a.limits.input_nodes = n(2);
    a.functions[0].arity = n(2);
    a.functions[0].blocks = vec![block(2, Instruction::Return(local(0)))];
  });
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  let forest = ValueForest {
    nodes: vec![
      ValueNode {
        kind: ValueKind::Constructor(artifact.constructors()[0].id.clone()),
        children: vec![1],
      },
      ValueNode { kind: ValueKind::Erased, children: vec![] },
      ValueNode { kind: ValueKind::Erased, children: vec![] },
    ],
    roots: vec![0, 2],
    depth: 2,
  };
  let input = Input { source: &[], values: forest }.encode();
  assert!(decode_input(&artifact, &input, DecodeLimits::default()).is_err());
  let bytes = changed(&bytes, |a| a.limits.input_nodes = n(3));
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  assert!(decode_input(&artifact, &input, DecodeLimits::default()).is_ok());
  assert!(
    decode_input(
      &artifact,
      &input,
      DecodeLimits { value_nodes: 2, ..DecodeLimits::default() }
    )
    .is_err()
  );
}

#[test]
fn deep_values_use_an_explicit_stack_and_exact_depth_bound() {
  let base = rich_program();
  let bytes = changed(&base, |a| a.limits.input_nodes = n(4096));
  let artifact = decode_program(&bytes, DecodeLimits::default()).unwrap();
  let depth = 2048;
  let mut nodes: Vec<_> = (0..depth - 1)
    .map(|index| ValueNode {
      kind: ValueKind::Constructor(artifact.constructors()[0].id.clone()),
      children: vec![index + 1],
    })
    .collect();
  nodes.push(ValueNode { kind: ValueKind::Erased, children: vec![] });
  let encoded =
    Input { source: &[], values: ValueForest { nodes, roots: vec![0], depth } }
      .encode();
  assert!(decode_input(&artifact, &encoded, DecodeLimits::default()).is_err());
  let decoded = decode_input(
    &artifact,
    &encoded,
    DecodeLimits { value_depth: depth, ..DecodeLimits::default() },
  )
  .unwrap();
  assert_eq!(decoded.values().depth(), depth);
  assert_eq!(decoded.values().nodes().len(), depth);
  assert_eq!(decoded.encode(), encoded);
  assert!(
    decode_input(
      &artifact,
      &encoded,
      DecodeLimits { value_depth: depth - 1, ..DecodeLimits::default() }
    )
    .is_err()
  );
}

#[test]
fn byte_arrays_borrow_the_canonical_buffer_and_output_cannot_select_its_arity()
{
  let artifact = decode_program(IDENTITY, DecodeLimits::default()).unwrap();
  let bytes = scalar_input(Scalar::Bytes(&[4, 5, 6]));
  let decoded =
    decode_input(&artifact, &bytes, DecodeLimits::default()).unwrap();
  let ValueKind::Scalar(Scalar::Bytes(value)) =
    decoded.values().nodes()[0].kind
  else {
    panic!("expected bytes")
  };
  assert_eq!(value.as_ptr(), bytes[16..].as_ptr());
  let mut wrong_arity = bytes.clone();
  wrong_arity[12] = 0;
  assert!(
    decode_input(&artifact, &wrong_arity, DecodeLimits::default()).is_err()
  );
  let mut wrong_domain = bytes.clone();
  wrong_domain[..4].copy_from_slice(b"IXBI");
  assert!(
    decode_input(&artifact, &wrong_domain, DecodeLimits::default()).is_err()
  );
  let mut output = b"IXFO\x01\0\0\0\0\0\0\0".to_vec();
  output.push(3);
  assert!(decode_output(&artifact, &output, DecodeLimits::default()).is_ok());
  output.push(3);
  assert!(decode_output(&artifact, &output, DecodeLimits::default()).is_err());
}
