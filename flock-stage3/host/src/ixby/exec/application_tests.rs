use super::application_fixtures::{CAPACITY, cases, setup};
use super::*;
use crate::ixby::decode::test_support::{
  Instruction as I, Operand as O, Value as V,
};
use application_fixtures::{example, function, identity, pair, word};
use flock_prover::circuit::builder::GateType;

fn run(
  compiled: &CompiledExec,
  case: (Vec<u8>, Vec<u8>, Vec<u8>),
  valid: bool,
) {
  let (code, input, output) = case;
  let expected = expected_statement(compiled.profile(), &code, &input, &output);
  let private = [
    proof::buffer(compiled.capacity.program.bytes, &code).unwrap(),
    proof::buffer(compiled.capacity.input.bytes, &input).unwrap(),
  ]
  .concat();
  let witness = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[])
  }));
  assert_eq!(
    witness.is_ok_and(|witness| witness.public
      == compiled.public.instantiate(&expected.limbs()).unwrap()),
    valid,
    "code={code:?}, input={input:?}"
  );
}

#[test]
fn native_closures_paps_and_apply_rest_execute_in_one_setup() {
  let compiled = setup();
  eprintln!(
    "Application Exec census nu={}, m={}, tables={}, largest_log_k={}, setup={}",
    compiled.nu,
    compiled.params.m,
    compiled.tables.len(),
    compiled.tables.iter().map(|t| t.k_log).max().unwrap(),
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex()
  );
  assert!(compiled.applications());
  assert_eq!(
    blake3::Hash::from_bytes(compiled.identities().digest()).to_hex().as_str(),
    "9ef161680676f2929322a59c5804f6c7cf3d3f8e3e36e61960c7d3f85df42953"
  );
  let fuel = [
    3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5, 8, 8, 6, 10, 8, 10, 6, 4, 4, 4, 5, 4, 3,
    3, 5, 7,
  ];
  for (index, (code, input, output)) in cases().into_iter().enumerate() {
    eprintln!(
      "Application execution {index}: program/input/output {}/{}/{}",
      code.len(),
      input.len(),
      output.len()
    );
    let expected =
      expected_statement(compiled.profile(), &code, &input, &output);
    let golden = match index {
      0 => Some([
        14687990384083634,
        5830356504901387565,
        14359430384946980301,
        11454731321620998259,
      ]),
      14 => Some([
        16522776896425344640,
        1119810387505576751,
        6309516584285128144,
        8596517101313489382,
      ]),
      24 => Some([
        1846894401329383370,
        878564278452078894,
        337315515468421852,
        2613245647962240889,
      ]),
      _ => None,
    };
    if let Some(golden) = golden {
      assert_eq!(
        expected
          .limbs()
          .iter()
          .flat_map(|word| [word.lo, word.hi])
          .collect::<Vec<_>>(),
        golden,
        "independent Lean application statement {index}"
      );
    }
    let private = [
      proof::buffer(CAPACITY.program.bytes, &code).unwrap(),
      proof::buffer(CAPACITY.input.bytes, &input).unwrap(),
    ]
    .concat();
    let witness =
      compiled.shape.run(&compiled.input.assign(&private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      compiled.public.instantiate(&expected.limbs()).unwrap(),
      "application case {index}"
    );
    assert_eq!(
      witness::drivers(&compiled, &witness).len(),
      compiled.tables.len()
    );
    let rows = witness.rows::<crate::ixby::control::ControlStepGate>(
      compiled.machine.control_slot.slot(),
    );
    assert_eq!(rows.len(), CAPACITY.steps);
    let mut last = Vec::new();
    compiled.machine.control_gate.eval(
      rows.last().unwrap().inputs(),
      &(),
      &mut last,
    );
    assert_eq!(last[0].lo as u32, 2, "real halt {index}");
    assert_eq!(
      (last[0].lo >> 32) as usize,
      CAPACITY.steps - fuel[index],
      "exact application fuel {index}"
    );
  }
}

#[test]
fn application_setup_is_explicit_and_authenticates_whole_program_and_value_forests()
 {
  let compiled = setup();
  assert!(
    compiled
      .transcript_domain()
      .starts_with(profile::APPLICATION_TRANSCRIPT_DOMAIN)
  );
  let bytes = ByteCapacity::new(33).unwrap();
  let objects = ObjectCapacity::new(2, 3, 7).unwrap();
  let mut capacity = CAPACITY;
  capacity.control.arguments = 1;
  assert!(
    compile_exec_application_profile(
      SemanticProfile::objects(capacity, bytes, objects).unwrap(),
      capacity,
      (bytes, objects, None),
      PrimitiveSet::crypto(),
      Blake3Backend::PackedWordsV0
    )
    .is_err()
  );
  for index in 0..14 {
    let mut p = compiled.profile().parameters();
    p[index] += 1;
    if let Ok(profile) = SemanticProfile::new(p) {
      assert!(
        compile_exec_application_profile(
          profile,
          CAPACITY,
          (bytes, objects, None),
          PrimitiveSet::crypto(),
          Blake3Backend::PackedWordsV0
        )
        .is_err(),
        "changed semantic capacity {index}"
      );
    }
  }
  let ignore = vec![function(2, vec![(2, I::Ret(word(42)))]), identity(1, 0)];
  run(
    &compiled,
    example(ignore.clone(), &[V::Word(0), V::Pap(1, vec![])], V::Word(42)),
    true,
  );
  for pap in [
    V::Pap(2, vec![]),
    V::Pap(1 << 31, vec![]),
    V::Pap(u32::MAX, vec![]),
    V::Pap(1, vec![V::Word(11)]),
    V::Pap(1, vec![V::Word(11), V::Word(22)]),
    pair(V::Erased, V::Pap(1, vec![V::Word(11)])),
    V::Pap(1, vec![V::Bytes(vec![0; 34])]),
  ] {
    run(
      &compiled,
      example(ignore.clone(), &[V::Word(0), pap], V::Word(42)),
      false,
    );
  }
  for captured in [vec![], vec![word(11)], vec![word(11), word(22)]] {
    let arity = captured.len() as u32;
    run(
      &compiled,
      example(
        vec![
          function(
            0,
            vec![(0, I::Closure(1, captured, 1)), (1, I::Ret(O::Local(0)))],
          ),
          function(arity, vec![(arity, I::Ret(word(42)))]),
        ],
        &[],
        V::Erased,
      ),
      false,
    );
  }
  for callee in [2, 1 << 31, u32::MAX] {
    run(
      &compiled,
      example(
        vec![
          function(
            0,
            vec![(0, I::Closure(callee, vec![], 1)), (1, I::Ret(O::Local(0)))],
          ),
          identity(1, 0),
        ],
        &[],
        V::Erased,
      ),
      false,
    );
  }
  // A bad closure in an unvisited block cannot be hidden behind an immediate return.
  run(
    &compiled,
    example(
      vec![
        function(
          0,
          vec![
            (0, I::Ret(word(42))),
            (0, I::Closure(1, vec![word(11)], 2)),
            (1, I::Ret(O::Local(0))),
          ],
        ),
        identity(1, 0),
      ],
      &[],
      V::Word(42),
    ),
    false,
  );
  for function_operand in [O::Local(1), O::Local(1 << 31), O::Local(u32::MAX)] {
    run(
      &compiled,
      example(
        vec![function(
          1,
          vec![
            (1, I::Ret(word(42))),
            (1, I::TailApply(function_operand, vec![])),
          ],
        )],
        &[V::Erased],
        V::Word(42),
      ),
      false,
    );
  }
  run(
    &compiled,
    example(
      vec![
        function(
          1,
          vec![(1, I::TailApply(O::Local(0), vec![word(1), word(2), word(3)]))],
        ),
        identity(1, 0),
      ],
      &[V::Pap(1, vec![])],
      V::Word(1),
    ),
    false,
  );
  for value in [V::Word(42), V::Bytes(vec![]), pair(V::Erased, V::Erased)] {
    run(
      &compiled,
      example(
        vec![function(1, vec![(1, I::TailApply(O::Local(0), vec![word(1)]))])],
        &[value],
        V::Erased,
      ),
      false,
    );
  }
  // Under-application cannot turn a returned scalar into a callable value.
  run(
    &compiled,
    example(
      vec![
        function(
          1,
          vec![(1, I::TailApply(O::Local(0), vec![word(1), word(2)]))],
        ),
        identity(1, 0),
      ],
      &[V::Pap(1, vec![])],
      V::Word(1),
    ),
    false,
  );
  // Output tree budgets apply to PAP captures as well as constructor fields.
  let deep = V::Pap(1, vec![V::Pap(1, vec![])]);
  run(
    &compiled,
    example(
      vec![
        function(
          1,
          vec![
            (1, I::Closure(1, vec![O::Local(0)], 1)),
            (2, I::Closure(1, vec![O::Local(1)], 2)),
            (3, I::Ret(O::Local(2))),
          ],
        ),
        identity(2, 0),
      ],
      &[deep],
      V::Erased,
    ),
    false,
  );
  let old = compile_exec_object_profile(
    compiled.profile(),
    CAPACITY,
    bytes,
    objects,
    PrimitiveSet::crypto(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap();
  assert!(!old.applications());
  assert_ne!(compiled.identities(), old.identities());
  for case in [
    cases().remove(0),
    cases().remove(2),
    example(ignore, &[V::Word(0), V::Pap(1, vec![])], V::Word(42)),
  ] {
    run(&old, case, false);
  }
}

#[test]
fn applications_compose_with_exact_nats_without_word_coercion() {
  use super::nat_fixtures::{nat, revision};
  let bytes = ByteCapacity::new(33).unwrap();
  let objects = ObjectCapacity::new(2, 3, 7).unwrap();
  let nats = NatCapacity::new(96).unwrap();
  let compiled = compile_exec_application_profile(
    SemanticProfile::nat(CAPACITY, bytes, Some(objects), nats).unwrap(),
    CAPACITY,
    (bytes, objects, Some(nats)),
    PrimitiveSet::crypto_nat(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap();
  let callee = function(
    2,
    vec![
      (2, I::Primitive(35, vec![O::Local(0), O::Local(1)], 1)),
      (3, I::Ret(O::Local(2))),
    ],
  );
  let big = (1u128 << 80) + 137;
  for captured in [nat(big), V::Word(137)] {
    let valid = matches!(captured, V::Nat(_));
    let (code, input, output) = example(
      vec![
        function(
          1,
          vec![(1, I::TailApply(O::Local(0), vec![O::Literal(nat(5u32))]))],
        ),
        callee.clone(),
      ],
      &[V::Pap(1, vec![captured])],
      nat(big + 5),
    );
    run(&compiled, (revision(code), revision(input), revision(output)), valid);
  }
  let (code, input, output) = example(
    vec![function(0, vec![(0, I::TailApply(O::Literal(nat(big)), vec![]))])],
    &[],
    nat(big),
  );
  run(&compiled, (revision(code), revision(input), revision(output)), true);
}
