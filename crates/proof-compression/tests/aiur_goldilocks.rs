use aiur::{
  FieldWord,
  artifact::WidePackage,
  bytecode::{CheckedProgram, Instruction},
  field::FieldBackend,
  hints::HintChannels,
  library::{goldilocks, io::Streams},
  maps::MapOverrides,
};
use ix_proof_compression::{aiur_backend::Bn254, kzg::Scalar};
use multi_stark::{
  p3_field::{Field, PrimeCharacteristicRing, PrimeField64},
  types::Val,
};
use std::sync::OnceLock;

const FIXTURE: &[u8] =
  include_bytes!("../../aiur/tests/fixtures/goldilocks-emulated.ixa");
const P: u64 = goldilocks::MODULUS;

fn program() -> &'static CheckedProgram<Bn254> {
  static PROGRAM: OnceLock<CheckedProgram<Bn254>> = OnceLock::new();
  PROGRAM.get_or_init(|| {
    WidePackage::decode(FIXTURE).unwrap().program.check_with(Bn254).unwrap()
  })
}

fn scalar(value: u64) -> Scalar {
  Bn254.from_u64(value)
}

fn product(a: u64, b: u64) -> u64 {
  u64::try_from(u128::from(a) * u128::from(b) % u128::from(P)).unwrap()
}

fn sum(a: u64, b: u64) -> u64 {
  u64::try_from((u128::from(a) + u128::from(b)) % u128::from(P)).unwrap()
}

fn difference(a: u64, b: u64) -> u64 {
  u64::try_from((u128::from(a) + u128::from(P) - u128::from(b)) % u128::from(P))
    .unwrap()
}

#[test]
fn emulated_operations_match_native_goldilocks_at_boundaries() {
  let prepared =
    stark_verifier::prepare_compress_gl(program(), &Streams::default())
      .unwrap();
  let run = |entry: &str, args: &[u64]| {
    prepared
      .execute(
        &format!("EmulatedGL::{entry}"),
        args.iter().copied().map(scalar).collect(),
      )
      .unwrap()
      .output
  };
  let mut cases = vec![0, 1, 2, 7, (1 << 32) - 1, 1 << 32, P / 2, P - 2, P - 1];
  let mut state = 0x95a7_3be8_4cf1_02d6u64;
  for _ in 0..16 {
    state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
    cases.push(state % P);
  }
  for &a in &cases {
    let inverse =
      Val::from_u64(a).try_inverse().unwrap_or(Val::ZERO).as_canonical_u64();
    assert_eq!(run("inverse", &[a]), [scalar(inverse)]);
    assert_eq!(run("neg", &[a]), [scalar(if a == 0 { 0 } else { P - a })]);
    assert_eq!(run("is_zero", &[a]), [scalar(u64::from(a == 0))]);
    for &b in &cases {
      assert_eq!(run("add", &[a, b]), [scalar(sum(a, b))]);
      assert_eq!(run("sub", &[a, b]), [scalar(difference(a, b))]);
      assert_eq!(run("mul", &[a, b]), [scalar(product(a, b))]);
      assert_eq!(run("eq", &[a, b]), [scalar(u64::from(a == b))]);
    }
  }
  assert_ne!(
    scalar(Val::from_u64(7).try_inverse().unwrap().as_canonical_u64()),
    Bn254.inverse(scalar(7)).unwrap(),
  );
}

#[test]
fn reducing_and_canonical_byte_boundaries_remain_distinct() {
  let prepared =
    stark_verifier::prepare_compress_gl(program(), &Streams::default())
      .unwrap();
  for value in [0, 1, P - 1, P, P + 1, u64::MAX] {
    let bytes: Vec<_> =
      value.to_le_bytes().map(|b| scalar(u64::from(b))).into();
    let reduced =
      prepared.execute("EmulatedGL::reduce", bytes.clone()).unwrap();
    assert_eq!(reduced.output, [scalar(value % P)]);
    let canonical = prepared.execute("EmulatedGL::decode", bytes);
    if value < P {
      assert_eq!(canonical.unwrap().output, [scalar(value)]);
      let encoded =
        prepared.execute("EmulatedGL::encode", vec![scalar(value)]).unwrap();
      assert_eq!(
        encoded.output,
        value.to_le_bytes().map(|b| scalar(u64::from(b)))
      );
    } else {
      assert!(canonical.is_err());
      assert!(
        prepared.execute("EmulatedGL::encode", vec![scalar(value)]).is_err()
      );
    }
  }
  let two_to_64 = Bn254.from_word(FieldWord::from_limbs_le([0, 1, 0, 0]));
  for entry in ["encode", "inverse", "neg", "is_zero"] {
    assert!(
      prepared
        .execute(&format!("EmulatedGL::{entry}"), vec![two_to_64])
        .is_err()
    );
  }
  for entry in ["add", "sub", "mul", "eq"] {
    for value in [scalar(P), scalar(P + 1), two_to_64] {
      assert!(
        prepared
          .execute(&format!("EmulatedGL::{entry}"), vec![value, scalar(1)])
          .is_err()
      );
    }
  }
}

#[test]
fn quadratic_extension_uses_nonresidue_seven() {
  let prepared =
    stark_verifier::prepare_compress_gl(program(), &Streams::default())
      .unwrap();
  let run = |entry: &str, args: &[u64]| {
    prepared
      .execute(
        &format!("EmulatedGL::{entry}"),
        args.iter().copied().map(scalar).collect(),
      )
      .unwrap()
      .output
  };
  for (a, b) in
    [([0, 1], [0, 1]), ([3, 5], [7, 11]), ([P - 1, P - 2], [7, P - 1])]
  {
    let expected = [
      sum(product(a[0], b[0]), product(7, product(a[1], b[1]))),
      sum(product(a[0], b[1]), product(a[1], b[0])),
    ];
    assert_eq!(
      run("extension_mul", &[a[0], a[1], b[0], b[1]]),
      expected.map(scalar)
    );
    let inverse = run("extension_inverse", &a);
    let roundtrip = prepared
      .execute(
        "EmulatedGL::extension_mul",
        vec![scalar(a[0]), scalar(a[1]), inverse[0], inverse[1]],
      )
      .unwrap()
      .output;
    assert_eq!(roundtrip, [scalar(1), scalar(0)]);
  }
  assert_eq!(run("extension_inverse", &[0, 0]), [scalar(0), scalar(0)]);
}

fn forged(entry: &str, args: &[u64], channel: &str, answer: &[u64]) -> String {
  let mut package = WidePackage::decode(FIXTURE).unwrap();
  let mut signature = None;
  for function in &mut package.program.functions {
    for instruction in &mut function.code {
      if let Instruction::Hint { channel: name, r#type, key_type, .. } =
        instruction
        && name == channel
      {
        // Advice names select providers; these programs retain the original
        // arithmetic and assertions while receiving an adversarial answer.
        *name = "test.forged".into();
        signature = Some((key_type.clone(), r#type.clone()));
      }
    }
  }
  let (input, output) = signature.expect("fixture contains the advice channel");
  let checked = package.program.check_with(Bn254).unwrap();
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, Bn254).unwrap();
  aiur::library::u64::register(&mut channels, Bn254).unwrap();
  goldilocks::register(&mut channels, Bn254).unwrap();
  let answer: Vec<_> = answer.iter().copied().map(scalar).collect();
  channels
    .insert("test.forged", input, output, move |_, output| {
      output.copy_from_slice(&answer);
      Ok(())
    })
    .unwrap();
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(&checked, &mut maps).unwrap();
  let prepared = checked
    .prepare_hint_channels(&[], &channels)
    .unwrap()
    .with_map_overrides(&maps)
    .unwrap();
  match prepared.execute(
    &format!("EmulatedGL::{entry}"),
    args.iter().copied().map(scalar).collect(),
  ) {
    Ok(_) => panic!("forged {channel} advice was accepted"),
    Err(error) => error.to_string(),
  }
}

#[test]
fn arithmetic_and_range_constraints_reject_forged_advice() {
  assert!(
    forged("add", &[P - 1, P - 1], "goldilocks.emulated.add", &[P - 2, 2])
      .contains("carry")
  );
  assert!(
    forged("add", &[1, 1], "goldilocks.emulated.add", &[3, 0])
      .contains("addition relation")
  );
  assert!(
    forged("sub", &[3, 4], "goldilocks.emulated.sub", &[P - 1, 0])
      .contains("subtraction relation")
  );
  assert!(
    forged(
      "mul",
      &[3, 4],
      "goldilocks.emulated.mul",
      &[P + 12, 0, 0, 0, 0, 0, 0, 0, 0]
    )
    .contains("noncanonical")
  );
  assert!(
    forged(
      "mul",
      &[P - 1, P - 1],
      "goldilocks.emulated.mul",
      &[1, 0, 0, 0, 0, 0, 0, 0, 0]
    )
    .contains("multiplication relation")
  );
  assert!(
    !forged(
      "mul",
      &[1, 1],
      "goldilocks.emulated.mul",
      &[1, 256, 0, 0, 0, 0, 0, 0, 0]
    )
    .is_empty()
  );
  assert!(
    forged("inverse", &[7], "goldilocks.emulated.inverse", &[1])
      .contains("inverse relation")
  );
  assert!(
    forged("inverse", &[0], "goldilocks.emulated.inverse", &[1])
      .contains("zero inverse")
  );
  assert!(
    !forged("encode", &[0], "bytes_le", &[256, 0, 0, 0, 0, 0, 0, 0]).is_empty()
  );
}
