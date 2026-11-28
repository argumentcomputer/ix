//! Native BLS12-381 scalar arithmetic, `WidePackage` execution helpers, and
//! `affine-u80-v1` base-field/G1 encoding for the Aiur interpreter.
//!
//! Execution uses [`Bls12381Scalar`] (`ark_bls12_381::Fr`, 255-bit prime).
//! Base-field `Fq` coordinates (381-bit prime) use five little-endian limbs
//! (four 80-bit limbs + one 61-bit top limb = 381 bits, matching
//! `CurveOpsPure::Limb5` and `tools/gnark/aiur_plonk_pairing.go`).

use crate::kzg::field::Bls12381Scalar;
use aiur::{
  Execution, FieldWord, artifact::WidePackage, bytecode::CheckedProgram,
  field::FieldBackend, hints::HintChannels, maps::MapOverrides,
  trace::TracePlan,
};
use ark_bls12_381::{Bls12_381, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::{BigInteger, Field, PrimeField};
use num_bigint::BigUint;
use std::sync::Arc;

/// Bits per low limb in BLS12-381 `affine-u80-v1` coordinates.
pub const FQ_LIMB_BITS: usize = 80;
/// Bits in the high (fifth) limb of a 381-bit BLS12-381 `Fq` element (`4*80 + 61 = 381`).
pub const FQ_TOP_LIMB_BITS: usize = 61;
/// Number of `Fr` words encoding one BLS12-381 `Fq` coordinate (`CurveOpsPure::Limb5`).
pub const FQ_LIMBS: usize = 5;
/// Number of `Fr` words encoding one affine BLS12-381 G1 point (`5 + 5 + 1`).
pub const G1_WORDS: usize = 2 * FQ_LIMBS + 1;
/// Number of private terminal output words for a 2-point BLS12-381 pairing accumulator (`2 * 11`).
pub const ACCUMULATOR_WORDS: usize = 2 * G1_WORDS;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Bls12381;

impl FieldBackend for Bls12381 {
  type Element = Bls12381Scalar;
  type Word = FieldWord;
  const ALL_ELEMENTS_VALID: bool = true;

  fn modulus(self) -> FieldWord {
    FieldWord::from_limbs_le(Fr::MODULUS.0)
  }

  fn from_u64(self, value: u64) -> Bls12381Scalar {
    Bls12381Scalar::new(Fr::from(value))
  }

  fn from_word(self, value: FieldWord) -> Bls12381Scalar {
    let mut bytes = [0u8; 32];
    for (chunk, limb) in
      bytes.as_chunks_mut::<8>().0.iter_mut().zip(value.limbs_le())
    {
      *chunk = limb.to_le_bytes();
    }
    Bls12381Scalar::new(Fr::from_le_bytes_mod_order(&bytes))
  }

  fn to_word(self, value: Bls12381Scalar) -> FieldWord {
    FieldWord::from_limbs_le(value.canonical_limbs_le())
  }

  fn add(self, a: Bls12381Scalar, b: Bls12381Scalar) -> Bls12381Scalar {
    a + b
  }

  fn sub(self, a: Bls12381Scalar, b: Bls12381Scalar) -> Bls12381Scalar {
    a - b
  }

  fn neg(self, a: Bls12381Scalar) -> Bls12381Scalar {
    -a
  }

  fn mul(self, a: Bls12381Scalar, b: Bls12381Scalar) -> Bls12381Scalar {
    a * b
  }

  fn inverse(self, a: Bls12381Scalar) -> Option<Bls12381Scalar> {
    a.0.inverse().map(Bls12381Scalar::new)
  }
}

fn scalar_to_biguint(value: Bls12381Scalar) -> BigUint {
  BigUint::from_bytes_le(&value.0.into_bigint().to_bytes_le())
}

fn fq_modulus() -> BigUint {
  BigUint::from_bytes_le(&Fq::MODULUS.to_bytes_le())
}

fn biguint_to_scalar(value: &BigUint) -> Result<Bls12381Scalar, String> {
  let digits = value.to_u64_digits();
  if digits.len() > 4 {
    return Err("BLS12-381 limb exceeds scalar representation".into());
  }
  let mut limbs = [0u64; 4];
  limbs[..digits.len()].copy_from_slice(&digits);
  let word = FieldWord::from_limbs_le(limbs);
  if !Bls12381.contains(word) {
    return Err("BLS12-381 value reaches scalar modulus".into());
  }
  Ok(Bls12381.from_word(word))
}

/// Encode a canonical BLS12-381 `Fq` element into five little-endian limbs
/// (four 80-bit limbs + one 61-bit top limb = 381 bits).
pub fn encode_fq(value: Fq) -> [Bls12381Scalar; FQ_LIMBS] {
  let integer = BigUint::from_bytes_le(&value.into_bigint().to_bytes_le());
  let mask = (BigUint::from(1u8) << FQ_LIMB_BITS) - 1u8;
  std::array::from_fn(|i| {
    let limb = (&integer >> (FQ_LIMB_BITS * i)) & &mask;
    biguint_to_scalar(&limb).expect("80-bit limb is below BLS12-381 Fr")
  })
}

/// Decode five little-endian limbs without modular reduction.
/// Rejects limb widths exceeding `80` (low) / `61` (top) bits and values `>= Fq::MODULUS`.
pub fn decode_fq(values: &[Bls12381Scalar]) -> Result<Fq, String> {
  if values.len() != FQ_LIMBS {
    return Err("BLS12-381 Fq coordinate needs five limbs".into());
  }
  let mut total = BigUint::from(0u8);
  for (i, &word) in values.iter().enumerate() {
    let limb = scalar_to_biguint(word);
    let max_bits = if i + 1 == FQ_LIMBS {
      FQ_TOP_LIMB_BITS as u64
    } else {
      FQ_LIMB_BITS as u64
    };
    if limb.bits() > max_bits {
      return Err(format!(
        "BLS12-381 Fq limb {i} exceeds {max_bits}-bit range"
      ));
    }
    total += limb << (FQ_LIMB_BITS * i);
  }
  if total >= fq_modulus() {
    return Err("noncanonical BLS12-381 Fq coordinate".into());
  }
  Ok(Fq::from_le_bytes_mod_order(&total.to_bytes_le()))
}

/// Encode an affine BLS12-381 G1 point into 11 `Fr` words (`5 x + 5 y + inf`).
/// Infinity always encodes as all-zero coordinates with `inf = 1`.
pub fn encode_g1(point: G1Affine) -> [Bls12381Scalar; G1_WORDS] {
  let (x, y) = if point.infinity {
    (Fq::from(0u8), Fq::from(0u8))
  } else {
    (point.x, point.y)
  };
  let x = encode_fq(x);
  let y = encode_fq(y);
  std::array::from_fn(|i| match i {
    0..=4 => x[i],
    5..=9 => y[i - 5],
    _ => Bls12381.from_u64(u64::from(point.infinity)),
  })
}

/// Decode 11 `Fr` words into a validated BLS12-381 G1 subgroup point.
/// Enforces boolean infinity, zero coordinates at infinity, canonical `Fq`,
/// curve membership, and prime-order subgroup membership.
pub fn decode_g1(values: &[Bls12381Scalar]) -> Result<G1Affine, String> {
  if values.len() != G1_WORDS {
    return Err("BLS12-381 G1 point needs 11 fields".into());
  }
  let x = decode_fq(&values[..FQ_LIMBS])?;
  let y = decode_fq(&values[FQ_LIMBS..2 * FQ_LIMBS])?;
  match Bls12381.try_to_u64(values[2 * FQ_LIMBS])? {
    1 if x == Fq::from(0u8) && y == Fq::from(0u8) => Ok(G1Affine::identity()),
    0 => {
      if x == Fq::from(0u8) && y == Fq::from(0u8) {
        return Err(
          "noncanonical BLS12-381 G1 zero without infinity flag".into(),
        );
      }
      let point = G1Affine::new_unchecked(x, y);
      if point.is_on_curve() && point.is_in_correct_subgroup_assuming_on_curve()
      {
        Ok(point)
      } else {
        Err("BLS12-381 G1 point is not in the prime-order subgroup".into())
      }
    },
    _ => Err("noncanonical BLS12-381 G1 infinity encoding".into()),
  }
}

/// Canonical decimal `Fq` coordinates `[x.c0, x.c1, y.c0, y.c1]` for a BLS12-381 G2 anchor.
pub fn encode_g2_coordinates(point: &G2Affine) -> [String; 4] {
  [
    point.x.c0.to_string(),
    point.x.c1.to_string(),
    point.y.c0.to_string(),
    point.y.c1.to_string(),
  ]
}

/// Decode four canonical decimal `Fq` coordinates `[x.c0, x.c1, y.c0, y.c1]`
/// into a validated nonzero BLS12-381 G2 subgroup anchor.
pub fn decode_g2_coordinates(coords: &[String; 4]) -> Result<G2Affine, String> {
  let p = fq_modulus();
  let mut limbs = [Fq::from(0u8); 4];
  for (i, text) in coords.iter().enumerate() {
    let value = BigUint::parse_bytes(text.as_bytes(), 10)
      .ok_or("BLS12-381 G2 coordinate is not decimal")?;
    if value >= p || value.to_string() != *text {
      return Err("BLS12-381 G2 coordinate is not canonical decimal Fq".into());
    }
    limbs[i] = Fq::from_le_bytes_mod_order(&value.to_bytes_le());
  }
  let point = G2Affine::new_unchecked(
    Fq2::new(limbs[0], limbs[1]),
    Fq2::new(limbs[2], limbs[3]),
  );
  if point.is_zero()
    || !point.is_on_curve()
    || !point.is_in_correct_subgroup_assuming_on_curve()
  {
    return Err(
      "BLS12-381 G2 anchor is not a nonzero prime-order subgroup point".into(),
    );
  }
  Ok(point)
}

/// Decode the 22 terminal output words and check the 2-pair BLS12-381 pairing
/// equation `e(P0, G2_0) * e(P1, G2_1) == 1`.
pub fn check_pairing(
  output: &[Bls12381Scalar],
  anchors: [G2Affine; 2],
) -> Result<(), String> {
  if output.len() != ACCUMULATOR_WORDS {
    return Err("BLS12-381 terminal accumulator needs 22 words".into());
  }
  for point in &anchors {
    if point.is_zero()
      || !point.is_on_curve()
      || !point.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err("invalid BLS12-381 G2 pairing anchor".into());
    }
  }
  let pair = [decode_g1(&output[..G1_WORDS])?, decode_g1(&output[G1_WORDS..])?];
  if Bls12_381::multi_pairing(pair, anchors).0
    != <Bls12_381 as Pairing>::TargetField::from(1u8)
  {
    return Err(
      "BLS12-381 terminal accumulator fails the pairing check".into(),
    );
  }
  Ok(())
}

/// Full 256-bit statement digest as two canonical little-endian 128-bit limbs in BLS12-381 `Fr`.
pub fn statement_arguments(statement: &[u8; 32]) -> [Bls12381Scalar; 2] {
  std::array::from_fn(|index| {
    Bls12381Scalar::new(Fr::from(u128::from_le_bytes(
      statement.as_chunks::<16>().0[index],
    )))
  })
}

/// Decode a version-3 [`WidePackage`] and check that its modulus is BLS12-381 `Fr`.
pub fn decode_package(bytes: &[u8]) -> Result<WidePackage, String> {
  let package = WidePackage::decode(bytes)?;
  if package.program.modulus != Bls12381.modulus() {
    return Err("WidePackage modulus is not BLS12-381 Fr".into());
  }
  Ok(package)
}

/// Decode and validate a BLS12-381 [`WidePackage`] into a [`CheckedProgram`],
/// tracking depth when a trace section is present.
pub fn load_program(bytes: &[u8]) -> Result<CheckedProgram<Bls12381>, String> {
  let package = decode_package(bytes)?;
  let mut program = package.program.check_with(Bls12381)?;
  if let Some(trace) = &package.trace {
    program.track_depth(trace)?;
  }
  Ok(program)
}

/// Decode and validate a BLS12-381 [`WidePackage`] with its trace section into
/// a [`TracePlan`].
pub fn load_trace_plan(
  bytes: &[u8],
) -> Result<TracePlan<'static, Bls12381>, String> {
  let package = decode_package(bytes)?;
  let trace =
    package.trace.ok_or("BLS12-381 package has no compiler trace section")?;
  let mut program = package.program.check_with(Bls12381)?;
  program.track_depth(&trace)?;
  TracePlan::new(Arc::new(program), trace)
}

/// Register the standard `u32`, `u64`, and `ixcc` (`divmod`, `divmod64`) hint
/// channels for BLS12-381 execution.
pub fn register_standard_hints(
  hints: &mut HintChannels<Bls12381Scalar>,
) -> Result<(), String> {
  aiur::library::u32::register(hints, Bls12381)?;
  aiur::library::u64::register(hints, Bls12381)?;
  aiur::library::ixcc::register(hints, Bls12381)
}

/// Execute an already-checked BLS12-381 [`CheckedProgram`], optionally binding
/// universal Tier-2 guess advice from `advice_bytes`.
pub fn execute_program(
  program: &CheckedProgram<Bls12381>,
  entry: &str,
  args: Vec<Bls12381Scalar>,
  advice_bytes: Option<&[u8]>,
) -> Result<Execution<Bls12381>, String> {
  let mut hints = HintChannels::new();
  register_standard_hints(&mut hints)?;
  if let Some(advice_bytes) = advice_bytes {
    let advice_program = load_program(advice_bytes)?;
    aiur::library::ixcc::register_advice_program(
      &mut hints,
      program,
      advice_program,
    )?;
  }
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(program, &mut maps)?;
  program
    .prepare_hint_channels(&[], &hints)?
    .with_map_overrides(&maps)?
    .execute(entry, args)
    .map_err(|error| error.to_string())
}

/// Execute a BLS12-381 [`TracePlan`] so the returned [`Execution`] is bound to
/// `plan.program()` and ready for trace generation and SCS witness export.
pub fn execute_plan(
  plan: &TracePlan<'_, Bls12381>,
  entry: &str,
  args: Vec<Bls12381Scalar>,
  advice_bytes: Option<&[u8]>,
) -> Result<Execution<Bls12381>, String> {
  execute_program(plan.program(), entry, args, advice_bytes)
}

/// Decode and execute an `ixcc-aiur --field bls12-381` [`WidePackage`],
/// optionally binding universal Tier-2 guess advice from `advice_bytes`.
pub fn execute_package(
  bytes: &[u8],
  entry: &str,
  args: Vec<Bls12381Scalar>,
  advice_bytes: Option<&[u8]>,
) -> Result<Execution<Bls12381>, String> {
  let program = load_program(bytes)?;
  execute_program(&program, entry, args, advice_bytes)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::aiur_backend::Bn254;
  use aiur::{
    Program,
    bytecode::{Binary, Entry, Function, Instruction as I, Map, Table, Type},
    value::IoType,
  };
  use ark_ec::CurveGroup;
  use std::path::Path;

  fn bls_program(
    inputs: usize,
    outputs: usize,
    registers: usize,
    code: Vec<I<FieldWord>>,
  ) -> Program<FieldWord> {
    Program {
      version: aiur::bytecode::VERSION,
      modulus: Bls12381.modulus(),
      functions: vec![Function {
        name: "Prog::main".into(),
        params: vec![Type::Field; inputs],
        result: Type::Tuple { items: vec![Type::Field; outputs] },
        registers,
        code,
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: "Prog::main".into(),
        function: 0,
        inputs: vec![IoType::Field; inputs],
        output: Some(IoType::Tuple { items: vec![IoType::Field; outputs] }),
      }],
    }
  }

  #[test]
  fn field_backend_arithmetic_and_canonical_bounds() {
    let minus_one = Bls12381.neg(Bls12381.one());
    let minus_one_word = Bls12381.to_word(minus_one);
    // BLS12-381 Fr modulus exceeds BN254 Fr modulus, so -1 mod r_bls is out of
    // range for BN254 while canonical for BLS12-381.
    assert!(Bls12381.contains(minus_one_word));
    assert!(!Bn254.contains(minus_one_word));

    let high = FieldWord::from_limbs_le([11, 2, 3, 1]);
    let decoded = Bls12381.decode_words(&[minus_one_word, high]).unwrap();
    assert_eq!(decoded[0], minus_one);
    assert_eq!(Bls12381.to_word(decoded[1]), high);
    assert!(Bls12381.try_to_u64(decoded[0]).is_err());
    assert_eq!(
      Bls12381.try_to_u64(Bls12381.from_u64(u64::MAX)).unwrap(),
      u64::MAX
    );
    assert!(Bls12381.decode_words(&[Bls12381.modulus()]).is_err());
    assert!(
      Bls12381
        .decode_words(&[FieldWord::from_limbs_le([u64::MAX; 4])])
        .is_err()
    );
    assert_eq!(Bls12381.from_word(Bls12381.modulus()), Bls12381.zero());

    let seven = Bls12381.from_u64(7);
    let inv = Bls12381.inverse(seven).unwrap();
    assert_eq!(Bls12381.mul(seven, inv), Bls12381.one());
    assert!(Bls12381.inverse(Bls12381.zero()).is_none());
    assert_eq!(Bls12381.add(minus_one, Bls12381.one()), Bls12381.zero());
    assert_eq!(Bls12381.sub(Bls12381.zero(), Bls12381.one()), minus_one);
  }

  #[test]
  fn fq_g1_and_pairing_codec_with_negative_controls() {
    let g1 = G1Affine::generator();
    let g2 = G2Affine::generator();
    let tau = Fr::from(7u64);
    let tau_g1 = (g1 * tau).into_affine();
    let neg_g1 = -g1;
    let tau_g2 = (g2 * tau).into_affine();

    for point in [G1Affine::identity(), g1, neg_g1, tau_g1] {
      let encoded = encode_g1(point);
      assert_eq!(decode_g1(&encoded).unwrap(), point);
    }

    let mut acc = Vec::with_capacity(ACCUMULATOR_WORDS);
    acc.extend(encode_g1(tau_g1));
    acc.extend(encode_g1(neg_g1));
    check_pairing(&acc, [g2, tau_g2]).unwrap();

    // Infinity pair satisfies pairing check.
    let mut inf_acc = Vec::with_capacity(ACCUMULATOR_WORDS);
    inf_acc.extend(encode_g1(G1Affine::identity()));
    inf_acc.extend(encode_g1(G1Affine::identity()));
    check_pairing(&inf_acc, [g2, tau_g2]).unwrap();

    // Wrong G1 point fails pairing check.
    let mut bad_acc = Vec::with_capacity(ACCUMULATOR_WORDS);
    bad_acc.extend(encode_g1((g1 * Fr::from(8u64)).into_affine()));
    bad_acc.extend(encode_g1(neg_g1));
    assert!(check_pairing(&bad_acc, [g2, tau_g2]).is_err());

    // Wrong G2 anchor fails pairing check.
    let wrong_g2 = (g2 * Fr::from(8u64)).into_affine();
    assert!(check_pairing(&acc, [g2, wrong_g2]).is_err());

    // Non-canonical Fq coordinate (Fq::MODULUS) rejected.
    let p = fq_modulus();
    let mask = (BigUint::from(1u8) << FQ_LIMB_BITS) - 1u8;
    let noncanon: [Bls12381Scalar; FQ_LIMBS] = std::array::from_fn(|i| {
      biguint_to_scalar(&((&p >> (FQ_LIMB_BITS * i)) & &mask)).unwrap()
    });
    assert!(decode_fq(&noncanon).is_err());

    // Top limb overflow (>= 2^61) rejected.
    let mut overflow = encode_fq(Fq::from(1u64));
    overflow[4] = Bls12381.from_u64(1u64 << FQ_TOP_LIMB_BITS);
    assert!(decode_fq(&overflow).is_err());

    // Non-subgroup torsion point (0, 2) on y^2 = x^3 + 4 rejected.
    let torsion = G1Affine::new_unchecked(Fq::from(0u64), Fq::from(2u64));
    assert!(torsion.is_on_curve());
    assert!(!torsion.is_in_correct_subgroup_assuming_on_curve());
    assert!(decode_g1(&encode_g1(torsion)).is_err());

    // Non-boolean infinity flag and nonzero coords with infinity flag rejected.
    let mut bad_inf = encode_g1(G1Affine::identity());
    bad_inf[10] = Bls12381.from_u64(2);
    assert!(decode_g1(&bad_inf).is_err());
    bad_inf[10] = Bls12381.one();
    bad_inf[0] = Bls12381.one();
    assert!(decode_g1(&bad_inf).is_err());

    // G2 decimal coordinate round-trip and negative controls.
    let coords = encode_g2_coordinates(&tau_g2);
    assert_eq!(decode_g2_coordinates(&coords).unwrap(), tau_g2);
    let mut bad_coords = coords.clone();
    bad_coords[0] = format!("0{}", bad_coords[0]);
    assert!(decode_g2_coordinates(&bad_coords).is_err());
    let mut mod_coords = coords;
    mod_coords[0] = p.to_string();
    assert!(decode_g2_coordinates(&mod_coords).is_err());
  }

  #[test]
  fn wide_package_decode_and_execute_with_advice() {
    let minus_one = Bls12381.neg(Bls12381.one());
    let mut main_prog = bls_program(
      1,
      2,
      7,
      vec![
        I::Literal { dest: 1, value: Bls12381.to_word(minus_one) },
        I::Binary { dest: 2, operator: Binary::Add, left: 0, right: 1 },
        I::Hint {
          channel: "ixcc.guess.f1".into(),
          r#type: Type::Field,
          key_type: Type::Field,
          key: vec![0],
          dest: vec![3],
        },
        I::Literal { dest: 4, value: FieldWord::from(7u64) },
        I::Binary { dest: 5, operator: Binary::Add, left: 0, right: 4 },
        I::AssertEq {
          left: vec![3],
          right: vec![5],
          message: Some("bls guess mismatch".into()),
          runtime_check: true,
        },
        I::Call { function: 1, args: vec![5], dest: vec![6] },
        I::Ret { value: vec![2, 6] },
      ],
    );
    let key_word = FieldWord::from_limbs_le([42, 0, 0, 0]);
    main_prog.tables = vec![
      Table {
        name: "k".into(),
        r#type: Type::Tuple { items: vec![Type::Field] },
        rows: vec![vec![key_word]],
      },
      Table {
        name: "v".into(),
        r#type: Type::Field,
        rows: vec![vec![Bls12381.to_word(minus_one)]],
      },
    ];
    main_prog.maps = vec![Map {
      name: "lookup".into(),
      params: vec![Type::Field],
      result: Type::Field,
      input: 0,
      output: 1,
    }];

    let advice_prog = Program {
      version: aiur::bytecode::VERSION,
      modulus: Bls12381.modulus(),
      functions: vec![Function {
        name: "Prog::f1".into(),
        params: vec![Type::Field],
        result: Type::Field,
        registers: 3,
        code: vec![
          I::Literal { dest: 1, value: FieldWord::from(7u64) },
          I::Binary { dest: 2, operator: Binary::Add, left: 0, right: 1 },
          I::Ret { value: vec![2] },
        ],
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: "Prog::f1".into(),
        function: 0,
        inputs: vec![IoType::Field],
        output: Some(IoType::Field),
      }],
    };

    let main_bytes =
      WidePackage { program: main_prog, trace: None }.encode().unwrap();
    let advice_bytes =
      WidePackage { program: advice_prog, trace: None }.encode().unwrap();

    // BN254 check MUST reject a BLS12-381 package.
    let decoded = WidePackage::decode(&main_bytes).unwrap();
    assert!(decoded.program.check_with(Bn254).is_err());

    let record = execute_package(
      &main_bytes,
      "Prog::main",
      vec![Bls12381.from_u64(35)],
      Some(&advice_bytes),
    )
    .unwrap();
    assert_eq!(record.output, vec![Bls12381.from_u64(34), minus_one]);

    // Tampered advice must be rejected by the circuit's assertion.
    let checked_main = load_program(&main_bytes).unwrap();
    let checked_advice = load_program(&advice_bytes).unwrap();
    let mut bad_hints = HintChannels::new();
    register_standard_hints(&mut bad_hints).unwrap();
    aiur::library::ixcc::register_tampered_advice_program(
      &mut bad_hints,
      &checked_main,
      checked_advice,
      "ixcc.guess.f1",
    )
    .unwrap();
    let err = checked_main
      .prepare_hint_channels(&[], &bad_hints)
      .unwrap()
      .execute("Prog::main", vec![Bls12381.from_u64(35)])
      .unwrap_err()
      .to_string();
    assert!(err.contains("bls guess mismatch"), "unexpected error: {err}");
  }

  #[test]
  fn decodes_and_executes_real_ixcc_aiur_bls12_381_package_when_present() {
    let Ok(path) = std::env::var("IX_AIUR_BLS_IXA") else {
      return;
    };
    let bytes = std::fs::read(Path::new(&path)).unwrap();
    let plan = load_trace_plan(&bytes).unwrap();
    let entry = std::env::var("IX_AIUR_BLS_ENTRY")
      .unwrap_or_else(|_| plan.program().program().entries[0].name.clone());
    let args: Vec<Bls12381Scalar> = std::env::var("IX_AIUR_BLS_ARGS")
      .unwrap_or_default()
      .split(',')
      .filter(|s| !s.is_empty())
      .map(|s| Bls12381.from_u64(s.trim().parse::<u64>().unwrap()))
      .collect();
    let advice = std::env::var("IX_AIUR_BLS_ADVICE")
      .ok()
      .map(|p| std::fs::read(p).unwrap());
    let record =
      execute_plan(&plan, &entry, args.clone(), advice.as_deref()).unwrap();
    let trace = plan.generate(&record, &entry, &args, true).unwrap();
    plan.check(&record, &trace, &entry, &args).unwrap();
  }
}
