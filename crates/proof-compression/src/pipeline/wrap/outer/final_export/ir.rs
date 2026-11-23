use super::*;
use crate::kzg::{
  curve::{Bn254, KzgCurve},
  field::CurveScalar,
};
use std::{ops, sync::Mutex};

const OUTER_IR_DOMAIN: &[u8] = b"ix/outer-ir/v1";

fn serialize_scalar<C: KzgCurve, S: serde::Serializer>(
  value: &CurveScalar<C>,
  serializer: S,
) -> std::result::Result<S::Ok, S::Error> {
  serializer.serialize_str(&scalar(*value))
}

#[derive(serde::Serialize)]
#[serde(tag = "op", rename_all = "snake_case", bound = "")]
pub(super) enum Instruction<C: KzgCurve = Bn254> {
  Constant {
    #[serde(serialize_with = "serialize_scalar")]
    value: CurveScalar<C>,
  },
  Input {
    kind: &'static str,
    index: usize,
  },
  Add {
    a: usize,
    b: usize,
  },
  Sub {
    a: usize,
    b: usize,
  },
  Mul {
    a: usize,
    b: usize,
  },
  Inverse {
    a: usize,
  },
}

#[derive(serde::Serialize)]
#[serde(bound = "")]
pub(super) struct Program<C: KzgCurve = Bn254> {
  pub nodes: Vec<Instruction<C>>,
  pub assertions: Vec<usize>,
  pub coefficients: Vec<usize>,
  pub witnesses: Vec<usize>,
}

impl<C: KzgCurve> Default for Program<C> {
  fn default() -> Self {
    Self {
      nodes: Vec::new(),
      assertions: Vec::new(),
      coefficients: Vec::new(),
      witnesses: Vec::new(),
    }
  }
}

fn push_u32(out: &mut Vec<u8>, value: usize) {
  let value = u32::try_from(value).expect("OuterIR index fits in u32");
  out.extend_from_slice(&value.to_le_bytes());
}

fn push_u32_slice(out: &mut Vec<u8>, values: &[usize]) {
  push_u32(out, values.len());
  for &value in values {
    push_u32(out, value);
  }
}

impl<C: KzgCurve> Program<C> {
  /// Canonical deterministic binary encoding shared with Go (`tools/gnark`)
  /// and Lean (`OuterIR`).
  pub(super) fn encode(&self) -> Vec<u8> {
    let mut out = Vec::with_capacity(
      OUTER_IR_DOMAIN.len()
        + 16
        + self.nodes.len() * 9
        + (self.assertions.len()
          + self.coefficients.len()
          + self.witnesses.len())
          * 4,
    );
    out.extend_from_slice(OUTER_IR_DOMAIN);
    push_u32(&mut out, self.nodes.len());
    for node in &self.nodes {
      match *node {
        Instruction::Constant { value } => {
          out.push(0);
          let bytes = value.0.into_bigint().to_bytes_be();
          assert_eq!(bytes.len(), 32);
          out.extend_from_slice(&bytes);
        },
        Instruction::Input { kind, index } => {
          out.push(1);
          let kind_tag = match kind {
            "challenge" => 0u8,
            "value" => 1u8,
            "public" => 2u8,
            other => panic!("unknown OuterIR input kind: {other}"),
          };
          out.push(kind_tag);
          push_u32(&mut out, index);
        },
        Instruction::Add { a, b } => {
          out.push(2);
          push_u32(&mut out, a);
          push_u32(&mut out, b);
        },
        Instruction::Sub { a, b } => {
          out.push(3);
          push_u32(&mut out, a);
          push_u32(&mut out, b);
        },
        Instruction::Mul { a, b } => {
          out.push(4);
          push_u32(&mut out, a);
          push_u32(&mut out, b);
        },
        Instruction::Inverse { a } => {
          out.push(5);
          push_u32(&mut out, a);
        },
      }
    }
    push_u32_slice(&mut out, &self.assertions);
    push_u32_slice(&mut out, &self.coefficients);
    push_u32_slice(&mut out, &self.witnesses);
    out
  }

  /// Canonical 32-byte BLAKE3 digest of [`Program::encode`].
  pub(super) fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.encode()).as_bytes()
  }
}

pub(super) enum Term<'a, C: KzgCurve = Bn254> {
  Constant(CurveScalar<C>),
  Node(usize, &'a Mutex<Program<C>>),
}

impl<C: KzgCurve> Clone for Term<'_, C> {
  fn clone(&self) -> Self {
    *self
  }
}
impl<C: KzgCurve> Copy for Term<'_, C> {}

impl<'a, C: KzgCurve> Term<'a, C> {
  fn input(
    arena: &'a Mutex<Program<C>>,
    kind: &'static str,
    index: usize,
  ) -> Self {
    Self::push(arena, Instruction::Input { kind, index })
  }

  fn push(arena: &'a Mutex<Program<C>>, instruction: Instruction<C>) -> Self {
    let mut program = arena.lock().unwrap();
    let id = program.nodes.len();
    program.nodes.push(instruction);
    Self::Node(id, arena)
  }

  fn id(self, arena: &'a Mutex<Program<C>>) -> usize {
    match self {
      Self::Node(id, owner) => {
        assert!(std::ptr::eq(owner, arena));
        id
      },
      Self::Constant(value) => {
        let Self::Node(id, _) =
          Self::push(arena, Instruction::Constant { value })
        else {
          unreachable!()
        };
        id
      },
    }
  }

  fn binary(
    self,
    other: Self,
    native: impl FnOnce(CurveScalar<C>, CurveScalar<C>) -> CurveScalar<C>,
    operation: impl FnOnce(usize, usize) -> Instruction<C>,
  ) -> Self {
    let arena = match (self, other) {
      (Self::Constant(a), Self::Constant(b)) => {
        return Self::Constant(native(a, b));
      },
      (Self::Node(_, arena), _) | (_, Self::Node(_, arena)) => arena,
    };
    let a = self.id(arena);
    let b = other.id(arena);
    Self::push(arena, operation(a, b))
  }

  fn inverse(self) -> Self {
    match self {
      Self::Constant(v) => {
        Self::Constant(v.try_inverse().expect("zero constant denominator"))
      },
      Self::Node(a, arena) => Self::push(arena, Instruction::Inverse { a }),
    }
  }

  fn power_of_two(self, log: usize) -> Self {
    let mut value = self;
    for _ in 0..log {
      value *= value;
    }
    value
  }
}

impl<C: KzgCurve> From<CurveScalar<C>> for Term<'_, C> {
  fn from(value: CurveScalar<C>) -> Self {
    Self::Constant(value)
  }
}
impl<C: KzgCurve> Algebra<CurveScalar<C>> for Term<'_, C> {
  const ZERO: Self = Self::Constant(CurveScalar::<C>::ZERO);
  const ONE: Self = Self::Constant(CurveScalar::<C>::ONE);
}
impl<C: KzgCurve> ops::Add for Term<'_, C> {
  type Output = Self;
  fn add(self, rhs: Self) -> Self {
    self.binary(rhs, |a, b| a + b, |a, b| Instruction::Add { a, b })
  }
}
impl<C: KzgCurve> ops::Sub for Term<'_, C> {
  type Output = Self;
  fn sub(self, rhs: Self) -> Self {
    self.binary(rhs, |a, b| a - b, |a, b| Instruction::Sub { a, b })
  }
}
impl<C: KzgCurve> ops::Mul for Term<'_, C> {
  type Output = Self;
  fn mul(self, rhs: Self) -> Self {
    self.binary(rhs, |a, b| a * b, |a, b| Instruction::Mul { a, b })
  }
}
impl<C: KzgCurve> ops::Mul<CurveScalar<C>> for Term<'_, C> {
  type Output = Self;
  fn mul(self, rhs: CurveScalar<C>) -> Self {
    self * Self::Constant(rhs)
  }
}
impl<C: KzgCurve> ops::Neg for Term<'_, C> {
  type Output = Self;
  fn neg(self) -> Self {
    Self::ZERO - self
  }
}
impl<C: KzgCurve> ops::AddAssign for Term<'_, C> {
  fn add_assign(&mut self, rhs: Self) {
    *self = *self + rhs;
  }
}
impl<C: KzgCurve> ops::SubAssign for Term<'_, C> {
  fn sub_assign(&mut self, rhs: Self) {
    *self = *self - rhs;
  }
}
impl<C: KzgCurve> ops::MulAssign for Term<'_, C> {
  fn mul_assign(&mut self, rhs: Self) {
    *self = *self * rhs;
  }
}

/// One entry of a claim row: a circuit constant or the index of a public
/// scalar the verifier supplies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::pipeline::wrap::outer) enum ClaimSlot<C: KzgCurve = Bn254> {
  Constant(CurveScalar<C>),
  Public(usize),
}

pub(super) fn build<C: KzgCurve>(
  system: &System<KzgConfig<C>>,
  layout: &codegen::OpeningLayout<C>,
  claims: &[Vec<ClaimSlot<C>>],
) -> Result<Program<C>> {
  let circuits = system.circuits.len();
  if circuits != layout.accumulator_count + 1 {
    return Err("layout accumulator count differs from the system".into());
  }
  let public_count = claims
    .iter()
    .flatten()
    .filter_map(|slot| match slot {
      ClaimSlot::Public(index) => Some(index + 1),
      ClaimSlot::Constant(_) => None,
    })
    .max()
    .unwrap_or(0);
  let arena = Mutex::new(Program::<C>::default());
  let ch: [_; 6] = std::array::from_fn(|i| Term::input(&arena, "challenge", i));
  let values: Vec<_> =
    (0..layout.field_count).map(|i| Term::input(&arena, "value", i)).collect();
  let publics: Vec<_> =
    (0..public_count).map(|i| Term::input(&arena, "public", i)).collect();
  let [beta, gamma, alpha, zeta, v, r] = ch;
  let mut assertions = Vec::new();
  let mut accumulator = Term::ZERO;
  for row in claims {
    let message = row.iter().rev().fold(Term::ZERO, |acc, slot| {
      let value = match *slot {
        ClaimSlot::Constant(value) => Term::Constant(value),
        ClaimSlot::Public(index) => publics[index],
      };
      acc * gamma + value
    });
    accumulator += (beta + message).inverse();
  }
  // An inverse node enforces the forbidden-challenge rejection even if its output is unused.
  let _ = zeta.inverse();
  for (i, c) in system.circuits.iter().enumerate() {
    let graph = GraphProgram::<C>::compile(
      &c.graph,
      GraphInputs::for_circuit(system, i)?,
    )?;
    let height = c.preprocessed_height;
    let domain = system.config.pcs().natural_domain_for_degree(height);
    let omega = domain.generator();
    let vanishing = zeta.power_of_two(height.ilog2() as usize) - Term::ONE;
    let _ = vanishing.inverse();
    let first = vanishing * (zeta - Term::ONE).inverse();
    let last = vanishing * (zeta * omega - Term::ONE).inverse() * omega;
    let next = if i + 1 < circuits { values[i] } else { Term::ZERO };
    let cp = [beta, gamma, accumulator, next];
    let rows = |round: usize| {
      let m = &layout.matrices[round * circuits + i];
      let current = &values[m.value_offset..m.value_offset + m.width];
      let following = if m.rows == 2 {
        &values[m.value_offset + m.width..m.value_offset + 2 * m.width]
      } else {
        &[]
      };
      [current, following]
    };
    let stage2 = rows(1);
    let nodes = graph.evaluate(
      |matrix, offset| values[layout.matrices[matrix].value_offset + offset],
      &cp,
      first,
      last,
      zeta - Term::Constant(omega.inverse()),
    );
    let mut constraints = c.graph.constraint_values(&nodes);
    let ext = multi_stark::system::extension_params::<KzgConfig<C>>();
    if ext.degree != 1 {
      return Err(
        "PLONK scalar export requires a native-field KZG proof".into(),
      );
    }
    let delta = (next - accumulator)
      * (CurveScalar::<C>::from_usize(height) * omega).inverse();
    multi_stark::lookup::logup_constraint_values(
      &c.graph.lookups,
      &nodes,
      stage2[0],
      stage2[1],
      &cp,
      &[delta],
      last,
      ext.modulus,
      ext.degree,
      c.lookup_group_size.max(1),
      &mut constraints,
    );
    let composition = constraints
      .into_iter()
      .fold(Term::ZERO, |acc, value| acc * alpha + value);
    let zn = vanishing + Term::ONE;
    let quotient =
      rows(2)[0].iter().rev().fold(Term::ZERO, |acc, value| acc * zn + *value);
    assertions.push((composition - vanishing * quotient).id(&arena));
    accumulator = next;
  }
  let mut coefficients = vec![Term::ZERO; layout.coefficient_count];
  let mut witnesses = vec![];
  let mut rp = Term::ONE;
  for (group, factor) in layout.factors.iter().enumerate() {
    let mut vp = Term::ONE;
    let mut y = Term::ZERO;
    for matrix in &layout.matrices {
      for (row, &g) in matrix.groups[..matrix.rows].iter().enumerate() {
        if g != group {
          continue;
        }
        for column in 0..matrix.width {
          coefficients[matrix.point_offset + column] += rp * vp;
          y += values[matrix.value_offset + row * matrix.width + column] * vp;
          vp *= v;
        }
      }
    }
    coefficients[layout.generator_index] -= rp * y;
    coefficients[layout.commitment_count + group] += rp * zeta * *factor;
    witnesses.push(rp.id(&arena));
    rp *= r;
  }
  let coefficients = coefficients.into_iter().map(|v| v.id(&arena)).collect();
  let mut program = arena.into_inner().unwrap();
  program.assertions = assertions;
  program.coefficients = coefficients;
  program.witnesses = witnesses;
  Ok(program)
}

#[cfg(test)]
pub(super) fn parse_program_json<C: KzgCurve>(
  value: &serde_json::Value,
) -> Program<C> {
  use ark_ff::PrimeField;

  let parse_scalar = |s: &str| -> CurveScalar<C> {
    let hex_str = s.strip_prefix("0x").expect("0x prefix");
    assert_eq!(hex_str.len(), 64);
    let mut bytes = [0u8; 32];
    for (i, slot) in bytes.iter_mut().enumerate() {
      *slot = u8::from_str_radix(&hex_str[2 * i..2 * i + 2], 16).unwrap();
    }
    let fr = C::Fr::from_be_bytes_mod_order(&bytes);
    assert_eq!(fr.into_bigint().to_bytes_be(), bytes);
    CurveScalar::<C>(fr)
  };
  let usize_field = |obj: &serde_json::Value, key: &str| -> usize {
    usize::try_from(obj[key].as_u64().unwrap()).unwrap()
  };
  let usize_list = |key: &str| -> Vec<usize> {
    value[key]
      .as_array()
      .unwrap()
      .iter()
      .map(|entry| usize::try_from(entry.as_u64().unwrap()).unwrap())
      .collect()
  };
  let nodes = value["nodes"]
    .as_array()
    .unwrap()
    .iter()
    .map(|node| match node["op"].as_str().unwrap() {
      "constant" => Instruction::Constant {
        value: parse_scalar(node["value"].as_str().unwrap()),
      },
      "input" => Instruction::Input {
        kind: match node["kind"].as_str().unwrap() {
          "challenge" => "challenge",
          "value" => "value",
          "public" => "public",
          other => panic!("unknown input kind: {other}"),
        },
        index: usize_field(node, "index"),
      },
      "add" => Instruction::Add {
        a: usize_field(node, "a"),
        b: usize_field(node, "b"),
      },
      "sub" => Instruction::Sub {
        a: usize_field(node, "a"),
        b: usize_field(node, "b"),
      },
      "mul" => Instruction::Mul {
        a: usize_field(node, "a"),
        b: usize_field(node, "b"),
      },
      "inverse" => Instruction::Inverse { a: usize_field(node, "a") },
      other => panic!("unknown op: {other}"),
    })
    .collect();
  Program {
    nodes,
    assertions: usize_list("assertions"),
    coefficients: usize_list("coefficients"),
    witnesses: usize_list("witnesses"),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::Scalar;

  const EMPTY_DIGEST: &str =
    "0x02d95030e924d62b65dcb11734967f540cddd90337d58184d90f02197df5a799";
  const GOLDEN_DIGEST: &str =
    "0x3841d46e6b5730d0f1d9faba16072a2c3caed66c64f8e32ee5ebdb69a57a2b28";
  const FIXTURE_VK_DIGEST: &str =
    "0x764a1979c109cbc92bff867f7f929950438365adfe3c502a82700ed4d6f7a7b0";

  fn golden_program() -> Program {
    Program {
      nodes: vec![
        Instruction::Constant { value: Scalar::ZERO },
        Instruction::Constant { value: Scalar::from_u8(94) },
        Instruction::Constant { value: -Scalar::ONE },
        Instruction::Input { kind: "challenge", index: 5 },
        Instruction::Input { kind: "value", index: 258 },
        Instruction::Input { kind: "public", index: 22 },
        Instruction::Add { a: 1, b: 3 },
        Instruction::Sub { a: 6, b: 4 },
        Instruction::Mul { a: 7, b: 2 },
        Instruction::Inverse { a: 8 },
      ],
      assertions: vec![9, 0],
      coefficients: vec![6, 7, 8],
      witnesses: vec![5],
    }
  }

  #[test]
  fn empty_program_encoding_and_digest() {
    let program = Program::<Bn254>::default();
    let encoded = program.encode();
    let mut expected = b"ix/outer-ir/v1".to_vec();
    expected.extend_from_slice(&[0u8; 16]);
    assert_eq!(encoded, expected);
    assert_eq!(hex_json(&program.digest()), EMPTY_DIGEST);
  }

  #[test]
  fn golden_program_encoding_and_digest_matches_go() {
    let program = golden_program();
    let encoded = program.encode();
    assert_eq!(encoded.len(), 203);
    assert_eq!(&encoded[..14], b"ix/outer-ir/v1");
    assert_eq!(&encoded[14..18], &10u32.to_le_bytes());
    assert_eq!(encoded[18], 0);
    assert_eq!(&encoded[19..51], &[0u8; 32]);
    assert_eq!(encoded[51], 0);
    assert_eq!(&encoded[52..83], &[0u8; 31]);
    assert_eq!(encoded[83], 0x5e);
    assert_eq!(encoded[84], 0);
    assert_eq!(encoded[85], 0x30);
    assert_eq!(encoded[116], 0x00);
    assert_eq!(&encoded[117..123], &[1, 0, 5, 0, 0, 0]);
    assert_eq!(&encoded[123..129], &[1, 1, 2, 1, 0, 0]);
    assert_eq!(&encoded[129..135], &[1, 2, 22, 0, 0, 0]);
    assert_eq!(&encoded[135..144], &[2, 1, 0, 0, 0, 3, 0, 0, 0]);
    assert_eq!(&encoded[144..153], &[3, 6, 0, 0, 0, 4, 0, 0, 0]);
    assert_eq!(&encoded[153..162], &[4, 7, 0, 0, 0, 2, 0, 0, 0]);
    assert_eq!(&encoded[162..167], &[5, 8, 0, 0, 0]);
    let expected_outputs: Vec<u8> = [2u32, 9, 0, 3, 6, 7, 8, 1, 5]
      .into_iter()
      .flat_map(u32::to_le_bytes)
      .collect();
    assert_eq!(&encoded[167..203], expected_outputs.as_slice());
    assert_eq!(hex_json(&program.digest()), GOLDEN_DIGEST);
  }

  #[test]
  fn digest_changes_on_any_mutation() {
    let base = golden_program().digest();

    let mut p = golden_program();
    p.nodes[1] = Instruction::Constant { value: Scalar::from_u8(95) };
    assert_ne!(p.digest(), base);

    let mut p = golden_program();
    p.nodes[3] = Instruction::Input { kind: "value", index: 5 };
    assert_ne!(p.digest(), base);

    let mut p = golden_program();
    p.nodes[4] = Instruction::Input { kind: "value", index: 259 };
    assert_ne!(p.digest(), base);

    let mut p = golden_program();
    p.nodes[6] = Instruction::Mul { a: 1, b: 3 };
    assert_ne!(p.digest(), base);

    let mut p = golden_program();
    p.nodes[7] = Instruction::Sub { a: 4, b: 6 };
    assert_ne!(p.digest(), base);

    let mut p = golden_program();
    p.nodes.push(Instruction::Constant { value: Scalar::ZERO });
    assert_ne!(p.digest(), base);

    let mut p = golden_program();
    p.assertions[0] = 8;
    assert_ne!(p.digest(), base);

    let mut p = golden_program();
    p.coefficients[2] = 6;
    assert_ne!(p.digest(), base);

    let mut p = golden_program();
    p.witnesses[0] = 4;
    assert_ne!(p.digest(), base);
  }

  #[test]
  fn constant_json_serialization_matches_scalar_hex() {
    let p = Program {
      nodes: vec![
        Instruction::Constant { value: Scalar::ZERO },
        Instruction::Constant { value: Scalar::from_u8(94) },
        Instruction::Constant { value: -Scalar::ONE },
      ],
      ..Program::default()
    };
    let json = serde_json::to_value(&p).unwrap();
    assert_eq!(json["nodes"][0]["op"], "constant");
    assert_eq!(json["nodes"][0]["value"], scalar(Scalar::ZERO));
    assert_eq!(json["nodes"][1]["value"], scalar(Scalar::from_u8(94)));
    assert_eq!(json["nodes"][2]["value"], scalar(-Scalar::ONE));
  }

  #[test]
  fn fixture_vk_program_digest_matches_go() {
    let raw: serde_json::Value = serde_json::from_slice(include_bytes!(
      "../../../../../../../tools/gnark/testdata/bn254/vk.json"
    ))
    .unwrap();
    let program = parse_program_json::<Bn254>(&raw["program"]);
    assert_eq!(hex_json(&program.digest()), FIXTURE_VK_DIGEST);
    assert_eq!(raw["programDigest"].as_str().unwrap(), FIXTURE_VK_DIGEST);
  }
}
