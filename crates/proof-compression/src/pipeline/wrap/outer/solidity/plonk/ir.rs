use super::*;
use std::{ops, sync::Mutex};

#[derive(serde::Serialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub(super) enum Instruction {
  Constant { value: String },
  Input { kind: &'static str, index: usize },
  Add { a: usize, b: usize },
  Sub { a: usize, b: usize },
  Mul { a: usize, b: usize },
  Inverse { a: usize },
}

#[derive(Default, serde::Serialize)]
pub(super) struct Program {
  pub nodes: Vec<Instruction>,
  pub assertions: Vec<usize>,
  pub coefficients: Vec<usize>,
  pub witnesses: Vec<usize>,
}

#[derive(Clone, Copy)]
pub(super) enum Term<'a> {
  Constant(Scalar),
  Node(usize, &'a Mutex<Program>),
}

impl<'a> Term<'a> {
  fn input(
    arena: &'a Mutex<Program>,
    kind: &'static str,
    index: usize,
  ) -> Self {
    Self::push(arena, Instruction::Input { kind, index })
  }

  fn push(arena: &'a Mutex<Program>, instruction: Instruction) -> Self {
    let mut program = arena.lock().unwrap();
    let id = program.nodes.len();
    program.nodes.push(instruction);
    Self::Node(id, arena)
  }

  fn id(self, arena: &'a Mutex<Program>) -> usize {
    match self {
      Self::Node(id, owner) => {
        assert!(std::ptr::eq(owner, arena));
        id
      },
      Self::Constant(value) => {
        let Self::Node(id, _) =
          Self::push(arena, Instruction::Constant { value: scalar(value) })
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
    native: impl FnOnce(Scalar, Scalar) -> Scalar,
    operation: impl FnOnce(usize, usize) -> Instruction,
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

impl From<Scalar> for Term<'_> {
  fn from(value: Scalar) -> Self {
    Self::Constant(value)
  }
}
impl Algebra<Scalar> for Term<'_> {
  const ZERO: Self = Self::Constant(Scalar::ZERO);
  const ONE: Self = Self::Constant(Scalar::ONE);
}
impl ops::Add for Term<'_> {
  type Output = Self;
  fn add(self, rhs: Self) -> Self {
    self.binary(rhs, |a, b| a + b, |a, b| Instruction::Add { a, b })
  }
}
impl ops::Sub for Term<'_> {
  type Output = Self;
  fn sub(self, rhs: Self) -> Self {
    self.binary(rhs, |a, b| a - b, |a, b| Instruction::Sub { a, b })
  }
}
impl ops::Mul for Term<'_> {
  type Output = Self;
  fn mul(self, rhs: Self) -> Self {
    self.binary(rhs, |a, b| a * b, |a, b| Instruction::Mul { a, b })
  }
}
impl ops::Mul<Scalar> for Term<'_> {
  type Output = Self;
  fn mul(self, rhs: Scalar) -> Self {
    self * Self::Constant(rhs)
  }
}
impl ops::Neg for Term<'_> {
  type Output = Self;
  fn neg(self) -> Self {
    Self::ZERO - self
  }
}
impl ops::AddAssign for Term<'_> {
  fn add_assign(&mut self, rhs: Self) {
    *self = *self + rhs;
  }
}
impl ops::SubAssign for Term<'_> {
  fn sub_assign(&mut self, rhs: Self) {
    *self = *self - rhs;
  }
}
impl ops::MulAssign for Term<'_> {
  fn mul_assign(&mut self, rhs: Self) {
    *self = *self * rhs;
  }
}

pub(super) fn build(
  system: &System<KzgConfig>,
  layout: &codegen::OpeningLayout,
) -> Result<Program> {
  let arena = Mutex::new(Program::default());
  let ch: [_; 6] = std::array::from_fn(|i| Term::input(&arena, "challenge", i));
  let values: Vec<_> =
    (0..layout.field_count).map(|i| Term::input(&arena, "value", i)).collect();
  let publics: Vec<_> =
    (0..23).map(|i| Term::input(&arena, "public", i)).collect();
  let [beta, gamma, alpha, zeta, v, r] = ch;
  let mut assertions = Vec::new();
  let mut accumulator = Term::ZERO;
  for (i, value) in publics.iter().copied().enumerate() {
    let row = [
      Term::Constant(Scalar::from_u8(94)),
      Term::ONE,
      Term::Constant(Scalar::from_usize(i)),
      value,
    ];
    let message =
      row.into_iter().rev().fold(Term::ZERO, |acc, value| acc * gamma + value);
    accumulator += (beta + message).inverse();
  }
  // An inverse node enforces the forbidden-challenge rejection even if its output is unused.
  let _ = zeta.inverse();
  for (i, c) in system.circuits.iter().enumerate() {
    GraphProgram::compile(&c.graph, GraphInputs::for_circuit(system, i)?)?;
    let height = c.preprocessed_height;
    let domain = system.config.pcs().natural_domain_for_degree(height);
    let omega = domain.generator();
    let vanishing = zeta.power_of_two(height.ilog2() as usize) - Term::ONE;
    let _ = vanishing.inverse();
    let first = vanishing * (zeta - Term::ONE).inverse();
    let last = vanishing * (zeta * omega - Term::ONE).inverse() * omega;
    let next = if i == 0 { values[0] } else { Term::ZERO };
    let cp = [beta, gamma, accumulator, next];
    let rows = |round: usize| {
      let m = &layout.matrices[round * 2 + i];
      let current = &values[m.value_offset..m.value_offset + m.width];
      let following = if m.rows == 2 {
        &values[m.value_offset + m.width..m.value_offset + 2 * m.width]
      } else {
        &[]
      };
      [current, following]
    };
    let stage2 = rows(1);
    let view = VarValues {
      main: rows(0),
      preprocessed: rows(3),
      stage2,
      publics: &cp,
      is_first_row: first,
      is_last_row: last,
      is_transition: zeta - Term::Constant(omega.inverse()),
    };
    let mut nodes = Vec::new();
    c.graph.sweep(&view, &mut nodes);
    let mut constraints = c.graph.constraint_values(&nodes);
    let ext = multi_stark::system::extension_params::<KzgConfig>();
    if ext.degree != 1 {
      return Err(
        "PLONK scalar export requires a native-field KZG proof".into(),
      );
    }
    let delta =
      (next - accumulator) * (Scalar::from_usize(height) * omega).inverse();
    multi_stark::lookup::logup_constraint_values(
      &c.graph.lookups,
      &nodes,
      stage2[0],
      stage2[1],
      &cp,
      &[delta],
      last,
      ext.w,
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
