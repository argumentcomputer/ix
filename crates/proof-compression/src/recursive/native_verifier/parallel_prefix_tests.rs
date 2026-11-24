use super::*;
use crate::kzg::curve::Bls12381;
use crate::recursive::native_field::limb_count;
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use multi_stark::plonkish::{Assignment, WitnessError};

struct PointFixture<C: KzgCurve> {
  circuit: Circuit<CurveScalar<C>>,
  inputs: Vec<(Value, CurveScalar<C>)>,
  expected_publics: Vec<CurveScalar<C>>,
  prefix_ends: Vec<usize>,
}

fn points<C: KzgCurve>(count: usize) -> Vec<G1AffineOf<C>> {
  let g = G1AffineOf::<C>::generator();
  let seven = (g * C::Fr::from(7u8)).into_affine();
  (0..count)
    .map(|i| match i % 8 {
      0 => G1AffineOf::<C>::identity(),
      1 | 2 => g,
      3 => -g,
      4 => seven,
      5 => -seven,
      _ => {
        let scalar = C::Fr::from_le_bytes_mod_order(
          blake3::hash(&(i as u64).to_le_bytes()).as_bytes(),
        );
        (g * scalar).into_affine()
      },
    })
    .collect()
}

impl<C: KzgCurve> PointFixture<C> {
  fn new(points: &[G1AffineOf<C>], parallel: bool) -> Self {
    let mut c = Context::<C>::new(Builder::<C>::new());
    let generator = G1AffineOf::<C>::generator();
    c.point(PointSource::Fixed(generator));
    let first_end = c.point_ends.clone();
    c.point(PointSource::Fixed(generator));
    assert_eq!(c.point_ends, first_end);
    c.point(PointSource::Fixed(G1AffineOf::<C>::identity()));
    for i in 0..points.len() {
      c.point(PointSource::Witness(i));
    }
    c.point(PointSource::Fixed(generator));
    let prefix_ends = c.point_ends.clone();
    assert_eq!(prefix_ends.last(), Some(&c.b.stats().values));
    assert!(prefix_ends.windows(2).all(|pair| pair[0] < pair[1]));
    let certified = parallel && c.seal_point_prefix();
    assert_eq!(certified, parallel);

    let mut inputs = Vec::new();
    let mut expected_publics = Vec::new();
    for binding in &c.points {
      let point = match binding.source {
        PointSource::Fixed(point) => point,
        PointSource::Witness(index) => {
          inputs.extend(binding.point.inputs(points[index]));
          points[index]
        },
        PointSource::Commitment { .. } => unreachable!(),
      };
      let mut encoded = Vec::new();
      point.serialize_compressed(&mut encoded).unwrap();
      expected_publics
        .extend(encoded.into_iter().map(CurveScalar::<C>::from_u8));
    }

    let dependencies: Vec<_> =
      c.encodings.iter().flatten().map(|byte| byte.value()).collect();
    for &value in &dependencies {
      c.b.expose_public(value);
    }
    // This opaque suffix hint reads derived values from every point block.
    let sum = c.b.hint("point encoding sum", &dependencies, |values| {
      Ok(
        values
          .iter()
          .copied()
          .fold(CurveScalar::<C>::ZERO, |sum, value| sum + value),
      )
    });
    let terms: Vec<_> = dependencies
      .iter()
      .map(|&value| (CurveScalar::<C>::ONE, value))
      .collect();
    let constrained_sum =
      c.b.linear_combination(&terms, CurveScalar::<C>::ZERO);
    c.b.assert_equal(sum, constrained_sum);
    c.b.expose_public(sum);
    expected_publics.push(
      expected_publics
        .iter()
        .copied()
        .fold(CurveScalar::<C>::ZERO, |sum, value| sum + value),
    );
    Self { circuit: c.b.finish(), inputs, expected_publics, prefix_ends }
  }

  fn generate(&self) -> Result<Assignment<CurveScalar<C>>, WitnessError> {
    self.generate_changed(None, None)
  }

  fn generate_changed(
    &self,
    missing: Option<usize>,
    corrupt: Option<usize>,
  ) -> Result<Assignment<CurveScalar<C>>, WitnessError> {
    let mut witness = self.circuit.witness();
    for (i, &(input, mut value)) in self.inputs.iter().enumerate() {
      if Some(i) == missing {
        continue;
      }
      if Some(i) == corrupt {
        value += CurveScalar::<C>::ONE;
      }
      witness.set(input, value)?;
    }
    witness.generate()
  }
}

fn same_relation<C: KzgCurve>(a: &PointFixture<C>, b: &PointFixture<C>) {
  assert_eq!(a.circuit.stats(), b.circuit.stats());
  assert_eq!(a.prefix_ends, b.prefix_ends);
  assert!(
    a.inputs
      .iter()
      .map(|(wire, value)| (wire.index(), value))
      .eq(b.inputs.iter().map(|(wire, value)| (wire.index(), value)))
  );
  for (a, b) in a.circuit.gates().iter().zip(b.circuit.gates()) {
    assert_eq!(a.wires.map(Value::index), b.wires.map(Value::index));
    assert_eq!(a.coefficients, b.coefficients);
  }
  for (a, b) in a.circuit.lookups().iter().zip(b.circuit.lookups()) {
    assert_eq!(a.table.index(), b.table.index());
    assert!(
      a.values
        .iter()
        .map(|wire| wire.index())
        .eq(b.values.iter().map(|wire| wire.index()))
    );
  }
  for (a, b) in a.circuit.tables().iter().zip(b.circuit.tables()) {
    assert_eq!(a.name(), b.name());
    assert_eq!(a.rows(), b.rows());
  }
  assert!(
    a.circuit
      .public_values()
      .iter()
      .map(|wire| wire.index())
      .eq(b.circuit.public_values().iter().map(|wire| wire.index()))
  );
  assert_eq!(a.expected_publics, b.expected_publics);
}

fn test_point_prefix_matches_serial<C: KzgCurve>() {
  let points = points::<C>(9);
  let serial = PointFixture::<C>::new(&points, false);
  let parallel = PointFixture::<C>::new(&points, true);
  same_relation(&serial, &parallel);
  let expected = serial.generate().unwrap();
  let actual = parallel.generate().unwrap();
  assert!(
    expected.values(serial.circuit.id()).unwrap()
      == actual.values(parallel.circuit.id()).unwrap()
  );
  assert_eq!(actual.public_values(), parallel.expected_publics);
  assert_eq!(expected.public_values(), actual.public_values());
  assert!(
    parallel.circuit.num_values() > *parallel.prefix_ends.last().unwrap()
  );
  assert_eq!(
    parallel.circuit.stats().inputs,
    (2 * limb_count::<C>() + 1) * points.len()
  );
}

#[test]
fn point_prefix_matches_serial_inputs_values_and_encodings() {
  test_point_prefix_matches_serial::<Bn254>();
  test_point_prefix_matches_serial::<Bls12381>();
}

fn test_point_prefix_preserves_earliest_error<C: KzgCurve>() {
  let points = points::<C>(4);
  let serial = PointFixture::<C>::new(&points, false);
  let parallel = PointFixture::<C>::new(&points, true);
  let stride = 2 * limb_count::<C>() + 1;
  for (missing, corrupt) in [
    (Some(0), None),
    (Some(2 * stride - 1), None),
    (Some(4 * stride - 1), None),
    (None, Some(stride)),
    (Some(0), Some(stride)),
    (Some(3 * stride), Some(stride)),
    (Some(3 * stride), Some(2 * stride)),
  ] {
    let expected = serial.generate_changed(missing, corrupt).err().unwrap();
    let actual = parallel.generate_changed(missing, corrupt).err().unwrap();
    assert_eq!(actual, expected, "missing={missing:?}, corrupt={corrupt:?}");
  }
}

#[test]
fn point_prefix_preserves_earliest_point_error() {
  test_point_prefix_preserves_earliest_error::<Bn254>();
  test_point_prefix_preserves_earliest_error::<Bls12381>();
}
