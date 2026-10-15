use super::*;
use ark_bls12_381::Fr;
use ark_ec::AffineRepr;
use ark_ff::PrimeField;
use multi_stark::plonkish::{Assignment, WitnessError};
use std::time::Instant;

struct PointFixture {
  circuit: Circuit<Scalar>,
  inputs: Vec<(Value, Scalar)>,
  expected_publics: Vec<Scalar>,
  prefix_ends: Vec<usize>,
  certified: bool,
}

fn points(count: usize) -> Vec<G1Affine> {
  let g = G1Affine::generator();
  let seven = (g * Fr::from(7u8)).into_affine();
  (0..count)
    .map(|i| match i % 8 {
      0 => G1Affine::identity(),
      1 | 2 => g,
      3 => -g,
      4 => seven,
      5 => -seven,
      _ => {
        let scalar = Fr::from_le_bytes_mod_order(
          blake3::hash(&(i as u64).to_le_bytes()).as_bytes(),
        );
        (g * scalar).into_affine()
      },
    })
    .collect()
}

impl PointFixture {
  fn new(points: &[G1Affine], parallel: bool) -> Self {
    let mut c = Context::new(Builder::new());
    let generator = G1Affine::generator();
    c.point(PointSource::Fixed(generator));
    let first_end = c.point_ends.clone();
    c.point(PointSource::Fixed(generator));
    assert_eq!(c.point_ends, first_end);
    c.point(PointSource::Fixed(G1Affine::identity()));
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
      expected_publics.extend(encoded.into_iter().map(Scalar::from_u8));
    }

    let dependencies: Vec<_> =
      c.encodings.iter().flatten().map(|byte| byte.value()).collect();
    for &value in &dependencies {
      c.b.expose_public(value);
    }
    // This opaque suffix hint reads derived values from every point block.
    let sum = c.b.hint("point encoding sum", &dependencies, |values| {
      Ok(values.iter().copied().fold(Scalar::ZERO, |sum, value| sum + value))
    });
    let terms: Vec<_> =
      dependencies.iter().map(|&value| (Scalar::ONE, value)).collect();
    let constrained_sum = c.b.linear_combination(&terms, Scalar::ZERO);
    c.b.assert_equal(sum, constrained_sum);
    c.b.expose_public(sum);
    expected_publics.push(
      expected_publics
        .iter()
        .copied()
        .fold(Scalar::ZERO, |sum, value| sum + value),
    );
    Self {
      circuit: c.b.finish(),
      inputs,
      expected_publics,
      prefix_ends,
      certified,
    }
  }

  fn generate(&self) -> Result<Assignment<Scalar>, WitnessError> {
    self.generate_changed(None, None)
  }

  fn generate_changed(
    &self,
    missing: Option<usize>,
    corrupt: Option<usize>,
  ) -> Result<Assignment<Scalar>, WitnessError> {
    let mut witness = self.circuit.witness();
    for (i, &(input, mut value)) in self.inputs.iter().enumerate() {
      if Some(i) == missing {
        continue;
      }
      if Some(i) == corrupt {
        value += Scalar::ONE;
      }
      witness.set(input, value)?;
    }
    witness.generate()
  }
}

fn same_relation(a: &PointFixture, b: &PointFixture) {
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

fn assignment_digest(
  circuit: &Circuit<Scalar>,
  assignment: &Assignment<Scalar>,
) -> String {
  let mut hash = blake3::Hasher::new();
  for value in assignment.values(circuit.id()).unwrap() {
    for limb in value.canonical_limbs_le() {
      hash.update(&limb.to_le_bytes());
    }
  }
  hash.finalize().to_hex().to_string()
}

#[test]
fn point_prefix_matches_serial_inputs_values_and_encodings() {
  let points = points(9);
  let serial = PointFixture::new(&points, false);
  let parallel = PointFixture::new(&points, true);
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
  assert_eq!(parallel.circuit.stats().inputs, 11 * points.len());
}

#[test]
fn point_prefix_preserves_earliest_point_error() {
  let points = points(4);
  let serial = PointFixture::new(&points, false);
  let parallel = PointFixture::new(&points, true);
  for (missing, corrupt) in [
    (Some(0), None),
    (Some(21), None),
    (Some(43), None),
    (None, Some(11)),
    (Some(0), Some(11)),
    (Some(33), Some(11)),
    (Some(33), Some(22)),
  ] {
    let expected = serial.generate_changed(missing, corrupt).err().unwrap();
    let actual = parallel.generate_changed(missing, corrupt).err().unwrap();
    assert_eq!(actual, expected, "missing={missing:?}, corrupt={corrupt:?}");
  }
}

#[test]
#[ignore = "isolated point-prefix witness comparison; default fixture has 335 dynamic points"]
fn native_point_prefix_operation_benchmark() {
  let count = std::env::var("IX_KZG_POINT_PREFIX_POINTS")
    .map_or(335, |value| value.parse::<usize>().expect("valid point count"));
  assert!(count >= 2);
  let points = points(count);
  let start = Instant::now();
  let serial = PointFixture::new(&points, false);
  let parallel = PointFixture::new(&points, true);
  let construction_seconds = start.elapsed().as_secs_f64();
  same_relation(&serial, &parallel);
  let stats = parallel.circuit.stats();
  println!(
    "NATIVE_POINT_PREFIX_SETUP {}",
    serde_json::json!({
        "dynamic_points": count,
        "fixed_points": 4,
        "prefix_blocks": parallel.prefix_ends.len(),
        "prefix_values": parallel.prefix_ends.last().unwrap(),
        "values": stats.values,
        "inputs": stats.inputs,
        "gates": stats.gates,
        "lookups": stats.lookups,
        "hint_calls": stats.hint_calls,
        "hint_outputs": stats.hint_outputs,
        "publics": stats.publics,
        "certified": parallel.certified,
        "construction_seconds": construction_seconds,
        "scope": "Point-input subgroup checks and encodings, then a dependent serial suffix; no recursive proof or lowering",
    })
  );
  let mut reference = None::<(Vec<Scalar>, Vec<Scalar>)>;
  let mut digest = String::new();
  let mut parallel_digest_checked = false;
  let mut serial_seconds = Vec::new();
  let mut parallel_seconds = Vec::new();
  for sample in 0..5 {
    let modes = if sample % 2 == 0 {
      [("serial", &serial), ("parallel", &parallel)]
    } else {
      [("parallel", &parallel), ("serial", &serial)]
    };
    for (mode, fixture) in modes {
      let start = Instant::now();
      let assignment = fixture.generate().unwrap();
      let seconds = start.elapsed().as_secs_f64();
      assert_eq!(assignment.public_values(), fixture.expected_publics);
      if let Some((values, publics)) = &reference {
        assert!(assignment.values(fixture.circuit.id()).unwrap() == values);
        assert_eq!(assignment.public_values(), publics);
      } else {
        digest = assignment_digest(&fixture.circuit, &assignment);
      }
      if fixture.certified && !parallel_digest_checked {
        assert_eq!(assignment_digest(&fixture.circuit, &assignment), digest);
        parallel_digest_checked = true;
      }
      if fixture.certified {
        parallel_seconds.push(seconds);
      } else {
        serial_seconds.push(seconds);
      }
      println!(
        "NATIVE_POINT_PREFIX_SAMPLE {}",
        serde_json::json!({
            "sample": sample,
            "mode": mode,
            "seconds": seconds,
            "full_assignment_equal": true,
            "input_mapping_equal": true,
            "public_encodings_equal": true,
            "full_relation_checked": true,
            "assignment_blake3": digest,
        })
      );
      if reference.is_none() {
        reference = Some((
          assignment.values(fixture.circuit.id()).unwrap().to_vec(),
          assignment.public_values().to_vec(),
        ));
      }
    }
  }
  serial_seconds.sort_by(f64::total_cmp);
  parallel_seconds.sort_by(f64::total_cmp);
  println!(
    "NATIVE_POINT_PREFIX_RESULT {}",
    serde_json::json!({
        "dynamic_points": count,
        "paired_samples": 5,
        "serial_median_seconds": serial_seconds[2],
        "parallel_median_seconds": parallel_seconds[2],
        "speedup": serial_seconds[2] / parallel_seconds[2],
        "full_assignment_equal": true,
        "assignment_blake3": digest,
        "timing_scope": "Input assignment, recipe evaluation and complete frontend relation checks; excludes construction, comparisons, checksums and assignment destruction",
    })
  );
}
