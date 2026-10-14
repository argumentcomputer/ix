use super::*;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

fn scalars(n: usize) -> Vec<Fr> {
  (0..n)
    .map(|i| {
      let mut bytes = [0; 64];
      blake3::Hasher::new()
        .update(&(i as u64).to_le_bytes())
        .finalize_xof()
        .fill(&mut bytes);
      Fr::from_le_bytes_mod_order(&bytes)
    })
    .collect()
}

#[test]
fn settings_install_once() {
  // The first installation wins; later ones report that they were ignored.
  let first = configure(Settings::default());
  assert!(!configure(Settings { srs_cache: true, ..Settings::default() }));
  if first {
    assert_eq!(*settings(), Settings::default());
  }
}

#[test]
fn device_leases_reject_reentrancy_and_release_on_unwind() {
  let devices = Devices {
    ids: vec![0, 1],
    busy: Mutex::new(vec![false; 2]),
    available: Condvar::new(),
    chunk_points: 1,
    resident_bytes: Mutex::new(vec![0; 2]),
    resident_limits: vec![0; 2],
  };
  for entry in 0..4 {
    let result = std::panic::catch_unwind(|| {
      let _lease = devices.acquire_at(0);
      match entry {
        0 => drop(devices.acquire()),
        1 => drop(devices.acquire_at(1)),
        2 => drop(devices.acquire_group(&[1])),
        _ => drop(quotient::acquire_columns(&[], &mut [], &[], 0)),
      }
    });
    assert!(result.is_err());
    assert_eq!(DEVICE_LEASES.get(), 0);
    assert!(devices.busy.lock().unwrap().iter().all(|busy| !busy));
  }
  let mut group = devices.acquire_group(&[0, 1]);
  assert_eq!(DEVICE_LEASES.get(), 2);
  drop(group.pop());
  assert_eq!(DEVICE_LEASES.get(), 1);
  drop(group);
  assert_eq!(DEVICE_LEASES.get(), 0);
  drop(devices.acquire());
  assert!(devices.busy.lock().unwrap().iter().all(|busy| !busy));
}

#[test]
fn opening_memory_admission_keeps_scratch_reserve() {
  let fixed = (1 << 30) + 32 * 1024;
  assert_eq!(opening_chunk(1024, 16, fixed - 1), None);
  assert_eq!(opening_chunk(1024, 16, fixed + 383), None);
  assert_eq!(opening_chunk(1024, 16, fixed + 384), Some(1));
  assert_eq!(opening_chunk(1024, 16, fixed + 384 * 32), Some(16));
  assert_eq!(opening_chunk(usize::MAX, 16, usize::MAX), None);
  assert_eq!(opening_chunk(1024, 0, usize::MAX), None);
}

#[test]
fn normalization_samples_structured_columns_only() {
  let structured = vec![Fr::from(19).inverse().unwrap(); 8192];
  assert!(msm_normalization(&structured).is_some());
  assert!(msm_normalization(&scalars(8192)).is_none());
  assert!(msm_normalization(&vec![Fr::ONE; 8192]).is_none());
  assert!(msm_normalization(&structured[..4095]).is_none());
}

// The tests below need a visible CUDA GPU.

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_msm_matches_arkworks_with_chunks_and_exceptional_points() {
  let mut scalars = scalars(4099);
  let mut points: Vec<_> = scalars
    .iter()
    .map(|&s| (G1Affine::generator() * s).into_affine())
    .collect();
  points[0] = G1Affine::zero();
  points[1] = G1Affine::generator();
  points[2] = -points[1];
  points[4].infinity = true;
  scalars[1] = Fr::ONE;
  scalars[2] = Fr::ONE;
  scalars[3] = Fr::ZERO;
  scalars[4] = -Fr::ONE;
  for n in [0, 1, 31, 32, 33, 257, 4099] {
    assert_eq!(
      msm_chunked(&points[..n], &scalars[..n], 257),
      G1Projective::msm(&points[..n], &scalars[..n]).unwrap()
    );
  }
  assert!(msm_chunked(&points, &vec![Fr::ZERO; points.len()], 1024).is_zero());
  assert!(msm_chunked(&points[1..3], &scalars[1..3], 1).is_zero());
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_resident_msm_columns_match_arkworks() {
  let input = scalars(4099);
  let mut points: Vec<_> =
    input.iter().map(|&s| (G1Affine::generator() * s).into_affine()).collect();
  points[0] = G1Affine::zero();
  let negative: Vec<_> = input.iter().map(|&s| -s).collect();
  let zeros = vec![Fr::ZERO; input.len()];
  let ones = vec![Fr::ONE; input.len()];
  let columns =
    [input.as_slice(), zeros.as_slice(), negative.as_slice(), ones.as_slice()];
  let actual = msm_columns_chunked(&points, &columns, 257);
  for (actual, coefficients) in actual.iter().zip(columns) {
    assert_eq!(*actual, G1Projective::msm(&points, coefficients).unwrap());
  }
  assert!((actual[0] + actual[2]).is_zero());
  points[1] = -points[1];
  assert_eq!(
    msm_chunked(&points, &input, 257),
    G1Projective::msm(&points, &input).unwrap()
  );
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_msm_normalizes_structured_columns() {
  let n = 65_537;
  let seeds = scalars(17);
  let mut basis: Vec<_> =
    seeds.iter().map(|&s| (G1Affine::generator() * s).into_affine()).collect();
  basis[0] = G1Affine::zero();
  let points: Vec<_> = (0..n).map(|i| basis[i % basis.len()]).collect();
  let scale = Fr::from(19).inverse().unwrap();
  let structured: Vec<_> = (0..n)
    .map(|i| {
      if i % 11 == 0 {
        Fr::ZERO
      } else if i % 257 == 0 {
        seeds[i % seeds.len()]
      } else if i % 7 == 0 {
        -scale
      } else {
        scale
      }
    })
    .collect();
  let scaled: Vec<_> = structured.iter().map(|&s| s * Fr::from(7)).collect();
  let random = scalars(n);
  let columns = [structured.as_slice(), scaled.as_slice(), random.as_slice()];
  let actual = msm_columns_chunked(&points, &columns, 1 << 15);
  for (actual, coefficients) in actual.into_iter().zip(columns) {
    assert_eq!(actual, G1Projective::msm(&points, coefficients).unwrap());
  }
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_fft_rejects_overflowing_domain_stride() {
  let mut value = Fr::ONE.0.0;
  let original = value;
  // The invalid size must be rejected before any transfer or allocation.
  let status = unsafe { ix_kzg_fft(0, &mut value, 32, false, &original) };
  assert_ne!(status, 0);
  assert_eq!(value, original);
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_fft_matches_arkworks_on_subgroups_and_arbitrary_cosets() {
  for lg in [0, 1, 5, 10, 11, 16] {
    for shift in [Fr::ONE, Fr::from(7), Fr::from(12345)] {
      let domain = Radix2EvaluationDomain::<Fr>::new(1 << lg)
        .unwrap()
        .get_coset(shift)
        .unwrap();
      let input = scalars(1 << lg);
      let mut actual = input.clone();
      fft(&mut actual, false, shift);
      assert_eq!(actual, domain.fft(&input), "forward lg={lg}");
      fft(&mut actual, true, shift);
      assert_eq!(actual, input, "inverse lg={lg}");
      let mut actual = input.clone();
      fft(&mut actual, true, shift);
      assert_eq!(actual, domain.ifft(&input), "inverse parity lg={lg}");
    }
  }
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_fft_from_pads_without_mutating_coefficients() {
  for lg in [0, 1, 10, 16] {
    let size = 1 << lg;
    let input = scalars(size);
    let saved = input.clone();
    for count in [0, 1, size / 3, size] {
      for shift in [Fr::ONE, Fr::from(7)] {
        let domain = Radix2EvaluationDomain::<Fr>::new(size)
          .unwrap()
          .get_coset(shift)
          .unwrap();
        assert_eq!(
          fft_from(&input[..count], lg, shift),
          domain.fft(&input[..count])
        );
        assert_eq!(input, saved);
      }
    }
  }
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_fft_queues_reuse_resident_inputs_and_preserve_order() {
  let lg = 17;
  let input = scalars(1 << lg);
  let resident = retain(&input).expect("test requires resident VRAM budget");
  let expected = Radix2EvaluationDomain::<Fr>::new(input.len())
    .unwrap()
    .get_coset(Fr::from(7))
    .unwrap()
    .fft(&input);
  // More jobs than lanes forces buffer reuse; mixed inputs exercise both
  // device affinity and host-only queues, with repeated immutable handles.
  let jobs: Vec<_> = (0..11)
    .map(|i| {
      (
        input.as_slice(),
        if i % 2 == 0 { Some(resident.as_ref()) } else { None },
      )
    })
    .collect();
  for _ in 0..2 {
    let actual = fft_columns(&jobs, lg, false, Fr::from(7));
    assert_eq!(actual.len(), jobs.len());
    assert!(actual.iter().all(|column| *column == expected));
  }
  let points = [Fr::ZERO, Fr::from(7), Fr::ONE, Fr::from(7)];
  let evaluations = evaluate_resident(&input, Some(&resident), &points);
  for (z, actual) in points.into_iter().zip(evaluations) {
    assert_eq!(actual, input.iter().rev().fold(Fr::ZERO, |acc, c| acc * z + c));
  }
  drop(resident);
  assert_eq!(fft_columns(&[], lg, false, Fr::ONE), Vec::<Vec<Fr>>::new());
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_interpolation_retains_outputs_for_msm_and_cosets() {
  let count = 1 << 16;
  let shift = Fr::from(7);
  let domain =
    Radix2EvaluationDomain::<Fr>::new(count).unwrap().get_coset(shift).unwrap();
  let coefficients =
    [scalars(count), vec![Fr::from(19).inverse().unwrap(); count]];
  let inputs = coefficients.iter().map(|c| domain.fft(c)).collect();
  let (actual, resident) = interpolate_columns(inputs, 16, shift);
  assert_eq!(actual, coefficients);
  assert!(resident.iter().all(Option::is_some));
  let points: Vec<_> = (0..count)
    .map(|i| {
      if i % 257 == 0 {
        G1Affine::zero()
      } else {
        (G1Affine::generator() * Fr::from((i % 31 + 1) as u64)).into_affine()
      }
    })
    .collect();
  let inputs: Vec<_> = actual
    .iter()
    .zip(&resident)
    .map(|(c, r)| (c.as_slice(), r.as_deref()))
    .collect();
  let commitments = msm_columns_resident(&points, &inputs);
  for (column, commitment) in actual.iter().zip(commitments) {
    assert_eq!(commitment, G1Projective::msm(&points, column).unwrap());
  }
  let output = fft_columns(&inputs, 16, false, Fr::from(123));
  let coset = Radix2EvaluationDomain::<Fr>::new(count)
    .unwrap()
    .get_coset(Fr::from(123))
    .unwrap();
  for (column, output) in coefficients.iter().zip(output) {
    assert_eq!(output, coset.fft(column));
  }
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_polynomial_evaluation_and_division_match_horner() {
  for n in [0, 1, 2, 31, 32, 33, 1023, 1024, 1025, 65537] {
    let coefficients = scalars(n);
    for z in [Fr::ZERO, Fr::ONE, -Fr::ONE, Fr::from(918273)] {
      let expected = coefficients.iter().rev().fold(Fr::ZERO, |v, c| v * z + c);
      assert_eq!(
        evaluate_many(&coefficients, &[z]),
        [expected],
        "evaluation n={n}"
      );
      let quotient = divide(&coefficients, z);
      assert_eq!(quotient.len(), n.saturating_sub(1));
      if n >= 2 {
        assert_eq!(coefficients[0] + z * quotient[0], expected);
        for i in 1..n {
          assert_eq!(
            quotient[i - 1] - z * quotient.get(i).copied().unwrap_or(Fr::ZERO),
            coefficients[i],
            "division n={n}, i={i}"
          );
        }
      }
    }
  }
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_polynomial_evaluates_all_points_in_order() {
  let mut points = scalars(41);
  points[..5].copy_from_slice(&[
    Fr::ZERO,
    Fr::ONE,
    -Fr::ONE,
    Fr::ONE,
    Fr::ZERO,
  ]);
  for n in [0, 1, 2, 31, 1025, 65_537] {
    let coefficients = scalars(n);
    for count in [0, 1, 2, 3, 4, 7, 8, 41] {
      let points = &points[..count];
      let expected: Vec<_> = points
        .iter()
        .map(|z| coefficients.iter().rev().fold(Fr::ZERO, |v, c| v * z + c))
        .collect();
      assert_eq!(
        evaluate_many(&coefficients, points),
        expected,
        "n={n}, points={count}"
      );
    }
  }
}

fn division_reference(coefficients: &[Fr], z: Fr) -> Vec<Fr> {
  let mut quotient = vec![Fr::ZERO; coefficients.len().saturating_sub(1)];
  let mut carry = Fr::ZERO;
  for i in (1..coefficients.len()).rev() {
    carry = coefficients[i] + z * carry;
    quotient[i - 1] = carry;
  }
  quotient
}

fn opening_points(count: usize) -> Vec<G1Affine> {
  let mut point = G1Projective::zero();
  let basis: Vec<_> = (0..256)
    .map(|_| {
      let output = point;
      point += G1Affine::generator();
      output
    })
    .collect();
  let basis = G1Projective::normalize_batch(&basis);
  crate::kzg::buffer::generate(count, |i| basis[i % basis.len()])
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_resident_division_msm_matches_arkworks() {
  for n in [0usize, 1, 2, 33, 4097, 65537] {
    let points = opening_points(n.saturating_sub(1));
    for (coefficients, z) in [
      (scalars(n), Fr::from(918273)),
      (vec![Fr::from(19).inverse().unwrap(); n], Fr::ZERO),
      (vec![Fr::ZERO; n], Fr::ONE),
    ] {
      let expected =
        G1Projective::msm(&points, &division_reference(&coefficients, z))
          .unwrap();
      assert_eq!(
        divide_and_msm_chunked(&points, &coefficients, z, 16385),
        Some(expected),
        "n={n}, z={z}"
      );
    }
  }
  assert!(
    divide_and_msm_chunked(&opening_points(1), &[Fr::ONE; 2], Fr::ZERO, 0)
      .is_none()
  );
  assert_eq!(
    divide_and_msm(&opening_points(1), &[Fr::ONE; 2], Fr::ZERO),
    Some(G1Projective::zero())
  );
}

/// Run `test` on its own thread and fail if it does not finish within the
/// deadline, so a device-lease deadlock cannot hang the test runner.
fn with_deadline(seconds: u64, test: impl FnOnce() + Send + 'static) {
  let (done, finished) = std::sync::mpsc::channel();
  std::thread::spawn(move || {
    test();
    let _ = done.send(());
  });
  finished
    .recv_timeout(std::time::Duration::from_secs(seconds))
    .expect("test did not complete within the deadline, or panicked");
}

#[test]
#[ignore = "requires one CUDA GPU; two Rayon threads race uncached MSMs and divisions"]
fn concurrent_uncached_msm_completes() {
  with_deadline(120, concurrent_uncached_msm_body);
}

fn concurrent_uncached_msm_body() {
  use std::sync::Barrier;
  assert_eq!(Devices::get().ids.len(), 1, "run with one device selected");
  assert!(!srs_cache::enabled());
  let n = 1 << 20;
  let basis: Vec<_> = (1u64..=17)
    .map(|i| (G1Affine::generator() * Fr::from(i)).into_affine())
    .collect();
  let points: Vec<_> = (0..n).map(|i| basis[i % basis.len()]).collect();
  let scalars = vec![Fr::from(37); n];
  assert!(msm_normalization(&scalars).is_some());
  let expected = G1Projective::msm(&points, &scalars).unwrap();
  let start = Barrier::new(2);
  std::thread::scope(|scope| {
    let jobs: Vec<_> = (0..2)
      .map(|_| {
        scope.spawn(|| {
          start.wait();
          assert_eq!(msm(&points, &scalars), expected);
          assert_eq!(divide(&scalars, Fr::ZERO), scalars[..n - 1]);
        })
      })
      .collect();
    for job in jobs {
      job.join().unwrap();
    }
  });
}

#[test]
#[ignore = "requires one CUDA GPU; concurrent shared-key hydration"]
fn concurrent_shared_matrix_hydration_completes() {
  with_deadline(120, concurrent_shared_matrix_hydration_body);
}

fn concurrent_shared_matrix_hydration_body() {
  use crate::kzg::{Scalar, domain::Radix2Coset, pcs::KzgProverData};
  let n = 1 << 16;
  let mut constant = vec![Fr::ZERO; n];
  constant[0] = Fr::from(37);
  let coefficients = vec![Fr::from(19); n];
  let data = KzgProverData::coefficient_fixture(
    Radix2Coset { log_size: 16, shift: Scalar(Fr::ONE) },
    vec![constant, coefficients.clone(), coefficients.clone()],
  );
  let matrix = &data.matrices[0];
  let columns: Vec<_> =
    (0..16).into_par_iter().map(|_| matrix.resident_columns()).collect();
  assert!(columns.iter().all(|view| std::ptr::eq(*view, columns[0])));
  let resident = columns[0];
  assert!(resident[0].is_none());
  let z = Fr::from(7);
  let expected = coefficients.iter().rev().fold(Fr::ZERO, |sum, c| sum * z + c);
  for column in &resident[1..] {
    assert!(column.is_some(), "small resident fixture must fit");
    assert_eq!(
      evaluate_resident(&coefficients, column.as_deref(), &[z]),
      [expected]
    );
  }
}
