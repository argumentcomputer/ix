use super::*;
use crate::kzg::curve::{Bls12381, Bn254};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

mod constraints;

fn check_ntt_parameters<C: KzgCurve>() {
  use crate::kzg::CurveScalar;
  use multi_stark::traits::TwoAdicField;
  for lg in 0..=C::MAX_FFT_LOG {
    let mut output = [[0; 4]; 3];
    let status =
      unsafe { C::ffi_ntt_parameters(u32::try_from(lg).unwrap(), &mut output) };
    assert_eq!(status, 0);
    let [root, inverse, scale] = output.map(C::fr_from_mont_limbs_unchecked);
    assert_eq!(root, CurveScalar::<C>::two_adic_generator(lg).0);
    assert_eq!(inverse, root.inverse().unwrap());
    assert_eq!(scale, C::Fr::from(1u64 << lg).inverse().unwrap());
  }
  let mut output = [[0; 4]; 3];
  assert_eq!(
    unsafe {
      C::ffi_ntt_parameters(
        u32::try_from(C::MAX_FFT_LOG).unwrap() + 1,
        &mut output,
      )
    },
    1
  );
}

#[test]
fn native_ntt_parameters_match_scalar_roots_without_large_allocations() {
  check_ntt_parameters::<Bn254>();
  check_ntt_parameters::<Bls12381>();
}

fn field_inputs<F: PrimeField>() -> [F; 32] {
  let mut values = std::array::from_fn(|i| {
    let mut bytes = [0; 64];
    blake3::Hasher::new()
      .update(&(i as u64).to_le_bytes())
      .finalize_xof()
      .fill(&mut bytes);
    F::from_le_bytes_mod_order(&bytes)
  });
  values[..5].copy_from_slice(&[
    F::ZERO,
    F::ONE,
    -F::ONE,
    F::from(2u8),
    -F::from(2u8),
  ]);
  for (value, bit) in values[5..9].iter_mut().zip([63, 64, 127, 192]) {
    *value = F::from(2u8).pow([bit]);
  }
  values
}

fn field_reference<F: PrimeField>(values: [F; 32]) -> Vec<F> {
  values
    .iter()
    .enumerate()
    .flat_map(|(i, &a)| {
      let b = values[(i + 1) % values.len()];
      [F::ONE, a + b, a - b, a * b, -a, a.inverse().unwrap_or(F::ZERO)]
    })
    .collect()
}

fn check_field_conformance<C: KzgCurve>() {
  let fq = field_inputs::<C::Fq>();
  let fr = field_inputs::<C::Fr>();
  let fq_input = fq.map(C::fq_to_mont_limbs);
  let fr_input = fr.map(C::fr_mont_limbs);
  let mut fq_output = [C::FqLimbs::default(); 192];
  let mut fr_output = [[0; 4]; 192];
  let device = Devices::get::<C>().acquire();
  check(
    unsafe {
      C::ffi_field_conformance(
        device.id(),
        &fq_input,
        &fr_input,
        &mut fq_output,
        &mut fr_output,
      )
    },
    "field conformance",
  );
  assert_eq!(
    fq_output.map(C::fq_from_mont_limbs_unchecked).as_slice(),
    field_reference(fq)
  );
  assert_eq!(
    fr_output.map(C::fr_from_mont_limbs_unchecked).as_slice(),
    field_reference(fr)
  );
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_base_and_scalar_arithmetic_match_arkworks() {
  check_field_conformance::<Bn254>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_bls12_381_base_and_scalar_arithmetic_match_arkworks() {
  check_field_conformance::<Bls12381>();
}

fn scalars<C: KzgCurve>(n: usize) -> Vec<C::Fr> {
  (0..n)
    .map(|i| {
      let mut bytes = [0; 64];
      blake3::Hasher::new()
        .update(&(i as u64).to_le_bytes())
        .finalize_xof()
        .fill(&mut bytes);
      C::Fr::from_le_bytes_mod_order(&bytes)
    })
    .collect()
}

fn check_oversized_fft<C: KzgCurve>() {
  let unsupported = C::MAX_FFT_LOG + 1;
  assert!(
    std::panic::catch_unwind(|| {
      fft_columns::<C>(&[], unsupported, false, C::FR_ONE)
    })
    .is_err()
  );
  assert!(
    std::panic::catch_unwind(|| {
      interpolate_columns::<C>(vec![], unsupported, C::FR_ONE)
    })
    .is_err()
  );
  assert!(
    std::panic::catch_unwind(|| fft_from::<C>(&[], unsupported, C::FR_ONE))
      .is_err()
  );
  let shift = C::fr_mont_limbs(C::FR_ONE);
  let mut value = C::fr_mont_limbs(C::FR_ZERO);
  let original = value;
  const INVALID_VALUE: i32 = 1;
  // Invalid domains must fail before the invalid ordinal is resolved.
  for lg in [u32::try_from(unsupported).unwrap(), u32::MAX] {
    let code = unsafe { C::ffi_fft(-1, &mut value, lg, false, &shift) };
    assert_eq!(code, INVALID_VALUE);
    let job = FftJob {
      input: &value,
      resident_input: std::ptr::null(),
      output: &mut value,
      input_count: 1,
      resident_output: std::ptr::null_mut(),
    };
    let code = unsafe {
      C::ffi_fft_batch(
        -1,
        std::ptr::from_ref(&job).cast(),
        1,
        lg,
        false,
        &shift,
        1,
      )
    };
    assert_eq!(code, INVALID_VALUE);
    assert_eq!(value, original);
  }
}

#[test]
fn oversized_fft_domains_fail_before_allocation_or_device_access() {
  check_oversized_fft::<Bn254>();
  check_oversized_fft::<Bls12381>();
}

fn check_projective_transport<C: KzgCurve>() {
  let generator = G1AffineOf::<C>::generator();
  for point in [generator, -generator, G1AffineOf::<C>::identity()] {
    let native = point.into_group();
    let decoded = projective::<C>([
      C::fq_to_mont_limbs(native.x),
      C::fq_to_mont_limbs(native.y),
      C::fq_to_mont_limbs(native.z),
    ]);
    assert_eq!(decoded.into_affine(), point);
  }
  assert!(projective::<C>([C::FqLimbs::default(); 3]).is_zero());
}

#[test]
fn projective_limb_transport_preserves_coordinates_and_infinity() {
  check_projective_transport::<Bn254>();
  check_projective_transport::<Bls12381>();
}

fn lease_devices() -> Devices {
  Devices {
    ids: vec![0, 1],
    busy: Mutex::new(vec![false; 2]),
    available: Condvar::new(),
    chunk_points: 1,
    resident_bytes: Mutex::new(vec![0; 2]),
    resident_limits: vec![0; 2],
  }
}

#[test]
fn device_leases_reject_reentrancy_and_release_on_unwind() {
  let devices = lease_devices();
  for entry in 0..4 {
    let result = std::panic::catch_unwind(|| {
      let _lease = devices.acquire_at(0);
      match entry {
        0 => drop(devices.acquire()),
        1 => drop(devices.acquire_at(1)),
        2 => drop(quotient::acquire_columns::<Bn254>(&mut [], &[], 0)),
        _ => drop(devices.acquire_admitted(&[1], |_| true)),
      }
    });
    assert!(result.is_err());
    assert_eq!(DEVICE_LEASES.get(), 0);
    assert!(devices.busy.lock().unwrap().iter().all(|busy| !busy));
  }
  drop(devices.acquire());
  assert!(devices.busy.lock().unwrap().iter().all(|busy| !busy));
}

#[test]
fn device_admission_waits_for_busy_candidates_to_release_scratch() {
  use std::sync::atomic::{AtomicUsize, Ordering};
  use std::sync::mpsc;
  use std::time::Duration;

  let devices = lease_devices();
  let occupied = devices.acquire_at(0);
  let free = AtomicUsize::new(12);
  let (rejected, rejection) = mpsc::channel();
  let (finished, completion) = mpsc::channel();
  std::thread::scope(|scope| {
    scope.spawn(|| {
      let mut attempted = Vec::new();
      let device = devices
        .acquire_admitted(&[0, 1], |device| {
          assert_eq!(DEVICE_LEASES.get(), 1);
          attempted.push(device.index);
          if device.index == 1 {
            rejected.send(()).unwrap();
            false
          } else {
            free.load(Ordering::SeqCst) >= 17
          }
        })
        .expect("released scratch admits the waiting operation");
      assert_eq!(device.index, 0);
      assert_eq!(attempted, [1, 0]);
      drop(device);
      finished.send(()).unwrap();
    });
    rejection.recv_timeout(Duration::from_secs(5)).unwrap();
    assert_eq!(completion.try_recv(), Err(mpsc::TryRecvError::Empty));
    free.store(28, Ordering::SeqCst);
    drop(occupied);
    completion.recv_timeout(Duration::from_secs(5)).unwrap();
  });
  assert!(devices.busy.lock().unwrap().iter().all(|busy| !busy));
}

#[test]
fn device_admission_uses_a_free_candidate_and_checks_every_rejection() {
  use std::sync::mpsc;
  use std::time::Duration;

  let devices = lease_devices();
  let occupied = devices.acquire_at(0);
  let (finished, completion) = mpsc::channel();
  std::thread::scope(|scope| {
    scope.spawn(|| {
      let device = devices.acquire_admitted(&[0, 1], |_| true).unwrap();
      assert_eq!(device.index, 1);
      drop(device);
      finished.send(()).unwrap();
    });
    completion.recv_timeout(Duration::from_secs(5)).unwrap();
    drop(occupied);
  });
  let mut attempted = Vec::new();
  assert!(
    devices
      .acquire_admitted(&[1, 0], |device| {
        assert_eq!(DEVICE_LEASES.get(), 1);
        attempted.push(device.index);
        false
      })
      .is_none()
  );
  assert_eq!(attempted, [1, 0]);
  assert_eq!(DEVICE_LEASES.get(), 0);
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
  let structured = vec![ark_bn254::Fr::from(19).inverse().unwrap(); 8192];
  assert!(msm_normalization::<Bn254>(&structured).is_some());
  assert!(msm_normalization::<Bn254>(&scalars::<Bn254>(8192)).is_none());
  assert!(msm_normalization::<Bn254>(&vec![Bn254::FR_ONE; 8192]).is_none());
  assert!(msm_normalization::<Bn254>(&structured[..4095]).is_none());
}

// The tests below need a visible CUDA GPU.

fn check_msm_destroy_rejection<C: KzgCurve>() {
  let points = [
    G1AffineOf::<C>::generator(),
    -G1AffineOf::<C>::generator(),
    G1AffineOf::<C>::identity(),
  ];
  let values = [C::FR_ONE, C::Fr::from(2u64), C::Fr::from(3u64)];
  let device = Devices::get::<C>().acquire();
  let context = upload_msm_points::<C>(&device, &points);
  assert_eq!(unsafe { C::ffi_msm_destroy(-1, context.context) }, 1);
  let mut output = [C::FqLimbs::default(); 3];
  check(
    unsafe {
      C::ffi_msm_invoke(
        device.id(),
        context.context,
        &mut output,
        values.as_ptr().cast(),
        values.len(),
        std::ptr::null(),
      )
    },
    "MSM after rejected destruction",
  );
  assert_eq!(
    projective::<C>(output),
    G1ProjectiveOf::<C>::msm(&points, &values).unwrap()
  );
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn msm_handle_rejects_destruction_on_another_device() {
  check_msm_destroy_rejection::<Bn254>();
}

fn check_cuda_msm<C: KzgCurve>() {
  let mut scalars = scalars::<C>(4099);
  let mut points: Vec<_> = scalars
    .iter()
    .map(|&s| (G1AffineOf::<C>::generator() * s).into_affine())
    .collect();
  points[0] = G1AffineOf::<C>::zero();
  points[1] = G1AffineOf::<C>::generator();
  points[2] = -points[1];
  points[4].infinity = true;
  scalars[1] = C::FR_ONE;
  scalars[2] = C::FR_ONE;
  scalars[3] = C::FR_ZERO;
  scalars[4] = -C::FR_ONE;
  for n in [0, 1, 31, 32, 33, 257, 4099] {
    assert_eq!(
      msm_chunked::<C>(&points[..n], &scalars[..n], 257),
      G1ProjectiveOf::<C>::msm(&points[..n], &scalars[..n]).unwrap()
    );
  }
  assert!(
    msm_chunked::<C>(&points, &vec![C::FR_ZERO; points.len()], 1024).is_zero()
  );
  assert!(msm_chunked::<C>(&points[1..3], &scalars[1..3], 1).is_zero());
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_msm_matches_arkworks_with_chunks_and_exceptional_points() {
  check_cuda_msm::<Bn254>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_bls12_381_msm_matches_arkworks_with_chunks_and_exceptional_points() {
  check_cuda_msm::<Bls12381>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_resident_msm_columns_match_arkworks() {
  let input = scalars::<Bn254>(4099);
  let mut points: Vec<_> = input
    .iter()
    .map(|&s| (ark_bn254::G1Affine::generator() * s).into_affine())
    .collect();
  points[0] = ark_bn254::G1Affine::zero();
  let negative: Vec<_> = input.iter().map(|&s| -s).collect();
  let zeros = vec![Bn254::FR_ZERO; input.len()];
  let ones = vec![Bn254::FR_ONE; input.len()];
  let columns =
    [input.as_slice(), zeros.as_slice(), negative.as_slice(), ones.as_slice()];
  let actual = msm_columns_chunked::<Bn254>(&points, &columns, 257);
  for (actual, coefficients) in actual.iter().zip(columns) {
    assert_eq!(
      *actual,
      ark_bn254::G1Projective::msm(&points, coefficients).unwrap()
    );
  }
  assert!((actual[0] + actual[2]).is_zero());
  points[1] = -points[1];
  assert_eq!(
    msm_chunked::<Bn254>(&points, &input, 257),
    ark_bn254::G1Projective::msm(&points, &input).unwrap()
  );
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_msm_normalizes_structured_columns() {
  let n = 65_537;
  let seeds = scalars::<Bn254>(17);
  let mut basis: Vec<_> = seeds
    .iter()
    .map(|&s| (ark_bn254::G1Affine::generator() * s).into_affine())
    .collect();
  basis[0] = ark_bn254::G1Affine::zero();
  let points: Vec<_> = (0..n).map(|i| basis[i % basis.len()]).collect();
  let scale = ark_bn254::Fr::from(19).inverse().unwrap();
  let structured: Vec<_> = (0..n)
    .map(|i| {
      if i % 11 == 0 {
        Bn254::FR_ZERO
      } else if i % 257 == 0 {
        seeds[i % seeds.len()]
      } else if i % 7 == 0 {
        -scale
      } else {
        scale
      }
    })
    .collect();
  let scaled: Vec<_> =
    structured.iter().map(|&s| s * ark_bn254::Fr::from(7)).collect();
  let random = scalars::<Bn254>(n);
  let columns = [structured.as_slice(), scaled.as_slice(), random.as_slice()];
  let actual = msm_columns_chunked::<Bn254>(&points, &columns, 1 << 15);
  for (actual, coefficients) in actual.into_iter().zip(columns) {
    assert_eq!(
      actual,
      ark_bn254::G1Projective::msm(&points, coefficients).unwrap()
    );
  }
}

fn check_cuda_fft<C: KzgCurve>() {
  for lg in [0, 1, 5, 10, 11, 16] {
    for shift in [C::FR_ONE, C::Fr::from(7u64), C::Fr::from(12345u64)] {
      let domain = Radix2EvaluationDomain::<C::Fr>::new(1 << lg)
        .unwrap()
        .get_coset(shift)
        .unwrap();
      let input = scalars::<C>(1 << lg);
      let mut actual = input.clone();
      fft::<C>(&mut actual, false, shift);
      assert_eq!(actual, domain.fft(&input), "forward lg={lg}");
      fft::<C>(&mut actual, true, shift);
      assert_eq!(actual, input, "inverse lg={lg}");
      let mut actual = input.clone();
      fft::<C>(&mut actual, true, shift);
      assert_eq!(actual, domain.ifft(&input), "inverse parity lg={lg}");
    }
  }
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_fft_matches_arkworks_on_subgroups_and_arbitrary_cosets() {
  check_cuda_fft::<Bn254>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_bls12_381_fft_matches_arkworks_on_subgroups_and_arbitrary_cosets() {
  check_cuda_fft::<Bls12381>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_fft_from_pads_without_mutating_coefficients() {
  for lg in [0, 1, 10, 16] {
    let size = 1 << lg;
    let input = scalars::<Bn254>(size);
    let saved = input.clone();
    for count in [0, 1, size / 3, size] {
      for shift in [Bn254::FR_ONE, ark_bn254::Fr::from(7)] {
        let domain = Radix2EvaluationDomain::<ark_bn254::Fr>::new(size)
          .unwrap()
          .get_coset(shift)
          .unwrap();
        assert_eq!(
          fft_from::<Bn254>(&input[..count], lg, shift),
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
  let input = scalars::<Bn254>(1 << lg);
  let resident =
    retain::<Bn254>(&input).expect("test requires resident VRAM budget");
  let expected = Radix2EvaluationDomain::<ark_bn254::Fr>::new(input.len())
    .unwrap()
    .get_coset(ark_bn254::Fr::from(7))
    .unwrap()
    .fft(&input);
  let jobs: Vec<_> = (0..11)
    .map(|i| {
      (
        input.as_slice(),
        if i % 2 == 0 { Some(resident.as_ref()) } else { None },
      )
    })
    .collect();
  for _ in 0..2 {
    let actual = fft_columns::<Bn254>(&jobs, lg, false, ark_bn254::Fr::from(7));
    assert_eq!(actual.len(), jobs.len());
    assert!(actual.iter().all(|column| *column == expected));
  }
  let points = [
    Bn254::FR_ZERO,
    ark_bn254::Fr::from(7),
    Bn254::FR_ONE,
    ark_bn254::Fr::from(7),
  ];
  let evaluations =
    evaluate_resident::<Bn254>(&input, Some(&resident), &points);
  for (z, actual) in points.into_iter().zip(evaluations) {
    assert_eq!(
      actual,
      input.iter().rev().fold(Bn254::FR_ZERO, |acc, c| acc * z + c)
    );
  }
  drop(resident);
  assert_eq!(
    fft_columns::<Bn254>(&[], lg, false, Bn254::FR_ONE),
    Vec::<Vec<ark_bn254::Fr>>::new()
  );
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_interpolation_retains_outputs_for_msm_and_cosets() {
  let count = 1 << 16;
  let shift = ark_bn254::Fr::from(7);
  let domain = Radix2EvaluationDomain::<ark_bn254::Fr>::new(count)
    .unwrap()
    .get_coset(shift)
    .unwrap();
  let coefficients = [
    scalars::<Bn254>(count),
    vec![ark_bn254::Fr::from(19).inverse().unwrap(); count],
  ];
  let inputs = coefficients.iter().map(|c| domain.fft(c)).collect();
  let (actual, resident) = interpolate_columns::<Bn254>(inputs, 16, shift);
  assert_eq!(actual, coefficients);
  assert!(resident.iter().all(Option::is_some));
  let points: Vec<_> = (0..count)
    .map(|i| {
      if i % 257 == 0 {
        ark_bn254::G1Affine::zero()
      } else {
        (ark_bn254::G1Affine::generator()
          * ark_bn254::Fr::from((i % 31 + 1) as u64))
        .into_affine()
      }
    })
    .collect();
  let inputs: Vec<_> = actual
    .iter()
    .zip(&resident)
    .map(|(c, r)| (c.as_slice(), r.as_deref()))
    .collect();
  let commitments = msm_columns_resident::<Bn254>(&points, &inputs);
  for (column, commitment) in actual.iter().zip(commitments) {
    assert_eq!(
      commitment,
      ark_bn254::G1Projective::msm(&points, column).unwrap()
    );
  }
  let output =
    fft_columns::<Bn254>(&inputs, 16, false, ark_bn254::Fr::from(123));
  let coset = Radix2EvaluationDomain::<ark_bn254::Fr>::new(count)
    .unwrap()
    .get_coset(ark_bn254::Fr::from(123))
    .unwrap();
  for (column, output) in coefficients.iter().zip(output) {
    assert_eq!(output, coset.fft(column));
  }
}

fn check_cuda_division<C: KzgCurve>() {
  for n in [0, 1, 2, 31, 32, 33, 1023, 1024, 1025, 65537] {
    let coefficients = scalars::<C>(n);
    for z in [C::FR_ZERO, C::FR_ONE, -C::FR_ONE, C::Fr::from(918273u64)] {
      let expected =
        coefficients.iter().rev().fold(C::FR_ZERO, |v, c| v * z + c);
      let quotient = divide::<C>(&coefficients, z);
      assert_eq!(quotient.len(), n.saturating_sub(1));
      if n >= 2 {
        assert_eq!(coefficients[0] + z * quotient[0], expected);
        for i in 1..n {
          assert_eq!(
            quotient[i - 1]
              - z * quotient.get(i).copied().unwrap_or(C::FR_ZERO),
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
fn cuda_polynomial_division_matches_horner() {
  check_cuda_division::<Bn254>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_bls12_381_polynomial_division_matches_horner() {
  check_cuda_division::<Bls12381>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_polynomial_evaluates_all_points_in_order() {
  let mut points = scalars::<Bn254>(41);
  points[..6].copy_from_slice(&[
    Bn254::FR_ZERO,
    Bn254::FR_ONE,
    -Bn254::FR_ONE,
    Bn254::FR_ONE,
    Bn254::FR_ZERO,
    ark_bn254::Fr::from(918273),
  ]);
  for n in [0, 1, 2, 31, 32, 33, 1023, 1024, 1025, 65_537] {
    let coefficients = scalars::<Bn254>(n);
    for count in [0, 1, 2, 3, 4, 7, 8, 41] {
      let points = &points[..count];
      let expected: Vec<_> = points
        .iter()
        .map(|z| {
          coefficients.iter().rev().fold(Bn254::FR_ZERO, |v, c| v * z + c)
        })
        .collect();
      assert_eq!(
        evaluate_many::<Bn254>(&coefficients, points),
        expected,
        "n={n}, points={count}"
      );
    }
  }
}

fn division_reference<C: KzgCurve>(
  coefficients: &[C::Fr],
  z: C::Fr,
) -> Vec<C::Fr> {
  let mut quotient = vec![C::FR_ZERO; coefficients.len().saturating_sub(1)];
  let mut carry = C::FR_ZERO;
  for i in (1..coefficients.len()).rev() {
    carry = coefficients[i] + z * carry;
    quotient[i - 1] = carry;
  }
  quotient
}

fn opening_points<C: KzgCurve>(count: usize) -> Vec<G1AffineOf<C>> {
  let mut point = G1ProjectiveOf::<C>::zero();
  let basis: Vec<_> = (0..256)
    .map(|_| {
      let output = point;
      point += G1AffineOf::<C>::generator();
      output
    })
    .collect();
  let basis = G1ProjectiveOf::<C>::normalize_batch(&basis);
  crate::kzg::pcs::generate_buffer(count, |i| basis[i % basis.len()])
}

fn check_resident_division_msm<C: KzgCurve>() {
  for n in [0usize, 1, 2, 33, 4097, 65537] {
    let points = opening_points::<C>(n.saturating_sub(1));
    for (coefficients, z) in [
      (scalars::<C>(n), C::Fr::from(918273u64)),
      (vec![C::Fr::from(19u64).inverse().unwrap(); n], C::FR_ZERO),
      (vec![C::FR_ZERO; n], C::FR_ONE),
    ] {
      let expected = G1ProjectiveOf::<C>::msm(
        &points,
        &division_reference::<C>(&coefficients, z),
      )
      .unwrap();
      assert_eq!(
        divide_and_msm_chunked::<C>(&points, &coefficients, z, 16385),
        Some(expected),
        "n={n}, z={z}"
      );
    }
  }
  assert!(
    divide_and_msm_chunked::<C>(
      &opening_points::<C>(1),
      &[C::FR_ONE; 2],
      C::FR_ZERO,
      0
    )
    .is_none()
  );
  assert_eq!(
    divide_and_msm::<C>(&opening_points::<C>(1), &[C::FR_ONE; 2], C::FR_ZERO),
    Some(G1ProjectiveOf::<C>::zero())
  );
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_resident_division_msm_matches_arkworks() {
  check_resident_division_msm::<Bn254>();
}

#[test]
#[ignore = "requires a CUDA GPU"]
fn cuda_bls12_381_resident_division_msm_matches_arkworks() {
  check_resident_division_msm::<Bls12381>();
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
#[ignore = "requires two CUDA GPUs; pass admission across resident columns on both"]
fn pass_admission_binds_only_the_admitted_devices_residents() {
  let devices = Devices::get::<Bn254>();
  assert!(devices.ids.len() >= 2, "run with two devices selected");
  let values = scalars::<Bn254>(1 << 16);
  let retained: Vec<_> = (0..4)
    .map(|_| retain::<Bn254>(&values).expect("resident column"))
    .collect();
  let a: &ResidentPolynomial<Bn254> = &retained[0];
  let b: &ResidentPolynomial<Bn254> = retained
    .iter()
    .map(|r| &**r)
    .find(|r| r.reservation.index != a.reservation.index)
    .expect("retentions spread over two devices");
  fn expect_device(
    all: &[quotient::PolynomialView<'_, Bn254>],
    expected: usize,
  ) {
    let empty = quotient::Program {
      nodes: vec![],
      roots: vec![],
      lookups: vec![],
      args: vec![],
      slots: 0,
    };
    let mut passes =
      vec![passes::Pass::new(empty, all, &[], 0, Bn254::FR_ONE).expect("pass")];
    let device =
      passes::admit::<Bn254>(&mut passes, all, 1 << 20).expect("admitted");
    assert_eq!(device.index, expected);
    for (column, (_, resident, _)) in passes[0].columns.iter().zip(all) {
      let local = resident.is_some_and(|r| r.reservation.index == expected);
      assert_eq!(!column.resident.is_null(), local);
    }
  }
  let host = (&values[..], None, false);
  let on_a = (&values[..], Some(a), false);
  let on_b = (&values[..], Some(b), false);
  expect_device(&[on_a, on_a, on_b, host], a.reservation.index);
  expect_device(&[on_b, host], b.reservation.index);
}

#[test]
#[ignore = "requires one CUDA GPU; two Rayon threads race uncached MSMs and divisions"]
fn concurrent_uncached_msm_completes() {
  with_deadline(120, concurrent_uncached_msm_body);
}

fn concurrent_uncached_msm_body() {
  use std::sync::Barrier;
  configure(Settings { srs_cache: false, ..Settings::default() });
  assert_eq!(
    Devices::get::<Bn254>().ids.len(),
    1,
    "run with one device selected"
  );
  assert!(!srs_residency::enabled());
  let n = 1 << 20;
  let basis: Vec<_> = (1u64..=17)
    .map(|i| {
      (ark_bn254::G1Affine::generator() * ark_bn254::Fr::from(i)).into_affine()
    })
    .collect();
  let points: Vec<_> = (0..n).map(|i| basis[i % basis.len()]).collect();
  let scalars = vec![ark_bn254::Fr::from(37); n];
  assert!(msm_normalization::<Bn254>(&scalars).is_some());
  let expected = ark_bn254::G1Projective::msm(&points, &scalars).unwrap();
  let start = Barrier::new(2);
  std::thread::scope(|scope| {
    let jobs: Vec<_> = (0..2)
      .map(|_| {
        scope.spawn(|| {
          start.wait();
          assert_eq!(msm::<Bn254>(&points, &scalars), expected);
          assert_eq!(
            divide::<Bn254>(&scalars, Bn254::FR_ZERO),
            scalars[..n - 1]
          );
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
  use crate::kzg::{CurveScalar, domain::Radix2Coset, pcs::KzgProverData};
  let n = 1 << 16;
  let mut constant = vec![Bn254::FR_ZERO; n];
  constant[0] = ark_bn254::Fr::from(37);
  let coefficients = vec![ark_bn254::Fr::from(19); n];
  let data = KzgProverData::<Bn254>::coefficient_fixture(
    Radix2Coset { log_size: 16, shift: CurveScalar(Bn254::FR_ONE) },
    vec![constant, coefficients.clone(), coefficients.clone()],
  );
  let matrix = &data.matrices[0];
  let columns: Vec<_> =
    (0..16).into_par_iter().map(|_| matrix.resident_columns()).collect();
  assert!(columns.iter().all(|view| std::ptr::eq(*view, columns[0])));
  let resident = columns[0];
  assert!(resident[0].is_none());
  let z = ark_bn254::Fr::from(7);
  let expected =
    coefficients.iter().rev().fold(Bn254::FR_ZERO, |sum, c| sum * z + c);
  for column in &resident[1..] {
    assert!(column.is_some(), "small resident fixture must fit");
    assert_eq!(
      evaluate_resident::<Bn254>(&coefficients, column.as_deref(), &[z]),
      [expected]
    );
  }
}
