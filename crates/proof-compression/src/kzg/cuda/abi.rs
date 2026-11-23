//! Zero-copy field and point layouts and per-curve FFI dispatch shared with
//! `libix_bn254_cuda.so` and `libix_bls12_381_cuda.so`.

use std::ffi::c_void;
use std::sync::{Mutex, OnceLock};

use super::{Devices, FftJob, SrsCache, lookup, passes, quotient};
use crate::kzg::curve::{Bls12381, Bn254, KzgCurve, bls12_381};
use ark_ff::{BigInt, FftField, PrimeField};

const _: () = {
  assert!(cfg!(target_endian = "little"));
  assert!(std::mem::offset_of!(BigInt<4>, 0) == 0);
  assert!(std::mem::offset_of!(BigInt<6>, 0) == 0);

  // BN254 layout assertions.
  assert!(size_of::<ark_bn254::Fr>() == size_of::<[u64; 4]>());
  assert!(align_of::<ark_bn254::Fr>() == align_of::<[u64; 4]>());
  assert!(std::mem::offset_of!(ark_bn254::Fr, 0) == 0);
  assert!(size_of::<ark_bn254::Fq>() == size_of::<[u64; 4]>());
  assert!(align_of::<ark_bn254::Fq>() == align_of::<[u64; 4]>());
  assert!(std::mem::offset_of!(ark_bn254::Fq, 0) == 0);
  assert!(
    size_of::<ark_bn254::G1Affine>()
      == 2 * size_of::<[u64; 4]>() + size_of::<u64>()
  );
  assert!(align_of::<ark_bn254::G1Affine>() == align_of::<[u64; 4]>());
  assert!(std::mem::offset_of!(ark_bn254::G1Affine, x) == 0);
  assert!(
    std::mem::offset_of!(ark_bn254::G1Affine, y) == size_of::<[u64; 4]>()
  );
  assert!(
    std::mem::offset_of!(ark_bn254::G1Affine, infinity)
      == 2 * size_of::<[u64; 4]>()
  );

  // BLS12-381 layout assertions.
  assert!(size_of::<bls12_381::Fr>() == size_of::<[u64; 4]>());
  assert!(align_of::<bls12_381::Fr>() == align_of::<[u64; 4]>());
  assert!(std::mem::offset_of!(bls12_381::Fr, 0) == 0);
  assert!(size_of::<bls12_381::Fq>() == size_of::<[u64; 6]>());
  assert!(align_of::<bls12_381::Fq>() == align_of::<[u64; 6]>());
  assert!(std::mem::offset_of!(bls12_381::Fq, 0) == 0);
  assert!(
    size_of::<bls12_381::G1Affine>()
      == 2 * size_of::<[u64; 6]>() + size_of::<u64>()
  );
  assert!(align_of::<bls12_381::G1Affine>() == align_of::<[u64; 6]>());
  assert!(std::mem::offset_of!(bls12_381::G1Affine, x) == 0);
  assert!(
    std::mem::offset_of!(bls12_381::G1Affine, y) == size_of::<[u64; 6]>()
  );
  assert!(
    std::mem::offset_of!(bls12_381::G1Affine, infinity)
      == 2 * size_of::<[u64; 6]>()
  );

  // Shared FftJob layout assertions.
  assert!(size_of::<FftJob>() == 40 && align_of::<FftJob>() == 8);
  assert!(std::mem::offset_of!(FftJob, resident_input) == 8);
  assert!(std::mem::offset_of!(FftJob, output) == 16);
  assert!(std::mem::offset_of!(FftJob, input_count) == 24);
  assert!(std::mem::offset_of!(FftJob, resident_output) == 32);
};

/// Internal per-curve CUDA FFI and device-registry dispatch.
#[doc(hidden)]
pub trait CudaCurve: Sized + Send + Sync + 'static {
  type FqLimbs: Copy + Default + Send + Sync + 'static;
  const FQ_LIMBS: usize;
  const DEVICE_AFFINE_BYTES: usize;
  // Sppark's 32-bit domain stride cannot represent 2^32.
  const MAX_FFT_LOG: usize;

  fn devices_slot() -> &'static OnceLock<Devices>;
  fn srs_caches_slot() -> &'static OnceLock<Vec<Mutex<SrsCache>>>;

  unsafe fn ffi_check_field_abi(
    fq: *const [Self::FqLimbs; 3],
    fq_bytes: usize,
    fr: *const [[u64; 4]; 3],
    fr_bytes: usize,
  ) -> i32;
  unsafe fn ffi_range_push(name: *const std::ffi::c_char);
  unsafe fn ffi_range_pop();
  unsafe fn ffi_devices(count: *mut i32) -> i32;
  unsafe fn ffi_device_ordinal(index: i32, ordinal: *mut i32) -> i32;
  unsafe fn ffi_memory(device: i32, free: *mut usize, total: *mut usize)
  -> i32;
  unsafe fn ffi_msm_create(
    device: i32,
    out: *mut *mut c_void,
    points: *const c_void,
    count: usize,
  ) -> i32;
  unsafe fn ffi_msm_invoke(
    device: i32,
    context: *mut c_void,
    out: *mut [Self::FqLimbs; 3],
    scalars: *const [u64; 4],
    count: usize,
    normalization: *const [u64; 4],
  ) -> i32;
  unsafe fn ffi_msm_invoke_resident(
    device: i32,
    context: *mut c_void,
    out: *mut [Self::FqLimbs; 3],
    polynomial: *const c_void,
    offset: usize,
    count: usize,
    normalization: *const [u64; 4],
  ) -> i32;
  unsafe fn ffi_msm_destroy(device: i32, context: *mut c_void) -> i32;
  unsafe fn ffi_polynomial_upload(
    device: i32,
    input: *const [u64; 4],
    count: usize,
    output: *mut *mut c_void,
  ) -> i32;
  unsafe fn ffi_polynomial_destroy(device: i32, pointer: *mut c_void) -> i32;
  unsafe fn ffi_polynomial_sample(
    device: i32,
    polynomial: *const c_void,
    offset: usize,
    count: usize,
    samples: *mut [u64; 4],
  ) -> i32;
  unsafe fn ffi_fft_batch(
    device: i32,
    jobs: *const c_void,
    job_count: usize,
    lg: u32,
    inverse: bool,
    shift: *const [u64; 4],
    slots: usize,
  ) -> i32;
  #[cfg(test)]
  unsafe fn ffi_fft(
    device: i32,
    values: *mut [u64; 4],
    lg: u32,
    inverse: bool,
    shift: *const [u64; 4],
  ) -> i32;
  #[cfg(test)]
  unsafe fn ffi_fft_from(
    device: i32,
    input: *const [u64; 4],
    input_count: usize,
    output: *mut [u64; 4],
    lg: u32,
    inverse: bool,
    shift: *const [u64; 4],
  ) -> i32;
  unsafe fn ffi_evaluate_resident(
    device: i32,
    coefficients: *const [u64; 4],
    resident: *const c_void,
    count: usize,
    points: *const [u64; 4],
    point_count: usize,
    results: *mut [u64; 4],
  ) -> i32;
  unsafe fn ffi_divide(
    device: i32,
    input: *const [u64; 4],
    output: *mut [u64; 4],
    count: usize,
    z: *const [u64; 4],
  ) -> i32;
  unsafe fn ffi_divide_resident(
    device: i32,
    input: *const [u64; 4],
    count: usize,
    z: *const [u64; 4],
    output: *mut *mut c_void,
  ) -> i32;
  unsafe fn ffi_srs_plan(
    device: i32,
    count: usize,
    window: *mut u32,
    persistent: *mut usize,
    temporary: *mut usize,
  ) -> i32;
  unsafe fn ffi_srs_upload(
    device: i32,
    input: *const c_void,
    count: usize,
    output: *mut *mut c_void,
  ) -> i32;
  unsafe fn ffi_srs_destroy(device: i32, points: *mut c_void) -> i32;
  unsafe fn ffi_srs_workspace_create(
    device: i32,
    count: usize,
    output: *mut *mut c_void,
  ) -> i32;
  unsafe fn ffi_srs_workspace_destroy(
    device: i32,
    workspace: *mut c_void,
  ) -> i32;
  #[allow(clippy::too_many_arguments)]
  unsafe fn ffi_srs_msm(
    device: i32,
    workspace: *mut c_void,
    points: *const c_void,
    point_offset: usize,
    output: *mut [Self::FqLimbs; 3],
    host: *const [u64; 4],
    polynomial: *const c_void,
    scalar_offset: usize,
    count: usize,
    normalization: *const [u64; 4],
  ) -> i32;
  #[allow(clippy::too_many_arguments)]
  unsafe fn ffi_lookup(
    device: i32,
    parameters: *const c_void,
    columns: *const c_void,
    column_count: usize,
    evaluation_columns: usize,
    nodes: *const c_void,
    node_count: usize,
    lookups: *const c_void,
    lookup_count: usize,
    args: *const u32,
    arg_count: usize,
    outputs: *const *mut [u64; 4],
    total: *mut [u64; 4],
  ) -> i32;
  #[allow(clippy::too_many_arguments)]
  unsafe fn ffi_quotient(
    device: i32,
    parameters: *const c_void,
    columns: *const c_void,
    column_count: usize,
    evaluation_columns: usize,
    nodes: *const c_void,
    node_count: usize,
    roots: *const u32,
    root_count: usize,
    lookups: *const c_void,
    lookup_count: usize,
    args: *const u32,
    arg_count: usize,
    publics: *const [u64; 4],
    public_count: usize,
    coset_shifts: *const [u64; 4],
    inverse_vanishing: *const [u64; 4],
    outputs: *const *mut [u64; 4],
  ) -> i32;
  unsafe fn ffi_lookup_passes(
    device: i32,
    parameters: *const c_void,
    passes: *const c_void,
    pass_count: usize,
    outputs: *const *mut [u64; 4],
    total: *mut [u64; 4],
  ) -> i32;
  #[allow(clippy::too_many_arguments)]
  unsafe fn ffi_quotient_passes(
    device: i32,
    parameters: *const c_void,
    passes: *const c_void,
    pass_count: usize,
    publics: *const [u64; 4],
    public_count: usize,
    shifts: *const [u64; 4],
    inverse_vanishing: *const [u64; 4],
    outputs: *const *mut [u64; 4],
  ) -> i32;
  #[cfg(test)]
  unsafe fn ffi_ntt_parameters(lg: u32, output: *mut [[u64; 4]; 3]) -> i32;
  #[cfg(test)]
  unsafe fn ffi_field_conformance(
    device: i32,
    fq: *const [Self::FqLimbs; 32],
    fr: *const [[u64; 4]; 32],
    fq_output: *mut [Self::FqLimbs; 192],
    fr_output: *mut [[u64; 4]; 192],
  ) -> i32;
}

macro_rules! impl_cuda_curve {
  (
    curve = $curve:ty,
    fr = $fr:ty,
    fq_limbs = $fq_limbs:literal,
    check_field_abi = $check_field_abi:ident,
    range_push = $range_push:ident,
    range_pop = $range_pop:ident,
    devices = $devices:ident,
    device_ordinal = $device_ordinal:ident,
    memory = $memory:ident,
    msm_create = $msm_create:ident,
    msm_invoke = $msm_invoke:ident,
    msm_invoke_resident = $msm_invoke_resident:ident,
    msm_destroy = $msm_destroy:ident,
    polynomial_upload = $polynomial_upload:ident,
    polynomial_destroy = $polynomial_destroy:ident,
    polynomial_sample = $polynomial_sample:ident,
    fft_batch = $fft_batch:ident,
    fft = $fft:ident,
    fft_from = $fft_from:ident,
    evaluate_resident = $evaluate_resident:ident,
    divide = $divide:ident,
    divide_resident = $divide_resident:ident,
    srs_plan = $srs_plan:ident,
    srs_upload = $srs_upload:ident,
    srs_destroy = $srs_destroy:ident,
    srs_workspace_create = $srs_workspace_create:ident,
    srs_workspace_destroy = $srs_workspace_destroy:ident,
    srs_msm = $srs_msm:ident,
    lookup = $lookup:ident,
    quotient = $quotient:ident,
    lookup_passes = $lookup_passes:ident,
    quotient_passes = $quotient_passes:ident,
    ntt_parameters = $ntt_parameters:ident,
    field_conformance = $field_conformance:ident,
  ) => {
    unsafe extern "C" {
      fn $check_field_abi(
        fq: *const [[u64; $fq_limbs]; 3],
        fq_bytes: usize,
        fr: *const [[u64; 4]; 3],
        fr_bytes: usize,
      ) -> i32;
      fn $range_push(name: *const std::ffi::c_char);
      fn $range_pop();
      fn $devices(count: *mut i32) -> i32;
      fn $device_ordinal(index: i32, ordinal: *mut i32) -> i32;
      fn $memory(device: i32, free: *mut usize, total: *mut usize) -> i32;
      fn $msm_create(
        device: i32,
        out: *mut *mut c_void,
        points: *const c_void,
        count: usize,
      ) -> i32;
      fn $msm_invoke(
        device: i32,
        context: *mut c_void,
        out: *mut [[u64; $fq_limbs]; 3],
        scalars: *const [u64; 4],
        count: usize,
        normalization: *const [u64; 4],
      ) -> i32;
      fn $msm_invoke_resident(
        device: i32,
        context: *mut c_void,
        out: *mut [[u64; $fq_limbs]; 3],
        polynomial: *const c_void,
        offset: usize,
        count: usize,
        normalization: *const [u64; 4],
      ) -> i32;
      fn $msm_destroy(device: i32, context: *mut c_void) -> i32;
      fn $polynomial_upload(
        device: i32,
        input: *const [u64; 4],
        count: usize,
        output: *mut *mut c_void,
      ) -> i32;
      fn $polynomial_destroy(device: i32, pointer: *mut c_void) -> i32;
      fn $polynomial_sample(
        device: i32,
        polynomial: *const c_void,
        offset: usize,
        count: usize,
        samples: *mut [u64; 4],
      ) -> i32;
      fn $fft_batch(
        device: i32,
        jobs: *const FftJob,
        job_count: usize,
        lg: u32,
        inverse: bool,
        shift: *const [u64; 4],
        slots: usize,
      ) -> i32;
      #[cfg(test)]
      fn $fft(
        device: i32,
        values: *mut [u64; 4],
        lg: u32,
        inverse: bool,
        shift: *const [u64; 4],
      ) -> i32;
      #[cfg(test)]
      fn $fft_from(
        device: i32,
        input: *const [u64; 4],
        input_count: usize,
        output: *mut [u64; 4],
        lg: u32,
        inverse: bool,
        shift: *const [u64; 4],
      ) -> i32;
      fn $evaluate_resident(
        device: i32,
        coefficients: *const [u64; 4],
        resident: *const c_void,
        count: usize,
        points: *const [u64; 4],
        point_count: usize,
        results: *mut [u64; 4],
      ) -> i32;
      fn $divide(
        device: i32,
        input: *const [u64; 4],
        output: *mut [u64; 4],
        count: usize,
        z: *const [u64; 4],
      ) -> i32;
      fn $divide_resident(
        device: i32,
        input: *const [u64; 4],
        count: usize,
        z: *const [u64; 4],
        output: *mut *mut c_void,
      ) -> i32;
      fn $srs_plan(
        device: i32,
        count: usize,
        window: *mut u32,
        persistent: *mut usize,
        temporary: *mut usize,
      ) -> i32;
      fn $srs_upload(
        device: i32,
        input: *const c_void,
        count: usize,
        output: *mut *mut c_void,
      ) -> i32;
      fn $srs_destroy(device: i32, points: *mut c_void) -> i32;
      fn $srs_workspace_create(
        device: i32,
        count: usize,
        output: *mut *mut c_void,
      ) -> i32;
      fn $srs_workspace_destroy(device: i32, workspace: *mut c_void) -> i32;
      fn $srs_msm(
        device: i32,
        workspace: *mut c_void,
        points: *const c_void,
        point_offset: usize,
        output: *mut [[u64; $fq_limbs]; 3],
        host: *const [u64; 4],
        polynomial: *const c_void,
        scalar_offset: usize,
        count: usize,
        normalization: *const [u64; 4],
      ) -> i32;
      fn $lookup(
        device: i32,
        parameters: *const lookup::Parameters,
        columns: *const quotient::Column,
        column_count: usize,
        evaluation_columns: usize,
        nodes: *const quotient::Instruction,
        node_count: usize,
        lookups: *const quotient::Lookup,
        lookup_count: usize,
        args: *const u32,
        arg_count: usize,
        outputs: *const *mut [u64; 4],
        total: *mut [u64; 4],
      ) -> i32;
      fn $quotient(
        device: i32,
        parameters: *const quotient::Parameters,
        columns: *const quotient::Column,
        column_count: usize,
        evaluation_columns: usize,
        nodes: *const quotient::Instruction,
        node_count: usize,
        roots: *const u32,
        root_count: usize,
        lookups: *const quotient::Lookup,
        lookup_count: usize,
        args: *const u32,
        arg_count: usize,
        publics: *const [u64; 4],
        public_count: usize,
        coset_shifts: *const [u64; 4],
        inverse_vanishing: *const [u64; 4],
        outputs: *const *mut [u64; 4],
      ) -> i32;
      fn $lookup_passes(
        device: i32,
        parameters: *const lookup::Parameters,
        passes: *const passes::NativePass,
        pass_count: usize,
        outputs: *const *mut [u64; 4],
        total: *mut [u64; 4],
      ) -> i32;
      fn $quotient_passes(
        device: i32,
        parameters: *const quotient::Parameters,
        passes: *const passes::NativePass,
        pass_count: usize,
        publics: *const [u64; 4],
        public_count: usize,
        shifts: *const [u64; 4],
        inverse_vanishing: *const [u64; 4],
        outputs: *const *mut [u64; 4],
      ) -> i32;
      #[cfg(test)]
      fn $ntt_parameters(lg: u32, output: *mut [[u64; 4]; 3]) -> i32;
      #[cfg(test)]
      fn $field_conformance(
        device: i32,
        fq: *const [[u64; $fq_limbs]; 32],
        fr: *const [[u64; 4]; 32],
        fq_output: *mut [[u64; $fq_limbs]; 192],
        fr_output: *mut [[u64; 4]; 192],
      ) -> i32;
    }

    impl CudaCurve for $curve {
      type FqLimbs = [u64; $fq_limbs];
      const FQ_LIMBS: usize = $fq_limbs;
      const DEVICE_AFFINE_BYTES: usize = 2 * $fq_limbs * size_of::<u64>();
      const MAX_FFT_LOG: usize = if <$fr as FftField>::TWO_ADICITY < 31 {
        <$fr as FftField>::TWO_ADICITY as usize
      } else {
        31
      };

      fn devices_slot() -> &'static OnceLock<Devices> {
        static SLOT: OnceLock<Devices> = OnceLock::new();
        &SLOT
      }

      fn srs_caches_slot() -> &'static OnceLock<Vec<Mutex<SrsCache>>> {
        static SLOT: OnceLock<Vec<Mutex<SrsCache>>> = OnceLock::new();
        &SLOT
      }

      unsafe fn ffi_check_field_abi(
        fq: *const [Self::FqLimbs; 3],
        fq_bytes: usize,
        fr: *const [[u64; 4]; 3],
        fr_bytes: usize,
      ) -> i32 {
        unsafe { $check_field_abi(fq, fq_bytes, fr, fr_bytes) }
      }
      unsafe fn ffi_range_push(name: *const std::ffi::c_char) {
        unsafe { $range_push(name) }
      }
      unsafe fn ffi_range_pop() {
        unsafe { $range_pop() }
      }
      unsafe fn ffi_devices(count: *mut i32) -> i32 {
        unsafe { $devices(count) }
      }
      unsafe fn ffi_device_ordinal(index: i32, ordinal: *mut i32) -> i32 {
        unsafe { $device_ordinal(index, ordinal) }
      }
      unsafe fn ffi_memory(
        device: i32,
        free: *mut usize,
        total: *mut usize,
      ) -> i32 {
        unsafe { $memory(device, free, total) }
      }
      unsafe fn ffi_msm_create(
        device: i32,
        out: *mut *mut c_void,
        points: *const c_void,
        count: usize,
      ) -> i32 {
        unsafe { $msm_create(device, out, points, count) }
      }
      unsafe fn ffi_msm_invoke(
        device: i32,
        context: *mut c_void,
        out: *mut [Self::FqLimbs; 3],
        scalars: *const [u64; 4],
        count: usize,
        normalization: *const [u64; 4],
      ) -> i32 {
        unsafe {
          $msm_invoke(device, context, out, scalars, count, normalization)
        }
      }
      unsafe fn ffi_msm_invoke_resident(
        device: i32,
        context: *mut c_void,
        out: *mut [Self::FqLimbs; 3],
        polynomial: *const c_void,
        offset: usize,
        count: usize,
        normalization: *const [u64; 4],
      ) -> i32 {
        unsafe {
          $msm_invoke_resident(
            device,
            context,
            out,
            polynomial,
            offset,
            count,
            normalization,
          )
        }
      }
      unsafe fn ffi_msm_destroy(device: i32, context: *mut c_void) -> i32 {
        unsafe { $msm_destroy(device, context) }
      }
      unsafe fn ffi_polynomial_upload(
        device: i32,
        input: *const [u64; 4],
        count: usize,
        output: *mut *mut c_void,
      ) -> i32 {
        unsafe { $polynomial_upload(device, input, count, output) }
      }
      unsafe fn ffi_polynomial_destroy(
        device: i32,
        pointer: *mut c_void,
      ) -> i32 {
        unsafe { $polynomial_destroy(device, pointer) }
      }
      unsafe fn ffi_polynomial_sample(
        device: i32,
        polynomial: *const c_void,
        offset: usize,
        count: usize,
        samples: *mut [u64; 4],
      ) -> i32 {
        unsafe {
          $polynomial_sample(device, polynomial, offset, count, samples)
        }
      }
      unsafe fn ffi_fft_batch(
        device: i32,
        jobs: *const c_void,
        job_count: usize,
        lg: u32,
        inverse: bool,
        shift: *const [u64; 4],
        slots: usize,
      ) -> i32 {
        unsafe {
          $fft_batch(device, jobs.cast(), job_count, lg, inverse, shift, slots)
        }
      }
      #[cfg(test)]
      unsafe fn ffi_fft(
        device: i32,
        values: *mut [u64; 4],
        lg: u32,
        inverse: bool,
        shift: *const [u64; 4],
      ) -> i32 {
        unsafe { $fft(device, values, lg, inverse, shift) }
      }
      #[cfg(test)]
      unsafe fn ffi_fft_from(
        device: i32,
        input: *const [u64; 4],
        input_count: usize,
        output: *mut [u64; 4],
        lg: u32,
        inverse: bool,
        shift: *const [u64; 4],
      ) -> i32 {
        unsafe {
          $fft_from(device, input, input_count, output, lg, inverse, shift)
        }
      }
      unsafe fn ffi_evaluate_resident(
        device: i32,
        coefficients: *const [u64; 4],
        resident: *const c_void,
        count: usize,
        points: *const [u64; 4],
        point_count: usize,
        results: *mut [u64; 4],
      ) -> i32 {
        unsafe {
          $evaluate_resident(
            device,
            coefficients,
            resident,
            count,
            points,
            point_count,
            results,
          )
        }
      }
      unsafe fn ffi_divide(
        device: i32,
        input: *const [u64; 4],
        output: *mut [u64; 4],
        count: usize,
        z: *const [u64; 4],
      ) -> i32 {
        unsafe { $divide(device, input, output, count, z) }
      }
      unsafe fn ffi_divide_resident(
        device: i32,
        input: *const [u64; 4],
        count: usize,
        z: *const [u64; 4],
        output: *mut *mut c_void,
      ) -> i32 {
        unsafe { $divide_resident(device, input, count, z, output) }
      }
      unsafe fn ffi_srs_plan(
        device: i32,
        count: usize,
        window: *mut u32,
        persistent: *mut usize,
        temporary: *mut usize,
      ) -> i32 {
        unsafe { $srs_plan(device, count, window, persistent, temporary) }
      }
      unsafe fn ffi_srs_upload(
        device: i32,
        input: *const c_void,
        count: usize,
        output: *mut *mut c_void,
      ) -> i32 {
        unsafe { $srs_upload(device, input, count, output) }
      }
      unsafe fn ffi_srs_destroy(device: i32, points: *mut c_void) -> i32 {
        unsafe { $srs_destroy(device, points) }
      }
      unsafe fn ffi_srs_workspace_create(
        device: i32,
        count: usize,
        output: *mut *mut c_void,
      ) -> i32 {
        unsafe { $srs_workspace_create(device, count, output) }
      }
      unsafe fn ffi_srs_workspace_destroy(
        device: i32,
        workspace: *mut c_void,
      ) -> i32 {
        unsafe { $srs_workspace_destroy(device, workspace) }
      }
      unsafe fn ffi_srs_msm(
        device: i32,
        workspace: *mut c_void,
        points: *const c_void,
        point_offset: usize,
        output: *mut [Self::FqLimbs; 3],
        host: *const [u64; 4],
        polynomial: *const c_void,
        scalar_offset: usize,
        count: usize,
        normalization: *const [u64; 4],
      ) -> i32 {
        unsafe {
          $srs_msm(
            device,
            workspace,
            points,
            point_offset,
            output,
            host,
            polynomial,
            scalar_offset,
            count,
            normalization,
          )
        }
      }
      unsafe fn ffi_lookup(
        device: i32,
        parameters: *const c_void,
        columns: *const c_void,
        column_count: usize,
        evaluation_columns: usize,
        nodes: *const c_void,
        node_count: usize,
        lookups: *const c_void,
        lookup_count: usize,
        args: *const u32,
        arg_count: usize,
        outputs: *const *mut [u64; 4],
        total: *mut [u64; 4],
      ) -> i32 {
        unsafe {
          $lookup(
            device,
            parameters.cast(),
            columns.cast(),
            column_count,
            evaluation_columns,
            nodes.cast(),
            node_count,
            lookups.cast(),
            lookup_count,
            args,
            arg_count,
            outputs,
            total,
          )
        }
      }
      unsafe fn ffi_quotient(
        device: i32,
        parameters: *const c_void,
        columns: *const c_void,
        column_count: usize,
        evaluation_columns: usize,
        nodes: *const c_void,
        node_count: usize,
        roots: *const u32,
        root_count: usize,
        lookups: *const c_void,
        lookup_count: usize,
        args: *const u32,
        arg_count: usize,
        publics: *const [u64; 4],
        public_count: usize,
        coset_shifts: *const [u64; 4],
        inverse_vanishing: *const [u64; 4],
        outputs: *const *mut [u64; 4],
      ) -> i32 {
        unsafe {
          $quotient(
            device,
            parameters.cast(),
            columns.cast(),
            column_count,
            evaluation_columns,
            nodes.cast(),
            node_count,
            roots,
            root_count,
            lookups.cast(),
            lookup_count,
            args,
            arg_count,
            publics,
            public_count,
            coset_shifts,
            inverse_vanishing,
            outputs,
          )
        }
      }
      unsafe fn ffi_lookup_passes(
        device: i32,
        parameters: *const c_void,
        passes: *const c_void,
        pass_count: usize,
        outputs: *const *mut [u64; 4],
        total: *mut [u64; 4],
      ) -> i32 {
        unsafe {
          $lookup_passes(
            device,
            parameters.cast(),
            passes.cast(),
            pass_count,
            outputs,
            total,
          )
        }
      }
      unsafe fn ffi_quotient_passes(
        device: i32,
        parameters: *const c_void,
        passes: *const c_void,
        pass_count: usize,
        publics: *const [u64; 4],
        public_count: usize,
        shifts: *const [u64; 4],
        inverse_vanishing: *const [u64; 4],
        outputs: *const *mut [u64; 4],
      ) -> i32 {
        unsafe {
          $quotient_passes(
            device,
            parameters.cast(),
            passes.cast(),
            pass_count,
            publics,
            public_count,
            shifts,
            inverse_vanishing,
            outputs,
          )
        }
      }
      #[cfg(test)]
      unsafe fn ffi_ntt_parameters(lg: u32, output: *mut [[u64; 4]; 3]) -> i32 {
        unsafe { $ntt_parameters(lg, output) }
      }
      #[cfg(test)]
      unsafe fn ffi_field_conformance(
        device: i32,
        fq: *const [Self::FqLimbs; 32],
        fr: *const [[u64; 4]; 32],
        fq_output: *mut [Self::FqLimbs; 192],
        fr_output: *mut [[u64; 4]; 192],
      ) -> i32 {
        unsafe { $field_conformance(device, fq, fr, fq_output, fr_output) }
      }
    }
  };
}

impl_cuda_curve!(
  curve = Bn254,
  fr = ark_bn254::Fr,
  fq_limbs = 4,
  check_field_abi = ix_kzg_check_field_abi,
  range_push = ix_kzg_range_push,
  range_pop = ix_kzg_range_pop,
  devices = ix_kzg_devices,
  device_ordinal = ix_kzg_device_ordinal,
  memory = ix_kzg_memory,
  msm_create = ix_kzg_msm_create,
  msm_invoke = ix_kzg_msm_invoke,
  msm_invoke_resident = ix_kzg_msm_invoke_resident,
  msm_destroy = ix_kzg_msm_destroy,
  polynomial_upload = ix_kzg_polynomial_upload,
  polynomial_destroy = ix_kzg_polynomial_destroy,
  polynomial_sample = ix_kzg_polynomial_sample,
  fft_batch = ix_kzg_fft_batch,
  fft = ix_kzg_fft,
  fft_from = ix_kzg_fft_from,
  evaluate_resident = ix_kzg_evaluate_resident,
  divide = ix_kzg_divide,
  divide_resident = ix_kzg_divide_resident,
  srs_plan = ix_kzg_srs_plan,
  srs_upload = ix_kzg_srs_upload,
  srs_destroy = ix_kzg_srs_destroy,
  srs_workspace_create = ix_kzg_srs_workspace_create,
  srs_workspace_destroy = ix_kzg_srs_workspace_destroy,
  srs_msm = ix_kzg_srs_msm,
  lookup = ix_kzg_lookup,
  quotient = ix_kzg_quotient,
  lookup_passes = ix_kzg_lookup_passes,
  quotient_passes = ix_kzg_quotient_passes,
  ntt_parameters = ix_kzg_ntt_parameters,
  field_conformance = ix_kzg_field_conformance,
);

impl_cuda_curve!(
  curve = Bls12381,
  fr = bls12_381::Fr,
  fq_limbs = 6,
  check_field_abi = ix_kzg_bls12_381_check_field_abi,
  range_push = ix_kzg_bls12_381_range_push,
  range_pop = ix_kzg_bls12_381_range_pop,
  devices = ix_kzg_bls12_381_devices,
  device_ordinal = ix_kzg_bls12_381_device_ordinal,
  memory = ix_kzg_bls12_381_memory,
  msm_create = ix_kzg_bls12_381_msm_create,
  msm_invoke = ix_kzg_bls12_381_msm_invoke,
  msm_invoke_resident = ix_kzg_bls12_381_msm_invoke_resident,
  msm_destroy = ix_kzg_bls12_381_msm_destroy,
  polynomial_upload = ix_kzg_bls12_381_polynomial_upload,
  polynomial_destroy = ix_kzg_bls12_381_polynomial_destroy,
  polynomial_sample = ix_kzg_bls12_381_polynomial_sample,
  fft_batch = ix_kzg_bls12_381_fft_batch,
  fft = ix_kzg_bls12_381_fft,
  fft_from = ix_kzg_bls12_381_fft_from,
  evaluate_resident = ix_kzg_bls12_381_evaluate_resident,
  divide = ix_kzg_bls12_381_divide,
  divide_resident = ix_kzg_bls12_381_divide_resident,
  srs_plan = ix_kzg_bls12_381_srs_plan,
  srs_upload = ix_kzg_bls12_381_srs_upload,
  srs_destroy = ix_kzg_bls12_381_srs_destroy,
  srs_workspace_create = ix_kzg_bls12_381_srs_workspace_create,
  srs_workspace_destroy = ix_kzg_bls12_381_srs_workspace_destroy,
  srs_msm = ix_kzg_bls12_381_srs_msm,
  lookup = ix_kzg_bls12_381_lookup,
  quotient = ix_kzg_bls12_381_quotient,
  lookup_passes = ix_kzg_bls12_381_lookup_passes,
  quotient_passes = ix_kzg_bls12_381_quotient_passes,
  ntt_parameters = ix_kzg_bls12_381_ntt_parameters,
  field_conformance = ix_kzg_bls12_381_field_conformance,
);

fn matches_native<C: KzgCurve>(
  fq: &[C::FqLimbs; 3],
  fr: &[[u64; 4]; 3],
) -> bool {
  // The native check reads only these fixed-size arrays and does not use CUDA.
  unsafe {
    C::ffi_check_field_abi(fq, size_of_val(fq), fr, size_of_val(fr)) == 0
  }
}

pub(super) fn validate<C: KzgCurve>() {
  assert!(
    matches_native::<C>(
      &C::fq_abi_triple(),
      &[C::Fr::MODULUS.0, C::FR_MONT_ONE, C::FR_MONT_R2],
    ),
    "KZG {} native and Rust field representations differ",
    C::NAME
  );
}

#[cfg(test)]
mod tests {
  use super::*;

  fn check_curve<C: KzgCurve>()
  where
    C::FqLimbs: AsMut<[u64]>,
  {
    validate::<C>();
    let fq = C::fq_abi_triple();
    let fr = [C::Fr::MODULUS.0, C::FR_MONT_ONE, C::FR_MONT_R2];
    for parameter in 0..3 {
      let mut wrong_fq = fq;
      wrong_fq[parameter].as_mut().reverse();
      assert!(!matches_native::<C>(&wrong_fq, &fr));
      let mut wrong_fr = fr;
      wrong_fr[parameter].reverse();
      assert!(!matches_native::<C>(&fq, &wrong_fr));
    }
    assert_ne!(
      unsafe {
        C::ffi_check_field_abi(&fq, size_of_val(&fq) - 8, &fr, size_of_val(&fr))
      },
      0
    );
  }

  #[test]
  fn native_montgomery_parameters_match_arkworks_for_both_curves() {
    check_curve::<Bn254>();
    check_curve::<Bls12381>();
  }
}
