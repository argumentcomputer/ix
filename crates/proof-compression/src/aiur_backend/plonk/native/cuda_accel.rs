//! Curve-generic MSM and FFT acceleration for native PLONK (`Bn254` and
//! `Bls12381`).
//!
//! Under `#[cfg(feature = "cuda")]` with `use_cuda = true`, dispatches large
//! MSMs and batched FFTs directly to Ix's sppark CUDA FFI (`libix_bn254_cuda.so`
//! and `libix_bls12_381_cuda.so` via [`crate::kzg::cuda::CudaCurve`]).
//! Otherwise executes cleanly on CPU using [`KzgCurve::cpu_msm`] (GLV Pippenger
//! on BN254, parallel Pippenger on BLS12-381) and parallel `ark-poly` FFTs.

use crate::kzg::curve::{G1AffineOf, G1ProjectiveOf, KzgCurve};
use ark_ff::Zero;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use p3_maybe_rayon::prelude::*;
use std::marker::PhantomData;

#[cfg(feature = "cuda")]
const CUDA_MSM_THRESHOLD: usize = 4096;
#[cfg(feature = "cuda")]
const CUDA_FFT_MIN_LOG: usize = 12;

/// Accelerator handle for native PLONK setup and proving on curve `C`.
#[derive(Clone, Copy, Debug)]
pub struct PlonkAccelerator<C: KzgCurve> {
  use_cuda: bool,
  _curve: PhantomData<C>,
}

impl<C: KzgCurve> Default for PlonkAccelerator<C> {
  fn default() -> Self {
    Self::cpu()
  }
}

impl<C: KzgCurve> PlonkAccelerator<C> {
  /// CPU-only execution (default; zero GPU requirement).
  pub const fn cpu() -> Self {
    Self { use_cuda: false, _curve: PhantomData }
  }

  /// Enable CUDA acceleration when compiled with `--features cuda`.
  /// Returns an error if CUDA support was not compiled in or no compatible
  /// device is visible.
  pub fn cuda() -> Result<Self, String> {
    #[cfg(feature = "cuda")]
    {
      cuda_impl::ensure_device::<C>()?;
      Ok(Self { use_cuda: true, _curve: PhantomData })
    }
    #[cfg(not(feature = "cuda"))]
    {
      Err(
        "native PLONK CUDA acceleration requires compiling with --features cuda"
          .into(),
      )
    }
  }

  /// Construct from a boolean flag (`true` requests CUDA when compiled in).
  pub fn new(use_cuda: bool) -> Result<Self, String> {
    if use_cuda { Self::cuda() } else { Ok(Self::cpu()) }
  }

  /// Whether GPU dispatch is active on this accelerator.
  pub const fn is_cuda(&self) -> bool {
    self.use_cuda
  }

  /// Compute a single multi-scalar multiplication `Σ bases[i] · scalars[i]`.
  pub fn msm(
    &self,
    bases: &[G1AffineOf<C>],
    scalars: &[C::Fr],
  ) -> G1ProjectiveOf<C> {
    assert_eq!(bases.len(), scalars.len(), "MSM length mismatch");
    if bases.is_empty() {
      return G1ProjectiveOf::<C>::zero();
    }
    #[cfg(feature = "cuda")]
    if self.use_cuda && bases.len() >= CUDA_MSM_THRESHOLD {
      return cuda_impl::msm_batch::<C>(bases, &[scalars])
        .pop()
        .expect("single MSM output");
    }
    C::cpu_msm(bases, scalars)
  }

  /// Compute several MSMs against a shared `bases` slice (amortizes GPU upload
  /// under CUDA). Each column may have length `<= bases.len()`.
  pub fn msm_batch(
    &self,
    bases: &[G1AffineOf<C>],
    columns: &[&[C::Fr]],
  ) -> Vec<G1ProjectiveOf<C>> {
    if columns.is_empty() {
      return Vec::new();
    }
    let max_len = columns.iter().map(|c| c.len()).max().unwrap_or(0);
    assert!(max_len <= bases.len(), "MSM column exceeds SRS length");
    #[cfg(feature = "cuda")]
    if self.use_cuda && max_len >= CUDA_MSM_THRESHOLD {
      let same_len = columns.iter().all(|c| c.len() == max_len);
      if same_len {
        return cuda_impl::msm_batch::<C>(&bases[..max_len], columns);
      }
      // Pad shorter columns to `max_len` with zeros so one upload serves all.
      let owned: Vec<Vec<C::Fr>> = columns
        .iter()
        .map(|c| {
          let mut v = Vec::with_capacity(max_len);
          v.extend_from_slice(c);
          v.resize(max_len, C::FR_ZERO);
          v
        })
        .collect();
      let refs: Vec<&[C::Fr]> = owned.iter().map(Vec::as_slice).collect();
      return cuda_impl::msm_batch::<C>(&bases[..max_len], &refs);
    }
    columns.iter().map(|c| C::cpu_msm(&bases[..c.len()], c)).collect()
  }

  /// In-place inverse FFT over the radix-2 subgroup of size `values.len()`.
  pub fn ifft_in_place(&self, values: &mut Vec<C::Fr>) {
    let n = values.len();
    assert!(n.is_power_of_two());
    if n <= 1 {
      return;
    }
    #[cfg(feature = "cuda")]
    if self.use_cuda && (n.ilog2() as usize) >= CUDA_FFT_MIN_LOG {
      let mut owned = vec![std::mem::take(values)];
      cuda_impl::fft_batch_in_place::<C>(&mut owned, true, C::FR_ONE);
      *values = owned.pop().expect("single FFT output");
      return;
    }
    let domain =
      Radix2EvaluationDomain::<C::Fr>::new(n).expect("valid radix-2 domain");
    domain.ifft_in_place(values);
  }

  /// In-place inverse FFT on a batch of equal-length evaluation vectors.
  pub fn ifft_batch(&self, polys: &mut [Vec<C::Fr>]) {
    if polys.is_empty() {
      return;
    }
    let n = polys[0].len();
    assert!(n.is_power_of_two() && polys.iter().all(|p| p.len() == n));
    if n <= 1 {
      return;
    }
    #[cfg(feature = "cuda")]
    if self.use_cuda && (n.ilog2() as usize) >= CUDA_FFT_MIN_LOG {
      cuda_impl::fft_batch_in_place::<C>(polys, true, C::FR_ONE);
      return;
    }
    let domain =
      Radix2EvaluationDomain::<C::Fr>::new(n).expect("valid radix-2 domain");
    polys.par_iter_mut().for_each(|p| domain.ifft_in_place(p));
  }

  /// Evaluate a batch of monomial-basis polynomials (each length `n`, a power
  /// of two) on the coset `shift · H_n`.
  pub fn coset_fft_batch(
    &self,
    polys: &[&[C::Fr]],
    shift: C::Fr,
  ) -> Vec<Vec<C::Fr>> {
    if polys.is_empty() {
      return Vec::new();
    }
    let n = polys[0].len();
    assert!(n.is_power_of_two() && polys.iter().all(|p| p.len() == n));
    #[cfg(feature = "cuda")]
    if self.use_cuda && (n.ilog2() as usize) >= CUDA_FFT_MIN_LOG {
      let mut out: Vec<Vec<C::Fr>> =
        polys.iter().map(|p| (*p).to_vec()).collect();
      cuda_impl::fft_batch_in_place::<C>(&mut out, false, shift);
      return out;
    }
    let domain = Radix2EvaluationDomain::<C::Fr>::new(n)
      .expect("valid radix-2 domain")
      .get_coset(shift)
      .expect("nonzero coset shift");
    polys
      .par_iter()
      .map(|p| {
        let mut buf = (*p).to_vec();
        domain.fft_in_place(&mut buf);
        buf
      })
      .collect()
  }

  /// In-place inverse coset FFT from evaluations on `shift · H_n` to monomial
  /// coefficients.
  pub fn coset_ifft_in_place(&self, values: &mut Vec<C::Fr>, shift: C::Fr) {
    let n = values.len();
    assert!(n.is_power_of_two());
    if n <= 1 {
      return;
    }
    #[cfg(feature = "cuda")]
    if self.use_cuda && (n.ilog2() as usize) >= CUDA_FFT_MIN_LOG {
      let mut owned = vec![std::mem::take(values)];
      cuda_impl::fft_batch_in_place::<C>(&mut owned, true, shift);
      *values = owned.pop().expect("single FFT output");
      return;
    }
    let domain = Radix2EvaluationDomain::<C::Fr>::new(n)
      .expect("valid radix-2 domain")
      .get_coset(shift)
      .expect("nonzero coset shift");
    domain.ifft_in_place(values);
  }
}

#[cfg(feature = "cuda")]
mod cuda_impl {
  use crate::kzg::cuda::{CudaCurve, FftJob};
  use crate::kzg::curve::{G1AffineOf, G1ProjectiveOf, KzgCurve};
  use ark_ff::{Field, PrimeField};
  use std::ffi::c_void;

  #[repr(C)]
  struct NativeFftJob {
    input: *const [u64; 4],
    resident_input: *const c_void,
    output: *mut [u64; 4],
    input_count: usize,
    resident_output: *mut *mut c_void,
  }

  const _: () = {
    assert!(size_of::<NativeFftJob>() == size_of::<FftJob>());
    assert!(align_of::<NativeFftJob>() == align_of::<FftJob>());
    assert!(size_of::<NativeFftJob>() == 40);
  };

  pub(super) fn ensure_device<C: KzgCurve>() -> Result<i32, String> {
    let fq = C::fq_abi_triple();
    let fr = [C::Fr::MODULUS.0, C::FR_MONT_ONE, C::FR_MONT_R2];
    let abi_code = unsafe {
      C::ffi_check_field_abi(&fq, size_of_val(&fq), &fr, size_of_val(&fr))
    };
    if abi_code != 0 {
      return Err(format!(
        "CUDA {} field ABI check failed ({abi_code})",
        C::NAME
      ));
    }
    let mut count = 0i32;
    let code = unsafe { C::ffi_devices(&mut count) };
    if code != 0 || count <= 0 {
      return Err(format!(
        "no visible {} CUDA device (status {code})",
        C::NAME
      ));
    }
    let mut ordinal = -1i32;
    let code = unsafe { C::ffi_device_ordinal(0, &mut ordinal) };
    if code != 0 {
      return Err(format!("CUDA device ordinal lookup failed ({code})"));
    }
    Ok(ordinal)
  }

  /// RAII guard owning a GPU MSM context allocated by `C::ffi_msm_create`,
  /// ensuring `C::ffi_msm_destroy` runs even if an invoke panics/unwinds.
  struct MsmContextGuard<C: KzgCurve> {
    device: i32,
    context: *mut c_void,
    _curve: std::marker::PhantomData<C>,
  }

  impl<C: KzgCurve> MsmContextGuard<C> {
    fn create(device: i32, bases: &[G1AffineOf<C>]) -> Self {
      let mut context: *mut c_void = std::ptr::null_mut();
      let code = unsafe {
        C::ffi_msm_create(
          device,
          &mut context,
          bases.as_ptr().cast(),
          bases.len(),
        )
      };
      assert_eq!(code, 0, "native PLONK CUDA MSM upload failed ({code})");
      assert!(!context.is_null());
      Self { device, context, _curve: std::marker::PhantomData }
    }

    fn as_ptr(&self) -> *mut c_void {
      self.context
    }

    fn destroy(mut self) {
      let ctx = std::mem::replace(&mut self.context, std::ptr::null_mut());
      if !ctx.is_null() {
        let destroy_code = unsafe { C::ffi_msm_destroy(self.device, ctx) };
        assert_eq!(
          destroy_code, 0,
          "native PLONK CUDA MSM destroy failed ({destroy_code})"
        );
      }
    }
  }

  impl<C: KzgCurve> Drop for MsmContextGuard<C> {
    fn drop(&mut self) {
      let ctx = std::mem::replace(&mut self.context, std::ptr::null_mut());
      if !ctx.is_null() {
        // Best-effort cleanup during unwind without risking a double-panic.
        let _ = unsafe { C::ffi_msm_destroy(self.device, ctx) };
      }
    }
  }

  pub(super) fn msm_batch<C: KzgCurve>(
    bases: &[G1AffineOf<C>],
    columns: &[&[C::Fr]],
  ) -> Vec<G1ProjectiveOf<C>> {
    let device = ensure_device::<C>().expect("CUDA device validated");
    let guard = MsmContextGuard::<C>::create(device, bases);

    let mut results = Vec::with_capacity(columns.len());
    for scalars in columns {
      let mut out = [C::FqLimbs::default(); 3];
      let code = unsafe {
        C::ffi_msm_invoke(
          device,
          guard.as_ptr(),
          &mut out,
          scalars.as_ptr().cast(),
          scalars.len(),
          std::ptr::null(),
        )
      };
      assert_eq!(code, 0, "native PLONK CUDA MSM invoke failed ({code})");
      results.push(G1ProjectiveOf::<C>::new_unchecked(
        C::fq_from_mont_limbs_unchecked(out[0]),
        C::fq_from_mont_limbs_unchecked(out[1]),
        C::fq_from_mont_limbs_unchecked(out[2]),
      ));
    }

    guard.destroy();
    results
  }

  pub(super) fn fft_batch_in_place<C: KzgCurve>(
    polys: &mut [Vec<C::Fr>],
    inverse: bool,
    shift: C::Fr,
  ) {
    let device = ensure_device::<C>().expect("CUDA device validated");
    let n = polys[0].len();
    let lg = n.ilog2();
    assert!((lg as usize) <= C::MAX_FFT_LOG, "domain exceeds CUDA FFT limit");
    let effective_shift =
      if inverse { shift.inverse().unwrap() } else { shift };
    let mut outputs: Vec<Vec<C::Fr>> =
      polys.iter().map(|_| vec![C::FR_ZERO; n]).collect();
    let jobs: Vec<NativeFftJob> = polys
      .iter()
      .zip(&mut outputs)
      .map(|(inp, out)| NativeFftJob {
        input: inp.as_ptr().cast(),
        resident_input: std::ptr::null(),
        output: out.as_mut_ptr().cast(),
        input_count: n,
        resident_output: std::ptr::null_mut(),
      })
      .collect();
    let slots = jobs.len().min(2);
    let code = unsafe {
      C::ffi_fft_batch(
        device,
        jobs.as_ptr().cast(),
        jobs.len(),
        lg,
        inverse,
        C::fr_mont_limbs_ref(&effective_shift),
        slots,
      )
    };
    assert_eq!(code, 0, "native PLONK CUDA FFT batch failed ({code})");
    for (dst, src) in polys.iter_mut().zip(outputs) {
      *dst = src;
    }
  }
}
