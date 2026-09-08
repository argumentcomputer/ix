//! Profile requested heap bytes while proving a synthetic multiplication circuit.
//! This fixture uses a public test-only tau. It is not a Flock proof or a
//! production setup. Allocator overhead, transient realloc internals, stack,
//! and resident pages are not measured; setup allocations are counted only
//! while they remain live during proving.

use ark_bls12_381::{Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{One, PrimeField};
use ix_fflonk::{
  FflonkBlindingV1, KzgUniversalSrsV1, arithmetize_r1cs, plan_fflonk_capacity,
  preprocess_fflonk, prove_fflonk, required_fflonk_srs_degree, verify_fflonk,
};
use ix_terminal_circuit::{
  CanonicalR1csV1, ConstraintPhase, LinearCombination, R1csBuilder, Witness,
};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::time::Instant;

struct CountedAllocator;
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

fn added(bytes: usize) {
  let live = LIVE.fetch_add(bytes, Relaxed) + bytes;
  PEAK.fetch_max(live, Relaxed);
}

// SAFETY: Every allocation operation forwards the caller's original pointer
// and layout to System. Counters never inspect or modify allocated storage.
unsafe impl GlobalAlloc for CountedAllocator {
  unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
    let pointer = unsafe { System.alloc(layout) };
    if !pointer.is_null() {
      added(layout.size());
    }
    pointer
  }

  unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
    let pointer = unsafe { System.alloc_zeroed(layout) };
    if !pointer.is_null() {
      added(layout.size());
    }
    pointer
  }

  unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
    unsafe { System.dealloc(pointer, layout) };
    LIVE.fetch_sub(layout.size(), Relaxed);
  }

  unsafe fn realloc(
    &self,
    pointer: *mut u8,
    layout: Layout,
    size: usize,
  ) -> *mut u8 {
    let result = unsafe { System.realloc(pointer, layout, size) };
    if !result.is_null() {
      if size >= layout.size() {
        added(size - layout.size());
      } else {
        LIVE.fetch_sub(layout.size() - size, Relaxed);
      }
    }
    result
  }
}

#[global_allocator]
static ALLOCATOR: CountedAllocator = CountedAllocator;

fn fixture(size: usize) -> (CanonicalR1csV1, Witness) {
  let mut builder = R1csBuilder::new();
  let public = builder.alloc_public(Fr::from(3u64)).unwrap();
  for index in 0..size - 4 {
    let value = Fr::from(u64::try_from(index).unwrap() + 5);
    let private = builder.alloc_private(value).unwrap();
    let product = builder.alloc_private(Fr::from(3u64) * value).unwrap();
    builder.enforce(
      ConstraintPhase::Statement,
      LinearCombination::from_variable(public),
      LinearCombination::from_variable(private),
      LinearCombination::from_variable(product),
    );
  }
  builder.finish().unwrap()
}

fn test_srs(max_degree: usize) -> KzgUniversalSrsV1 {
  let tau = Fr::from(29u64);
  let mut scalar = Fr::one();
  let powers = (0..=max_degree)
    .map(|_| {
      let point = G1Affine::generator().mul_bigint(scalar.into_bigint());
      scalar *= tau;
      point.into_affine()
    })
    .collect();
  let tau_g2 =
    G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine();
  KzgUniversalSrsV1::new(powers, G2Affine::generator(), tau_g2).unwrap()
}

fn main() {
  let log_size: u32 =
    std::env::args().nth(1).unwrap_or_else(|| "14".into()).parse().unwrap();
  assert!(
    (3..=20).contains(&log_size),
    "choose a domain log size from 3 to 20"
  );
  let size = 1usize << log_size;
  let size_u64 = u64::try_from(size).unwrap();
  println!("Synthetic multiplication fixture; public test-only tau; n={size}");
  let (r1cs, witness) = fixture(size);
  let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
  assert_eq!(arithmetization.census().domain_size, size_u64);
  println!(
    "capacity={:?}",
    plan_fflonk_capacity(arithmetization.census()).unwrap()
  );
  let degree = required_fflonk_srs_degree(size_u64).unwrap();
  let srs = test_srs(usize::try_from(degree).unwrap());
  let key = preprocess_fflonk(&srs, arithmetization).unwrap();
  let blinding = FflonkBlindingV1 {
    wire_evaluations: core::array::from_fn(|index| {
      Fr::from(u64::try_from(index).unwrap() + 31)
    }),
    z_coefficients: [Fr::from(41u64), Fr::from(43u64), Fr::from(47u64)],
  };
  let retained = LIVE.load(Relaxed);
  PEAK.store(retained, Relaxed);
  let start = Instant::now();
  let output = prove_fflonk(&srs, &key, &r1cs, &witness, blinding).unwrap();
  let elapsed = start.elapsed();
  let peak = PEAK.load(Relaxed);
  println!(
    "retained_bytes={retained} peak_bytes={peak} incremental_peak_bytes={} prove_seconds={:.6}",
    peak - retained,
    elapsed.as_secs_f64(),
  );
  assert_eq!(
    verify_fflonk(
      &key.verification_key(),
      &output.proof,
      &output.public_inputs
    ),
    Ok(true),
  );
  println!(
    "verified=true proof_digest={}",
    blake3::hash(&output.proof.to_bytes())
  );
}
