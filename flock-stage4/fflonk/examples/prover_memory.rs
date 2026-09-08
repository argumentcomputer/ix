//! Profile requested heap bytes while proving a synthetic multiplication circuit.
//! This fixture uses a public test-only tau. It is not a Flock proof or a
//! production setup. Allocator overhead, transient realloc internals, stack,
//! and resident pages are not measured; setup allocations are counted only
//! while they remain live during proving.
//! Pass an archive path as the second argument to stream the test SRS to disk
//! and prove with `KzgFileSrsV1<File>`. Existing matching archives are validated
//! and reused; existing files are never overwritten.
//! Files use uncompressed points by default; pass `compressed` as the third
//! argument to trade decompression work for a smaller archive.
//! An optional fourth argument names a new, empty polynomial scratch file.
//! That mode preprocesses and proves with an authenticated file-backed key.

use ark_bls12_381::{Fr, G1Affine, G2Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{One, PrimeField};
use ix_fflonk::{
  FflonkBlindingV1, FflonkProvingKeyV1, KzgCommitmentSourceV1, KzgFileSrsV1,
  KzgSrsFileEncodingV1, KzgUniversalSrsV1, PlonkArithmetizationV1,
  arithmetize_r1cs, plan_fflonk_capacity, preprocess_fflonk,
  preprocess_fflonk_to_file, prove_fflonk, required_fflonk_srs_degree,
  verify_fflonk, write_kzg_srs_file,
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

fn test_powers(max_degree: usize) -> impl Iterator<Item = G1Affine> {
  let tau = Fr::from(29u64);
  let mut scalar = Fr::one();
  (0..=max_degree).map(move |_| {
    let point = G1Affine::generator().mul_bigint(scalar.into_bigint());
    scalar *= tau;
    point.into_affine()
  })
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
  let degree =
    usize::try_from(required_fflonk_srs_degree(size_u64).unwrap()).unwrap();
  let tau_g2 = G2Affine::generator()
    .mul_bigint(Fr::from(29u64).into_bigint())
    .into_affine();
  if let Some(path) = std::env::args_os().nth(2) {
    let encoding = match std::env::args().nth(3).as_deref() {
      Some("compressed") => KzgSrsFileEncodingV1::Compressed,
      Some("uncompressed") | None => KzgSrsFileEncodingV1::Uncompressed,
      Some(_) => panic!("choose compressed or uncompressed SRS storage"),
    };
    let created =
      std::fs::OpenOptions::new().write(true).create_new(true).open(&path);
    match created {
      Ok(mut archive) => write_kzg_srs_file(
        &mut archive,
        degree + 1,
        test_powers(degree),
        G2Affine::generator(),
        tau_g2,
        encoding,
      )
      .unwrap(),
      Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {},
      Err(error) => panic!("create test SRS archive: {error}"),
    }
    let srs = KzgFileSrsV1::open(std::fs::File::open(&path).unwrap()).unwrap();
    assert_eq!(srs.max_degree(), degree, "archive has a different domain");
    assert_eq!(
      srs.verifier_key().tau_g2,
      tau_g2,
      "archive has a different test tau"
    );
    assert_eq!(srs.encoding(), encoding, "archive has a different encoding");
    println!(
      "srs_backend=file encoding={:?} archive_bytes={} authentication_bytes={}",
      srs.encoding(),
      std::fs::metadata(&path).unwrap().len(),
      srs.authentication_bytes(),
    );
    profile(&srs, arithmetization, &r1cs, &witness);
  } else {
    let srs = KzgUniversalSrsV1::new(
      test_powers(degree).collect(),
      G2Affine::generator(),
      tau_g2,
    )
    .unwrap();
    println!("srs_backend=memory");
    profile(&srs, arithmetization, &r1cs, &witness);
  }
}

fn profile(
  srs: &impl KzgCommitmentSourceV1,
  arithmetization: PlonkArithmetizationV1,
  r1cs: &CanonicalR1csV1,
  witness: &Witness,
) {
  let retained = LIVE.load(Relaxed);
  PEAK.store(retained, Relaxed);
  let start = Instant::now();
  if let Some(path) = std::env::args_os().nth(4) {
    let storage = std::fs::OpenOptions::new()
      .read(true)
      .write(true)
      .create_new(true)
      .open(path)
      .expect("create new polynomial scratch file");
    let key = preprocess_fflonk_to_file(srs, arithmetization, storage).unwrap();
    let elapsed = start.elapsed();
    let peak = PEAK.load(Relaxed);
    println!(
      "key_backend=file storage_bytes={} authentication_bytes={}",
      key.storage_bytes(),
      key.authentication_bytes()
    );
    println!(
      "preprocess_initial_bytes={retained} preprocess_peak_bytes={peak} preprocess_seconds={:.6}",
      elapsed.as_secs_f64()
    );
    profile_key(srs, &key, r1cs, witness);
  } else {
    let key = preprocess_fflonk(srs, arithmetization).unwrap();
    let elapsed = start.elapsed();
    let peak = PEAK.load(Relaxed);
    println!("key_backend=memory");
    println!(
      "preprocess_initial_bytes={retained} preprocess_peak_bytes={peak} preprocess_seconds={:.6}",
      elapsed.as_secs_f64()
    );
    profile_key(srs, &key, r1cs, witness);
  }
}

fn profile_key(
  srs: &impl KzgCommitmentSourceV1,
  key: &impl FflonkProvingKeyV1,
  r1cs: &CanonicalR1csV1,
  witness: &Witness,
) {
  let blinding = FflonkBlindingV1 {
    wire_evaluations: core::array::from_fn(|index| {
      Fr::from(u64::try_from(index).unwrap() + 31)
    }),
    z_coefficients: [Fr::from(41u64), Fr::from(43u64), Fr::from(47u64)],
  };
  let retained = LIVE.load(Relaxed);
  PEAK.store(retained, Relaxed);
  let start = Instant::now();
  let output = prove_fflonk(srs, key, r1cs, witness, blinding).unwrap();
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
