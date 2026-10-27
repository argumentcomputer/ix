//! FRI compression of an exported aggregate root proof.
use super::stages::statement::decode_claims;
use crate::fri::ImplementationOptions;
use crate::fri::VerifierKey;
use crate::fri::VerifierLimits;
use multi_stark::batch::BatchProof;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;
use p3_blake3::Blake3;
use p3_field::TwoAdicField;
use p3_symmetric::CryptographicHasher;
use std::{fs, path::PathBuf, time::Instant};

/// Compiled worker features for deployment checks.
fn print_capabilities() {
  println!(
    concat!(
      "{{\"format\":\"ix-compression-capabilities/v1\",\"binary\":\"ix-compression-worker\",",
      "\"cuda\":{},\"parallel\":{}}}"
    ),
    cfg!(feature = "cuda"),
    cfg!(feature = "parallel"),
  );
}

/// Report the process's resident and virtual size every 30 seconds so a
/// long stage's memory profile is visible in its log.
fn spawn_memory_monitor() {
  std::thread::spawn(|| {
    loop {
      std::thread::sleep(std::time::Duration::from_secs(30));
      if let Ok(status) = fs::read_to_string("/proc/self/status") {
        eprintln!(
          "{}",
          status
            .lines()
            .filter(|l| l.starts_with("VmRSS:") || l.starts_with("VmSize:"))
            .collect::<Vec<_>>()
            .join(" ")
        );
      }
    }
  });
}

pub(super) fn run(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
  if args.len() == 1 && args[0] == "capabilities" {
    print_capabilities();
    return Ok(());
  }
  if args.len() < 2 {
    return Err("usage: ix-compression-worker fri <ix-artifacts> <output-dir> [--native-only | --check-only | --prove-outer]".into());
  }
  let dir = PathBuf::from(&args[0]);
  let out = PathBuf::from(&args[1]);
  let mode = args.get(2).map_or("--check-only", String::as_str);
  if args.len() > 3
    || !matches!(mode, "--native-only" | "--check-only" | "--prove-outer")
  {
    return Err("invalid mode".into());
  }
  fs::create_dir_all(&out)?;
  spawn_memory_monitor();
  let input_span = tracing::info_span!("compression/load_input").entered();
  let vk_bytes = fs::read(dir.join("root-vk.bin"))?;
  let native_key = aiur::vk_codec::AiurVerifyingKey::from_bytes(&vk_bytes)?;
  let system = native_key.system();
  let cp = native_key.commitment_parameters();
  let fp = native_key.fri_parameters();
  let bytes = fs::read(dir.join("root-proof.bin"))?;
  let proof = BatchProof::<GoldilocksBlake3Config>::from_bytes(&bytes)?;
  if proof.to_bytes()? != bytes {
    return Err("noncanonical proof transport".into());
  }
  let claims = decode_claims(&fs::read(dir.join("root-claims.bin"))?)?;
  if claims.len() != 1 || claims[0].len() != super::statement::WORDS {
    return Err("root claims must hold one statement of 18 words".into());
  }
  drop(input_span);
  let start = Instant::now();
  tracing::info_span!("compression/verify_input")
    .in_scope(|| native_key.verify(&claims[0], &proof))
    .map_err(|e| format!("Aiur policy: {e:?}"))?;
  println!(
    "Native Ix root batch verified in {:?}: {} bytes, {} circuits, {} shards",
    start.elapsed(),
    bytes.len(),
    system.circuits.len(),
    proof.proofs.len()
  );
  println!(
    "log_blowup={} cap={} final_log={} arity={} queries={} commit_pow={} query_pow={}",
    cp.log_blowup,
    cp.cap_height,
    fp.log_final_poly_len,
    fp.max_log_arity,
    fp.num_queries,
    fp.commit_proof_of_work_bits,
    fp.query_proof_of_work_bits
  );
  println!("Trusted VK BLAKE3: {:02x?}", Blake3.hash_iter(vk_bytes));
  println!("Expected public claims: {claims:?}");
  println!(
    "Fixed messages (validated Aiur memory-closure policy): {}",
    proof.preamble.messages.len()
  );
  if mode == "--native-only" {
    return Ok(());
  }
  let verifier_key = VerifierKey::from_system(system);
  let plan = super::stages::root::RootPlan::new(
    &verifier_key,
    &proof,
    VerifierLimits::default(),
  )?;
  let compact = std::env::var_os("IX_ROOT_GENERIC_HASHES").is_none();
  let options = ImplementationOptions { compact_blake3: compact };
  fs::write(out.join("inner-vk.bin"), verifier_key.to_bytes()?)?;
  fs::write(out.join("plan-id.bin"), plan.identity()?)?;
  fs::write(out.join("build-id.bin"), plan.build_identity(options)?)?;
  fs::write(out.join("statement-schema.txt"), plan.description())?;
  let start = Instant::now();
  let prepared = plan.prepare(&proof, &claims[0], options)?;
  let max_trace_height = 1usize << 24;
  let layout =
    prepared.circuit().multi_stark_layout_with_max_height(max_trace_height)?;
  println!(
    "Circuit preparation: {:?}; {:?}",
    start.elapsed(),
    prepared.circuit().stats()
  );
  fs::write(
    out.join("circuit-cost.txt"),
    format!("Stats: {:?}\nLayout: {layout:?}\n", prepared.circuit().stats()),
  )?;
  fs::write(
    out.join("CHECKED"),
    "all constraints satisfied; expected claims and query indices matched\n",
  )?;
  let largest_trace = *layout
    .main_heights
    .iter()
    .chain(&layout.table_heights)
    .chain(layout.custom_traces.iter().map(|(height, _, _)| height))
    .max()
    .unwrap();
  let log_lde = largest_trace.ilog2() as usize + cp.log_blowup;
  println!(
    "Largest outer LDE: 2^{log_lde}; {} computation traces",
    layout.main_heights.len()
  );
  if log_lde > Val::TWO_ADICITY {
    return Err(format!("outer LDE requires 2^{log_lde} points; Goldilocks supports at most 2^{}; a smaller/partitioned layout is required", Val::TWO_ADICITY).into());
  }
  if mode == "--check-only" {
    return Ok(());
  }
  // This estimate excludes stage 2, quotients and scratch; enforce a separate
  // process memory limit when running the prover.
  let base_lde_bytes = layout
    .trace_field_bytes
    .checked_mul(1usize << cp.log_blowup)
    .ok_or("LDE size overflow")?;
  println!(
    "Advice + fixed LDE bytes (not total prover memory): {base_lde_bytes}"
  );
  if base_lde_bytes > (192usize << 30) {
    return Err(
            "advice/fixed LDE arrays alone exceed 192 GiB; refusing unsafe prover allocation"
                .into(),
        );
  }
  drop(proof);
  drop(plan);
  drop(verifier_key);
  let public = prepared.public_values().to_vec();
  let start = Instant::now();
  let (verifier, outer_proof) = prepared
    .prove_fri(GoldilocksBlake3Config::new(cp, fp), max_trace_height)?;
  println!("FRI proving and verification: {:?}", start.elapsed());
  let _output_span = tracing::info_span!("compression/write_output").entered();
  let bytes = outer_proof.to_bytes()?;
  println!("Outer proof: {} bytes", bytes.len());
  fs::write(out.join("outer-proof.bin"), bytes)?;
  fs::write(out.join("outer-vk.bin"), verifier.key.to_bytes()?)?;
  fs::write(
    out.join("outer-claims.bin"),
    super::stages::statement::encode_claims(
      &verifier.statement.claims(&public)?,
    ),
  )?;
  fs::write(
    out.join("statement-values.bin"),
    bincode::serde::encode_to_vec(&public, bincode::config::standard())?,
  )?;
  Ok(())
}
