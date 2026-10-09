//! FRI compression of the exported Init root proof.
#[path = "support/init_claim.rs"]
mod init_claim;
use ix_proof_compression::fri::Envelope;
use ix_proof_compression::fri::ImplementationOptions;
use ix_proof_compression::fri::Message;
use ix_proof_compression::fri::ProofEnvelope;
use ix_proof_compression::fri::ProofProfile;
use ix_proof_compression::fri::Statement;
use ix_proof_compression::fri::StatementBinding;
use ix_proof_compression::fri::StatementSlot;
use ix_proof_compression::fri::VerifierKey;
use ix_proof_compression::fri::VerifierLimits;
use ix_proof_compression::fri::VerifierPlan;
use multi_stark::batch::BatchProof;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;
use p3_blake3::Blake3;
use p3_field::{PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_symmetric::CryptographicHasher;
use std::{fs, path::PathBuf, time::Instant};

fn claims_from_bytes(bytes: &[u8]) -> Result<Vec<Vec<Val>>, String> {
  let (words, remainder) = bytes.as_chunks::<8>();
  if !remainder.is_empty() {
    return Err("unaligned claims".into());
  }
  let mut words = words.iter();
  let n = u64::from_le_bytes(*words.next().ok_or("missing claims count")?);
  let mut claims = Vec::new();
  for _ in 0..n {
    let len = u64::from_le_bytes(*words.next().ok_or("missing claim length")?);
    let mut claim = Vec::new();
    for _ in 0..len {
      let v = u64::from_le_bytes(*words.next().ok_or("missing claim value")?);
      if v >= Val::ORDER_U64 {
        return Err("noncanonical claim".into());
      }
      claim.push(Val::from_u64(v));
    }
    claims.push(claim);
  }
  if words.next().is_some() {
    return Err("trailing claims".into());
  }
  Ok(claims)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if args.len() < 2 {
    return Err("usage: init_fri <ix-artifacts> <output-dir> [--native-only | --check-only | --prove-outer]".into());
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
  tracing_subscriber::fmt()
    .with_ansi(false)
    .with_target(false)
    .with_max_level(tracing::Level::INFO)
    .init();
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
  let claims = claims_from_bytes(&fs::read(dir.join("root-claims.bin"))?)?;
  if claims.as_slice()
    != [init_claim::INIT_PUBLIC_WORDS.map(Val::from_u64).to_vec()]
  {
    return Err("unexpected Init claim".into());
  }
  let start = Instant::now();
  native_key
    .verify(&claims[0], &proof)
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
  let h = &proof.preamble.headers[0];
  let verifier_key = VerifierKey::from_system(system);
  let plan = VerifierPlan::validate(
    &verifier_key,
    ProofProfile {
      envelope: Envelope::SingleBatch,
      active: h.active.clone(),
      log_degrees: h.log_degrees.clone(),
      claim_lengths: claims.iter().map(Vec::len).collect(),
      message_lengths: proof
        .preamble
        .messages
        .iter()
        .map(|m| m.args.len())
        .collect(),
      max_field_retries: 2,
    },
    VerifierLimits::default(),
  )?;
  let shape = plan.shape();
  println!(
    "Fixed shape: {} active circuits, max trace log {}, {} queries; batch messages are circuit constants",
    shape.log_degrees.len(),
    shape.log_trace,
    shape.queries
  );
  let start = Instant::now();
  let expanded = plan.expand_witness(ProofEnvelope::SingleBatch(&proof))?;
  println!("Untrusted witness expansion: {:?}", start.elapsed());
  if mode == "--native-only" {
    return Ok(());
  }
  let start = Instant::now();
  let mut builder = CircuitBuilder::new();
  let compact = std::env::var_os("IX_ROOT_GENERIC_HASHES").is_none();
  if compact {
    builder.enable_compact_blake3();
  }
  println!("Compact BLAKE3: {compact}");
  let claim_wires = claims
    .iter()
    .enumerate()
    .map(|(i, claim)| {
      (0..claim.len())
        .map(|j| {
          StatementBinding::Wire(
            builder.public_input(format!("claim[{i}][{j}]")),
          )
        })
        .collect()
    })
    .collect();
  let inputs = plan.constrain(
    &mut builder,
    Statement {
      claims: claim_wires,
      messages: proof
        .preamble
        .messages
        .iter()
        .map(|m| Message {
          args: m
            .args
            .iter()
            .copied()
            .map(StatementBinding::Constant)
            .collect(),
          multiplicity: StatementBinding::Constant(m.multiplicity),
        })
        .collect(),
    },
    ImplementationOptions { compact_blake3: compact },
  )?;
  let schema = Statement {
    claims: claims
      .iter()
      .map(|c| vec![StatementSlot::Public; c.len()])
      .collect(),
    messages: proof
      .preamble
      .messages
      .iter()
      .map(|m| Message {
        args: m.args.iter().copied().map(StatementSlot::Constant).collect(),
        multiplicity: StatementSlot::Constant(m.multiplicity),
      })
      .collect(),
  };
  fs::write(out.join("inner-vk.bin"), verifier_key.to_bytes()?)?;
  fs::write(out.join("plan-id.bin"), plan.identity(&schema)?)?;
  let compiler =
    std::process::Command::new("rustc").arg("--version").output()?;
  if !compiler.status.success() {
    return Err("could not identify Rust compiler".into());
  }
  let compiler = String::from_utf8(compiler.stdout)?;
  fs::write(
    out.join("build-id.bin"),
    plan.build_identity(
      &schema,
      ImplementationOptions { compact_blake3: compact },
      compiler.trim(),
      "plonkish-multi-stark/v1",
      "max-height=16777216;lookup-group=3",
    )?,
  )?;
  fs::write(
    out.join("statement-schema.txt"),
    format!(
      "Public order: claims in order, then message arguments and multiplicity; constants omitted.\nProfile: {:?}\nSchema: {schema:?}\nCompiler: {compiler}Compact BLAKE3: {compact}\n",
      plan.profile()
    ),
  )?;
  let circuit = builder.finish();
  println!("Circuit build: {:?}; {:?}", start.elapsed(), circuit.stats());
  // Bound each computation domain, without changing the inner verifier.
  let max_trace_height = 1usize << 24;
  let layout = circuit.multi_stark_layout_with_max_height(max_trace_height)?;
  println!("STARK layout: {layout:?}");
  fs::write(
    out.join("circuit-cost.txt"),
    format!("Stats: {:?}\nLayout: {layout:?}\n", circuit.stats()),
  )?;
  let start = Instant::now();
  let mut witness = circuit.witness();
  expanded.assign_proof(&mut witness, &inputs)?;
  for (wires, claim) in inputs.proof().algebra.claims.iter().zip(&claims) {
    for (&wire, &value) in wires.iter().zip(claim) {
      witness.set(wire, value)?;
    }
  }
  let assignment = witness.generate()?;
  let public: Vec<_> = claims.iter().flatten().copied().collect();
  assert_eq!(assignment.public_values(), public);
  for (bits, &expected) in
    inputs.proof().query_bits.iter().zip(expanded.query_indices())
  {
    let actual: u64 = bits
      .iter()
      .enumerate()
      .map(|(i, b)| {
        assignment.value(b.value()).unwrap().as_canonical_u64() << i
      })
      .sum();
    assert_eq!(actual, expected as u64);
  }
  println!(
    "Full Plonkish witness/constraint check passed: {:?}; all query indices match native",
    start.elapsed()
  );
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
  // This counts only advice/fixed LDEs, not stage 2, quotients, or scratch.
  // The process must ALSO be run under an address-space cap. The old generic
  // circuit fails this gate; the measured compact layout fits the gate.
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
  drop(expanded);
  drop(proof);

  drop(inputs);
  drop(plan);
  drop(verifier_key);
  let start = Instant::now();
  let compiled = circuit.lower_to_multi_stark_with_max_height(
    Val::from_u8(107),
    max_trace_height,
  )?;
  println!("Lowering: {:?}", start.elapsed());
  let outer_claims = compiled.claims(&public)?;
  let mut wrong_public = public.clone();
  wrong_public[0] += Val::ONE;
  let wrong_claims = compiled.claims(&wrong_public)?;
  let start = Instant::now();
  let traces = compiled.traces(&assignment)?;
  let mut definitions = compiled.circuit_inputs();
  for d in &mut definitions {
    d.lookup_group_size = 3;
  }
  println!("Trace construction: {:?}", start.elapsed());
  drop(compiled);
  drop(assignment);
  // Same commitment/FRI parameters as the real Ix root, not the showcase's
  // four-query development profile.
  let config = GoldilocksBlake3Config::new(cp, fp);
  let start = Instant::now();
  let (outer, key) = System::new(config, definitions);
  println!("Outer setup: {:?}", start.elapsed());
  let refs: Vec<_> = outer_claims.iter().map(Vec::as_slice).collect();
  let start = Instant::now();
  let outer_proof = outer.prove_multiple_claims(
    &key,
    &refs,
    SystemWitness::from_stage_1(traces, &outer),
  );
  println!("Outer proving: {:?}", start.elapsed());
  let start = Instant::now();
  outer
    .verify_multiple_claims(&refs, &outer_proof)
    .map_err(|e| format!("outer verification: {e:?}"))?;
  println!("Outer verification: {:?}", start.elapsed());
  assert!(
    outer
      .verify_multiple_claims(
        &wrong_claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        &outer_proof
      )
      .is_err()
  );
  let bytes = outer_proof.to_bytes()?;
  println!("Outer proof: {} bytes; altered public claim rejected", bytes.len());
  fs::write(out.join("outer-proof.bin"), bytes)?;
  fs::write(
    out.join("outer-vk.bin"),
    VerifierKey::from_system(&outer).to_bytes()?,
  )?;
  fs::write(out.join("outer-claims.bin"), {
    let mut bytes = (outer_claims.len() as u64).to_le_bytes().to_vec();
    for claim in &outer_claims {
      bytes.extend((claim.len() as u64).to_le_bytes());
      for value in claim {
        bytes.extend(value.as_canonical_u64().to_le_bytes());
      }
    }
    bytes
  })?;
  fs::write(
    out.join("statement-values.bin"),
    bincode::serde::encode_to_vec(&public, bincode::config::standard())?,
  )?;
  Ok(())
}
