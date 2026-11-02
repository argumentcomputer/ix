//! The aggregate root and its FRI compression: the circuit verifying an
//! exported root proof, generic over the proof's geometry or fixed by the
//! layout of a normalized root, and the FRI stage that proves it.
mod fixed;
pub use fixed::FixedRoot;

use super::{
  Result,
  claims::{decode_claims, encode_claims},
  stage::{FriVerifier, Prepared},
};
use crate::fri::*;
use aiur::{synthesis::AiurProof, vk_codec::AiurVerifyingKey};
use multi_stark::batch::BatchProof;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;
use p3_blake3::Blake3;
use p3_field::{PrimeField64, TwoAdicField};
use p3_symmetric::CryptographicHasher;
use std::{fs, path::Path, time::Instant};

/// Layout file a normalized root carries beside its proof.
pub(super) const FIXED_ROOT_LAYOUT: &str = "fixed-root.json";
/// Largest trace of the FRI stage's lowered verifier circuit.
const MAX_TRACE_HEIGHT: usize = 1 << 24;

/// The FRI stage's verifier for roots of the aggregation backend `key`
/// normalized to `layout`, derived without a proof: `run` proves the same
/// circuit, lowered and committed under the same parameters.
pub(super) fn verifier(
  key: &AiurVerifyingKey,
  layout: &FixedRoot,
) -> Result<FriVerifier> {
  FriVerifier::derive(
    layout.circuit(key, VerifierLimits::default())?,
    config(key),
    MAX_TRACE_HEIGHT,
  )
}

fn config(key: &AiurVerifyingKey) -> GoldilocksBlake3Config {
  GoldilocksBlake3Config::new(key.commitment_parameters(), key.fri_parameters())
}

/// Verify the root input in `dir`, build its FRI verifier circuit and check
/// its constraints, writing the circuit's identity and cost to `out`. With
/// `prove`, also prove the circuit and write the outer FRI proof.
pub(super) fn run(dir: &Path, out: &Path, prove: bool) -> Result<()> {
  fs::create_dir_all(out)?;
  let input_span = tracing::info_span!("compression/load_input").entered();
  let vk_bytes = fs::read(dir.join("root-vk.bin"))?;
  let native_key = AiurVerifyingKey::from_bytes(&vk_bytes)?;
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
  eprintln!(
    "Native Ix root batch verified in {:?}: {} bytes, {} circuits, {} shards",
    start.elapsed(),
    bytes.len(),
    system.circuits.len(),
    proof.proofs.len()
  );
  eprintln!(
    "log_blowup={} cap={} final_log={} arity={} queries={} commit_pow={} query_pow={}",
    cp.log_blowup,
    cp.cap_height,
    fp.log_final_poly_len,
    fp.max_log_arity,
    fp.num_queries,
    fp.commit_proof_of_work_bits,
    fp.query_proof_of_work_bits
  );
  eprintln!("Trusted VK BLAKE3: {:02x?}", Blake3.hash_iter(vk_bytes));
  eprintln!("Expected public claims: {claims:?}");
  eprintln!(
    "Fixed messages (validated Aiur memory-closure policy): {}",
    proof.preamble.messages.len()
  );
  let verifier_key = VerifierKey::from_system(system);
  fs::write(out.join("inner-vk.bin"), verifier_key.to_bytes()?)?;
  // A normalized root carries its layout; the verifier circuit then depends
  // only on the backend and layout, never on this proof's geometry.
  let layout_path = dir.join(FIXED_ROOT_LAYOUT);
  let start = Instant::now();
  let prepared = if layout_path.exists() {
    let fixed = FixedRoot::from_json(&fs::read_to_string(&layout_path)?)?;
    fs::write(out.join(FIXED_ROOT_LAYOUT), fixed.to_json())?;
    fs::write(out.join("plan-id.bin"), fixed.identity(&native_key))?;
    fixed.prepare(&native_key, &proof, &claims[0], VerifierLimits::default())?
  } else {
    let plan = RootPlan::new(&verifier_key, &proof, VerifierLimits::default())?;
    let compact = std::env::var_os("IX_ROOT_GENERIC_HASHES").is_none();
    let options = ImplementationOptions { compact_blake3: compact };
    fs::write(out.join("plan-id.bin"), plan.identity()?)?;
    fs::write(out.join("build-id.bin"), plan.build_identity(options)?)?;
    fs::write(out.join("statement-schema.txt"), plan.description())?;
    plan.prepare(&proof, &claims[0], options)?
  };
  let layout =
    prepared.circuit().multi_stark_layout_with_max_height(MAX_TRACE_HEIGHT)?;
  eprintln!(
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
  eprintln!(
    "Largest outer LDE: 2^{log_lde}; {} computation traces",
    layout.main_heights.len()
  );
  if log_lde > Val::TWO_ADICITY {
    return Err(format!("outer LDE requires 2^{log_lde} points; Goldilocks supports at most 2^{}; a smaller/partitioned layout is required", Val::TWO_ADICITY).into());
  }
  if !prove {
    return Ok(());
  }
  // This estimate excludes stage 2, quotients and scratch; enforce a separate
  // process memory limit when running the prover.
  let base_lde_bytes = layout
    .trace_field_bytes
    .checked_mul(1usize << cp.log_blowup)
    .ok_or("LDE size overflow")?;
  eprintln!(
    "Advice + fixed LDE bytes (not total prover memory): {base_lde_bytes}"
  );
  if base_lde_bytes > (192usize << 30) {
    return Err(
            "advice/fixed LDE arrays alone exceed 192 GiB; refusing unsafe prover allocation"
                .into(),
        );
  }
  drop(proof);
  drop(verifier_key);
  let public = prepared.public_values().to_vec();
  let start = Instant::now();
  let (verifier, outer_proof) =
    prepared.prove_fri(config(&native_key), MAX_TRACE_HEIGHT)?;
  eprintln!("FRI proving and verification: {:?}", start.elapsed());
  let _output_span = tracing::info_span!("compression/write_output").entered();
  let bytes = outer_proof.to_bytes()?;
  eprintln!("Outer proof: {} bytes", bytes.len());
  fs::write(out.join("outer-proof.bin"), bytes)?;
  fs::write(out.join("outer-vk.bin"), verifier.key.to_bytes()?)?;
  fs::write(
    out.join("outer-claims.bin"),
    encode_claims(&verifier.statement.claims(&public)?),
  )?;
  fs::write(
    out.join("statement-values.bin"),
    bincode::serde::encode_to_vec(&public, bincode::config::standard())?,
  )?;
  Ok(())
}

/// Prepare every trace shard under the trusted Aiur policy. Claim values
/// remain public; activation, heights and memory-closure messages fix the
/// circuit's shape.
pub fn prepare_root(
  key: &AiurVerifyingKey,
  proof: &AiurProof,
  expected: &[Val],
  limits: VerifierLimits,
) -> Result<Prepared<Val>> {
  key.verify(expected, proof).map_err(|e| format!("aggregate root: {e:?}"))?;
  let verifier = VerifierKey::from_system(key.system());
  RootPlan::new(&verifier, proof, limits)?.prepare(
    proof,
    expected,
    Default::default(),
  )
}

pub(in crate::pipeline) struct RootPlan<'a> {
  key: &'a VerifierKey,
  plans: Vec<VerifierPlan<'a>>,
  schemas: Vec<Statement<StatementSlot>>,
}

impl<'a> RootPlan<'a> {
  pub(in crate::pipeline) fn new(
    key: &'a VerifierKey,
    proof: &AiurProof,
    limits: VerifierLimits,
  ) -> Result<Self> {
    if proof.preamble.headers.is_empty() {
      return Err("empty aggregate batch".into());
    }
    let mut plans = Vec::new();
    let mut schemas = Vec::new();
    let mut proof_values = 0usize;
    for header in &proof.preamble.headers {
      let plan = VerifierPlan::validate(
        key,
        ProofProfile {
          envelope: Envelope::SingleBatch,
          active: header.active.clone(),
          log_degrees: header.log_degrees.clone(),
          claim_lengths: header.claims.iter().map(Vec::len).collect(),
          message_lengths: proof
            .preamble
            .messages
            .iter()
            .map(|m| m.args.len())
            .collect(),
          max_field_retries: DEFAULT_FIELD_RETRIES,
        },
        limits,
      )?;
      proof_values = proof_values
        .checked_add(plan.resources().proof_values)
        .ok_or("batch proof size overflow")?;
      if proof_values > limits.max_proof_values {
        return Err("batch exceeds proof value limit".into());
      }
      schemas.push(Statement {
        claims: header
          .claims
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
      });
      plans.push(plan);
    }
    Ok(Self { key, plans, schemas })
  }

  pub(in crate::pipeline) fn identity(&self) -> Result<[u8; 32]> {
    let ids = self
      .plans
      .iter()
      .zip(&self.schemas)
      .map(|(p, s)| p.identity(s))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    if let [id] = ids.as_slice() {
      return Ok(*id);
    }
    let mut hash = blake3::Hasher::new();
    hash.update(b"ix/aggregate-batch-plan/v1");
    for id in ids {
      hash.update(&id);
    }
    Ok(*hash.finalize().as_bytes())
  }

  pub(in crate::pipeline) fn build_identity(
    &self,
    options: ImplementationOptions,
  ) -> Result<[u8; 32]> {
    let ids = self
      .plans
      .iter()
      .zip(&self.schemas)
      .map(|(p, s)| {
        p.build_identity(
          s,
          options,
          concat!("ix-proof-compression/", env!("CARGO_PKG_VERSION")),
          "plonkish-multi-stark/v1",
          "max-height=16777216;lookup-group=3",
        )
      })
      .collect::<std::result::Result<Vec<_>, _>>()?;
    if let [id] = ids.as_slice() {
      return Ok(*id);
    }
    let mut hash = blake3::Hasher::new();
    hash.update(b"ix/aggregate-batch-build/v1");
    for id in ids {
      hash.update(&id);
    }
    Ok(*hash.finalize().as_bytes())
  }

  pub(in crate::pipeline) fn description(&self) -> String {
    format!(
      "Profiles: {:?}\nSchemas: {:?}\n",
      self.plans.iter().map(VerifierPlan::profile).collect::<Vec<_>>(),
      self.schemas
    )
  }

  pub(in crate::pipeline) fn prepare(
    &self,
    proof: &AiurProof,
    expected: &[Val],
    options: ImplementationOptions,
  ) -> Result<Prepared<Val>> {
    let shapes: Vec<_> = self.plans.iter().map(|p| p.shape().clone()).collect();
    let expanded = tracing::info_span!("compression/expand_witness")
      .in_scope(|| expand_batch_witness(self.key.system(), &shapes, proof))?;
    let build_span = tracing::info_span!("compression/build_circuit").entered();
    let mut builder = CircuitBuilder::new();
    if options.compact_blake3 {
      builder.enable_compact_blake3();
    }
    let public: Vec<_> = (0..expected.len())
      .map(|i| builder.public_input(format!("claim[0][{i}]")))
      .collect();
    let claims = self
      .schemas
      .iter()
      .map(|s| {
        s.claims
          .iter()
          .map(|claim| {
            if claim.len() != public.len() {
              return Err("root claim dimensions differ");
            }
            Ok(public.clone())
          })
          .collect::<std::result::Result<Vec<_>, _>>()
      })
      .collect::<std::result::Result<Vec<_>, _>>()?;
    // Constant binding precedes the byte gadgets in the production layout.
    let messages = proof
      .preamble
      .messages
      .iter()
      .map(|m| Message {
        args: m.args.iter().map(|&v| builder.constant(v)).collect(),
        multiplicity: builder.constant(m.multiplicity),
      })
      .collect::<Vec<_>>();
    let bytes = ByteGadgets::new(&mut builder);
    let inputs = constrain_batch_verifier(
      &mut builder,
      &bytes,
      self.key.system(),
      &shapes,
      claims,
      &messages,
    );
    let circuit = builder.finish();
    drop(build_span);
    let _witness_span = tracing::info_span!("compression/witness").entered();
    let mut witness = circuit.witness();
    for (&wire, &value) in public.iter().zip(expected) {
      witness.set(wire, value)?;
    }
    for (expanded, inputs) in expanded.iter().zip(&inputs) {
      expanded.assign_proof(&mut witness, inputs)?;
    }
    let assignment = witness.generate()?;
    for (expanded, inputs) in expanded.iter().zip(&inputs) {
      for (bits, &expected) in
        inputs.query_bits.iter().zip(&expanded.query_indices)
      {
        let actual: u64 = bits
          .iter()
          .enumerate()
          .map(|(i, b)| {
            assignment.value(b.value()).unwrap().as_canonical_u64() << i
          })
          .sum();
        if actual != expected as u64 {
          return Err("query index differs from native verification".into());
        }
      }
    }
    Ok(Prepared { circuit, assignment })
  }
}
