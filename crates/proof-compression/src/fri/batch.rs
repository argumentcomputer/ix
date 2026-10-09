//! Shared one-shard batch transcript and residual balance, distinct from the
//! ordinary-proof transcript. Compatibility helpers specialize messages to
//! constants; the validated plan uses the same implementation with bound wires.
//! Application policy belongs to the caller in both cases.
use super::AlgebraicInputs;
use super::Blake3Challenger;
use super::ByteGadgets;
use super::ExpandedPcsWitness;
use super::FixedPcsShape;
use super::FixedVerifierInputs;
use super::PcsInputs;
use super::QuadraticValue as Q;
use super::TranscriptCommitments;
use super::algebra::constrain_algebraic_checks_with_residual;
use super::pcs::constrain_pcs;
use super::pcs_witness::expand_after_lookup;
use multi_stark::batch::BatchMessage;
use multi_stark::batch::BatchProof;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::plonkish::Circuit;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Value;
use multi_stark::system::System;
use multi_stark::types::GoldilocksBlake3Config as Config;
use multi_stark::types::Val;
use p3_challenger::CanObserve;

pub fn build_single_batch_verifier(
  system: &System<Config>,
  shape: &FixedPcsShape,
  claim_lengths: &[usize],
  messages: &[BatchMessage<Config>],
) -> (Circuit<Val>, FixedVerifierInputs) {
  let mut b = CircuitBuilder::new();
  let claims = claim_lengths
    .iter()
    .enumerate()
    .map(|(i, &n)| {
      (0..n).map(|j| b.public_input(format!("claim[{i}][{j}]"))).collect()
    })
    .collect();
  let bytes = ByteGadgets::new(&mut b);
  let inputs = constrain_single_batch_verifier(
    &mut b, &bytes, system, shape, claims, messages,
  );
  (b.finish(), inputs)
}

/// All claims remain caller-owned wires. Every message is fixed into the
/// transcript and residual-balance constraints, never trusted witness advice.
pub fn constrain_single_batch_verifier(
  b: &mut CircuitBuilder<Val>,
  bytes: &ByteGadgets,
  system: &System<Config>,
  shape: &FixedPcsShape,
  claims: Vec<Vec<Value>>,
  messages: &[BatchMessage<Config>],
) -> FixedVerifierInputs {
  let messages: Vec<_> = messages
    .iter()
    .map(|m| super::plan::Message {
      args: m.args.iter().map(|&v| b.constant(v)).collect(),
      multiplicity: b.constant(m.multiplicity),
    })
    .collect();
  constrain_bound_batch_verifier(b, bytes, system, shape, claims, &messages)
}

pub(super) fn constrain_bound_batch_verifier(
  b: &mut CircuitBuilder<Val>,
  bytes: &ByteGadgets,
  system: &System<Config>,
  shape: &FixedPcsShape,
  claims: Vec<Vec<Value>>,
  messages: &[super::plan::Message<Value>],
) -> FixedVerifierInputs {
  constrain_bound_batch_queries(
    b,
    bytes,
    system,
    shape,
    claims,
    messages,
    0..system.config.fri_parameters().num_queries,
    true,
  )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn constrain_bound_batch_queries(
  b: &mut CircuitBuilder<Val>,
  bytes: &ByteGadgets,
  system: &System<Config>,
  shape: &FixedPcsShape,
  claims: Vec<Vec<Value>>,
  messages: &[super::plan::Message<Value>],
  queries: std::ops::Range<usize>,
  check_algebra: bool,
) -> FixedVerifierInputs {
  let mut checked =
    FixedPcsShape::from_profile(system, &shape.active, &shape.log_degrees);
  checked.max_field_retries = shape.max_field_retries;
  let shape = checked;
  let circuits: Vec<_> = system
    .circuits
    .iter()
    .zip(&shape.active)
    .filter_map(|(c, &active)| active.then_some(c))
    .collect();
  let algebra = AlgebraicInputs::with_claims(b, &circuits, claims);
  let commitments = TranscriptCommitments::allocate(b, bytes);
  let mut ch = Blake3Challenger::with_retry_limit(
    b,
    bytes,
    system.config.challenger_seed(),
    shape.max_field_retries,
  );
  ch.observe_constant(b, bytes, system.circuits.len());
  for c in &system.circuits {
    for value in [
      c.constraint_count(),
      c.max_constraint_degree(),
      c.preprocessed_height,
      c.preprocessed_width,
      c.main_width,
      c.stage_2_width,
      c.lookup_group_size,
    ] {
      ch.observe_constant(b, bytes, value);
    }
  }
  if let Some(commit) = &system.preprocessed_commit {
    assert_eq!(commit.roots().len(), 1);
    ch.observe_bytes(&commit.roots()[0].map(|v| bytes.constant(b, v)));
  }
  ch.observe_constant(b, bytes, 1); // batch header count
  for &active in &shape.active {
    ch.observe_constant(b, bytes, usize::from(active));
  }
  ch.observe_bytes(&commitments.stage1);
  ch.observe_constant(b, bytes, shape.log_degrees.len());
  for &log in &shape.log_degrees {
    ch.observe_constant(b, bytes, usize::from(log));
  }
  ch.observe_constant(b, bytes, algebra.claims.len());
  for claim in &algebra.claims {
    ch.observe_constant(b, bytes, claim.len());
    for &value in claim {
      ch.observe_field(b, bytes, value);
    }
  }
  ch.observe_constant(b, bytes, messages.len());
  for message in messages {
    ch.observe_constant(b, bytes, message.args.len());
    for &value in
      message.args.iter().chain(std::iter::once(&message.multiplicity))
    {
      ch.observe_field(b, bytes, value);
    }
  }
  let beta = ch.sample_extension(b, bytes);
  beta.assert_equal(b, algebra.challenges.beta);
  ch.observe_extension(b, bytes, beta);
  let gamma = ch.sample_extension(b, bytes);
  gamma.assert_equal(b, algebra.challenges.gamma);
  ch.observe_extension(b, bytes, gamma);
  ch.observe_constant(b, bytes, 0); // shard index, even for a one-shard batch
  ch.observe_bytes(&commitments.stage2);
  for opening in &algebra.openings {
    ch.observe_extension(b, bytes, opening.accumulator);
  }
  let alpha = ch.sample_extension(b, bytes);
  alpha.assert_equal(b, algebra.challenges.alpha);
  ch.observe_bytes(&commitments.quotient);
  let zeta = ch.sample_extension(b, bytes);
  zeta.assert_equal(b, algebra.challenges.zeta);
  tracing::info!(stats = ?b.stats(), "Plonkish batch transcript built");

  if check_algebra {
    let zero = Q::constant(b, [Val::ZERO; 2]);
    let mut message_sum = zero;
    for message in messages {
      let mut fingerprint = zero;
      for &value in message.args.iter().rev() {
        fingerprint = fingerprint.mul(b, gamma);
        let arg = Q::from_base(b, value);
        fingerprint = fingerprint.add(b, arg);
      }
      let term =
        beta.add(b, fingerprint).inverse(b).mul_base(b, message.multiplicity);
      message_sum = message_sum.add(b, term);
    }
    let residual = message_sum.neg(b);
    constrain_algebraic_checks_with_residual(
      b,
      &circuits,
      &shape.log_degrees,
      &algebra,
      residual,
    );
    tracing::info!(stats = ?b.stats(), "Plonkish batch algebra built");
  }
  let pcs = PcsInputs::allocate_queries(b, bytes, &shape, queries);
  let query_bits =
    constrain_pcs(b, bytes, system, &shape, &algebra, &commitments, &pcs, ch);
  FixedVerifierInputs { shape, algebra, commitments, pcs, query_bits }
}

/// Untrusted normalization. Native verification is not used as an oracle.
/// The circuit replays every challenge and constrains all openings and paths.
pub fn expand_single_batch_witness(
  system: &System<Config>,
  shape: &FixedPcsShape,
  batch: &BatchProof<Config>,
  messages: &[BatchMessage<Config>],
) -> Result<ExpandedPcsWitness, String> {
  if batch.preamble.headers.len() != 1 || batch.proofs.len() != 1 {
    return Err("expected exactly one batch shard".into());
  }
  if batch.preamble.messages.len() != messages.len()
    || batch
      .preamble
      .messages
      .iter()
      .zip(messages)
      .any(|(a, b)| a.args != b.args || a.multiplicity != b.multiplicity)
  {
    return Err("batch messages differ from the circuit profile".into());
  }
  let header = &batch.preamble.headers[0];
  let proof = &batch.proofs[0];
  if header.active != proof.active
    || header.log_degrees != proof.log_degrees
    || header.stage_1_trace != proof.commitments.stage_1_trace
  {
    return Err("batch header differs from proof".into());
  }
  let (mut challenger, beta, gamma) = system.batch_challenger(&batch.preamble);
  challenger.observe(Val::ZERO);
  let claims: Vec<_> = header.claims.iter().map(Vec::as_slice).collect();
  expand_after_lookup(system, shape, proof, &claims, challenger, beta, gamma)
}
