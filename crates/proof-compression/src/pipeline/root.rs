use super::{Prepared, Result};
use crate::fri::*;
use aiur::{synthesis::AiurProof, vk_codec::AiurVerifyingKey};
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::types::Val;

/// Prepare compression of an aggregate root's Aiur proof, including every
/// trace shard. `expected` is the outer call claim reconstructed by the host
/// from its trusted aggregate entrypoint, allowed keys and certificate claim.
///
/// Aiur policy is checked before construction. Activation, heights, claim
/// placement and memory-closure messages are then fixed into the circuit, so
/// its witness cannot bypass that policy. The claim values remain public.
pub fn prepare_root(
  key: &AiurVerifyingKey,
  proof: &AiurProof,
  expected: &[Val],
  limits: VerifierLimits,
) -> Result<Prepared<Val>> {
  key.verify(expected, proof).map_err(|e| format!("aggregate root: {e:?}"))?;
  prepare_batch(
    &VerifierKey::from_system(key.system()),
    proof,
    expected,
    limits,
  )
}

fn prepare_batch(
  key: &VerifierKey,
  proof: &AiurProof,
  expected: &[Val],
  limits: VerifierLimits,
) -> Result<Prepared<Val>> {
  let mut shapes = Vec::new();
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
    shapes.push(plan.shape().clone());
  }
  let expanded = expand_batch_witness(key.system(), &shapes, proof)?;
  let mut b = CircuitBuilder::new();
  b.enable_compact_blake3();
  let public: Vec<_> = (0..expected.len())
    .map(|i| b.public_input(format!("claim[{i}]")))
    .collect();
  let claims: Vec<_> = proof
    .preamble
    .headers
    .iter()
    .map(|header| header.claims.iter().map(|_| public.clone()).collect())
    .collect();
  let bytes = ByteGadgets::new(&mut b);
  let messages: Vec<_> = proof
    .preamble
    .messages
    .iter()
    .map(|m| Message {
      args: m.args.iter().map(|&v| b.constant(v)).collect(),
      multiplicity: b.constant(m.multiplicity),
    })
    .collect();
  let inputs = constrain_batch_verifier(
    &mut b,
    &bytes,
    key.system(),
    &shapes,
    claims,
    &messages,
  );
  let circuit = b.finish();
  let mut witness = circuit.witness();
  for (&wire, &value) in public.iter().zip(expected) {
    witness.set(wire, value)?;
  }
  for (expanded, inputs) in expanded.iter().zip(&inputs) {
    expanded.assign_proof(&mut witness, inputs)?;
  }
  let assignment = witness.generate()?;
  Ok(Prepared { circuit, assignment })
}
