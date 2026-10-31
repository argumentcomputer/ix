//! Aggregate-root construction shared by file and in-memory callers.
use super::{Prepared, Result};
use crate::fri::*;
use aiur::{synthesis::AiurProof, vk_codec::AiurVerifyingKey};
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::types::Val;
use p3_field::PrimeField64;

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
