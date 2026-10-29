//! Root normalization: one more `ix_aggr` wrap of an aggregate root, proved
//! in a fixed trace layout. Every root that fits the layout then compresses
//! under the same FRI verifier, whatever the shape of the original root.
use super::protocol::{
  ChildKind, aggregate_outer_claim, serialize_claims, shape_code,
};
use aiur::{
  G,
  execute::{IOBuffer, QueryRecord},
  synthesis::{AiurProof, AiurSystem},
  vk_codec::aiur_system_to_bytes,
};
use ix_proof_compression::pipeline::FixedRoot;
use ixvm_codegen::aiur_ix_aggr_runner::{
  AggrAdvice, aggr_io_buffer, execute_ix_aggr,
};

/// The trusted aggregation backend and the root claim being wrapped.
pub(crate) struct RootWrap<'a> {
  pub(crate) system: &'a AiurSystem,
  pub(crate) aggr_idx: usize,
  pub(crate) allowed: &'a [u8],
  pub(crate) ixvm_vk: &'a [u8],
  pub(crate) claim: &'a [u8],
}

struct Executed {
  expected: Vec<G>,
  io: IOBuffer,
  record: QueryRecord,
  output: Vec<G>,
}

impl RootWrap<'_> {
  /// Execute a wrap of `proof`: shape 1 verifies one `ix_aggr` proof and
  /// passes its claim through. The root proof is verified natively first.
  fn execute(&self, proof: &AiurProof) -> Result<Executed, String> {
    let expected =
      aggregate_outer_claim(self.aggr_idx, self.allowed, self.claim);
    let advice = self
      .system
      .proof_to_advice_bytes(&expected, proof)
      .map_err(|e| format!("aggregate root: {e}"))?;
    let self_vk = aiur_system_to_bytes(self.system)?;
    let claims = serialize_claims(&[&expected]);
    let mut io = aggr_io_buffer(&AggrAdvice {
      shape: shape_code(ChildKind::Aggr, None),
      proof_advice: [&advice, &[]],
      ixvm_vk: self.ixvm_vk,
      self_vk: &self_vk,
      child_claims: [&claims, &[]],
      output_claim: self.claim,
      allowed: self.allowed,
      preimages: &[],
      trees: &[],
      paths: &[],
    });
    drop(advice);
    // The aggregate call is [channel, entrypoint, inputs…], with no outputs.
    let (record, output) = execute_ix_aggr(
      self.system.toplevel(),
      self.aggr_idx,
      expected[2..].to_vec(),
      &mut io,
    )
    .map_err(|e| format!("root wrap execution: {e}"))?;
    if !output.is_empty() {
      return Err("root wrap returned unexpected outputs".into());
    }
    Ok(Executed { expected, io, record, output })
  }

  /// Rows each circuit of the wrap execution needs, in system order.
  pub(crate) fn rows(&self, proof: &[u8]) -> Result<Vec<usize>, String> {
    let proof = decode(proof)?;
    let executed = self.execute(&proof)?;
    Ok(self.system.execution_rows(&executed.record))
  }

  /// Prove the wrap in `layout`'s fixed shape and return the serialized proof.
  pub(crate) fn normalize(
    &self,
    proof: &[u8],
    layout: &FixedRoot,
  ) -> Result<Vec<u8>, String> {
    if layout.memory_traces() != self.system.memory_circuits() {
      return Err("fixed root layout belongs to a different backend".into());
    }
    let proof = decode(proof)?;
    let executed = self.execute(&proof)?;
    drop(proof);
    let Executed { expected, io, record, output } = executed;
    let (claim, normalized) = self.system.prove_from_execution_normalized(
      self.aggr_idx,
      &expected[2..],
      &io,
      record,
      &output,
      layout.log_heights(),
    )?;
    if claim != expected {
      return Err("normalization changed the root claim".into());
    }
    normalized.to_bytes().map_err(|e| e.to_string())
  }
}

/// The fixed layout holding every execution in `rows` (elementwise maxima of
/// per-circuit rows), with `headroom` extra doublings per circuit.
pub(crate) fn layout(
  system: &AiurSystem,
  rows: &[usize],
  headroom: u8,
  claim_len: usize,
) -> Result<FixedRoot, String> {
  let logs = system.normalized_log_heights(rows, headroom)?;
  FixedRoot::new(logs, system.memory_circuits(), claim_len)
    .map_err(|e| e.to_string())
}

fn decode(proof: &[u8]) -> Result<AiurProof, String> {
  let decoded = AiurProof::from_bytes(proof).map_err(|e| e.to_string())?;
  if decoded.to_bytes().map_err(|e| e.to_string())? != proof {
    return Err("noncanonical aggregate root proof".into());
  }
  Ok(decoded)
}
