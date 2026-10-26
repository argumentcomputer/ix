//! Bounded trace shards and verifier-only keys. Function rows may be partitioned
//! freely; memory rows remain consecutive and are closed by the batch preamble.
use super::*;
use multi_stark::batch::{BatchMessage, Retention};

fn commitment_parameters(p: Parameters) -> CommitmentParameters {
  CommitmentParameters { log_blowup: p.log_blowup, cap_height: 0 }
}
fn fri_parameters(p: Parameters) -> FriParameters {
  FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: p.num_queries,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  }
}

/// Decode only trusted compiler output (or compare its digest with a trusted
/// key). A key is a statement, not evidence that its program is the intended one.
pub struct VerifyingKey {
  system: System<GoldilocksBlake3Config>,
  cp: CommitmentParameters,
  fp: FriParameters,
}
impl VerifyingKey {
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let (system, cp, fp) = stark_key::from_bytes(bytes)?;
    if cp.cap_height != 0
      || !(1..=4).contains(&cp.log_blowup)
      || fp.log_final_poly_len != 0
      || fp.max_log_arity != 1
      || fp.num_queries == 0
    {
      return Err("unsupported Aiur proving parameters".into());
    }
    Ok(Self { system, cp, fp })
  }
  pub fn to_bytes(&self) -> Vec<u8> {
    stark_key::to_bytes(&self.system, self.cp, self.fp)
  }
  pub fn verify(
    &self,
    claims: &[Vec<Val>],
    proof: &BatchProof,
  ) -> Result<(), String> {
    verify(&self.system, self.cp.log_blowup, claims, proof)
  }
}

fn verify(
  system: &System<GoldilocksBlake3Config>,
  log_blowup: usize,
  claims: &[Vec<Val>],
  proof: &BatchProof,
) -> Result<(), String> {
  let headers = &proof.preamble.headers;
  if headers.is_empty()
    || headers.len() > 65536
    || headers.len() != proof.proofs.len()
  {
    return Err("invalid batch shard count".into());
  }
  if !headers.iter().flat_map(|h| &h.claims).eq(claims) {
    return Err("batch public claims mismatch".into());
  }
  let mut budget = claims.len() as u128;
  for header in headers {
    if header.active.len() != system.circuits.len()
      || !header.active.contains(&true)
    {
      return Err("invalid circuit activation".into());
    }
    let mut degrees = header.log_degrees.iter();
    for (circuit, &on) in system.circuits.iter().zip(&header.active) {
      if !on {
        if circuit.preprocessed_height != 0 {
          return Err("inactive fixed table".into());
        }
        continue;
      }
      let log = *degrees.next().ok_or("missing trace height")?;
      if usize::from(log) + log_blowup > 32 {
        return Err("trace domain exceeds Goldilocks capacity".into());
      }
      let height = 1u128 << log;
      if circuit.preprocessed_height != 0
        && circuit.preprocessed_height as u128 != height
      {
        return Err("fixed table height mismatch".into());
      }
      budget = budget
        .checked_add(height * circuit.num_lookups.max(1) as u128)
        .filter(|&n| n < u128::from(Val::ORDER_U64))
        .ok_or("batch height/lookup budget exceeds field")?;
    }
    if degrees.next().is_some() {
      return Err("extra trace heights".into());
    }
  }
  let messages = &proof.preamble.messages;
  if !messages.len().is_multiple_of(2) {
    return Err("unpaired memory boundaries".into());
  }
  let mut previous = None;
  for pair in messages.as_chunks::<2>().0 {
    let (pull, push) = (&pair[0], &pair[1]);
    if pull.multiplicity != -Val::ONE
      || push.multiplicity != Val::ONE
      || pull.args.len() != 3
      || push.args.len() != 3
      || pull.args[0] != Val::from_u64(MEMSEG)
      || push.args[0] != pull.args[0]
      || push.args[1] != pull.args[1]
    {
      return Err("invalid memory boundary message".into());
    }
    let width = pull.args[1].as_canonical_u64();
    let a = pull.args[2].as_canonical_u64();
    let b = push.args[2].as_canonical_u64();
    if a > b
      || previous.is_some_and(|(w, end)| width < w || (width == w && a < end))
    {
      return Err("overlapping or unordered memory intervals".into());
    }
    previous = Some((width, b));
  }
  system
    .verify_batch(proof)
    .map_err(|e| format!("STARK batch verification failed: {e:?}"))
}

impl<'p, 'a, B: WitnessField> Backend<'p, 'a, B> {
  pub fn verifying_key_bytes(&self) -> Result<Vec<u8>, String> {
    if !self.segmented_memory {
      return Err("export a batch backend key for recursion".into());
    }
    Ok(stark_key::to_bytes(
      &self.system,
      commitment_parameters(self.parameters),
      fri_parameters(self.parameters),
    ))
  }

  /// Partition stage-one matrices into at most `max_rows` rows per function
  /// or memory chip. Fixed tables retain their exact domain in every shard.
  /// Regenerate keeps only headers at the barrier, bounding committed state
  /// by one shard. The execution record and source stage-one matrices remain.
  pub fn prove_batch(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    witness: SystemWitness<Val>,
    max_rows: usize,
    retention: Retention,
  ) -> Result<BatchProof, String> {
    let SystemWitness { traces, lookups } = witness;
    // Whole-trace lookup rows are invalid at the new shard boundaries and
    // would otherwise remain resident through both proving rounds.
    drop(lookups);
    self.prove_batch_stage_1(entry, args, output, traces, max_rows, retention)
  }

  /// Prove directly from stage-one matrices, computing lookup buffers only
  /// for the shard currently being committed. Pair with `generate_stage_1`.
  pub fn prove_batch_stage_1(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    traces: Vec<RowMajorMatrix<Val>>,
    max_rows: usize,
    retention: Retention,
  ) -> Result<BatchProof, String> {
    if !self.segmented_memory {
      return Err("batch proving requires Backend::for_batch".into());
    }
    if max_rows == 0 || !max_rows.is_power_of_two() {
      return Err("shard rows must be a positive power of two".into());
    }
    let claim = self.claim(entry, args, output)?;
    let (active, degrees) = self.trace_shape(&traces)?;
    self.check_shape(&active, &degrees)?;
    let shards = traces
      .iter()
      .zip(&self.system.circuits)
      .filter(|(_, c)| c.preprocessed_height == 0)
      .map(|(t, _)| t.height().div_ceil(max_rows))
      .max()
      .unwrap_or(1)
      .max(1);
    if shards > 65536 {
      return Err("too many trace shards".into());
    }
    let memory_start = self.members.len() + self.tables.len();
    let mut messages = Vec::new();
    for trace in &traces[memory_start..] {
      let total = trace
        .values
        .chunks_exact(trace.width)
        .take_while(|row| row[1] == Val::ONE)
        .count();
      if total != 0 {
        let width = Val::from_usize(trace.width - 3);
        messages.push(BatchMessage::pull(vec![
          Val::from_u64(MEMSEG),
          width,
          Val::ZERO,
        ]));
        messages.push(BatchMessage::push(vec![
          Val::from_u64(MEMSEG),
          width,
          Val::from_usize(total),
        ]));
      }
    }
    let mut claims = vec![vec![]; shards];
    claims[0].push(claim);
    // Lookup rows depend on shard boundaries and are regenerated from each
    // slice, including the IsFirst/Last/Transition selectors.
    let retention =
      if self.gpu_lookup_only { Retention::Regenerate } else { retention };
    let proof = self.system.prove_batch_with(
      &self.key,
      &claims,
      messages,
      retention,
      |shard| {
        let sliced = traces
          .iter()
          .zip(&self.system.circuits)
          .map(|(trace, circuit)| {
            if circuit.preprocessed_height != 0 {
              return if shard == 0 {
                trace.clone()
              } else {
                RowMajorMatrix::new(
                  Val::zero_vec(trace.values.len()),
                  trace.width,
                )
              };
            }
            let begin = (shard * max_rows).min(trace.height());
            let end = (begin + max_rows).min(trace.height());
            RowMajorMatrix::new(
              trace.values[begin * trace.width..end * trace.width].to_vec(),
              trace.width,
            )
          })
          .collect();
        self.witness_from_main(sliced)
      },
    );
    self.verify_batch(entry, args, output, &proof)?;
    Ok(proof)
  }

  pub fn verify_batch(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    proof: &BatchProof,
  ) -> Result<(), String> {
    if !self.segmented_memory {
      return Err("batch verification requires Backend::for_batch".into());
    }
    verify(
      &self.system,
      self.parameters.log_blowup,
      &[self.claim(entry, args, output)?],
      proof,
    )
  }
}
