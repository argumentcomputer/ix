//! Bounded trace shards and verifier-only keys. Function rows may be partitioned
//! freely; memory rows remain consecutive and are closed by the batch preamble.
use super::*;
#[cfg(test)]
use multi_stark::system::Circuit;
#[cfg(all(feature = "cuda", test))]
use multi_stark::witness::TraceSource;
use multi_stark::{
  batch::{BatchMessage, Retention},
  witness::PreparedWitness,
};
#[cfg(all(feature = "cuda", test))]
use std::sync::Arc;

/// A streamed batch authenticates one public claim across independently
/// executed records. Memory intervals are half-open and width-separated.
pub struct StreamPlan {
  pub shards: usize,
  pub memory_intervals: Vec<(u64, u64, u64)>,
  pub retention: Retention,
}

/// A streamed proof, the time its prover waited for witnesses, and whether
/// they were built ahead of it.
pub struct Streamed {
  pub proof: BatchProof,
  pub stall: std::time::Duration,
  pub pipelined: bool,
}

/// The threads that build a lane's next trace-shard witness while its
/// prover commits or proves the current one. Population runs on its own
/// operating-system thread inside this pool, never on the prover's threads,
/// so it always starts and cannot wait behind a caller blocked in a join.
pub struct ShardFeed {
  #[cfg(feature = "parallel")]
  pool: rayon::ThreadPool,
}

impl ShardFeed {
  /// A feed of `threads` population threads.
  pub fn new(threads: usize) -> Result<Self, String> {
    #[cfg(feature = "parallel")]
    {
      let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(threads.max(1))
        .thread_name(|i| format!("aiur-population-{i}"))
        .build()
        .map_err(|e| e.to_string())?;
      Ok(Self { pool })
    }
    #[cfg(not(feature = "parallel"))]
    {
      let _ = threads;
      Ok(Self {})
    }
  }

  /// A feed as wide as the calling thread's pool.
  pub fn matching_current() -> Result<Self, String> {
    #[cfg(feature = "parallel")]
    let threads = rayon::current_num_threads();
    #[cfg(not(feature = "parallel"))]
    let threads = 1;
    Self::new(threads)
  }

  fn install<R: Send>(&self, work: impl FnOnce() -> R + Send) -> R {
    #[cfg(feature = "parallel")]
    {
      self.pool.install(work)
    }
    #[cfg(not(feature = "parallel"))]
    {
      work()
    }
  }
}

/// Copy a run of rows. One shard of a large trace is gigabytes, so a serial
/// `to_vec` cost more than committing the shard on a GPU.
#[cfg(test)]
fn copy_rows(values: &[Val]) -> Vec<Val> {
  #[cfg(feature = "parallel")]
  {
    const CHUNK: usize = 1 << 16;
    if values.len() > 4 * CHUNK {
      let mut copy = Val::zero_vec(values.len());
      copy
        .par_chunks_mut(CHUNK)
        .zip(values.par_chunks(CHUNK))
        .for_each(|(to, from)| to.copy_from_slice(from));
      return copy;
    }
  }
  values.to_vec()
}

/// Stage-one traces ready for batch proving: host rows, plus the device
/// record of the function circuits the GPU fills
/// (`AIUR_GPU_TRACE=generated`), whose host matrices are empty placeholders.
#[cfg(test)]
pub struct StageOne {
  pub traces: Vec<RowMajorMatrix<Val>>,
  #[cfg(feature = "cuda")]
  device: Option<Arc<gpu::DeviceRecord>>,
}

#[cfg(test)]
impl StageOne {
  pub fn host(traces: Vec<RowMajorMatrix<Val>>) -> Self {
    Self {
      traces,
      #[cfg(feature = "cuda")]
      device: None,
    }
  }

  /// Heights of device-populated circuits, by circuit; empty without any.
  fn device_heights(&self) -> Vec<Option<usize>> {
    #[cfg(feature = "cuda")]
    if let Some(device) = &self.device {
      return (0..self.traces.len()).map(|ci| device.height(ci)).collect();
    }
    vec![]
  }

  fn height(&self, ci: usize, device: &[Option<usize>]) -> usize {
    device
      .get(ci)
      .copied()
      .flatten()
      .unwrap_or_else(|| self.traces[ci].height())
  }

  /// Stage-one cells, on the host and the device, for resource plans.
  pub fn cells(&self) -> u64 {
    let device = self.device_heights();
    (0..self.traces.len())
      .map(|ci| (self.height(ci, &device) * self.traces[ci].width) as u64)
      .sum()
  }
}

/// Arguments for a memory-segment boundary message (`[MEMSEG, width, ptr]`).
pub fn memseg_args(width: usize, ptr: Val) -> [Val; 3] {
  [Val::from_u64(MEMSEG), Val::from_usize(width), ptr]
}

/// Decode only trusted compiler output (or compare its digest with a trusted
/// key). A key is a statement, not evidence that its program is the intended one.
pub struct VerifyingKey {
  system: System<GoldilocksBlake3Config>,
  cp: CommitmentParameters,
  fp: FriParameters,
}
impl Clone for VerifyingKey {
  fn clone(&self) -> Self {
    // Already accepted, possibly through the test-only waiver.
    Self::decode(&self.to_bytes(), false).expect("valid VerifyingKey")
  }
}
impl std::fmt::Debug for VerifyingKey {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("VerifyingKey")
      .field("num_circuits", &self.num_circuits())
      .finish()
  }
}
impl VerifyingKey {
  /// Decode a key, rejecting parameters this adapter does not produce or
  /// that are below the security floor ([`stark_key::security`]).
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    Self::decode(bytes, true)
  }
  /// [`Self::from_bytes`] without the security floor, for tests whose toy
  /// keys keep recursive verifier circuits small. A verifier must never trust
  /// a key decoded this way.
  #[doc(hidden)]
  pub fn from_bytes_below_floor(bytes: &[u8]) -> Result<Self, String> {
    Self::decode(bytes, false)
  }
  fn decode(bytes: &[u8], floor: bool) -> Result<Self, String> {
    let (system, cp, fp) = if floor {
      stark_key::from_bytes(bytes)?
    } else {
      stark_key::from_bytes_below_floor(bytes)?
    };
    if cp.cap_height != 0
      || !stark_key::security::LOG_BLOWUP_RANGE.contains(&cp.log_blowup)
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
  pub const fn commitment_parameters(&self) -> CommitmentParameters {
    self.cp
  }
  pub const fn fri_parameters(&self) -> FriParameters {
    self.fp
  }
  pub const fn system(&self) -> &System<GoldilocksBlake3Config> {
    &self.system
  }
  pub fn num_circuits(&self) -> usize {
    self.system.circuits.len()
  }
  pub fn validate_preamble(
    &self,
    claim: &[Val],
    preamble: &multi_stark::batch::BatchPreamble<GoldilocksBlake3Config>,
  ) -> Result<(), String> {
    validate_preamble(&self.system, self.cp.log_blowup, &[claim], preamble)
  }
  pub fn verify(
    &self,
    claims: &[Vec<Val>],
    proof: &BatchProof,
  ) -> Result<(), String> {
    verify(&self.system, self.cp.log_blowup, claims, proof)
  }
}

fn validate_preamble<C: AsRef<[Val]>>(
  system: &System<GoldilocksBlake3Config>,
  log_blowup: usize,
  claims: &[C],
  preamble: &multi_stark::batch::BatchPreamble<GoldilocksBlake3Config>,
) -> Result<(), String> {
  let headers = &preamble.headers;
  if headers.is_empty() || headers.len() > 65536 {
    return Err("invalid batch shard count".into());
  }
  if !headers
    .iter()
    .flat_map(|h| h.claims.iter().map(Vec::as_slice))
    .eq(claims.iter().map(C::as_ref))
  {
    return Err("batch public claims mismatch".into());
  }
  let mut budget = claims.len() as u128;
  let mut rows = 0u128;
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
      // The depth pass's row bound, over every shard ([`MAX_BATCH_ROWS`]).
      rows += height;
      if rows > u128::from(MAX_BATCH_ROWS) {
        return Err("batch rows exceed the row bound (2^39)".into());
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
  let messages = &preamble.messages;
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
  Ok(())
}

fn verify(
  system: &System<GoldilocksBlake3Config>,
  log_blowup: usize,
  claims: &[Vec<Val>],
  proof: &BatchProof,
) -> Result<(), String> {
  if proof.preamble.headers.len() != proof.proofs.len() {
    return Err("invalid batch shard count".into());
  }
  validate_preamble(system, log_blowup, claims, &proof.preamble)?;
  system
    .verify_batch(proof)
    .map_err(|e| format!("STARK batch verification failed: {e:?}"))
}

impl<'p, 'a, B: WitnessField> Backend<'p, 'a, B> {
  /// Multiple GPU shards still regenerate to bound device residency. A single
  /// shard needs the same committed state in round two either way: discarding
  /// it only repeats the upload, LDE and Merkle commitment, without saving peak
  /// memory. Lookup storage and commitment retention are independent choices.
  pub(super) fn requires_regeneration(&self, shards: usize) -> bool {
    self.gpu_lookup_only && shards > 1
  }

  /// Fallible two-round streaming. The supplier may replay a record and keep
  /// only its current trace matrices; no whole-environment trace is retained.
  #[cfg(test)]
  pub fn prove_streamed_stage_1(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    plan: StreamPlan,
    mut supply: impl FnMut(usize) -> Result<Vec<RowMajorMatrix<Val>>, String>,
  ) -> Result<BatchProof, String> {
    self.prove_streamed(entry, args, output, plan, |shard| {
      Ok(self.witness_from_main(supply(shard)?).into())
    })
  }

  /// Each supplied witness owns only one shard. Regenerated commitments
  /// must match the headers that fixed the batch transcript.
  pub fn prove_streamed(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    mut plan: StreamPlan,
    mut supply: impl FnMut(usize) -> Result<PreparedWitness<Val>, String>,
  ) -> Result<BatchProof, String> {
    if !self.segmented_memory || !(1..=65536).contains(&plan.shards) {
      return Err("invalid streamed batch".into());
    }
    let claim = self.claim(entry, args, output)?;
    plan.memory_intervals.sort_unstable();
    let mut previous = None;
    let mut messages = Vec::new();
    for (width, start, end) in plan.memory_intervals {
      if start >= end
        || end >= Val::ORDER_U64
        || previous.is_some_and(|(w, e)| w == width && start < e)
        || !self.system.circuits[self.members.len() + self.tables.len()..]
          .iter()
          .any(|c| (c.main_width - 3) as u64 == width)
      {
        return Err("invalid streamed memory intervals".into());
      }
      previous = Some((width, end));
      messages.push(BatchMessage::pull(vec![
        Val::from_u64(MEMSEG),
        Val::from_u64(width),
        Val::from_u64(start),
      ]));
      messages.push(BatchMessage::push(vec![
        Val::from_u64(MEMSEG),
        Val::from_u64(width),
        Val::from_u64(end),
      ]));
    }
    let mut headers = Vec::new();
    let mut retained = Vec::new();
    let retain = !self.requires_regeneration(plan.shards)
      && matches!(plan.retention, Retention::Retain);
    let mut lookup_budget = 1u128;
    for shard in 0..plan.shards {
      let witness = supply(shard)?;
      self.check_prepared_shape(&witness)?;
      for (trace, circuit) in witness.traces.iter().zip(&self.system.circuits) {
        lookup_budget +=
          trace.height() as u128 * circuit.num_lookups.max(1) as u128;
      }
      if lookup_budget >= u128::from(Val::ORDER_U64) {
        return Err("batch height/lookup budget exceeds field".into());
      }
      let stage = self.system.prove_stage_1(witness);
      let claims = if shard == 0 { vec![claim.as_slice()] } else { vec![] };
      headers.push(stage.header(&claims));
      retained.push(if retain { Some(stage) } else { None });
    }
    let preamble = multi_stark::batch::BatchPreamble { headers, messages };
    let mut proofs = Vec::new();
    for (shard, cached) in retained.into_iter().enumerate() {
      let claims = if shard == 0 { vec![claim.as_slice()] } else { vec![] };
      let stage = if let Some(stage) = cached {
        stage
      } else {
        let witness = supply(shard)?;
        self.check_prepared_shape(&witness)?;
        let stage = self.system.prove_stage_1(witness);
        if stage.header(&claims) != preamble.headers[shard] {
          return Err(format!("streamed shard {shard} changed between rounds"));
        }
        stage
      };
      proofs.push(
        self
          .system
          .prove_batch_shard(&self.key, stage, &claims, &preamble, shard),
      );
    }
    let proof = BatchProof { preamble, proofs };
    self.verify_batch(entry, args, output, &proof)?;
    Ok(proof)
  }

  /// [`Self::prove_streamed`] with `supply(round, shard)`. With a `feed`,
  /// a producer thread on the feed's pool builds the next witness while the
  /// calling thread commits or proves the current one; a rendezvous channel
  /// keeps at most one finished witness ahead, and the producer stops at
  /// its first error. Supplies happen in the serial order either way, so
  /// the proof bytes are the same.
  ///
  /// The producer makes no device calls: generated traces are descriptors
  /// that the prover fills on the calling thread during commitment, and
  /// they exist only with device lookups, so the worker never materializes
  /// one to build host lookups. Should a supplier touch the device anyway,
  /// every CUDA entry point selects its device and synchronizes its
  /// per-thread stream before returning, so a handed-over witness carries
  /// no pending device work.
  pub fn prove_streamed_scheduled(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    plan: StreamPlan,
    feed: Option<&ShardFeed>,
    supply: impl Fn(usize, usize) -> Result<PreparedWitness<Val>, String> + Sync,
  ) -> Result<Streamed, String>
  where
    Self: Sync,
  {
    let shards = plan.shards.max(1);
    let rounds = if !self.requires_regeneration(plan.shards)
      && matches!(plan.retention, Retention::Retain)
    {
      1
    } else {
      2
    };
    let Some(feed) = feed.filter(|_| rounds * plan.shards >= 2) else {
      return self.supply_serially(entry, args, output, plan, shards, &supply);
    };
    let mut stall = std::time::Duration::ZERO;
    let order: Vec<_> = (0..rounds)
      .flat_map(|round| (0..plan.shards).map(move |shard| (round, shard)))
      .collect();
    let (sender, receiver) = std::sync::mpsc::sync_channel(0);
    let supply = &supply;
    let produce = move || {
      for (round, shard) in order {
        let witness = supply(round, shard);
        let failed = witness.is_err();
        if sender.send((shard, witness)).is_err() || failed {
          break;
        }
      }
    };
    let consume = move || {
      let proof = self.prove_streamed(entry, args, output, plan, |shard| {
        let start = std::time::Instant::now();
        let (supplied, witness) = receiver
          .recv()
          .map_err(|_| "shard population worker stopped".to_owned())?;
        stall += start.elapsed();
        if supplied != shard {
          return Err(format!(
            "population worker supplied shard {supplied} for {shard}"
          ));
        }
        witness
      });
      (proof, stall)
    };
    let (proof, stall) = std::thread::scope(|scope| {
      let producer = scope.spawn(move || feed.install(produce));
      // Returning drops the receiver, which stops the producer at its next
      // send.
      let consumed = consume();
      producer
        .join()
        .map_err(|_| "shard population worker panicked".to_owned())?;
      Ok::<_, String>(consumed)
    })?;
    Ok(Streamed { proof: proof?, stall, pipelined: true })
  }

  fn supply_serially(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    plan: StreamPlan,
    shards: usize,
    supply: &(impl Fn(usize, usize) -> Result<PreparedWitness<Val>, String> + Sync),
  ) -> Result<Streamed, String> {
    let mut stall = std::time::Duration::ZERO;
    let mut calls = 0;
    let proof = self.prove_streamed(entry, args, output, plan, |shard| {
      let start = std::time::Instant::now();
      let witness = supply(calls / shards, shard);
      calls += 1;
      stall += start.elapsed();
      witness
    })?;
    Ok(Streamed { proof, stall, pipelined: false })
  }

  fn check_prepared_shape(
    &self,
    witness: &PreparedWitness<Val>,
  ) -> Result<(), String> {
    if witness.traces.len() != self.system.circuits.len()
      || witness.lookups.len() != witness.traces.len()
    {
      return Err("wrong circuit count".into());
    }
    let mut active = Vec::new();
    let mut degrees = Vec::new();
    for (trace, circuit) in witness.traces.iter().zip(&self.system.circuits) {
      if trace.width() != circuit.main_width || trace.width() == 0 {
        return Err("invalid main trace width".into());
      }
      if let multi_stark::witness::TraceSource::Host(matrix) = trace
        && !matrix.values.len().is_multiple_of(matrix.width)
      {
        return Err("partial main trace row".into());
      }
      let height = trace.height();
      if height != 0 && !height.is_power_of_two() {
        return Err("invalid main trace shape".into());
      }
      active.push(height != 0);
      if height != 0 {
        degrees.push(height.ilog2() as u8);
      }
    }
    self.check_shape(&active, &degrees)
  }

  #[cfg(test)]
  pub fn slice_stage_1(
    &self,
    traces: &[RowMajorMatrix<Val>],
    shard: usize,
    max_rows: usize,
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    if max_rows == 0
      || !max_rows.is_power_of_two()
      || traces.len() != self.system.circuits.len()
    {
      return Err("invalid stage-one slice".into());
    }
    let begin = shard.checked_mul(max_rows).ok_or("shard offset overflow")?;
    let slice = |(trace, circuit): (&RowMajorMatrix<Val>, &Circuit<Val>)| {
      Self::slice_matrix(trace, circuit, shard, begin, max_rows)
    };
    #[cfg(feature = "parallel")]
    let sliced =
      traces.par_iter().zip(&self.system.circuits).map(slice).collect();
    #[cfg(not(feature = "parallel"))]
    let sliced = traces.iter().zip(&self.system.circuits).map(slice).collect();
    Ok(sliced)
  }

  #[cfg(test)]
  fn slice_matrix(
    trace: &RowMajorMatrix<Val>,
    circuit: &Circuit<Val>,
    shard: usize,
    begin: usize,
    max_rows: usize,
  ) -> RowMajorMatrix<Val> {
    if circuit.preprocessed_height != 0 {
      return if shard == 0 {
        RowMajorMatrix::new(copy_rows(&trace.values), trace.width)
      } else {
        RowMajorMatrix::new(Val::zero_vec(trace.values.len()), trace.width)
      };
    }
    let begin = begin.min(trace.height());
    let end = begin.saturating_add(max_rows).min(trace.height());
    RowMajorMatrix::new(
      copy_rows(&trace.values[begin * trace.width..end * trace.width]),
      trace.width,
    )
  }

  /// The supplier's slice for `shard`. On the shard's last supply, a matrix
  /// that no other shard reads (shard zero's fixed tables and every circuit
  /// no taller than one shard) moves out of the source instead of being
  /// copied; later shards only need its dimensions. With one retained shard
  /// this moves the whole witness.
  #[cfg(test)]
  fn take_stage_1(
    &self,
    source: &mut [RowMajorMatrix<Val>],
    fixed_cells: &[usize],
    shard: usize,
    max_rows: usize,
    last: bool,
  ) -> Vec<RowMajorMatrix<Val>> {
    let begin = shard * max_rows;
    let mut taken: Vec<_> = (0..source.len()).map(|_| None).collect();
    if last && shard == 0 {
      for ((trace, circuit), slot) in
        source.iter_mut().zip(&self.system.circuits).zip(&mut taken)
      {
        if circuit.preprocessed_height != 0 || trace.height() <= max_rows {
          let width = trace.width;
          *slot = Some(std::mem::replace(
            trace,
            RowMajorMatrix::new(Vec::new(), width),
          ));
        }
      }
    }
    let source = &*source;
    let slice = |(i, taken): (usize, Option<RowMajorMatrix<Val>>)| {
      taken.unwrap_or_else(|| {
        let (trace, circuit) = (&source[i], &self.system.circuits[i]);
        if circuit.preprocessed_height != 0 && shard != 0 {
          RowMajorMatrix::new(Val::zero_vec(fixed_cells[i]), trace.width)
        } else {
          Self::slice_matrix(trace, circuit, shard, begin, max_rows)
        }
      })
    };
    #[cfg(feature = "parallel")]
    let sliced = taken.into_par_iter().enumerate().map(slice).collect();
    #[cfg(not(feature = "parallel"))]
    let sliced = taken.into_iter().enumerate().map(slice).collect();
    sliced
  }

  pub fn verifying_key_bytes(&self) -> Result<Vec<u8>, String> {
    if !self.segmented_memory {
      return Err("export a batch backend key for recursion".into());
    }
    Ok(stark_key::to_bytes(
      &self.system,
      self.parameters.commitment(),
      self.parameters.fri(),
    ))
  }

  /// Partition stage-one matrices into at most `max_rows` rows per function
  /// or memory chip. Fixed tables retain their exact domain in every shard.
  /// Regenerate keeps only headers at the barrier, bounding committed state
  /// by one shard. The execution record and source stage-one matrices remain.
  #[cfg(test)]
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
  #[cfg(test)]
  pub fn prove_batch_stage_1(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    traces: Vec<RowMajorMatrix<Val>>,
    max_rows: usize,
    retention: Retention,
  ) -> Result<BatchProof, String> {
    self.prove_stage_one(
      entry,
      args,
      output,
      StageOne::host(traces),
      max_rows,
      retention,
    )
  }

  /// Stage one for [`Self::prove_stage_one`]: like
  /// [`Self::generate_stage_1`], except that with `AIUR_GPU_TRACE=generated`
  /// the function circuits the GPU can fill are left to the device, which
  /// receives the record tables they read. The record can then be dropped.
  #[cfg(test)]
  pub fn prepare_stage_1(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<StageOne, String> {
    #[cfg(feature = "cuda")]
    if let Some(plans) = self.device_plans_for(record) {
      self.plan.validate_record(record)?;
      let device = gpu::DeviceRecord::upload(self, plans, record, self.device)?;
      let heights: Vec<_> =
        (0..self.system.circuits.len()).map(|ci| device.height(ci)).collect();
      let traces = self
        .generate_with::<false>(
          record,
          Some((entry, args)),
          &heights,
          device.ranges(),
        )?
        .traces;
      return Ok(StageOne { traces, device: Some(Arc::new(device)) });
    }
    Ok(StageOne::host(self.generate_stage_1(record, entry, args)?))
  }

  #[cfg(test)]
  pub fn prove_stage_one(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    stage: StageOne,
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
    let device_heights = stage.device_heights();
    let (active, degrees) =
      self.trace_shape_with(&stage.traces, &device_heights)?;
    self.check_shape(&active, &degrees)?;
    let shards = (0..stage.traces.len())
      .filter(|&ci| self.system.circuits[ci].preprocessed_height == 0)
      .map(|ci| stage.height(ci, &device_heights).div_ceil(max_rows))
      .max()
      .unwrap_or(1)
      .max(1);
    #[cfg(feature = "cuda")]
    let StageOne { traces, device } = stage;
    #[cfg(not(feature = "cuda"))]
    let StageOne { traces } = stage;
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
    // Build lookup buffers from the sliced rows. LookupPlan::compile rejects
    // nonlocal lookup expressions; boundary selectors belong to constraints.
    let retention = if self.requires_regeneration(shards) {
      Retention::Regenerate
    } else {
      retention
    };
    // Shards are supplied in order, once per round: twice when regenerated.
    // The source matrices remain resident until their last supply.
    let supplies = if matches!(retention, Retention::Retain) { 1 } else { 2 };
    let mut supplied = vec![0u8; shards];
    let fixed_cells: Vec<_> = traces.iter().map(|t| t.values.len()).collect();
    let mut traces = traces;
    let proof = self.system.prove_batch_with(
      &self.key,
      &claims,
      messages,
      retention,
      |shard| {
        #[cfg(feature = "trace-profile")]
        let profile = super::profile::Span::new("shard_copy", 0);
        supplied[shard] += 1;
        let last = supplied[shard] == supplies;
        let sliced =
          self.take_stage_1(&mut traces, &fixed_cells, shard, max_rows, last);
        #[cfg(feature = "trace-profile")]
        drop(profile);
        #[cfg(feature = "cuda")]
        if let Some(device) = &device {
          return self.device_witness(sliced, device, shard, max_rows);
        }
        PreparedWitness::from(self.witness_from_main(sliced))
      },
    );
    self.verify_batch(entry, args, output, &proof)?;
    Ok(proof)
  }

  /// A shard's witness with the device circuits as generated traces over
  /// their rows of this shard and every lookup derived on the device.
  #[cfg(feature = "cuda")]
  #[cfg(test)]
  fn device_witness(
    &self,
    sliced: Vec<RowMajorMatrix<Val>>,
    device: &Arc<gpu::DeviceRecord>,
    shard: usize,
    max_rows: usize,
  ) -> PreparedWitness<Val> {
    let begin = shard * max_rows;
    let traces: Vec<_> = sliced
      .into_iter()
      .enumerate()
      .map(|(ci, matrix)| match device.height(ci) {
        Some(height) if begin < height => {
          TraceSource::Generated(Arc::new(gpu::DeviceTrace {
            record: Arc::clone(device),
            circuit: ci,
            base: begin,
            height: max_rows.min(height - begin),
            real_rows: max_rows.min(height - begin),
          }))
        },
        _ => TraceSource::Host(matrix),
      })
      .collect();
    let lookups = traces
      .iter()
      .zip(&self.system.circuits)
      .map(|(trace, circuit)| {
        let widths: Vec<_> =
          circuit.graph.lookups.iter().map(|l| l.args.len()).collect();
        multi_stark::lookup::LookupValues::shape_only(trace.height(), &widths)
      })
      .collect();
    PreparedWitness { traces, lookups }
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

  /// Unpadded row count for every circuit in `self.system.circuits` order:
  /// function circuits (`0 .. self.members.len()`), fixed tables
  /// (`self.members.len() .. self.members.len() + self.tables.len()`), and
  /// ROM circuits (`self.members.len() + self.tables.len() ..`).
  pub fn execution_rows(&self, record: &Execution<B>) -> Vec<usize> {
    let mut rows = Vec::with_capacity(self.system.circuits.len());
    for members in &self.members {
      rows.push(members.iter().map(|&f| record.queries.tables[f].len()).sum());
    }
    for ci in self.members.len()..self.members.len() + self.tables.len() {
      rows.push(self.system.circuits[ci].preprocessed_height);
    }
    for &width in &self.rom.widths {
      rows.push(record.memory.indices_for_width(width).len());
    }
    rows
  }

  /// Target power-of-two log heights for a fixed-shape root proof.
  pub fn normalized_log_heights(
    &self,
    rows: &[usize],
    headroom: u8,
  ) -> Result<Vec<u8>, String> {
    if rows.len() != self.system.circuits.len() {
      return Err(format!(
        "expected {} circuit row counts, got {}",
        self.system.circuits.len(),
        rows.len()
      ));
    }
    rows
      .iter()
      .zip(&self.system.circuits)
      .enumerate()
      .map(|(index, (&count, circuit))| {
        if circuit.preprocessed_height != 0 {
          if count != circuit.preprocessed_height {
            return Err(format!(
              "fixed circuit {index} has {count} rows, expected {}",
              circuit.preprocessed_height
            ));
          }
          return u8::try_from(circuit.preprocessed_height.ilog2())
            .map_err(|e| format!("fixed circuit {index} log height: {e}"));
        }
        let base = count
          .max(2)
          .checked_next_power_of_two()
          .ok_or_else(|| {
            format!("circuit {index} row count {count} overflows power of two")
          })?
          .ilog2();
        let log = base
          .checked_add(u32::from(headroom))
          .and_then(|log| u8::try_from(log).ok())
          .filter(|&log| log <= 26)
          .ok_or_else(|| {
            format!(
              "circuit {index} normalized log height exceeds the 2^26 KZG limit (rows={count}, headroom={headroom})"
            )
          })?;
        Ok(log)
      })
      .collect()
  }

  /// `(payload_width, circuit_index)` for every ROM circuit in ascending width
  /// order.
  pub fn memory_circuits(&self) -> Vec<(usize, usize)> {
    let base = self.members.len() + self.tables.len();
    self
      .rom
      .widths
      .iter()
      .enumerate()
      .map(|(i, &width)| (width, base + i))
      .collect()
  }

  /// Prove a single-shard root execution padded to `log_heights`, emitting
  /// `[0, unpadded)` `MEMSEG` boundary messages for every ROM circuit (including
  /// empty `0..0` intervals) to match the fixed-shape outer verifier.
  pub fn prove_normalized(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    record: Execution<B>,
    log_heights: &[u8],
  ) -> Result<(Vec<Val>, BatchProof), String> {
    if !self.segmented_memory {
      return Err("normalized proving requires Backend::for_batch".into());
    }
    if log_heights.len() != self.system.circuits.len() {
      return Err(format!(
        "expected {} normalized circuit log heights, got {}",
        self.system.circuits.len(),
        log_heights.len()
      ));
    }
    for (index, (&log, circuit)) in
      log_heights.iter().zip(&self.system.circuits).enumerate()
    {
      if !(1..=26).contains(&log) {
        return Err(format!(
          "circuit {index} normalized log height {log} must be in 1..=26"
        ));
      }
      if circuit.preprocessed_height != 0
        && circuit.preprocessed_height != (1usize << log)
      {
        return Err(format!(
          "fixed circuit {index} requires height {}, got 2^{log}",
          circuit.preprocessed_height
        ));
      }
    }
    let unpadded_rows = self.execution_rows(&record);
    for (index, (&rows, &log)) in
      unpadded_rows.iter().zip(log_heights).enumerate()
    {
      let capacity = 1usize << log;
      if rows > capacity {
        return Err(format!(
          "circuit {index} has {rows} unpadded rows, exceeding normalized height 2^{log} ({capacity})"
        ));
      }
    }
    let active = vec![true; log_heights.len()];
    self.check_shape(&active, log_heights)?;
    let claim = self.claim(entry, args, output)?;
    let mut traces = self.generate_stage_1(&record, entry, args)?;
    drop(record);
    for (index, (trace, &log)) in traces.iter_mut().zip(log_heights).enumerate()
    {
      let target_height = 1usize << log;
      if trace.height() > target_height {
        return Err(format!(
          "circuit {index} trace height {} exceeds normalized height {target_height}",
          trace.height()
        ));
      }
      let target_values = trace
        .width
        .checked_mul(target_height)
        .ok_or_else(|| format!("circuit {index} padded trace size overflow"))?;
      trace.values.resize(target_values, Val::ZERO);
    }
    let rom_base = self.members.len() + self.tables.len();
    let mut messages = Vec::with_capacity(self.rom.widths.len() * 2);
    for (i, &width) in self.rom.widths.iter().enumerate() {
      let unpadded = unpadded_rows[rom_base + i];
      messages.push(BatchMessage::pull(memseg_args(width, Val::ZERO).to_vec()));
      messages.push(BatchMessage::push(
        memseg_args(width, Val::from_usize(unpadded)).to_vec(),
      ));
    }
    let witness = self.witness_from_main(traces);
    let proof = self.system.prove_batch(
      &self.key,
      vec![multi_stark::batch::ShardInput {
        claims: vec![claim.clone()],
        witness,
      }],
      messages,
    );
    self.verify_batch(entry, args, output, &proof)?;
    Ok((claim, proof))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// A feed starts its producer even when every thread of the caller's
  /// pool is a caller waiting for its own producer.
  #[cfg(feature = "parallel")]
  #[test]
  fn feeds_start_when_every_pool_thread_waits() {
    let pool = rayon::ThreadPoolBuilder::new().num_threads(2).build().unwrap();
    let (done, finished) = std::sync::mpsc::channel();
    pool.spawn_broadcast(move |_| {
      let feed = ShardFeed::new(1).unwrap();
      let (sender, receiver) = std::sync::mpsc::sync_channel::<()>(0);
      let received = std::thread::scope(|scope| {
        scope.spawn(|| feed.install(move || sender.send(()).is_ok()));
        receiver.recv().is_ok()
      });
      done.send(received).unwrap();
    });
    for _ in 0..2 {
      let received = finished
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("a caller deadlocked waiting for its producer");
      assert!(received);
    }
  }

  #[cfg(feature = "parallel")]
  #[test]
  fn feeds_run_population_on_their_own_pool() {
    let feed = ShardFeed::new(3).unwrap();
    assert_eq!(feed.install(rayon::current_num_threads), 3);
  }

  #[test]
  fn copy_rows_matches_a_serial_copy() {
    for len in [0_u64, 1, 4 << 16, (4 << 16) + 1, (9 << 16) + 12345] {
      let values: Vec<Val> = (0..len).map(Val::from_u64).collect();
      assert_eq!(copy_rows(&values), values);
    }
  }
}
