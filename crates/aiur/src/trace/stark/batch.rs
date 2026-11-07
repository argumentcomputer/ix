//! Bounded trace shards and verifier-only keys. Function rows may be partitioned
//! freely; memory rows remain consecutive and are closed by the batch preamble.
use super::*;
#[cfg(feature = "cuda")]
use multi_stark::witness::TraceSource;
use multi_stark::{
  batch::{BatchMessage, Retention},
  system::Circuit,
  witness::PreparedWitness,
};
#[cfg(feature = "cuda")]
use std::sync::Arc;

/// A streamed batch authenticates one public claim across independently
/// executed records. Memory intervals are half-open and width-separated.
pub struct StreamPlan {
  pub shards: usize,
  pub memory_intervals: Vec<(u64, u64, u64)>,
  pub retention: Retention,
}

/// Copy a run of rows. One shard of a large trace is gigabytes, so a serial
/// `to_vec` cost more than committing the shard on a GPU.
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
pub struct StageOne {
  pub traces: Vec<RowMajorMatrix<Val>>,
  #[cfg(feature = "cuda")]
  device: Option<Arc<gpu::DeviceRecord>>,
}

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
  pub fn prove_streamed_stage_1(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    mut plan: StreamPlan,
    mut supply: impl FnMut(usize) -> Result<Vec<RowMajorMatrix<Val>>, String>,
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
    for shard in 0..plan.shards {
      let traces = supply(shard)?;
      let (active, degrees) = self.trace_shape(&traces)?;
      self.check_shape(&active, &degrees)?;
      let stage = self.system.prove_stage_1(self.witness_from_main(traces));
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
        let traces = supply(shard)?;
        let (active, degrees) = self.trace_shape(&traces)?;
        self.check_shape(&active, &degrees)?;
        let stage = self.system.prove_stage_1(self.witness_from_main(traces));
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
  pub fn prepare_stage_1(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<StageOne, String> {
    #[cfg(feature = "cuda")]
    if let Some(plans) = &self.device_plans {
      let device = gpu::DeviceRecord::upload(self, plans, record, self.device)?;
      let heights: Vec<_> =
        (0..self.system.circuits.len()).map(|ci| device.height(ci)).collect();
      let traces = self
        .generate_with::<false>(record, Some((entry, args)), &heights)?
        .traces;
      return Ok(StageOne { traces, device: Some(Arc::new(device)) });
    }
    Ok(StageOne::host(self.generate_stage_1(record, entry, args)?))
  }

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
            .map_err(|_| format!("fixed circuit {index} log height overflow"));
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

  #[test]
  fn copy_rows_matches_a_serial_copy() {
    for len in [0, 1, 4 << 16, (4 << 16) + 1, (9 << 16) + 12345] {
      let values: Vec<Val> = (0..len as u64).map(Val::from_u64).collect();
      assert_eq!(copy_rows(&values), values);
    }
  }
}
