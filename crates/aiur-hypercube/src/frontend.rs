//! Bridging Aiur toplevels to the Hypercube machine.
//!
//! Aiur's synthesis ([`build_circuit_inputs`]) and witness generation
//! ([`build_witness`]) are field-generic and backend-agnostic; this module
//! feeds their output into [`AiurMachine`].

use aiur::{
  AiurField,
  bytecode::{FunIdx, Toplevel},
  execute::{ExecError, IOBuffer, QueryRecord},
  function_channel, memory_channel, memory_counter_channel,
  synthesis::{
    CircuitType, build_circuit_inputs, build_witness, circuit_types,
  },
};
use multi_stark::{
  expr::Expr,
  lookup::{Lookup, LookupValues},
  p3_field::PrimeField64,
  p3_matrix::dense::RowMajorMatrix,
};

use crate::{
  machine::{AiurMachine, BuildError, CircuitSpec},
  prover::{AiurProof, AiurVerifyingKey, ProverParams, prove},
  record::AiurRecord,
  shard::{ShardingParams, partition_records},
};

/// Aiur's memory circuit for Hypercube.
///
/// Aiur's own memory circuit pins pointers to row indices with a transition
/// constraint (`ptr + 1 = ptr_next`), which Hypercube's row-local AIRs cannot
/// express. Instead the pointers of one table are threaded through a lookup
/// chain on [`memory_counter_channel`]: every real row pulls `(size, ptr)`
/// and pushes `(size, ptr + 1)`, and the boundary circuit pushes `(size, 0)`
/// and pulls `(size, N)`, `N` being the table's number of real rows. The
/// chain forces the real pointers to be exactly `0..N`, each once (a
/// duplicate pointer would need a second push of it, which nothing emits, and
/// a cycle would need the counter to wrap the field), so a pointer determines
/// its stored values. The trace layout is `Memory::witness_data`'s:
/// `[multiplicity, is_real, pointer, values..]`, sent raw (the multiplicities
/// vanish on padding rows).
fn memory_spec<FF: AiurField + PrimeField64>(size: usize) -> CircuitSpec<FF> {
  let k = |x: FF| Expr::constant(x);
  let (mult, is_real, ptr) = (Expr::main(0), Expr::main(1), Expr::main(2));
  let size_k = || k(FF::from_usize(size));
  let mut args = vec![k(memory_channel()), size_k(), ptr.clone()];
  args.extend((0..size).map(|i| {
    Expr::main(u32::try_from(3 + i).expect("column index exceeds u32"))
  }));
  CircuitSpec {
    name: circuit_name(CircuitType::Memory { width: size }),
    main_width: 3 + size,
    preprocessed: None,
    constraints: vec![is_real.clone() * (is_real.clone() - k(FF::ONE))],
    lookups: vec![
      Lookup { multiplicity: -mult, args },
      Lookup {
        multiplicity: -is_real.clone(),
        args: vec![k(memory_counter_channel()), size_k(), ptr.clone()],
      },
      Lookup {
        multiplicity: is_real,
        args: vec![k(memory_counter_channel()), size_k(), ptr + k(FF::ONE)],
      },
    ],
  }
}

/// The boundary circuit's trace: `N` per memory size, read off the memory
/// traces (`is_real` column) in system order.
fn boundary_trace<FF: AiurField + PrimeField64>(
  toplevel: &Toplevel<FF>,
  traces: &[(RowMajorMatrix<FF>, LookupValues<FF>)],
) -> RowMajorMatrix<FF> {
  let types = circuit_types(toplevel);
  let counts = toplevel.memory_sizes.iter().map(|&width| {
    let idx = types
      .iter()
      .position(|t| *t == CircuitType::Memory { width })
      .expect("memory circuit present");
    let trace = &traces[idx].0;
    let real = trace
      .values
      .chunks(trace.width.max(1))
      .filter(|row| row.get(1) == Some(&FF::ONE))
      .count();
    FF::from_usize(real)
  });
  RowMajorMatrix::new(counts.collect(), 1)
}

/// A Hypercube machine for one Aiur toplevel and one entry function.
///
/// The entry function fixes the claim layout
/// `[function_channel, fun_idx, inputs.., outputs..]` — the message its
/// return lookup provides — which the claim chip pins to the public values.
pub struct ToplevelMachine {
  machine: AiurMachine,
  slot_widths: Vec<Vec<usize>>,
  fun_idx: FunIdx,
}

fn circuit_name(circuit_type: CircuitType) -> String {
  match circuit_type {
    CircuitType::Function { idx } => format!("AiurFunction{idx}"),
    CircuitType::Memory { width } => format!("AiurMemory{width}"),
    CircuitType::Bytes1 => "AiurBytes1".to_string(),
    CircuitType::Bytes2 => "AiurBytes2".to_string(),
  }
}

impl ToplevelMachine {
  /// Synthesizes every circuit of `toplevel` and assembles the machine for
  /// proving calls to `fun_idx`.
  pub fn build<FF: AiurField + PrimeField64>(
    toplevel: &Toplevel<FF>,
    fun_idx: FunIdx,
  ) -> Result<Self, BuildError> {
    let (inputs, slot_widths) = build_circuit_inputs(toplevel);
    let types = circuit_types(toplevel);
    let entry = types
      .iter()
      .position(|t| *t == CircuitType::Function { idx: fun_idx })
      .ok_or(BuildError::NoCircuit { fun_idx })?;
    // The return lookup occupies the entry circuit's first slot; its
    // message is exactly the claim.
    let claim_len = inputs[entry].lookups[0].args.len();
    let affinity_slots: Vec<usize> = types
      .iter()
      .enumerate()
      .filter(|(_, t)| matches!(t, CircuitType::Memory { .. }))
      .map(|(i, _)| i)
      .collect();
    let specs: Vec<CircuitSpec<FF>> = inputs
      .into_iter()
      .zip(types)
      .map(|(ci, t)| match t {
        CircuitType::Memory { width } => memory_spec(width),
        _ => CircuitSpec {
          name: circuit_name(t),
          main_width: ci.main_width,
          preprocessed: ci.preprocessed,
          constraints: ci.constraints,
          lookups: ci.lookups,
        },
      })
      .collect();
    let machine = AiurMachine::build_with_affinity(
      specs,
      &toplevel.memory_sizes,
      claim_len,
      affinity_slots,
    )?;
    Ok(Self { machine, slot_widths, fun_idx })
  }

  pub fn machine(&self) -> &AiurMachine {
    &self.machine
  }

  pub fn fun_idx(&self) -> FunIdx {
    self.fun_idx
  }

  /// The claim for a call of the entry function: the message its return
  /// lookup provides, `[function_channel, fun_idx, input.., output..]`.
  pub fn claim<FF: AiurField>(&self, input: &[FF], output: &[FF]) -> Vec<FF> {
    let mut claim = Vec::with_capacity(2 + input.len() + output.len());
    claim.push(function_channel());
    claim.push(FF::from_usize(self.fun_idx));
    claim.extend_from_slice(input);
    claim.extend_from_slice(output);
    claim
  }

  /// Builds the Hypercube record for an execution: Aiur's per-circuit
  /// witness traces (the lookup witness multi-stark's stage 2 would consume
  /// is discarded — Hypercube derives its LogUp-GKR witness from the traces
  /// themselves), the memory boundary trace, and the claim.
  pub fn record<FF: AiurField + PrimeField64>(
    &self,
    toplevel: &Toplevel<FF>,
    query_record: &QueryRecord<FF>,
    io_buffer: &IOBuffer<FF>,
    claim: &[FF],
  ) -> Result<AiurRecord, BuildError> {
    let witness =
      build_witness(toplevel, query_record, io_buffer, &self.slot_widths);
    let boundary = boundary_trace(toplevel, &witness);
    let traces = witness
      .into_iter()
      .map(|(trace, _lookups)| Some(trace))
      .chain([Some(boundary)])
      .collect();
    self.machine.record(traces, claim)
  }

  /// Executes the entry function on `input` and proves the execution —
  /// split into shards under `sharding` — returning the claim, the
  /// verifying key and the proof.
  pub fn execute_and_prove<FF: AiurField + PrimeField64>(
    &self,
    toplevel: &Toplevel<FF>,
    input: &[FF],
    io_buffer: &mut IOBuffer<FF>,
    params: ProverParams,
    sharding: ShardingParams,
  ) -> Result<(Vec<FF>, AiurVerifyingKey, AiurProof), ExecuteProveError> {
    let (query_record, output) = toplevel
      .execute(self.fun_idx, input.to_vec(), io_buffer)
      .map_err(ExecuteProveError::Exec)?;
    let claim = self.claim(input, &output);
    let witness =
      build_witness(toplevel, &query_record, io_buffer, &self.slot_widths);
    drop(query_record);
    let boundary = boundary_trace(toplevel, &witness);
    let traces = witness
      .into_iter()
      .map(|(trace, _lookups)| Some(trace))
      .chain([Some(boundary)])
      .collect();
    let claim_backend: Vec<crate::F> =
      claim.iter().map(|x| crate::expr::convert_element(*x)).collect();
    let extended =
      self.machine.extended_traces(traces).map_err(ExecuteProveError::Build)?;
    let records =
      partition_records(&self.machine, &extended, &claim_backend, &sharding)
        .map_err(ExecuteProveError::Build)?;
    let (vk, proof) = prove(&self.machine, records, params);
    Ok((claim, vk, proof))
  }
}

/// Errors from [`ToplevelMachine::execute_and_prove`].
#[derive(Debug)]
pub enum ExecuteProveError {
  Exec(ExecError),
  Build(BuildError),
}

impl std::fmt::Display for ExecuteProveError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Exec(e) => write!(f, "Aiur execution failed: {e:?}"),
      Self::Build(e) => write!(f, "record construction failed: {e}"),
    }
  }
}

impl std::error::Error for ExecuteProveError {}
