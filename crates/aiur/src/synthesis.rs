use multi_stark::{
  expr::Expr,
  lookup::Lookup,
  p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
  prover::Proof,
  system::{CircuitInputs, ProverKey, System, SystemWitness},
  types::{
    CommitmentParameters, FriParameters, GoldilocksBlake3Config, PcsError,
  },
  verifier::VerificationError,
};
use rayon::iter::{
  IndexedParallelIterator, IntoParallelIterator, ParallelIterator,
};

use crate::{
  G,
  bytecode::{FunIdx, Toplevel},
  execute::{ExecError, IOBuffer, QueryRecord},
  function_channel,
  gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
};

/// The concrete STARK configuration Aiur instantiates multi-stark with.
pub type AiurConfig = GoldilocksBlake3Config;
/// A proof under [`AiurConfig`].
pub type AiurProof = Proof<AiurConfig>;

pub struct AiurSystem {
  toplevel: Toplevel,
  // perhaps remove the key from the system in verifier only mode?
  key: ProverKey<AiurConfig>,
  /// The parameters the system's config was built from, kept for the
  /// verifying-key codec (the config itself doesn't expose them back).
  pub(crate) commitment_parameters: CommitmentParameters,
  pub(crate) fri_parameters: FriParameters,
  pub(crate) system: System<AiurConfig>,
  /// Per-circuit lookup-slot argument widths (in system order), retained so
  /// the witness builder can size its `LookupValues` without reading them
  /// back off the (now AIR-free) compiled circuits.
  slot_widths: Vec<Vec<usize>>,
}

enum CircuitType {
  Function { idx: usize },
  Memory { width: usize },
  Bytes1,
  Bytes2,
}

impl AiurSystem {
  pub fn build(
    toplevel: Toplevel,
    commitment_parameters: CommitmentParameters,
    fri_parameters: FriParameters,
  ) -> Self {
    let mut circuit_inputs: Vec<CircuitInputs<G>> = Vec::new();
    let mut slot_widths: Vec<Vec<usize>> = Vec::new();

    let mut push_circuit =
      |main_width: usize,
       preprocessed: Option<RowMajorMatrix<G>>,
       constraints: Vec<Expr<G>>,
       lookups: Vec<Lookup<Expr<G>>>| {
        slot_widths.push(lookups.iter().map(|l| l.args.len()).collect());
        circuit_inputs.push(CircuitInputs {
          main_width,
          preprocessed,
          constraints,
          ext_constraints: vec![],
          lookups,
        });
      };

    // Constrained functions (ascending index).
    for i in 0..toplevel.functions.len() {
      if !toplevel.functions[i].constrained {
        continue;
      }
      let (constraints, lookups) = toplevel.build_constraints(i);
      push_circuit(constraints.width, None, constraints.zeros, lookups);
    }
    // Memories.
    for &size in &toplevel.memory_sizes {
      let (memory, constraints, lookups) = Memory::build(size);
      push_circuit(memory.width, None, constraints, lookups);
    }
    // Gadgets.
    push_circuit(
      Bytes1.main_width(),
      Bytes1.preprocessed(),
      vec![],
      Bytes1.lookups(),
    );
    push_circuit(
      Bytes2.main_width(),
      Bytes2.preprocessed(),
      vec![],
      Bytes2.lookups(),
    );

    let config = AiurConfig::new(commitment_parameters, fri_parameters);
    let (system, key) = System::new(config, circuit_inputs);
    AiurSystem {
      system,
      key,
      toplevel,
      commitment_parameters,
      fri_parameters,
      slot_widths,
    }
  }

  /// The circuit list in system order: constrained functions (ascending
  /// index), then memories, then `Bytes1`, then `Bytes2`. This matches the
  /// order the circuits were chained in [`AiurSystem::build`], so index `i`
  /// of the returned `Vec` corresponds to `self.system.circuits[i]`.
  fn circuit_types(&self) -> Vec<CircuitType> {
    let functions = (0..self.toplevel.functions.len()).filter_map(|idx| {
      self.toplevel.functions[idx]
        .constrained
        .then_some(CircuitType::Function { idx })
    });
    let memories = self
      .toplevel
      .memory_sizes
      .iter()
      .map(|&width| CircuitType::Memory { width });
    let gadgets = [CircuitType::Bytes1, CircuitType::Bytes2];
    functions.chain(memories).chain(gadgets).collect()
  }

  /// The argument width of each lookup slot of circuit `circuit_idx`, taken
  /// from the lookups built at construction so the witness layout always
  /// matches the compiled circuit.
  fn slot_arg_widths(&self, circuit_idx: usize) -> Vec<usize> {
    self.slot_widths[circuit_idx].clone()
  }

  #[tracing::instrument(level = "info", skip_all, name = "aiur/prove")]
  pub fn prove(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &mut IOBuffer,
  ) -> (Vec<G>, AiurProof) {
    tracing_texray::examine_current();

    // Execute the Aiur bytecode.
    let _g = tracing::info_span!("aiur/execute").entered();
    // Execute the Aiur bytecode. The prover assumes inputs are valid; any
    // execution error here is a programmer bug, so we unwrap.
    let (query_record, output) = self
      .toplevel
      .execute(fun_idx, input.to_vec(), io_buffer)
      .expect("Aiur execution failed during prove");
    drop(_g);

    // Build the `SystemWitness`
    let _g = tracing::info_span!("aiur/witness").entered();
    let circuit_types = self.circuit_types();
    let witness_data = circuit_types
      .into_par_iter()
      .enumerate()
      .map(|(circuit_idx, circuit_type)| {
        let slot_arg_widths = self.slot_arg_widths(circuit_idx);
        match circuit_type {
          CircuitType::Function { idx } => self.toplevel.witness_data(
            idx,
            &query_record,
            io_buffer,
            &slot_arg_widths,
          ),
          CircuitType::Memory { width } => {
            Memory::witness_data(width, &query_record, &slot_arg_widths)
          },
          CircuitType::Bytes1 => {
            Bytes1.witness_data(&query_record, &slot_arg_widths)
          },
          CircuitType::Bytes2 => {
            Bytes2.witness_data(&query_record, &slot_arg_widths)
          },
        }
      })
      .collect::<Vec<_>>();
    drop(query_record); // Early drop to free memory.
    let (traces, lookups) = witness_data.into_iter().unzip();
    let witness = SystemWitness { traces, lookups };
    drop(_g);

    // Construct the claim.
    let mut claim = vec![function_channel(), G::from_usize(fun_idx)];
    claim.extend(input);
    claim.extend(output);

    // Finally prove.
    let proof = self.system.prove(&self.key, &claim, witness);
    (claim, proof)
  }

  /// IxVM-native prove: identical to `prove` except the execute step
  /// is provided by the caller as `executor` (a closure that runs
  /// the codegen'd Rust kernel `ix::aiur_ixvm_runner::execute_ixvm`
  /// instead of the bytecode interpreter). Avoids a circular crate
  /// dependency: `aiur` doesn't know about `ix`; `ix` (or its
  /// downstream `ffi`) injects the executor.
  ///
  /// QueryRecord shape + witness construction + claim layout + proof
  /// generation are all unchanged — the proof produced here is
  /// verification-compatible with one produced by `prove`.
  #[tracing::instrument(level = "info", skip_all, name = "aiur/prove_ixvm")]
  pub fn prove_ixvm<F>(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &mut IOBuffer,
    executor: F,
  ) -> (Vec<G>, AiurProof)
  where
    F: FnOnce(
      &Toplevel,
      FunIdx,
      Vec<G>,
      &mut IOBuffer,
    ) -> Result<(QueryRecord, Vec<G>), ExecError>,
  {
    tracing_texray::examine_current();
    let _g = tracing::info_span!("aiur/execute_ixvm").entered();
    let (query_record, output) =
      executor(&self.toplevel, fun_idx, input.to_vec(), io_buffer)
        .expect("IxVM-native Aiur execution failed during prove_ixvm");
    drop(_g);

    let _g = tracing::info_span!("aiur/witness").entered();
    let circuit_types = self.circuit_types();
    let witness_data = circuit_types
      .into_par_iter()
      .enumerate()
      .map(|(circuit_idx, circuit_type)| {
        let slot_arg_widths = self.slot_arg_widths(circuit_idx);
        match circuit_type {
          CircuitType::Function { idx } => self.toplevel.witness_data(
            idx,
            &query_record,
            io_buffer,
            &slot_arg_widths,
          ),
          CircuitType::Memory { width } => {
            Memory::witness_data(width, &query_record, &slot_arg_widths)
          },
          CircuitType::Bytes1 => {
            Bytes1.witness_data(&query_record, &slot_arg_widths)
          },
          CircuitType::Bytes2 => {
            Bytes2.witness_data(&query_record, &slot_arg_widths)
          },
        }
      })
      .collect::<Vec<_>>();
    drop(query_record);
    let (traces, lookups) = witness_data.into_iter().unzip();
    let witness = SystemWitness { traces, lookups };
    drop(_g);

    let mut claim = vec![function_channel(), G::from_usize(fun_idx)];
    claim.extend(input);
    claim.extend(output);

    let proof = self.system.prove(&self.key, &claim, witness);
    (claim, proof)
  }

  #[inline]
  pub fn verify(
    &self,
    claim: &[G],
    proof: &AiurProof,
  ) -> Result<(), VerificationError<PcsError>> {
    self.system.verify(claim, proof)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
    execute::IOBuffer,
  };
  use multi_stark::{
    p3_field::PrimeCharacteristicRing,
    types::{CommitmentParameters, FriParameters},
  };
  use rustc_hash::FxHashMap;

  /// Small FRI parameters mirroring `vk_codec`'s test config: cheap to prove
  /// while still exercising the full FRI pipeline (log_blowup 1, 64 queries,
  /// no proof-of-work).
  fn test_parameters() -> (CommitmentParameters, FriParameters) {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    (cp, fp)
  }

  fn empty_io_buffer() -> IOBuffer {
    IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() }
  }

  /// Hand-build the toplevel for a single constrained function `f(a, b) = a*b`.
  ///
  /// Body: `Mul(0, 1)` (multiplies the two inputs, which live at value indices
  /// 0 and 1, producing value index 2), then `Return(0, [2])`.
  ///
  /// Layout — matched against how `constraints.rs`/`trace.rs` walk the block:
  /// - `input_size = 2`: the two inputs `a`, `b`.
  /// - `selectors = 1`: the single `Return` (selector index 0).
  /// - `auxiliaries = 2`: the multiplicity column (allocated first for every
  ///   function) plus one auxiliary for the `Mul` — `a` and `b` each have
  ///   degree 1, so `a*b` has degree 2 and `constraints.rs` spills it into a
  ///   fresh auxiliary column pinned by `sel * (col - a*b)`.
  /// - `lookups = 1`: the function-provide (return) lookup in slot 0, which
  ///   pulls the claim `[function_channel, fun_idx, a, b, a*b]`.
  fn mul_toplevel() -> Toplevel {
    let body =
      Block { ops: vec![Op::Mul(0, 1)], ctrl: Ctrl::Return(0, vec![2]) };
    let function = Function {
      body,
      layout: FunctionLayout {
        input_size: 2,
        selectors: 1,
        auxiliaries: 2,
        lookups: 1,
      },
      entry: true,
      constrained: true,
    };
    Toplevel { functions: vec![function], memory_sizes: vec![] }
  }

  #[test]
  fn prove_verify_mul_roundtrip() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(mul_toplevel(), cp, fp);

    let a = G::from_u64(3);
    let b = G::from_u64(5);
    let input = [a, b];
    let mut io_buffer = empty_io_buffer();

    let (claim, proof) = system.prove(0, &input, &mut io_buffer);

    // Claim layout is [function_channel(), fun_idx, input.., output..].
    assert_eq!(
      claim,
      vec![function_channel(), G::from_usize(0), a, b, a * b],
      "unexpected claim layout / computed output"
    );

    system.verify(&claim, &proof).expect("valid proof must verify");

    // Negative check: tampering with the output element must make the claim
    // inconsistent with the (honest) proof, so verification must fail.
    let mut bad_claim = claim.clone();
    let last = bad_claim.len() - 1;
    bad_claim[last] += G::ONE;
    assert!(
      system.verify(&bad_claim, &proof).is_err(),
      "verification must reject a tampered claim"
    );
  }
}
