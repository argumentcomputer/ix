use multi_stark::{
  config::PcsError,
  config::{StarkGenericConfig, Val},
  expr::Expr,
  lookup::Lookup,
  p3_matrix::dense::RowMajorMatrix,
  prover::Proof,
  system::{CircuitInputs, ProverKey, System, SystemWitness},
  traits::Field,
  types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config},
  verifier::VerificationError,
};
use rayon::iter::{
  IndexedParallelIterator, IntoParallelIterator, ParallelIterator,
};

use crate::{
  AiurField,
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

pub struct AiurSystem<SC: StarkGenericConfig = AiurConfig> {
  toplevel: Toplevel<Val<SC>>,
  // perhaps remove the key from the system in verifier only mode?
  key: ProverKey<SC>,
  /// The parameters the system's config was built from, kept for the
  /// verifying-key codec (the config itself doesn't expose them back).
  pub(crate) commitment_parameters: CommitmentParameters,
  pub(crate) fri_parameters: FriParameters,
  pub(crate) system: System<SC>,
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

/// Shape of one compiled circuit, as needed by the Lean-side FFT cost model
/// (`Ix/Aiur/Statistics.lean`). Heights of function and memory circuits are
/// execution-dependent and are NOT part of the shape; `preprocessed_height`
/// doubles as the fixed trace height of the byte-gadget circuits (256 and
/// 65536), whose witness builders always emit the full table.
pub struct CircuitShape {
  pub main_width: usize,
  pub stage2_width: usize,
  pub quotient_degree: usize,
  pub preprocessed_width: usize,
  pub preprocessed_height: usize,
}

/// The circuit list of a toplevel, in system order (constrained functions
/// ascending, memories, `Bytes1`, `Bytes2`), plus the per-circuit lookup
/// slot widths. Field-generic: the same bytecode synthesizes over any
/// [`AiurField`].
fn build_circuit_inputs<F: AiurField>(
  toplevel: &Toplevel<F>,
) -> (Vec<CircuitInputs<F>>, Vec<Vec<usize>>) {
  {
    let mut circuit_inputs: Vec<CircuitInputs<F>> = Vec::new();
    let mut slot_widths: Vec<Vec<usize>> = Vec::new();

    let mut push_circuit =
      |main_width: usize,
       preprocessed: Option<RowMajorMatrix<F>>,
       constraints: Vec<Expr<F>>,
       lookups: Vec<Lookup<Expr<F>>>,
       lookup_group_size: usize| {
        slot_widths.push(lookups.iter().map(|l| l.args.len()).collect());
        circuit_inputs.push(CircuitInputs {
          main_width,
          preprocessed,
          constraints,
          ext_constraints: vec![],
          lookups,
          lookup_group_size,
        });
      };

    // Constrained functions (ascending index).
    for i in 0..toplevel.functions.len() {
      if !toplevel.functions[i].constrained {
        continue;
      }
      let (constraints, lookups) = toplevel.build_constraints(i);
      // A branchless function's lookup arguments are sent raw (degree 1;
      // see `ConstraintState::gate`), so two lookups fit in one chained
      // accumulator step at degree 3 — within the degree the selector-gated
      // constraints already pay for. Branching functions keep k = 1: their
      // superposed arguments are degree 2, and grouping would push the
      // logUp constraints past the quotient budget.
      let group_size =
        if toplevel.functions[i].layout.selectors == 1 && lookups.len() >= 2 {
          2
        } else {
          1
        };
      push_circuit(
        constraints.width,
        None,
        constraints.zeros,
        lookups,
        group_size,
      );
    }
    // Memories.
    for &size in &toplevel.memory_sizes {
      let (memory, constraints, lookups) = Memory::build(size);
      push_circuit(memory.width, None, constraints, lookups, 1);
    }
    // Gadgets. The byte chips' lookup arguments are preprocessed columns
    // and their multiplicities main columns (all degree 1), so their
    // lookups also group 2 per chained step at degree 3 — halving the
    // stage-2 accumulators (Bytes2: 10 → 5 at height 65536).
    push_circuit(
      AiurGadget::<F>::main_width(&Bytes1),
      AiurGadget::<F>::preprocessed(&Bytes1),
      vec![],
      AiurGadget::<F>::lookups(&Bytes1),
      2,
    );
    push_circuit(
      AiurGadget::<F>::main_width(&Bytes2),
      AiurGadget::<F>::preprocessed(&Bytes2),
      vec![],
      AiurGadget::<F>::lookups(&Bytes2),
      2,
    );

    (circuit_inputs, slot_widths)
  }
}

impl AiurSystem {
  pub fn build(
    toplevel: Toplevel,
    commitment_parameters: CommitmentParameters,
    fri_parameters: FriParameters,
  ) -> Self {
    let (circuit_inputs, slot_widths) = build_circuit_inputs(&toplevel);
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
}

#[cfg(feature = "kzg")]
impl AiurSystem<multi_stark::ark_adapter::KzgConfig> {
  /// Build over the BLS12-381 scalar field with the KZG backend (the
  /// terminal stage: constant-size proofs, natively verified). Public
  /// parameters are caller-supplied — see `Srs` in multi-stark.
  ///
  /// The FRI parameter fields are vestigial in this instantiation (they
  /// feed the FRI vk codec only, which is Goldilocks-only); they are
  /// stored zeroed.
  pub fn build_kzg(
    toplevel: Toplevel<multi_stark::ark_adapter::Scalar>,
    srs: std::sync::Arc<multi_stark::ark_adapter::Srs>,
    max_quotient_degree: usize,
  ) -> Self {
    let (circuit_inputs, slot_widths) = build_circuit_inputs(&toplevel);
    let config =
      multi_stark::ark_adapter::KzgConfig::new(srs, max_quotient_degree);
    let (system, key) = System::new(config, circuit_inputs);
    AiurSystem {
      system,
      key,
      toplevel,
      commitment_parameters: CommitmentParameters {
        log_blowup: 0,
        cap_height: 0,
      },
      fri_parameters: FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 0,
        num_queries: 0,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
      slot_widths,
    }
  }
}

impl<SC: StarkGenericConfig> AiurSystem<SC>
where
  Val<SC>: AiurField,
{
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

  /// Per-circuit shape data for the FFT cost model, read straight off the
  /// compiled [`System`] circuits (same order as [`Self::circuit_types`]:
  /// constrained functions ascending, memories, `Bytes1`, `Bytes2`).
  pub fn circuit_shapes(&self) -> Vec<CircuitShape> {
    self
      .system
      .circuits
      .iter()
      .map(|circuit| CircuitShape {
        main_width: circuit.main_width,
        stage2_width: circuit.stage_2_width,
        quotient_degree: circuit.quotient_degree(),
        preprocessed_width: circuit.preprocessed_width,
        preprocessed_height: circuit.preprocessed_height,
      })
      .collect()
  }

  #[tracing::instrument(level = "info", skip_all, name = "aiur/prove")]
  pub fn prove(
    &self,
    fun_idx: FunIdx,
    input: &[Val<SC>],
    io_buffer: &mut IOBuffer<Val<SC>>,
  ) -> (Vec<Val<SC>>, Proof<SC>)
  where
    // The witness builder fans out per circuit under rayon with `&self`
    // captured; the bound lands here (not on the impl) so read-only
    // paths stay unconstrained.
    Self: Sync,
  {
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
    let mut claim = vec![function_channel(), Val::<SC>::from_usize(fun_idx)];
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
  pub fn prove_ixvm<E>(
    &self,
    fun_idx: FunIdx,
    input: &[Val<SC>],
    io_buffer: &mut IOBuffer<Val<SC>>,
    executor: E,
  ) -> (Vec<Val<SC>>, Proof<SC>)
  where
    E: FnOnce(
      &Toplevel<Val<SC>>,
      FunIdx,
      Vec<Val<SC>>,
      &mut IOBuffer<Val<SC>>,
    ) -> Result<(QueryRecord<Val<SC>>, Vec<Val<SC>>), ExecError>,
    Self: Sync,
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

    let mut claim = vec![function_channel(), Val::<SC>::from_usize(fun_idx)];
    claim.extend(input);
    claim.extend(output);

    let proof = self.system.prove(&self.key, &claim, witness);
    (claim, proof)
  }

  #[inline]
  pub fn verify(
    &self,
    claim: &[Val<SC>],
    proof: &Proof<SC>,
  ) -> Result<(), VerificationError<PcsError<SC>>> {
    self.system.verify(claim, proof)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::G;
  use crate::{
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
    execute::IOBuffer,
  };
  use multi_stark::{
    traits::Algebra,
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

  pub(super) fn empty_io_buffer<F: AiurField>() -> IOBuffer<F> {
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
  pub(super) fn mul_toplevel<F: AiurField>() -> Toplevel<F> {
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

  pub(super) fn xor_splits_toplevel<F: AiurField>() -> Toplevel<F> {
    let body = Block {
      ops: vec![Op::U8XorSplit7(0, 1), Op::U8XorSplit4(0, 1)],
      ctrl: Ctrl::Return(0, vec![2, 3, 4, 5]),
    };
    let function = Function {
      body,
      layout: FunctionLayout {
        input_size: 2,
        selectors: 1,
        auxiliaries: 5,
        lookups: 3,
      },
      entry: true,
      constrained: true,
    };
    Toplevel { functions: vec![function], memory_sizes: vec![] }
  }

  #[test]
  fn prove_verify_xor_splits() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(xor_splits_toplevel(), cp, fp);
    let input = [G::from_u8(0xd3), G::from_u8(0x69)];
    let mut io_buffer = empty_io_buffer();

    let (claim, proof) = system.prove(0, &input, &mut io_buffer);
    let (s7_hi, s7_lo) = Bytes2::xor_split7(&input[0], &input[1]);
    let (s4_hi, s4_lo) = Bytes2::xor_split4(&input[0], &input[1]);
    assert_eq!(
      claim,
      vec![
        function_channel(),
        G::ZERO,
        input[0],
        input[1],
        s7_hi,
        s7_lo,
        s4_hi,
        s4_lo,
      ]
    );
    system.verify(&claim, &proof).expect("xor split outputs must verify");
  }

  /// Hand-build a toplevel exercising the two migrated integration paths that
  /// the `Mul` test does not: the cross-circuit **function-channel** lookup (a
  /// function calling another) and the **memory circuit** (a `Store` followed
  /// by a `Load`, which adds a `Memory` circuit and proves its migrated
  /// transition + memory-channel-lookup constraints).
  ///
  /// Functions:
  /// - `f` (idx 0, entry): `f(a, b) = g(a) * b`, but routing `b` through
  ///   memory so the memory path is live:
  ///   - `Call(1, [a], 1, false)` → `g(a)` at value idx 2, allocating one
  ///     output auxiliary + one function-channel lookup slot.
  ///   - `Store([b])` → pointer at value idx 3, allocating one pointer
  ///     auxiliary + one memory-channel lookup slot (multiplicity pushed).
  ///   - `Load(1, 3)` → the loaded `b` at value idx 4, allocating one value
  ///     auxiliary + one memory-channel lookup slot.
  ///   - `Mul(2, 4)` → `g(a) * b` (both degree 1 ⇒ degree 2 ⇒ spilled into a
  ///     fresh auxiliary at value idx 5).
  ///   - `Return(0, [5])`.
  ///
  ///   Layout for `f` — matched against how `constraints.rs`/`trace.rs` walk
  ///   the block:
  ///   - `input_size = 2` (`a`, `b`).
  ///   - `selectors = 1` (the single `Return`).
  ///   - `auxiliaries = 5`: multiplicity(1) + call output(1) + store ptr(1) +
  ///     load value(1) + mul spill(1).
  ///   - `lookups = 4`: return(slot 0) + call(1) + store(1) + load(1).
  ///
  /// - `g` (idx 1): `g(x) = x + 1`:
  ///   - `Const(1)` at value idx 1, `Add(0, 1)` at value idx 2,
  ///     `Return(0, [2])`. `Const`/`Add` allocate no auxiliaries.
  ///   - Layout: `input_size = 1`, `selectors = 1`, `auxiliaries = 1`
  ///     (multiplicity only), `lookups = 1` (return only).
  ///
  /// `memory_sizes = [1]`: a memory of size-1 values, which materializes one
  /// `Memory` circuit. The single `Store` inserts the entry (memory
  /// multiplicity 1); the `Load` bumps it to 2. The function circuit pushes
  /// `+1` for the store lookup and `+1` for the load lookup; the memory circuit
  /// pulls `-2`. The whole system balances across the function↔function and
  /// function↔memory channels.
  fn call_and_memory_toplevel() -> Toplevel {
    let f_body = Block {
      ops: vec![
        Op::Call(1, vec![0], 1, false),
        Op::Store(vec![1]),
        Op::Load(1, 3),
        Op::Mul(2, 4),
      ],
      ctrl: Ctrl::Return(0, vec![5]),
    };
    let f = Function {
      body: f_body,
      layout: FunctionLayout {
        input_size: 2,
        selectors: 1,
        auxiliaries: 5,
        lookups: 4,
      },
      entry: true,
      constrained: true,
    };

    let g_body = Block {
      ops: vec![Op::Const(G::ONE), Op::Add(0, 1)],
      ctrl: Ctrl::Return(0, vec![2]),
    };
    let g = Function {
      body: g_body,
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 1,
        lookups: 1,
      },
      entry: false,
      constrained: true,
    };

    Toplevel { functions: vec![f, g], memory_sizes: vec![1] }
  }

  #[test]
  fn prove_verify_call_and_memory_roundtrip() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(call_and_memory_toplevel(), cp, fp);

    let a = G::from_u64(3);
    let b = G::from_u64(5);
    let input = [a, b];
    let mut io_buffer = empty_io_buffer();

    // f(a, b) = g(a) * b = (a + 1) * b, with b routed through a Store/Load.
    let expected = (a + G::ONE) * b;
    let (claim, proof) = system.prove(0, &input, &mut io_buffer);

    // Claim layout is [function_channel(), fun_idx, input.., output..].
    assert_eq!(
      claim,
      vec![function_channel(), G::from_usize(0), a, b, expected],
      "unexpected claim layout / computed output"
    );

    system
      .verify(&claim, &proof)
      .expect("valid proof over Call + Store/Load must verify");

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

  /// Exercise promotion of a cached unconstrained call through nested calls.
  ///
  /// `f` first computes `g(x)` as an unconstrained hint, then calls `g(x)`
  /// constrained.  Since `g` calls `h`, promoting the cached `g` query must
  /// replay its body and promote the cached `h` query as well.  Merely bumping
  /// `g`'s multiplicity leaves the `g -> h` function channel unbalanced.
  fn unconstrained_call_promotion_toplevel() -> Toplevel {
    let f = Function {
      body: Block {
        ops: vec![
          Op::Call(1, vec![0], 1, true),
          Op::Call(1, vec![0], 1, false),
        ],
        ctrl: Ctrl::Return(0, vec![2]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 3,
        lookups: 2,
      },
      entry: true,
      constrained: true,
    };

    let g = Function {
      body: Block {
        ops: vec![Op::Call(2, vec![0], 1, false)],
        ctrl: Ctrl::Return(0, vec![1]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 2,
        lookups: 2,
      },
      entry: false,
      constrained: true,
    };

    let h = Function {
      body: Block {
        ops: vec![Op::Const(G::ONE), Op::Add(0, 1)],
        ctrl: Ctrl::Return(0, vec![2]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 1,
        lookups: 1,
      },
      entry: false,
      constrained: true,
    };

    Toplevel { functions: vec![f, g, h], memory_sizes: vec![] }
  }

  #[test]
  fn prove_verify_promotes_nested_unconstrained_call() {
    let (cp, fp) = test_parameters();
    let system =
      AiurSystem::build(unconstrained_call_promotion_toplevel(), cp, fp);
    let input = [G::from_u64(3)];
    let mut io_buffer = empty_io_buffer();

    let (claim, proof) = system.prove(0, &input, &mut io_buffer);
    assert_eq!(
      claim,
      vec![function_channel(), G::ZERO, input[0], input[0] + G::ONE]
    );
    system
      .verify(&claim, &proof)
      .expect("nested constrained promotion must balance function channels");
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

  #[test]
  fn circuit_shapes_match_system() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(call_and_memory_toplevel(), cp, fp);
    let shapes = system.circuit_shapes();

    // Canonical order and count: 2 constrained functions, 1 memory, Bytes1,
    // Bytes2.
    assert_eq!(shapes.len(), 5);
    assert_eq!(shapes.len(), system.system.circuits.len());

    for (shape, circuit) in shapes.iter().zip(&system.system.circuits) {
      assert_eq!(shape.main_width, circuit.main_width);
      assert_eq!(shape.stage2_width, circuit.stage_2_width);
      assert_eq!(shape.quotient_degree, circuit.quotient_degree());
      assert_eq!(shape.preprocessed_width, circuit.preprocessed_width);
      assert_eq!(shape.preprocessed_height, circuit.preprocessed_height);
    }

    // Function circuits: main width = inputs + selectors + auxiliaries, no
    // preprocessed matrix.
    assert_eq!(shapes[0].main_width, 2 + 1 + 5);
    assert_eq!(shapes[1].main_width, 1 + 1 + 1);
    // Memory of size 1: multiplicity + selector + pointer + 1 value.
    assert_eq!(shapes[2].main_width, 3 + 1);
    for shape in &shapes[..3] {
      assert_eq!(shape.preprocessed_width, 0);
      assert_eq!(shape.preprocessed_height, 0);
    }

    // Byte gadgets: always-active fixed-height tables whose preprocessed
    // height doubles as the committed trace height.
    assert_eq!(shapes[3].preprocessed_width, 11);
    assert_eq!(shapes[3].preprocessed_height, 256);
    assert_eq!(shapes[4].preprocessed_width, 14);
    assert_eq!(shapes[4].preprocessed_height, 65536);
  }
}

#[cfg(all(test, feature = "kzg"))]
mod kzg_tests {
  use super::tests::{empty_io_buffer, mul_toplevel, xor_splits_toplevel};
  use super::*;
  use multi_stark::ark_adapter::{Scalar, Srs};
  use multi_stark::traits::{Algebra, Field};
  use std::sync::Arc;

  fn dev_srs() -> Arc<Srs> {
    // Bytes2's preprocessed table is 65536 rows, so the SRS must cover
    // at least 2^16-length columns.
    Arc::new(Srs::unsafe_dev_setup(1 << 17, b"aiur-kzg-test"))
  }

  /// Aiur over the BLS12-381 scalar field: build, prove, verify, and
  /// reject tampering — the same pipeline the Goldilocks tests run,
  /// with KZG commitments instead of FRI.
  #[test]
  fn kzg_prove_verify_mul() {
    let system = AiurSystem::build_kzg(mul_toplevel::<Scalar>(), dev_srs(), 8);
    let a = Scalar::from_u64(3);
    let b = Scalar::from_u64(5);
    let (claim, proof) = system.prove(0, &[a, b], &mut empty_io_buffer());
    assert_eq!(claim.last(), Some(&(a * b)));
    system.verify(&claim, &proof).expect("KZG Aiur proof failed to verify");

    let mut bad_claim = claim.clone();
    let last = bad_claim.len() - 1;
    bad_claim[last] += <Scalar as Algebra<Scalar>>::ONE;
    assert!(system.verify(&bad_claim, &proof).is_err());
  }

  /// Byte-gadget coverage over Fr: the xor-split ops route through the
  /// Bytes2 chip (65536-row preprocessed table committed via MSM).
  #[test]
  fn kzg_prove_verify_xor_splits() {
    let system =
      AiurSystem::build_kzg(xor_splits_toplevel::<Scalar>(), dev_srs(), 8);
    let a = Scalar::from_u64(0xd3);
    let b = Scalar::from_u64(0x69);
    let (claim, proof) = system.prove(0, &[a, b], &mut empty_io_buffer());
    system.verify(&claim, &proof).expect("KZG Aiur proof failed to verify");
  }
}
