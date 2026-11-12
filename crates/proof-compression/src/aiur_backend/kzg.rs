//! KZG proving for the final circuits exported by the Aiur compiler.
//!
//! The checked program, trace artifact and fixed tables are trusted inputs.
//! Only witness population depends on an execution record. Verification binds
//! the public call to those compiler circuits using the existing KZG protocol.
//! This host adapter is outside the Lean compiler's proof boundary.

use super::Bn254;
use crate::kzg::{KzgConfig, Scalar};
use aiur::{
    Execution, FieldWord,
    trace::{Placement, Trace, TracePlan},
};
use multi_stark::{
    config::ProofConfig,
    lookup::logup_max_degree,
    system::{CircuitInputs, ProverKey, System, SystemWitness, extension_params},
};

mod circuits;
mod witness;

pub type Proof = multi_stark::prover::Proof<KzgConfig>;

/// Conservative row cap shared by the Aiur adapters. The compiler's depth
/// gaps are below `2^24`; `2^39 * 2^24` is below the BN254 scalar modulus,
/// so a memo cycle cannot wrap its strictly decreasing depth around the field.
pub const MAX_TOTAL_ROWS: u64 = 1 << 39;

/// Lower every compiler group, singleton chip, fixed map and ROM width to
/// the KZG circuit interface. Fixed columns come from the checked program.
pub fn circuit_inputs(plan: &TracePlan<'_, Bn254>) -> Result<Vec<CircuitInputs<Scalar>>, String> {
    Ok(circuits::build(plan)?.inputs)
}

pub struct Backend<'p, 'a> {
    plan: &'p TracePlan<'a, Bn254>,
    system: System<KzgConfig>,
    key: ProverKey<KzgConfig>,
    names: Vec<String>,
    placements: Vec<Placement<FieldWord>>,
    function_circuits: usize,
    tables: Vec<circuits::FixedTable>,
    memory_widths: Vec<usize>,
}

impl<'p, 'a> Backend<'p, 'a> {
    /// The configuration must carry trusted proving powers. Production callers
    /// authenticate their Ignition prefix before constructing `KzgConfig`.
    pub fn new(plan: &'p TracePlan<'a, Bn254>, config: KzgConfig) -> Result<Self, String> {
        let lowered = circuits::build(plan)?;
        let params = extension_params::<KzgConfig>();
        for (input, name) in lowered.inputs.iter().zip(&lowered.names) {
            let graph = input
                .compile_graph(&params)
                .map_err(|error| format!("{name}: invalid compiler circuit: {error:?}"))?;
            let degree = graph
                .max_constraint_degree
                .max(logup_max_degree(&graph, input.lookup_group_size))
                as usize;
            let quotient = (degree.max(2) - 1)
                .checked_next_power_of_two()
                .ok_or("quotient degree overflow")?;
            if quotient > config.max_quotient_degree() {
                return Err(format!(
                    "{name}: quotient degree {quotient} exceeds KZG capacity {}",
                    config.max_quotient_degree()
                ));
            }
            if let Some(fixed) = &input.preprocessed {
                let log = fixed
                    .values
                    .len()
                    .checked_div(fixed.width)
                    .filter(|height| height.is_power_of_two())
                    .ok_or("invalid fixed table domain")?
                    .ilog2() as usize;
                if log > config.max_log_degree()
                    || log + quotient.ilog2() as usize > config.max_log_quotient_domain()
                {
                    return Err(format!("{name}: fixed table domain exceeds KZG capacity"));
                }
            }
        }
        let (system, key) = System::new(config, lowered.inputs);
        Ok(Self {
            plan,
            system,
            key,
            names: lowered.names,
            placements: lowered.placements,
            function_circuits: lowered.function_circuits,
            tables: lowered.tables,
            memory_widths: lowered.memory_widths,
        })
    }

    pub fn system(&self) -> &System<KzgConfig> {
        &self.system
    }

    pub fn circuit_names(&self) -> &[String] {
        &self.names
    }

    /// `[CALL, callable, inputs..., depth?, outputs...]`, with the compiler's
    /// typed layouts checked before the public lookup demand is constructed.
    pub fn claim(
        &self,
        entry: &str,
        args: &[Scalar],
        output: &[Scalar],
    ) -> Result<Vec<Scalar>, String> {
        self.plan.public_claim(entry, args, output)
    }

    pub fn generate(
        &self,
        record: &Execution<Bn254>,
        entry: &str,
        args: &[Scalar],
    ) -> Result<SystemWitness<Scalar>, String> {
        let trace = self.plan.generate(record, entry, args, true)?;
        self.witness(record, &trace, entry, args)
    }

    /// Validate the populated compiler rows and exact integer lookup balance
    /// before packing native scalar columns for the prover. The verifier never
    /// consumes this record or trusts these diagnostics.
    pub fn witness(
        &self,
        record: &Execution<Bn254>,
        trace: &Trace<Scalar>,
        entry: &str,
        args: &[Scalar],
    ) -> Result<SystemWitness<Scalar>, String> {
        self.plan.check(record, trace, entry, args)?;
        let widths: Vec<_> = self.system.circuits[..self.function_circuits]
            .iter()
            .map(|circuit| circuit.main_width)
            .collect();
        let traces = witness::Packing {
            plan: self.plan,
            placements: &self.placements,
            function_widths: &widths,
            tables: &self.tables,
            memory_widths: &self.memory_widths,
        }
        .main_traces(record, trace)?;
        let (active, degrees) = self.trace_shape(&traces)?;
        self.check_shape(&active, &degrees)?;
        Ok(SystemWitness::from_stage_1(traces, &self.system))
    }

    /// A malformed witness can produce an invalid proof. Verification against
    /// the trusted compiler artifact and independently expected call is final.
    pub fn prove(
        &self,
        entry: &str,
        args: &[Scalar],
        output: &[Scalar],
        witness: SystemWitness<Scalar>,
    ) -> Result<Proof, String> {
        let claim = self.claim(entry, args, output)?;
        let (active, degrees) = self.trace_shape(&witness.traces)?;
        self.check_shape(&active, &degrees)?;
        if witness.lookups.len() != self.system.circuits.len() {
            return Err("wrong lookup witness count".into());
        }
        Ok(self.system.prove(&self.key, &claim, witness))
    }

    pub fn verify(
        &self,
        entry: &str,
        args: &[Scalar],
        output: &[Scalar],
        proof: &Proof,
    ) -> Result<(), String> {
        let claim = self.claim(entry, args, output)?;
        self.check_shape(&proof.active, &proof.log_degrees)?;
        self.system
            .verify(&claim, proof)
            .map_err(|error| format!("Aiur KZG verification failed: {error:?}"))
    }

    fn check_shape(&self, active: &[bool], degrees: &[u8]) -> Result<(), String> {
        if active.len() != self.system.circuits.len() || !active.contains(&true) {
            return Err("invalid circuit activation".into());
        }
        let mut degrees = degrees.iter();
        let mut rows = 0u64;
        let mut budget = 1u64;
        for (circuit, &on) in self.system.circuits.iter().zip(active) {
            if !on {
                if circuit.preprocessed_height != 0 {
                    return Err("inactive fixed table".into());
                }
                continue;
            }
            let log = usize::from(*degrees.next().ok_or("missing trace height")?);
            if log > self.system.config.max_log_degree()
                || log + circuit.quotient_degree().ilog2() as usize
                    > self.system.config.max_log_quotient_domain()
            {
                return Err("trace domain exceeds KZG capacity".into());
            }
            let height = 1u64
                .checked_shl(u32::try_from(log).map_err(|_error| "trace height overflow")?)
                .ok_or("trace height overflow")?;
            if circuit.preprocessed_height != 0
                && u64::try_from(circuit.preprocessed_height).ok() != Some(height)
            {
                return Err("fixed table height mismatch".into());
            }
            rows = rows
                .checked_add(height)
                .filter(|&rows| rows <= MAX_TOTAL_ROWS)
                .ok_or("trace rows exceed the Aiur row bound (2^39)")?;
            // Every u64 integer is below the BN254 scalar characteristic. Requiring
            // this aggregate to fit u64 is a conservative no-wrap lookup bound.
            budget = height
                .checked_mul(
                    u64::try_from(circuit.num_lookups.max(1))
                        .map_err(|_error| "lookup count overflow")?,
                )
                .and_then(|count| budget.checked_add(count))
                .ok_or("lookup count overflow")?;
        }
        if degrees.next().is_some() {
            return Err("extra trace heights".into());
        }
        Ok(())
    }
}

/// Shared compiler lowering and witness packing, independent of the proof
/// protocol and its setup. Capacities belong to each consuming backend.
pub struct Compiler<'p, 'a> {
    plan: &'p TracePlan<'a, Bn254>,
    lowered: circuits::Lowered,
    function_widths: Vec<usize>,
}

impl<'p, 'a> Compiler<'p, 'a> {
    pub fn new(plan: &'p TracePlan<'a, Bn254>) -> Result<Self, String> {
        let lowered = circuits::build(plan)?;
        let function_widths = lowered.inputs[..lowered.function_circuits]
            .iter()
            .map(|input| input.main_width)
            .collect();
        Ok(Self {
            plan,
            lowered,
            function_widths,
        })
    }

    pub fn inputs(&self) -> &[CircuitInputs<Scalar>] {
        &self.lowered.inputs
    }
    pub fn names(&self) -> &[String] {
        &self.lowered.names
    }

    /// Function circuits receive their first message and send the rest.
    /// Fixed maps and ROM circuits only receive lookup demands.
    pub fn lookup_pulls(&self, circuit: usize) -> Option<impl ExactSizeIterator<Item = bool>> {
        let count = self.lowered.inputs.get(circuit)?.lookups.len();
        let table = circuit >= self.lowered.function_circuits;
        Some((0..count).map(move |lookup| table || lookup == 0))
    }

    /// Exact padded main-trace heights in `inputs()`/`names()` order. This
    /// reads query and ROM counts without populating rows or lookup witnesses;
    /// it estimates storage for the record and does not validate its arithmetic.
    pub fn row_counts(&self, record: &Execution<Bn254>) -> Result<Vec<usize>, String> {
        let mut heights = vec![0usize; self.lowered.inputs.len()];
        for (function, &chip) in self.plan.function_chips().iter().enumerate() {
            let count = record
                .queries
                .callable_rows(function)
                .ok_or("missing function query table")?;
            if record.queries.fixed_counts(function).is_some() {
                return Err("function query table has fixed-map storage".into());
            }
            let circuit = self.lowered.placements[chip].circuit;
            heights[circuit] = heights[circuit]
                .checked_add(count)
                .ok_or("function row count overflow")?;
        }
        let program = self.plan.program().program();
        for (map, definition) in program.maps.iter().enumerate() {
            let counts = record
                .queries
                .fixed_counts(program.functions.len() + map)
                .ok_or("missing fixed-map counts")?;
            if counts.len() != program.tables[definition.input].rows.len() {
                return Err("fixed-map row count mismatch".into());
            }
        }
        for (table, definition) in self.lowered.tables.iter().enumerate() {
            heights[self.lowered.function_circuits + table] = definition.height;
        }
        let memory_start = self.lowered.function_circuits + self.lowered.tables.len();
        for (width, count) in record.memory.width_counts() {
            if count == 0 {
                continue;
            }
            let bucket = self
                .lowered
                .memory_widths
                .binary_search(&width)
                .map_err(|_error| "recorded ROM width absent from compiler circuits")?;
            heights[memory_start + bucket] = count;
        }
        for height in &mut heights {
            if *height != 0 {
                *height = height
                    .checked_next_power_of_two()
                    .ok_or("trace height overflow")?;
            }
        }
        Ok(heights)
    }

    pub fn generate(
        &self,
        record: &Execution<Bn254>,
        entry: &str,
        args: &[Scalar],
    ) -> Result<Vec<p3_matrix::dense::RowMajorMatrix<Scalar>>, String> {
        let trace = self.plan.generate(record, entry, args, true)?;
        self.plan.check(record, &trace, entry, args)?;
        witness::Packing {
            plan: self.plan,
            placements: &self.lowered.placements,
            function_widths: &self.function_widths,
            tables: &self.lowered.tables,
            memory_widths: &self.lowered.memory_widths,
        }
        .main_traces(record, &trace)
    }
}
