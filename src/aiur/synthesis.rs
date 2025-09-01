use multi_stark::{
    lookup::LookupAir,
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::dense::RowMajorMatrix,
    prover::Proof,
    system::{ProverKey, System, SystemWitness},
    types::{CommitmentParameters, FriParameters, PcsError},
    verifier::VerificationError,
};
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::aiur::{
    G,
    bytecode::{FunIdx, Toplevel},
    constraints::Constraints,
    execute::IOBuffer,
    function_channel,
    gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
    memory::Memory,
};

pub struct AiurSystem {
    toplevel: Toplevel,
    // perhaps remove the key from the system in verifier only mode?
    key: ProverKey,
    system: System<AiurCircuit>,
}

enum AiurCircuit {
    Function(Constraints),
    Memory(Memory),
    Bytes1,
    Bytes2,
}

impl BaseAir<G> for AiurCircuit {
    fn width(&self) -> usize {
        match self {
            Self::Function(constraints) => constraints.width(),
            Self::Memory(memory) => memory.width(),
            Self::Bytes1 => Bytes1.width(),
            Self::Bytes2 => Bytes2.width(),
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<G>> {
        match self {
            Self::Function(constraints) => constraints.preprocessed_trace(),
            Self::Memory(memory) => memory.preprocessed_trace(),
            Self::Bytes1 => Bytes1.preprocessed_trace(),
            Self::Bytes2 => Bytes2.preprocessed_trace(),
        }
    }
}

impl<AB> Air<AB> for AiurCircuit
where
    AB: AirBuilder<F = G>,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::Function(constraints) => constraints.eval(builder),
            Self::Memory(memory) => memory.eval(builder),
            Self::Bytes1 => Bytes1.eval(builder),
            Self::Bytes2 => Bytes2.eval(builder),
        }
    }
}

enum CircuitType {
    Function { idx: usize },
    Memory { width: usize },
    Bytes1,
    Bytes2,
}

impl AiurSystem {
    pub fn build(toplevel: Toplevel, commitment_parameters: CommitmentParameters) -> Self {
        let function_circuits = (0..toplevel.functions.len()).map(|i| {
            let (constraints, lookups) = toplevel.build_constraints(i);
            LookupAir::new(AiurCircuit::Function(constraints), lookups)
        });
        let memory_circuits = toplevel.memory_sizes.iter().map(|&width| {
            let (memory, lookups) = Memory::build(width);
            LookupAir::new(AiurCircuit::Memory(memory), lookups)
        });

        // Gadgets attached
        let gadget_circuits = [
            LookupAir::new(AiurCircuit::Bytes1, Bytes1.lookups()),
            LookupAir::new(AiurCircuit::Bytes2, Bytes2.lookups()),
        ]
        .into_iter();

        let (system, key) = System::new(
            commitment_parameters,
            function_circuits
                .chain(memory_circuits)
                .chain(gadget_circuits),
        );
        AiurSystem {
            system,
            key,
            toplevel,
        }
    }

    pub fn prove(
        &self,
        fri_parameters: FriParameters,
        fun_idx: FunIdx,
        input: &[G],
        io_buffer: &mut IOBuffer,
    ) -> (Vec<G>, Proof) {
        // Execute the Aiur bytecode.
        let (query_record, output) = self.toplevel.execute(fun_idx, input.to_vec(), io_buffer);

        // Build the `SystemWitness`
        let functions = (0..self.toplevel.functions.len())
            .into_par_iter()
            .map(|idx| CircuitType::Function { idx });
        let memories = self
            .toplevel
            .memory_sizes
            .par_iter()
            .map(|&width| CircuitType::Memory { width });
        let gadgets = [CircuitType::Bytes1, CircuitType::Bytes2].into_par_iter();
        let witness_data = functions
            .chain(memories)
            .chain(gadgets)
            .map(|circuit_type| match circuit_type {
                CircuitType::Function { idx } => {
                    self.toplevel.witness_data(idx, &query_record, io_buffer)
                }
                CircuitType::Memory { width } => Memory::witness_data(width, &query_record),
                CircuitType::Bytes1 => Bytes1.witness_data(&query_record),
                CircuitType::Bytes2 => Bytes2.witness_data(&query_record),
            })
            .collect::<Vec<_>>();
        drop(query_record); // Early drop to free memory.
        let (traces, lookups) = witness_data.into_iter().unzip();
        let witness = SystemWitness { traces, lookups };

        // Construct the claim.
        let mut claim = vec![function_channel(), G::from_usize(fun_idx)];
        claim.extend(input);
        claim.extend(output);

        // Finally prove.
        let proof = self
            .system
            .prove(fri_parameters, &self.key, &claim, witness);
        (claim, proof)
    }

    #[inline]
    pub fn verify(
        &self,
        fri_parameters: FriParameters,
        claim: &[G],
        proof: &Proof,
    ) -> Result<(), VerificationError<PcsError>> {
        self.system.verify(fri_parameters, claim, proof)
    }
}
