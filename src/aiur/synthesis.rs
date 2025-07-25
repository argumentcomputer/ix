use multi_stark::{
    lookup::LookupAir,
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    prover::Proof,
    system::{Circuit, System, SystemWitness},
    types::{FriParameters, PcsError, new_stark_config},
    verifier::VerificationError,
};
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};

use crate::aiur::{
    G,
    bytecode::{FunIdx, Toplevel},
    constraints::Constraints,
    memory::Memory,
    trace::Channel,
};

pub struct AiurSystem {
    toplevel: Toplevel,
    system: System<AiurCircuit>,
}

enum AiurCircuit {
    Function(Constraints),
    Memory(Memory),
}

impl BaseAir<G> for AiurCircuit {
    fn width(&self) -> usize {
        // Even though the inner types might have `width` attributes, we dispatch
        // to their trait implementations for correctness.
        match self {
            Self::Function(constraints) => constraints.width(),
            Self::Memory(memory) => memory.width(),
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
        }
    }
}

impl BaseAir<G> for Constraints {
    fn width(&self) -> usize {
        self.width
    }
}

impl<AB> Air<AB> for Constraints
where
    AB: AirBuilder<F = G>,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let row = main.row_slice(0).unwrap();
        for zero in self.zeros.iter() {
            builder.assert_zero(zero.interpret(&row));
        }
        for sel in self.selectors.clone() {
            builder.assert_bool(row[sel].clone());
        }
    }
}

enum CircuitType {
    Function { idx: usize },
    Memory { width: usize },
}

impl AiurSystem {
    pub fn build(toplevel: Toplevel) -> Self {
        let function_circuits = (0..toplevel.functions.len()).map(|i| {
            let (constraints, lookups) = toplevel.build_constraints(i);
            let air = LookupAir::new(AiurCircuit::Function(constraints), lookups);
            Circuit::from_air(air).unwrap()
        });
        let memory_circuits = toplevel.memory_sizes.iter().map(|&width| {
            let (memory, lookup) = Memory::build(width);
            let air = LookupAir::new(AiurCircuit::Memory(memory), vec![lookup]);
            Circuit::from_air(air).unwrap()
        });
        let system = System::new(function_circuits.chain(memory_circuits));
        AiurSystem { system, toplevel }
    }

    pub fn prove(
        &self,
        fri_parameters: &FriParameters,
        fun_idx: FunIdx,
        input: &[G],
    ) -> (Vec<G>, Proof) {
        let (query_record, output) = self.toplevel.execute(fun_idx, input.to_vec());
        let mut witness = SystemWitness {
            traces: vec![],
            lookups: vec![],
        };
        let functions = (0..self.toplevel.functions.len())
            .into_par_iter()
            .map(|idx| CircuitType::Function { idx });
        let memories = self
            .toplevel
            .memory_sizes
            .par_iter()
            .map(|&width| CircuitType::Memory { width });
        let witness_data = functions
            .chain(memories)
            .map(|circuit_type| match circuit_type {
                CircuitType::Function { idx } => self.toplevel.generate_trace(idx, &query_record),
                CircuitType::Memory { width } => Memory::generate_trace(width, &query_record),
            })
            .collect::<Vec<_>>();
        for (trace, lookups) in witness_data {
            witness.traces.push(trace);
            witness.lookups.push(lookups);
        }
        let mut claim = vec![Channel::Function.to_field(), G::from_usize(fun_idx)];
        claim.extend(input);
        claim.extend(output);
        let config = new_stark_config(fri_parameters);
        let proof = self.system.prove(&config, &claim, witness);
        (claim, proof)
    }

    #[inline]
    pub fn verify(
        &self,
        fri_parameters: &FriParameters,
        claim: &[G],
        proof: &Proof,
    ) -> Result<(), VerificationError<PcsError>> {
        let config = new_stark_config(fri_parameters);
        self.system.verify(&config, claim, proof)
    }
}
