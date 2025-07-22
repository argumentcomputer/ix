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

use crate::aiur2::{
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
        // TODO: parallelize
        for function_index in 0..self.toplevel.functions.len() {
            let (trace, lookups_per_function) =
                self.toplevel.generate_trace(function_index, &query_record);
            witness.traces.push(trace);
            witness.lookups.push(lookups_per_function);
        }
        // TODO: parallelize
        for width in &self.toplevel.memory_sizes {
            let (trace, lookups) = Memory::generate_trace(*width, &query_record);
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
