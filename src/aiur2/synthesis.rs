use multi_stark::{
    lookup::LookupAir,
    prover::Proof,
    system::{Circuit, System, SystemWitness},
    types::{FriParameters, PcsError, new_stark_config},
    verifier::VerificationError,
};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

use crate::aiur2::{
    G, bytecode::FunIdx, bytecode::Toplevel, constraints::Constraints, trace::Channel,
};

pub struct AiurSystem {
    toplevel: Toplevel,
    system: System<Constraints>,
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
        let iter = (0..toplevel.functions.len()).map(|i| {
            let (constraints, lookups) = toplevel.build_constraints(i);
            let air = LookupAir::new(constraints, lookups);
            Circuit::from_air(air).unwrap()
        });
        let system = System::new(iter);
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
