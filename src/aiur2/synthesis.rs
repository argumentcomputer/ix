use multi_stark::{
    builder::symbolic::SymbolicExpression,
    lookup::{AirWithLookup, Lookup, LookupAir},
    prover::{Claim, Proof},
    system::{Circuit, CircuitWitness, System, SystemWitness},
    types::{PcsError, StarkConfig},
    verifier::VerificationError,
};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

use crate::aiur2::trace::Channel;

use super::{G, bytecode::Toplevel, constraints::Constraints};

pub struct AiurSystem {
    toplevel: Toplevel,
    system: System<LookupAir<Constraints>>,
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
    }
}

impl AirWithLookup<G> for Constraints {
    fn lookups(&self) -> Vec<Lookup<SymbolicExpression<G>>> {
        self.lookups.clone()
    }
}

impl Toplevel {
    pub fn build_system(self) -> AiurSystem {
        let iter = self.functions.iter().enumerate().map(|(i, f)| {
            let constraints = self.build_constraints(i);
            let stage_2_width = constraints.lookups.len() + 1;
            let air = LookupAir::new(constraints);
            (
                f.name.as_str(),
                Circuit::from_air(air, stage_2_width).unwrap(),
            )
        });
        let system = System::new(iter);
        AiurSystem {
            system,
            toplevel: self,
        }
    }
}

impl AiurSystem {
    pub fn prove(&self, config: &StarkConfig, name: &str, input: &[G]) -> (Claim, Proof) {
        let function_index = *self.system.circuit_names.get(name).unwrap();
        let query_record = self.toplevel.execute(function_index, input.to_vec());
        let mut witness = SystemWitness { circuits: vec![] };
        let mut lookups = vec![];
        for function_index in 0..self.toplevel.functions.len() {
            let (trace, lookups_per_function) =
                self.toplevel.generate_trace(function_index, &query_record);
            witness.circuits.push(CircuitWitness { trace });
            lookups.push(lookups_per_function);
        }
        let stage_2 = witness.stage_2_from_lookups(lookups);
        let mut args = vec![Channel::Function.to_field(), G::from_usize(function_index)];
        args.extend(input);
        args.extend(
            &query_record.function_queries[function_index]
                .get(input)
                .unwrap()
                .output,
        );
        let claim = Claim {
            circuit_name: name.to_string(),
            args,
        };
        let proof = self.system.prove(config, &claim, witness, stage_2);
        (claim, proof)
    }

    pub fn verify(
        &self,
        config: &StarkConfig,
        claim: &Claim,
        proof: &Proof,
    ) -> Result<(), VerificationError<PcsError>> {
        self.system.verify(config, claim, proof)
    }
}
