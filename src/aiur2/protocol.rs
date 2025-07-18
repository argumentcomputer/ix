use multi_stark::{
    lookup::LookupAir,
    prover::{Claim, Proof},
    system::{Circuit, CircuitWitness, System, SystemWitness},
    types::{FriParameters, PcsError, new_stark_config},
    verifier::VerificationError,
};
use p3_field::PrimeCharacteristicRing;

use crate::aiur2::{
    G,
    bytecode::{FunIdx, Toplevel},
    constraints::Constraints,
    trace::Channel,
};

pub struct AiurSystem(System<LookupAir<Constraints, G>>);

impl AiurSystem {
    pub fn build(toplevel: &Toplevel) -> Self {
        let iter = toplevel.functions.iter().enumerate().map(|(i, f)| {
            let (constraints, lookups) = toplevel.build_constraints(i);
            let air = LookupAir::new(constraints, lookups);
            (f.name.as_str(), Circuit::from_air(air).unwrap())
        });
        AiurSystem(System::new(iter))
    }

    pub fn prove(
        &self,
        fri_parameters: &FriParameters,
        toplevel: &Toplevel,
        fun_idx: FunIdx,
        input: &[G],
    ) -> (Claim, Proof) {
        let query_record = toplevel.execute(fun_idx, input.to_vec());
        let output = &query_record.function_queries[fun_idx]
            .get(input)
            .unwrap()
            .output;
        let mut witness = SystemWitness { circuits: vec![] };
        let mut lookups = vec![];
        // TODO: parallelize
        for function_index in 0..toplevel.functions.len() {
            let (trace, lookups_per_function) =
                toplevel.generate_trace(function_index, &query_record);
            witness.circuits.push(CircuitWitness { trace });
            lookups.push(lookups_per_function);
        }
        let stage_2 = witness.stage_2_from_lookups(lookups);
        let mut args = vec![Channel::Function.to_field(), G::from_usize(fun_idx)];
        args.extend(input);
        args.extend(output);
        let circuit_name = toplevel.functions[fun_idx].name.clone();
        let claim = Claim { circuit_name, args };
        let config = new_stark_config(fri_parameters);
        let proof = self.0.prove(&config, &claim, witness, stage_2);
        (claim, proof)
    }

    pub fn verify(
        &self,
        fri_parameters: &FriParameters,
        claim: &Claim,
        proof: &Proof,
    ) -> Result<(), VerificationError<PcsError>> {
        self.0
            .verify(&new_stark_config(fri_parameters), claim, proof)
    }
}
