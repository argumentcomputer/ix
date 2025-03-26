use anyhow::Result;
use binius_circuits::builder::types::U;
use binius_core::{
    constraint_system::{
        Proof as ProofCore, channel::Boundary, prove as prove_core,
        validate::validate_witness as validate_witness_core, verify as verify_core,
    },
    fiat_shamir::HasherChallenger,
    tower::CanonicalTowerFamily,
};
use binius_field::BinaryField8b as B8;
use binius_hal::ComputationBackend;
use binius_hash::compress::Groestl256ByteCompression;
use binius_math::EvaluationDomainFactory;
use groestl_crypto::Groestl256;

use super::{
    F,
    circuit::{CircuitModule, compile_circuit_modules},
    witness::Witness,
};

pub struct Proof {
    proof_core: ProofCore,
    modules_n_vars: Vec<u8>,
}

pub fn validate_witness(
    circuit_modules: &[CircuitModule],
    witness: &Witness<'_>,
    boundaries: &[Boundary<F>],
) -> Result<()> {
    let Witness {
        mlei,
        modules_n_vars,
    } = witness;
    let constraint_system = compile_circuit_modules(circuit_modules, modules_n_vars)?;
    validate_witness_core(&constraint_system, boundaries, mlei)?;
    Ok(())
}

pub fn prove<DomainFactory, Backend>(
    circuit_modules: &[CircuitModule],
    witness: Witness<'_>,
    boundaries: &[Boundary<F>],
    log_inv_rate: usize,
    security_bits: usize,
    domain_factory: &DomainFactory,
    backend: &Backend,
) -> Result<Proof>
where
    Backend: ComputationBackend,
    DomainFactory: EvaluationDomainFactory<B8>,
{
    let Witness {
        mlei,
        modules_n_vars,
    } = witness;
    let constraint_system = compile_circuit_modules(circuit_modules, &modules_n_vars)?;
    let proof_core = prove_core::<
        U,
        CanonicalTowerFamily,
        _,
        Groestl256,
        Groestl256ByteCompression,
        HasherChallenger<Groestl256>,
        _,
    >(
        &constraint_system,
        log_inv_rate,
        security_bits,
        boundaries,
        mlei,
        domain_factory,
        backend,
    )?;
    Ok(Proof {
        proof_core,
        modules_n_vars,
    })
}

pub fn verify(
    circuit_modules: &[CircuitModule],
    boundaries: &[Boundary<F>],
    proof: Proof,
    log_inv_rate: usize,
    security_bits: usize,
) -> Result<()> {
    let Proof {
        proof_core,
        modules_n_vars,
    } = proof;
    let constraint_system = compile_circuit_modules(circuit_modules, &modules_n_vars)?;
    verify_core::<
        U,
        CanonicalTowerFamily,
        Groestl256,
        Groestl256ByteCompression,
        HasherChallenger<Groestl256>,
    >(
        &constraint_system,
        log_inv_rate,
        security_bits,
        boundaries,
        proof_core,
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use binius_core::oracle::OracleId;
    use binius_field::BinaryField1b as B1;

    use crate::archon::{
        ModuleId,
        arith_expr::ArithExpr,
        circuit::{CircuitModule, init_witness_modules},
        protocol::validate_witness,
        witness::{WitnessModule, compile_witness_modules},
    };

    struct Oracles {
        a: OracleId,
        b: OracleId,
    }

    fn a_xor_b_circuit_module(module_id: ModuleId) -> Result<(CircuitModule, Oracles)> {
        let mut circuit_module = CircuitModule::new(module_id);
        let a = circuit_module.add_committed::<B1>("a")?;
        let b = circuit_module.add_committed::<B1>("b")?;
        circuit_module.assert_zero("a xor b", [], ArithExpr::Oracle(a) + ArithExpr::Oracle(b));
        circuit_module.freeze_oracles();
        Ok((circuit_module, Oracles { a, b }))
    }

    fn populate_a_xor_b_witness_with_zeros(witness_module: &mut WitnessModule, oracles: &Oracles) {
        let zeros = witness_module.new_entry_with_capacity(7);
        witness_module.push_u128_to(0, zeros);
        witness_module.bind_oracle_to::<B1>(oracles.a, zeros);
        witness_module.bind_oracle_to::<B1>(oracles.b, zeros);
    }

    #[test]
    fn test_invalid_witness() {
        let (circuit_module, oracles) = a_xor_b_circuit_module(0).unwrap();
        let mut witness_module = circuit_module.init_witness_module().unwrap();
        let a = witness_module.new_entry_with_capacity(7);
        let b = witness_module.new_entry_with_capacity(7);
        witness_module.push_u128_to(0, a);
        witness_module.push_u128_to(1, b);
        witness_module.bind_oracle_to::<B1>(oracles.a, a);
        witness_module.bind_oracle_to::<B1>(oracles.b, b);
        let witness_modules = [witness_module];
        let witness = compile_witness_modules(&witness_modules).unwrap();
        assert!(validate_witness(&[circuit_module], &witness, &[]).is_err());
    }

    #[test]
    fn test_single_module() {
        let (circuit_module, oracles) = a_xor_b_circuit_module(0).unwrap();
        let mut witness_module = circuit_module.init_witness_module().unwrap();
        populate_a_xor_b_witness_with_zeros(&mut witness_module, &oracles);
        let witness_modules = [witness_module];
        let witness = compile_witness_modules(&witness_modules).unwrap();
        assert!(validate_witness(&[circuit_module], &witness, &[]).is_ok());
    }

    #[test]
    fn test_multiple_modules() {
        let (circuit_module0, oracles0) = a_xor_b_circuit_module(0).unwrap();
        let (circuit_module1, oracles1) = a_xor_b_circuit_module(1).unwrap();
        let circuit_modules = [circuit_module0, circuit_module1];
        let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
        populate_a_xor_b_witness_with_zeros(&mut witness_modules[0], &oracles0);
        populate_a_xor_b_witness_with_zeros(&mut witness_modules[1], &oracles1);
        let witness = compile_witness_modules(&witness_modules).unwrap();
        assert!(validate_witness(&circuit_modules, &witness, &[]).is_ok());
    }

    #[test]
    fn test_deactivated_module() {
        let (circuit_module0, oracles0) = a_xor_b_circuit_module(0).unwrap();
        let (circuit_module1, _) = a_xor_b_circuit_module(1).unwrap();
        let circuit_modules = [circuit_module0, circuit_module1];
        let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
        populate_a_xor_b_witness_with_zeros(&mut witness_modules[0], &oracles0);
        // Witness module 1 isn't populated
        let witness = compile_witness_modules(&witness_modules).unwrap();
        assert!(validate_witness(&circuit_modules, &witness, &[]).is_ok());
    }
}
