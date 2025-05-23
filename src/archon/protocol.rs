use anyhow::Result;
use binius_circuits::builder::types::U;
use binius_core::{
    constraint_system::{
        Proof as ProofCore, channel::Boundary, prove as prove_binius,
        validate::validate_witness as validate_witness_binius, verify as verify_binius,
    },
    fiat_shamir::HasherChallenger,
};
use binius_field::tower::CanonicalTowerFamily;
use binius_hal::ComputationBackend;
use binius_hash::groestl::Groestl256ByteCompression;
use groestl_crypto::Groestl256;

use super::{
    F,
    circuit::{CircuitModule, compile_circuit_modules},
    witness::Witness,
};

pub struct Proof {
    pub(crate) modules_heights: Vec<u64>,
    pub(crate) proof_core: ProofCore,
}

impl Default for Proof {
    fn default() -> Self {
        Proof {
            modules_heights: vec![],
            proof_core: ProofCore { transcript: vec![] },
        }
    }
}

pub fn validate_witness_core(
    circuit_modules: &[&CircuitModule],
    boundaries: &[Boundary<F>],
    witness: &Witness<'_>,
) -> Result<()> {
    let Witness {
        mlei,
        modules_heights,
    } = witness;
    let constraint_system = compile_circuit_modules(circuit_modules, modules_heights)?;
    validate_witness_binius(&constraint_system, boundaries, mlei)?;
    Ok(())
}

#[inline]
pub fn validate_witness(
    circuit_modules: &[CircuitModule],
    boundaries: &[Boundary<F>],
    witness: &Witness<'_>,
) -> Result<()> {
    validate_witness_core(
        &circuit_modules.iter().collect::<Vec<_>>(),
        boundaries,
        witness,
    )
}

pub fn prove_core<Backend: ComputationBackend>(
    circuit_modules: &[&CircuitModule],
    boundaries: &[Boundary<F>],
    log_inv_rate: usize,
    security_bits: usize,
    witness: Witness<'_>,
    backend: &Backend,
) -> Result<Proof> {
    let Witness {
        mlei,
        modules_heights,
    } = witness;
    let constraint_system = compile_circuit_modules(circuit_modules, &modules_heights)?;
    let proof_core = prove_binius::<
        U,
        CanonicalTowerFamily,
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
        backend,
    )?;
    Ok(Proof {
        modules_heights,
        proof_core,
    })
}

#[inline]
pub fn prove<Backend: ComputationBackend>(
    circuit_modules: &[CircuitModule],
    boundaries: &[Boundary<F>],
    log_inv_rate: usize,
    security_bits: usize,
    witness: Witness<'_>,
    backend: &Backend,
) -> Result<Proof> {
    prove_core::<Backend>(
        &circuit_modules.iter().collect::<Vec<_>>(),
        boundaries,
        log_inv_rate,
        security_bits,
        witness,
        backend,
    )
}

pub fn verify_core(
    circuit_modules: &[&CircuitModule],
    boundaries: &[Boundary<F>],
    proof: Proof,
    log_inv_rate: usize,
    security_bits: usize,
) -> Result<()> {
    let Proof {
        modules_heights,
        proof_core,
    } = proof;
    let constraint_system = compile_circuit_modules(circuit_modules, &modules_heights)?;
    verify_binius::<
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

#[inline]
pub fn verify(
    circuit_modules: &[CircuitModule],
    boundaries: &[Boundary<F>],
    proof: Proof,
    log_inv_rate: usize,
    security_bits: usize,
) -> Result<()> {
    verify_core(
        &circuit_modules.iter().collect::<Vec<_>>(),
        boundaries,
        proof,
        log_inv_rate,
        security_bits,
    )
}

#[cfg(test)]
mod tests {
    use crate::archon::OracleIdx;
    use crate::archon::precompiles::blake3::blake3_compress;
    use crate::archon::precompiles::blake3::tests::generate_trace;
    use crate::archon::protocol::{prove, verify};
    use crate::archon::{
        ModuleId,
        arith_expr::ArithExpr,
        circuit::{CircuitModule, init_witness_modules},
        protocol::validate_witness,
        witness::{WitnessModule, compile_witness_modules},
    };
    use anyhow::Result;
    use binius_field::BinaryField1b as B1;
    use binius_hal::make_portable_backend;

    struct Oracles {
        s: OracleIdx,
        a: OracleIdx,
        b: OracleIdx,
    }

    fn a_xor_b_circuit_module(module_id: ModuleId) -> Result<(CircuitModule, Oracles)> {
        let mut circuit_module = CircuitModule::new(module_id);
        let s = circuit_module.selector();
        let a = circuit_module.add_committed::<B1>("a")?;
        let b = circuit_module.add_committed::<B1>("b")?;
        circuit_module.assert_zero("a xor b", [], ArithExpr::Oracle(a) + ArithExpr::Oracle(b));
        circuit_module.freeze_oracles();
        Ok((circuit_module, Oracles { s, a, b }))
    }

    fn populate_a_xor_b_witness_with_ones(witness_module: &mut WitnessModule, oracles: &Oracles) {
        let ones = witness_module.new_entry_with_capacity(7);
        witness_module.push_u128_to(u128::MAX, ones);
        witness_module.bind_oracle_to::<B1>(oracles.s, ones);
        witness_module.bind_oracle_to::<B1>(oracles.a, ones);
        witness_module.bind_oracle_to::<B1>(oracles.b, ones);
    }

    #[test]
    fn test_invalid_witness() {
        let (circuit_module, oracles) = a_xor_b_circuit_module(0).unwrap();
        let mut witness_module = circuit_module.init_witness_module().unwrap();
        let zeros = witness_module.new_entry_with_capacity(7);
        let ones = witness_module.new_entry_with_capacity(7);
        witness_module.push_u128_to(0, zeros);
        witness_module.push_u128_to(u128::MAX, ones);
        witness_module.bind_oracle_to::<B1>(oracles.s, ones);
        witness_module.bind_oracle_to::<B1>(oracles.a, ones);
        witness_module.bind_oracle_to::<B1>(oracles.b, zeros);
        let witness_modules = [witness_module];
        let witness = compile_witness_modules(&witness_modules, vec![128]).unwrap();
        assert!(validate_witness(&[circuit_module], &[], &witness).is_err());
    }

    #[test]
    fn test_single_module() {
        let (circuit_module, oracles) = a_xor_b_circuit_module(0).unwrap();
        let mut witness_module = circuit_module.init_witness_module().unwrap();
        populate_a_xor_b_witness_with_ones(&mut witness_module, &oracles);
        let witness_modules = [witness_module];
        let witness = compile_witness_modules(&witness_modules, vec![128]).unwrap();
        assert!(validate_witness(&[circuit_module], &[], &witness).is_ok());
    }

    #[test]
    fn test_multiple_modules() {
        let (circuit_module0, oracles0) = a_xor_b_circuit_module(0).unwrap();
        let (circuit_module1, oracles1) = a_xor_b_circuit_module(1).unwrap();
        let circuit_modules = [circuit_module0, circuit_module1];
        let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
        populate_a_xor_b_witness_with_ones(&mut witness_modules[0], &oracles0);
        populate_a_xor_b_witness_with_ones(&mut witness_modules[1], &oracles1);
        let witness = compile_witness_modules(&witness_modules, vec![128, 128]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok());
    }

    #[test]
    fn test_deactivated_module() {
        let (circuit_module0, oracles0) = a_xor_b_circuit_module(0).unwrap();
        let (circuit_module1, _) = a_xor_b_circuit_module(1).unwrap();
        let circuit_modules = [circuit_module0, circuit_module1];
        let mut witness_modules = init_witness_modules(&circuit_modules).unwrap();
        populate_a_xor_b_witness_with_ones(&mut witness_modules[0], &oracles0);
        // Witness module 1 isn't populated
        let witness = compile_witness_modules(&witness_modules, vec![128, 0]).unwrap();
        assert!(validate_witness(&circuit_modules, &[], &witness).is_ok());
    }

    #[test]
    fn test_blake3_compression_end_to_end() {
        // FIXME: length of traces must be power of 2. Investigate later if we can tackle this limitation
        let trace_len = 2usize.pow(5u32);
        let (_, traces) = generate_trace(trace_len);

        let (circuit_modules, witness_modules, heights, _) =
            blake3_compress(&traces, trace_len).unwrap();

        let witness = compile_witness_modules(&witness_modules, heights).unwrap();

        let backend = make_portable_backend();
        let proof = prove(&circuit_modules, &[], 1usize, 100usize, witness, &backend).unwrap();
        assert!(verify(&circuit_modules, &[], proof, 1usize, 100usize).is_ok());
    }
}
