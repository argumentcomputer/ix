//! End to end: an Aiur toplevel proven on Hypercube, then normalize →
//! compose → shrink → wrap through SP1's recursion machines, each stage
//! verified natively, with the pipeline's vk allowlist enforced. The gnark
//! PLONK stage runs only with `IX_RECURSION_PLONK=1` (it needs Docker or a
//! native gnark build).

use std::borrow::Borrow;

use aiur::{
  bytecode::{Block, Circuit, Ctrl, Function, FunctionLayout, Op, Toplevel},
  execute::IOBuffer,
};
use aiur_hypercube::{
  AiurProof, AiurVerifyingKey, ProverParams, ShardingParams, ToplevelMachine,
  verify,
};
use aiur_recursion::{AiurRecursionProver, PinnedShapes, claim_digest_bytes};
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_koala_bear::KoalaBear as FF;
use slop_algebra::{AbstractField, PrimeField32};
use sp1_hypercube::HashableKey;
use sp1_primitives::{SP1Field, SP1GlobalContext, SP1OuterGlobalContext};
use sp1_recursion_executor::RecursionPublicValues;

/// `f(a, b) = (a + 1) * b`: one branchless function.
fn mul_toplevel() -> Toplevel<FF> {
  let body = Block {
    ops: vec![Op::Const(FF::ONE), Op::Add(0, 2), Op::Mul(3, 1)],
    ctrl: Ctrl::Return(0, vec![4]),
  };
  let function = Function {
    body,
    layout: FunctionLayout {
      input_size: 2,
      selectors: 1,
      auxiliaries: 3,
      lookups: 1,
    },
    entry: true,
    constrained: true,
  };
  let circuits = vec![Circuit { members: vec![0], layout: function.layout }];
  Toplevel { functions: vec![function], memory_sizes: vec![], circuits }
}

/// `g(a, b) = a * b + a * a`: a different function of the same arity,
/// whose machine differs from `mul_toplevel`'s in its constraints.
fn other_toplevel() -> Toplevel<FF> {
  let body = Block {
    ops: vec![Op::Mul(0, 1), Op::Mul(0, 0), Op::Add(2, 3)],
    ctrl: Ctrl::Return(0, vec![4]),
  };
  let function = Function {
    body,
    layout: FunctionLayout {
      input_size: 2,
      selectors: 1,
      auxiliaries: 3,
      lookups: 1,
    },
    entry: true,
    constrained: true,
  };
  let circuits = vec![Circuit { members: vec![0], layout: function.layout }];
  Toplevel { functions: vec![function], memory_sizes: vec![], circuits }
}

fn params() -> ProverParams {
  ProverParams { log_blowup: 1, log_stacking_height: 18, max_log_row_count: 17 }
}

const ARITY: usize = 2;

/// Prove a call of `toplevel`'s entry function on Hypercube.
fn hypercube_proof(
  toplevel: &Toplevel<FF>,
) -> (ToplevelMachine, Vec<FF>, AiurVerifyingKey, AiurProof) {
  let machine = ToplevelMachine::build(toplevel, 0).unwrap();
  let (a, b) = (FF::from_u32(3), FF::from_u32(5));
  let mut io = IOBuffer { data: Default::default(), map: Default::default() };
  let (claim, vk, proof) = machine
    .execute_and_prove(
      toplevel,
      &[a, b],
      &mut io,
      params(),
      ShardingParams::default(),
    )
    .unwrap();
  verify(machine.machine(), params(), &vk, &proof).unwrap();
  assert_eq!(proof.shard_proofs.len(), 1);
  (machine, claim, vk, proof)
}

/// The tail over one proof: compress, checked against the allowlist and
/// the compress verifier; shrink; wrap, checked against the wrap verifier.
fn tail(
  prover: &AiurRecursionProver,
  claim: &[FF],
  vk: &AiurVerifyingKey,
  proof: &AiurProof,
) -> aiur_recursion::WrapProof {
  // Compress: one shard, so one leaf folded by the arity-1 compose program
  // into a complete compress-level proof.
  let compressed = prover.compress(vk, proof).unwrap();
  assert!(prover.vks().contains(&compressed.vk));
  let mut challenger =
    <SP1GlobalContext as slop_challenger::IopCtx>::default_challenger();
  compressed.vk.observe_into(&mut challenger);
  prover
    .compress_verifier()
    .shard_verifier()
    .verify_shard(&compressed.vk, &compressed.proof, &mut challenger)
    .expect("compress-level proof verifies");
  let pv: &RecursionPublicValues<SP1Field> =
    compressed.proof.public_values.as_slice().borrow();
  assert_eq!(pv.is_complete, SP1Field::one());
  assert_eq!(pv.contains_first_shard, SP1Field::one());
  assert_eq!(pv.sp1_vk_digest, vk.hash_koalabear());
  assert_eq!(pv.vk_root, prover.vk_root());
  // The claim digest, byte for byte.
  let claim_felts: Vec<SP1Field> = claim
    .iter()
    .map(|x| SP1Field::from_canonical_u64(x.as_canonical_u64()))
    .collect();
  let expected = claim_digest_bytes(&claim_felts);
  let got: Vec<u8> = pv
    .committed_value_digest
    .iter()
    .flat_map(|word| {
      word.iter().map(|limb| u8::try_from(limb.as_canonical_u32()).unwrap())
    })
    .collect();
  assert_eq!(got, expected.to_vec());

  // Shrink, then wrap.
  let shrunk = prover.shrink(compressed).unwrap();
  assert!(prover.vks().contains(&shrunk.vk));
  let wrapped = prover.wrap(shrunk).unwrap();
  let mut challenger =
    <SP1OuterGlobalContext as slop_challenger::IopCtx>::default_challenger();
  wrapped.vk.observe_into(&mut challenger);
  prover
    .wrap_verifier()
    .shard_verifier()
    .verify_shard(&wrapped.vk, &wrapped.proof, &mut challenger)
    .expect("wrap proof verifies");
  wrapped
}

/// The shapes the tests pin to: computed for `other_toplevel`'s machine
/// (the built-in shapes are sized for production machines, which would
/// make these proofs needlessly large).
fn test_shapes() -> PinnedShapes {
  let toplevel = other_toplevel();
  let machine = ToplevelMachine::build(&toplevel, 0).unwrap();
  AiurRecursionProver::compute_shapes(machine.machine(), params(), ARITY)
    .unwrap()
}

#[test]
fn compress_shrink_wrap_a_toplevel_call() {
  let toplevel = mul_toplevel();
  let (machine, claim, vk, proof) = hypercube_proof(&toplevel);
  let prover = AiurRecursionProver::with_shapes(
    machine.machine(),
    params(),
    ARITY,
    test_shapes(),
  )
  .unwrap();
  let wrapped = tail(&prover, &claim, &vk, &proof);

  if let Some(path) = std::env::var_os("IX_RECURSION_WRAP_OUT") {
    std::fs::write(path, bincode::serialize(&wrapped).unwrap()).unwrap();
  }
  if std::env::var_os("IX_RECURSION_PLONK").is_some() {
    plonk_stage(wrapped);
  }
}

/// Two different toplevels, pinned to the same shapes, wrap to the same
/// verifying key: the circuit above the leaves does not depend on the
/// machine. Their leaf keys — and so their allowlist roots — differ.
#[test]
fn different_toplevels_share_the_wrap_vk() {
  let shapes = test_shapes();
  let mut wraps = Vec::new();
  let mut roots = Vec::new();
  for toplevel in [mul_toplevel(), other_toplevel()] {
    let (machine, claim, vk, proof) = hypercube_proof(&toplevel);
    let prover = AiurRecursionProver::with_shapes(
      machine.machine(),
      params(),
      ARITY,
      shapes.clone(),
    )
    .unwrap();
    roots.push(prover.vk_root());
    wraps.push(
      bincode::serialize(&tail(&prover, &claim, &vk, &proof).vk).unwrap(),
    );
  }
  assert_ne!(roots[0], roots[1], "different machines, different leaf keys");
  assert_eq!(wraps[0], wraps[1], "one wrap vk for every machine");
}

fn plonk_stage(wrapped: aiur_recursion::WrapProof) {
  let dir = aiur_recursion::plonk::ensure_artifacts(&wrapped).unwrap();
  let (plonk, inputs) = aiur_recursion::plonk::prove(wrapped, &dir).unwrap();
  println!("plonk proof {} bytes, inputs {inputs:?}", plonk.raw_proof.len());
}

/// The PLONK stage alone, over a wrap proof saved by the roundtrip with
/// `IX_RECURSION_WRAP_OUT` (`IX_RECURSION_WRAP_IN` names the file).
#[test]
#[ignore]
fn plonk_from_saved_wrap() {
  let path =
    std::env::var_os("IX_RECURSION_WRAP_IN").expect("IX_RECURSION_WRAP_IN");
  let bytes = std::fs::read(path).unwrap();
  let wrapped: aiur_recursion::WrapProof =
    bincode::deserialize(&bytes).unwrap();
  plonk_stage(wrapped);
}

/// gnark's `test` mode over a saved wrap proof: compiles the outer circuit
/// and checks the witness satisfies it, without proving. Splits "the wrap
/// proof does not satisfy the circuit" from "prove/verify disagree".
#[test]
#[ignore]
fn plonk_circuit_test_from_saved_wrap() {
  let path =
    std::env::var_os("IX_RECURSION_WRAP_IN").expect("IX_RECURSION_WRAP_IN");
  let bytes = std::fs::read(path).unwrap();
  let wrapped: aiur_recursion::WrapProof =
    bincode::deserialize(&bytes).unwrap();
  let (constraints, witness) =
    sp1_prover::build::build_constraints_and_witness(
      &wrapped.vk,
      &wrapped.proof,
    )
    .unwrap();
  println!("outer circuit: {} constraints", constraints.len());
  sp1_recursion_gnark_ffi::PlonkBn254Prover::test(constraints, witness);
  println!("gnark test passed");
}
