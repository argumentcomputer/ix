//! End to end: an Aiur toplevel proven on Hypercube, then normalize →
//! compose → shrink → wrap through SP1's recursion machines, each stage
//! verified natively. The gnark PLONK stage runs only with
//! `IX_RECURSION_PLONK=1` (it needs Docker or a native gnark build).

use std::borrow::Borrow;

use aiur::{
  bytecode::{Block, Circuit, Ctrl, Function, FunctionLayout, Op, Toplevel},
  execute::IOBuffer,
};
use aiur_hypercube::{ProverParams, ShardingParams, ToplevelMachine, verify};
use aiur_recursion::{AiurRecursionProver, claim_digest_bytes};
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

fn params() -> ProverParams {
  ProverParams { log_blowup: 1, log_stacking_height: 18, max_log_row_count: 17 }
}

#[test]
fn compress_shrink_wrap_a_toplevel_call() {
  let toplevel = mul_toplevel();
  let machine = ToplevelMachine::build(&toplevel, 0).unwrap();
  let (a, b) = (FF::from_u32(3), FF::from_u32(5));
  let mut io = IOBuffer { data: Default::default(), map: Default::default() };
  let (claim, vk, proof) = machine
    .execute_and_prove(
      &toplevel,
      &[a, b],
      &mut io,
      params(),
      ShardingParams::default(),
    )
    .unwrap();
  verify(machine.machine(), params(), &vk, &proof).unwrap();
  assert_eq!(proof.shard_proofs.len(), 1);

  let prover =
    AiurRecursionProver::new(machine.machine(), params(), 2).unwrap();

  // Compress: one shard, so one normalize marked complete.
  let compressed = prover.compress(&vk, &proof).unwrap();
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
  // The claim digest, byte for byte.
  let claim_felts: Vec<SP1Field> = claim
    .iter()
    .map(|x| SP1Field::from_canonical_u64(x.as_canonical_u64()))
    .collect();
  let expected = claim_digest_bytes(&claim_felts);
  let got: Vec<u8> = pv
    .committed_value_digest
    .iter()
    .flat_map(|word| word.iter().map(|limb| limb.as_canonical_u32() as u8))
    .collect();
  assert_eq!(got, expected.to_vec());

  // Shrink, then wrap.
  let shrunk = prover.shrink(compressed).unwrap();
  let wrapped = prover.wrap(shrunk).unwrap();
  let mut challenger =
    <SP1OuterGlobalContext as slop_challenger::IopCtx>::default_challenger();
  wrapped.vk.observe_into(&mut challenger);
  prover
    .wrap_verifier()
    .shard_verifier()
    .verify_shard(&wrapped.vk, &wrapped.proof, &mut challenger)
    .expect("wrap proof verifies");

  if std::env::var_os("IX_RECURSION_PLONK").is_some() {
    let dir = aiur_recursion::plonk::ensure_artifacts(&wrapped).unwrap();
    let (plonk, inputs) = aiur_recursion::plonk::prove(wrapped, &dir).unwrap();
    println!("plonk proof {} bytes, inputs {inputs:?}", plonk.raw_proof.len());
  }
}
