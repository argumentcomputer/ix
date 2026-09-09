//! The leaf of the recursion tree: one Aiur Hypercube shard proof, verified
//! in SP1's recursion circuit and re-expressed as SP1 recursion public values.
//!
//! This is the Aiur analogue of `SP1RecursiveVerifier` (sp1-recursion-circuit
//! `machine/core.rs`). SP1's core-level program cannot be reused as is: after
//! the generic shard verification it asserts RISC-V execution state (program
//! counters, exit codes, memory-initialization digests). The Aiur machine has
//! none of that; its shard public values carry the zero-padded claim, the
//! claim-shard flag, and the shard's septic chain digest (see
//! `aiur_hypercube::record`). This program verifies the shard exactly like
//! SP1's does — same verifying-key observation, same `verify_shard` — and then
//! maps the Aiur public values onto `RecursionPublicValues` so that SP1's
//! compress, shrink and wrap programs fold and finish them unchanged:
//!
//! | `RecursionPublicValues`          | Aiur meaning                                   |
//! |----------------------------------|------------------------------------------------|
//! | `committed_value_digest`         | 32 bytes of Poseidon2(zero-padded claim)       |
//! | `prev_committed_value_digest`    | 0 on the first shard, else the same digest     |
//! | `global_cumulative_sum`          | the shard's septic chain digest (`PV_DIGEST`)  |
//! | `contains_first_shard`           | the claim-shard flag (`PV_CLAIM_FLAG`)         |
//! | `initial_timestamp[3]`/`last..`  | shard ordinal `k + 1` / `k + 2`                |
//! | `pc_start` / `next_pc`           | the halt pc, constant                          |
//! | init/finalize addr, commit flags | 0 → 1 on the first shard, 1 → 1 afterwards     |
//! | `sp1_vk_digest`                  | Poseidon2 hash of the Aiur machine's vk        |
//! | everything else                  | zero                                           |
//!
//! With that mapping the invariants SP1 enforces mean exactly what the native
//! Aiur verifier (`aiur_hypercube::prover::verify`) checks: compress chains
//! every shard's `prev_*` to its predecessor's `*` (so the ordinals form
//! `0..n`, every shard commits to the same claim digest, and `contains_first
//! _shard` sums the claim flags), `assert_complete` at the root requires the
//! first shard's zeros, exactly one claim flag, and the summed septic digest
//! to be the zero point — Aiur's "every cross-shard boundary cancels". The
//! claim itself is bound by the claim shard, whose flag gates the return
//! lookup in the AIR; the other shards' claim slots are only pinned through
//! the compress chain to the claim shard's digest.
//!
//! The septic digest convention matches SP1's: an Aiur shard's chain starts
//! at `SepticDigest::zero()` (the same point SP1 accumulates from), so the
//! exposed digest is already what `sum_digest_v2` expects.

use std::borrow::BorrowMut;

use serde::{Deserialize, Serialize};
use slop_algebra::{AbstractField, Field, PrimeField32};
use sp1_hypercube::{
  MachineVerifyingKey, SP1PcsProofInner, ShardProof, septic_curve::SepticCurve,
  septic_digest::SepticDigest, septic_extension::SepticExtension,
};
use sp1_primitives::{SP1Field, SP1GlobalContext};
use sp1_recursion_circuit::{
  CircuitConfig, SP1FieldConfigVariable,
  challenger::CanObserveVariable,
  hash::Poseidon2SP1FieldHasherVariable,
  shard::{
    MachineVerifyingKeyVariable, RecursiveShardVerifier, ShardProofVariable,
  },
  witness::{WitnessWriter, Witnessable},
};
use sp1_recursion_compiler::{
  circuit::CircuitV2Builder,
  config::InnerConfig,
  ir::{Builder, Felt},
};
use sp1_recursion_executor::{
  DIGEST_SIZE, NUM_PV_ELMS_TO_HASH, RECURSIVE_PROOF_NUM_PV_ELTS,
  RecursionPublicValues,
};

use aiur_hypercube::{
  AiurAir,
  record::{CLAIM_WIDTH, NUM_AIUR_PVS, PV_CLAIM_FLAG, PV_DIGEST},
};

/// `sp1_core_executor::HALT_PC`: the program counter a complete SP1
/// execution ends on. Aiur has no program counter; every shard reports it as
/// both its start and next pc so the compress chain is trivially satisfied
/// and `assert_complete` (which requires it) passes at the root.
pub const HALT_PC: u64 = 1;

/// The witness of one leaf: the Aiur machine's verifying key, one of its
/// shard proofs, and the shard's position in the recursion order.
#[derive(Clone, Serialize, Deserialize)]
pub struct AiurNormalizeWitnessValues {
  pub vk: MachineVerifyingKey<SP1GlobalContext>,
  pub shard_proof: ShardProof<SP1GlobalContext, SP1PcsProofInner>,
  /// The shard's ordinal `k` in the order the shards are composed.
  pub shard_index: SP1Field,
  /// `k^-1` (zero when `k = 0`): the witness of the `is_first` gadget.
  pub shard_index_inv: SP1Field,
  /// `k == 0`.
  pub is_first: bool,
  /// Whether this single shard is the whole proof (single-shard systems).
  pub is_complete: bool,
  /// The recursion vk allowlist root the compress stage will check against.
  pub vk_root: [SP1Field; DIGEST_SIZE],
}

impl AiurNormalizeWitnessValues {
  pub fn new(
    vk: MachineVerifyingKey<SP1GlobalContext>,
    shard_proof: ShardProof<SP1GlobalContext, SP1PcsProofInner>,
    shard_index: usize,
    is_complete: bool,
    vk_root: [SP1Field; DIGEST_SIZE],
  ) -> Self {
    let k = SP1Field::from_canonical_usize(shard_index);
    let shard_index_inv =
      if shard_index == 0 { SP1Field::zero() } else { k.inverse() };
    Self {
      vk,
      shard_proof,
      shard_index: k,
      shard_index_inv,
      is_first: shard_index == 0,
      is_complete,
      vk_root,
    }
  }
}

pub struct AiurNormalizeWitnessVariable<
  C: CircuitConfig,
  SC: SP1FieldConfigVariable<C>,
> {
  pub vk: MachineVerifyingKeyVariable<C, SC>,
  pub shard_proof: ShardProofVariable<C, SC>,
  pub shard_index: Felt<SP1Field>,
  pub shard_index_inv: Felt<SP1Field>,
  pub is_first: Felt<SP1Field>,
  pub is_complete: Felt<SP1Field>,
  pub vk_root: [Felt<SP1Field>; DIGEST_SIZE],
}

impl Witnessable<InnerConfig> for AiurNormalizeWitnessValues {
  type WitnessVariable =
    AiurNormalizeWitnessVariable<InnerConfig, SP1GlobalContext>;

  fn read(&self, builder: &mut Builder<InnerConfig>) -> Self::WitnessVariable {
    let vk = self.vk.read(builder);
    let shard_proof = self.shard_proof.read(builder);
    let shard_index = self.shard_index.read(builder);
    let shard_index_inv = self.shard_index_inv.read(builder);
    let is_first = SP1Field::from_bool(self.is_first).read(builder);
    let is_complete = SP1Field::from_bool(self.is_complete).read(builder);
    let vk_root = self.vk_root.read(builder);
    AiurNormalizeWitnessVariable {
      vk,
      shard_proof,
      shard_index,
      shard_index_inv,
      is_first,
      is_complete,
      vk_root,
    }
  }

  fn write(&self, witness: &mut impl WitnessWriter<InnerConfig>) {
    self.vk.write(witness);
    self.shard_proof.write(witness);
    self.shard_index.write(witness);
    self.shard_index_inv.write(witness);
    SP1Field::from_bool(self.is_first).write(witness);
    SP1Field::from_bool(self.is_complete).write(witness);
    self.vk_root.write(witness);
  }
}

/// The recursion program verifying one Aiur shard proof.
pub struct AiurRecursiveVerifier;

impl AiurRecursiveVerifier {
  /// Verify one Aiur shard proof and commit the SP1 recursion public values
  /// described in the module docs.
  pub fn verify<C>(
    builder: &mut Builder<C>,
    machine: &RecursiveShardVerifier<SP1GlobalContext, AiurAir, C>,
    input: AiurNormalizeWitnessVariable<C, SP1GlobalContext>,
  ) where
    C: CircuitConfig<Bit = Felt<SP1Field>>,
  {
    let AiurNormalizeWitnessVariable {
      vk,
      shard_proof,
      shard_index,
      shard_index_inv,
      is_first,
      is_complete,
      vk_root,
    } = input;

    let zero: Felt<_> = builder.eval(SP1Field::zero());
    let one: Felt<_> = builder.eval(SP1Field::one());

    // ── The shard proof, verified exactly as the native verifier does: the
    // challenger observes the vk (`MachineVerifyingKey::observe_into`), then
    // `verify_shard` replays the transcript.
    let mut challenger = SP1GlobalContext::challenger_variable(builder);
    challenger.observe(builder, vk.preprocessed_commit);
    challenger.observe_slice(builder, vk.pc_start);
    challenger.observe_slice(builder, vk.initial_global_cumulative_sum.0.x.0);
    challenger.observe_slice(builder, vk.initial_global_cumulative_sum.0.y.0);
    challenger.observe(builder, vk.untrusted_config.enable_untrusted_programs);
    for _ in 0..6 {
      challenger.observe(builder, zero);
    }
    machine.verify_shard(builder, &vk, &shard_proof, &mut challenger);

    // ── Aiur public values.
    let pv = &shard_proof.public_values;
    assert!(
      pv.len() >= NUM_AIUR_PVS,
      "shard proof carries too few public values"
    );
    let flag = pv[PV_CLAIM_FLAG];
    builder.assert_felt_eq(flag * (flag - one), zero);

    // The claim digest: Poseidon2 over the zero-padded claim, as 32 bytes.
    let claim: Vec<Felt<_>> = pv[..CLAIM_WIDTH].to_vec();
    let claim_hash = SP1GlobalContext::poseidon2_hash(builder, &claim);
    let committed_value_digest = digest_to_words(builder, claim_hash);

    // The shard's septic chain digest, already in SP1's accumulation
    // convention (the chain starts at `SepticDigest::zero()`).
    let septic =
      |at: usize| SepticExtension(core::array::from_fn(|k| pv[at + k]));
    let global_cumulative_sum = SepticDigest(SepticCurve {
      x: septic(PV_DIGEST),
      y: septic(PV_DIGEST + 7),
    });

    // ── The `is_first` gadget: `is_first` is boolean, forces `k = 0`, and
    // `!is_first` forces `k != 0` through the witnessed inverse.
    builder.assert_felt_eq(is_first * (is_first - one), zero);
    builder.assert_felt_eq(is_first * shard_index, zero);
    builder.assert_felt_eq(
      (one - is_first) * (shard_index * shard_index_inv - one),
      zero,
    );
    // `0` on the first shard, `1` afterwards: the "previous" side of every
    // chained flag SP1 expects to start at zero.
    let prev_flag: Felt<_> = builder.eval(one - is_first);
    let halt: Felt<_> = builder.eval(SP1Field::from_canonical_u64(HALT_PC));
    let ts_start: Felt<_> = builder.eval(shard_index + one);
    let ts_end: Felt<_> = builder.eval(shard_index + one + one);

    // ── Recursion public values.
    let vk_digest = vk.hash(builder);
    let mut stream = [zero; RECURSIVE_PROOF_NUM_PV_ELTS];
    let rpv: &mut RecursionPublicValues<Felt<SP1Field>> =
      stream.as_mut_slice().borrow_mut();
    rpv.committed_value_digest = committed_value_digest;
    rpv.prev_committed_value_digest = committed_value_digest
      .map(|word| word.map(|limb| builder.eval(limb * prev_flag)));
    rpv.prev_deferred_proofs_digest = [zero; 8];
    rpv.deferred_proofs_digest = [zero; 8];
    rpv.prev_deferred_proof = zero;
    rpv.deferred_proof = zero;
    rpv.pc_start = [halt, zero, zero];
    rpv.next_pc = [halt, zero, zero];
    rpv.initial_timestamp = [zero, zero, zero, ts_start];
    rpv.last_timestamp = [zero, zero, zero, ts_end];
    rpv.previous_init_addr = [prev_flag, zero, zero];
    rpv.last_init_addr = [one, zero, zero];
    rpv.previous_finalize_addr = [prev_flag, zero, zero];
    rpv.last_finalize_addr = [one, zero, zero];
    rpv.previous_init_page_idx = [zero; 3];
    rpv.last_init_page_idx = [zero; 3];
    rpv.previous_finalize_page_idx = [zero; 3];
    rpv.last_finalize_page_idx = [zero; 3];
    rpv.start_reconstruct_deferred_digest = [zero; 8];
    rpv.end_reconstruct_deferred_digest = [zero; 8];
    rpv.sp1_vk_digest = vk_digest;
    rpv.vk_root = vk_root;
    rpv.global_cumulative_sum = global_cumulative_sum;
    rpv.contains_first_shard = flag;
    rpv.num_included_shard = one;
    rpv.is_complete = is_complete;
    rpv.prev_exit_code = zero;
    rpv.exit_code = zero;
    rpv.prev_commit_syscall = prev_flag;
    rpv.commit_syscall = one;
    rpv.prev_commit_deferred_syscall = prev_flag;
    rpv.commit_deferred_syscall = one;
    rpv.proof_nonce = [zero; 4];
    rpv.digest = recursion_public_values_digest(builder, rpv);

    assert_complete(builder, rpv, is_complete);
    SP1GlobalContext::commit_recursion_public_values(builder, *rpv);
  }
}

/// Split a Poseidon2 digest into SP1's `[[byte; 4]; 8]` word layout: each
/// (31-bit) limb as four little-endian bytes, bit-decomposed in-circuit.
fn digest_to_words<C: CircuitConfig<Bit = Felt<SP1Field>>>(
  builder: &mut Builder<C>,
  digest: [Felt<SP1Field>; DIGEST_SIZE],
) -> [[Felt<SP1Field>; 4]; 8] {
  digest.map(|limb| {
    let bits = builder.num2bits_v2_f(limb, 31);
    core::array::from_fn(|j| {
      let lo = 8 * j;
      let hi = (lo + 8).min(31);
      builder.bits2num_v2_f(bits[lo..hi].iter().copied())
    })
  })
}

/// The native counterpart of the in-circuit claim commitment: the 32 bytes
/// `committed_value_digest` carries for a shard exposing `claim`.
pub fn claim_digest_bytes(claim: &[SP1Field]) -> [u8; 32] {
  assert!(claim.len() <= CLAIM_WIDTH, "claim wider than CLAIM_WIDTH");
  let mut padded = claim.to_vec();
  padded.resize(CLAIM_WIDTH, SP1Field::zero());
  let digest = sp1_primitives::poseidon2_hash(padded);
  let mut out = [0u8; 32];
  for (i, limb) in digest.iter().enumerate() {
    out[4 * i..4 * i + 4]
      .copy_from_slice(&limb.as_canonical_u32().to_le_bytes());
  }
  out
}

/// `sp1_recursion_circuit::machine::recursion_public_values_digest`, which is
/// crate-private there: the Poseidon2 hash of every public value before the
/// digest field.
pub fn recursion_public_values_digest<C: CircuitConfig>(
  builder: &mut Builder<C>,
  public_values: &RecursionPublicValues<Felt<SP1Field>>,
) -> [Felt<SP1Field>; DIGEST_SIZE] {
  let pv_slice = public_values.as_array();
  SP1GlobalContext::poseidon2_hash(builder, &pv_slice[..NUM_PV_ELMS_TO_HASH])
}

/// `sp1_recursion_circuit::machine::assert_complete`, which is crate-private
/// there: what a complete proof's public values must look like, gated by
/// `is_complete`.
pub fn assert_complete<C: CircuitConfig>(
  builder: &mut Builder<C>,
  public_values: &RecursionPublicValues<Felt<SP1Field>>,
  is_complete: Felt<SP1Field>,
) {
  let RecursionPublicValues {
    prev_committed_value_digest,
    prev_deferred_proofs_digest,
    deferred_proofs_digest,
    prev_exit_code,
    next_pc,
    initial_timestamp,
    start_reconstruct_deferred_digest,
    end_reconstruct_deferred_digest,
    global_cumulative_sum,
    contains_first_shard,
    previous_init_addr,
    last_init_addr,
    previous_finalize_addr,
    last_finalize_addr,
    previous_init_page_idx,
    previous_finalize_page_idx,
    prev_commit_syscall,
    commit_syscall,
    prev_commit_deferred_syscall,
    commit_deferred_syscall,
    prev_deferred_proof,
    ..
  } = public_values;

  builder.assert_felt_eq(
    is_complete * (is_complete - SP1Field::one()),
    SP1Field::zero(),
  );
  for word in prev_committed_value_digest {
    for limb in word {
      builder.assert_felt_eq(is_complete * *limb, SP1Field::zero());
    }
  }
  for limb in prev_deferred_proofs_digest {
    builder.assert_felt_eq(is_complete * *limb, SP1Field::zero());
  }
  builder.assert_felt_eq(
    is_complete * (next_pc[0] - SP1Field::from_canonical_u64(HALT_PC)),
    SP1Field::zero(),
  );
  builder.assert_felt_eq(is_complete * next_pc[1], SP1Field::zero());
  builder.assert_felt_eq(is_complete * next_pc[2], SP1Field::zero());
  builder.assert_felt_eq(
    is_complete * (*contains_first_shard - SP1Field::one()),
    SP1Field::zero(),
  );
  for limb in initial_timestamp[0..3].iter() {
    builder.assert_felt_eq(is_complete * *limb, SP1Field::zero());
  }
  builder.assert_felt_eq(
    is_complete * (initial_timestamp[3] - SP1Field::one()),
    SP1Field::zero(),
  );
  for limb in previous_init_addr.iter() {
    builder.assert_felt_eq(is_complete * *limb, SP1Field::zero());
  }
  builder.assert_felt_ne(
    last_init_addr[0] + last_init_addr[1] + last_init_addr[2],
    is_complete - SP1Field::one(),
  );
  for limb in previous_finalize_addr.iter() {
    builder.assert_felt_eq(is_complete * *limb, SP1Field::zero());
  }
  builder.assert_felt_ne(
    last_finalize_addr[0] + last_finalize_addr[1] + last_finalize_addr[2],
    is_complete - SP1Field::one(),
  );
  for limb in previous_init_page_idx.iter() {
    builder.assert_felt_eq(is_complete * *limb, SP1Field::zero());
  }
  for limb in previous_finalize_page_idx.iter() {
    builder.assert_felt_eq(is_complete * *limb, SP1Field::zero());
  }
  for start_digest in start_reconstruct_deferred_digest {
    builder.assert_felt_eq(is_complete * *start_digest, SP1Field::zero());
  }
  for (end_digest, deferred_digest) in
    end_reconstruct_deferred_digest.iter().zip(deferred_proofs_digest.iter())
  {
    builder.assert_felt_eq(
      is_complete * (*end_digest - *deferred_digest),
      SP1Field::zero(),
    );
  }
  builder.assert_felt_eq(is_complete * *prev_deferred_proof, SP1Field::zero());
  builder.assert_felt_eq(is_complete * *prev_exit_code, SP1Field::zero());
  builder.assert_felt_eq(is_complete * *prev_commit_syscall, SP1Field::zero());
  builder.assert_felt_eq(
    is_complete * *prev_commit_deferred_syscall,
    SP1Field::zero(),
  );
  builder.assert_felt_eq(
    is_complete * (*commit_syscall - SP1Field::one()),
    SP1Field::zero(),
  );
  builder.assert_felt_eq(
    is_complete * (*commit_deferred_syscall - SP1Field::one()),
    SP1Field::zero(),
  );
  builder.assert_digest_zero_v2(is_complete, *global_cumulative_sum);
}
