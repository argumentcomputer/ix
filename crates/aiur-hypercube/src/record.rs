//! The execution record and program types the Hypercube prover consumes.
//!
//! Aiur's witness generation already produces one trace per circuit; the
//! record simply carries those traces (converted to the backend field and
//! lowered) plus the public values.

use hashbrown::HashMap;

use slop_algebra::{AbstractField, PrimeField32};
use slop_matrix::{Matrix, dense::RowMajorMatrix};
use sp1_hypercube::{
  InteractionKind, MachineRecord, PROOF_MAX_NUM_PVS, UntrustedConfig,
  air::{AirInteraction, InteractionScope, MachineProgram, SP1AirBuilder},
  septic_digest::SepticDigest,
};

use crate::{F, air::AIUR_INTERACTION_KIND};

/// Width of the claim message sent from the public values.
///
/// The claim — `[function_channel, fun_idx, inputs.., outputs..]`, the
/// message the entry function's return lookup provides — enters the lookup
/// argument as a verifier-side `send` from the public values, the analogue of
/// multi-stark seeding its accumulator with the claim. `eval_public_values`
/// has no access to the machine, so the message has a fixed width: the claim
/// is zero-padded to `CLAIM_WIDTH`. Trailing zeros do not change a LogUp
/// fingerprint (`α + β₀·kind + Σ βᵢ₊₁·valueᵢ`), so the padded message
/// balances against the function's unpadded provide, and the shard verifier
/// already enforces that public values past the machine's `num_pv_elts` are
/// zero.
///
/// Prover and verifier must sample the same number of fingerprint
/// challenges: the prover derives it from the chips' interaction arities, the
/// verifier from those and the public-value kinds' table arities. Every
/// machine therefore includes an internal chip with a zero-multiplicity
/// interaction of `CLAIM_WIDTH` values, which pins both derivations to the
/// same power of two (see `AiurMachine::build`).
pub const CLAIM_WIDTH: usize = 64;

/// Public-value layout: the zero-padded claim, then the sharding values.
/// The claim message is sent with the `PV_CLAIM_FLAG` multiplicity, so
/// exactly the shard carrying the entry function's return row sets the flag
/// (the top-level verifier checks there is exactly one). `PV_CHAIN_LEN` and
/// `PV_DIGEST` expose the shard's adapter chain end (see [`crate::global`]);
/// a shard with no cross-shard boundary exposes length 0 and the start
/// digest, which cancels the chain-start push below.
pub const PV_CLAIM_FLAG: usize = CLAIM_WIDTH;
/// Number of adapter rows in the shard (the accumulator chain's length).
pub const PV_CHAIN_LEN: usize = CLAIM_WIDTH + 1;
/// The shard's septic digest, `x` then `y` (14 limbs).
pub const PV_DIGEST: usize = CLAIM_WIDTH + 2;
/// Total public values an Aiur shard carries.
pub const NUM_AIUR_PVS: usize = PV_DIGEST + 14;

/// One shard's worth of traces, indexed like the machine's chips.
#[derive(Clone, Default, Debug)]
pub struct AiurRecord {
  /// `traces[i]` is chip `i`'s padded main trace; `None` deactivates it.
  pub traces: Vec<Option<RowMajorMatrix<F>>>,
  /// The machine's public values (unpadded): the zero-padded claim, the
  /// claim-shard flag, and the adapter chain end (see [`PV_CLAIM_FLAG`]).
  pub public_values: Vec<F>,
}

impl MachineRecord for AiurRecord {
  fn stats(&self) -> HashMap<String, usize> {
    self
      .traces
      .iter()
      .enumerate()
      .filter_map(|(i, t)| {
        t.as_ref().map(|t| (format!("chip_{i}_rows"), t.height()))
      })
      .collect()
  }

  fn append(&mut self, other: &mut Self) {
    if self.traces.is_empty() {
      self.traces = std::mem::take(&mut other.traces);
    } else {
      for (slot, other) in self.traces.iter_mut().zip(other.traces.drain(..)) {
        if slot.is_none() {
          *slot = other;
        }
      }
    }
    if self.public_values.is_empty() {
      self.public_values = std::mem::take(&mut other.public_values);
    }
  }

  fn public_values<T: AbstractField>(&self) -> Vec<T> {
    assert!(
      self.public_values.len() <= PROOF_MAX_NUM_PVS,
      "public values exceed PROOF_MAX_NUM_PVS"
    );
    let mut pvs: Vec<T> = self
      .public_values
      .iter()
      .map(|x| T::from_canonical_u32(x.as_canonical_u32()))
      .collect();
    pvs.resize(PROOF_MAX_NUM_PVS, T::zero());
    pvs
  }

  /// The claim is required from the public values (see [`CLAIM_WIDTH`]),
  /// gated by the claim-shard flag, and the adapter chain's endpoints are
  /// pushed/pulled from the sharding public values (see [`crate::global`]).
  fn eval_public_values<AB: SP1AirBuilder>(builder: &mut AB) {
    let pvs: Vec<AB::Expr> =
      builder.public_values().iter().map(|v| (*v).into()).collect();
    let pv = |i: usize| -> AB::Expr { pvs[i].clone() };
    let flag = pv(PV_CLAIM_FLAG);
    builder.assert_bool(flag.clone());
    let values: Vec<AB::Expr> = (0..CLAIM_WIDTH).map(pv).collect();
    builder.send(
      AirInteraction::new(values, flag, AIUR_INTERACTION_KIND),
      InteractionScope::Local,
    );

    let chain_channel =
      AB::Expr::from_canonical_u32(crate::global::CHAIN_CHANNEL);
    // Push the chain start `(CHAIN, 0, START)`...
    let start = SepticDigest::<AB::F>::zero().0;
    let mut values = vec![chain_channel.clone(), AB::Expr::zero()];
    values.extend(start.x.0.iter().map(|v| AB::Expr::from(*v)));
    values.extend(start.y.0.iter().map(|v| AB::Expr::from(*v)));
    builder.send(
      AirInteraction::new(values, AB::Expr::one(), AIUR_INTERACTION_KIND),
      InteractionScope::Local,
    );
    // ...and pull the chain end `(CHAIN, len, digest)` the shard exposes.
    let mut values = vec![chain_channel, pv(PV_CHAIN_LEN)];
    values.extend((0..14).map(|k| pv(PV_DIGEST + k)));
    builder.send(
      AirInteraction::new(values, -AB::Expr::one(), AIUR_INTERACTION_KIND),
      InteractionScope::Local,
    );
  }

  fn interactions_in_public_values() -> Vec<InteractionKind> {
    vec![AIUR_INTERACTION_KIND]
  }
}

/// The (trivial) program: Aiur has no program counter and no global
/// interactions in the single-shard setting.
#[derive(Clone, Copy, Debug, Default)]
pub struct AiurProgram;

impl MachineProgram<F> for AiurProgram {
  fn pc_start(&self) -> [F; 3] {
    [F::zero(); 3]
  }

  fn initial_global_cumulative_sum(&self) -> SepticDigest<F> {
    SepticDigest::<F>::zero()
  }

  fn untrusted_config(&self) -> UntrustedConfig<F> {
    UntrustedConfig::zero()
  }
}
