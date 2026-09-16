//! Proof-free merged PCS and forked multipoint/anchor topology. Transcript
//! addresses follow the pinned recorder's inline child-before-parent order,
//! including fork seeds and child closure. No proof values are synthesized.

use super::VerifierSetup;
use super::{algebra::Addresses, boolean::BooleanBlueprint};
use anyhow::{Result, ensure};
use flock_prover::union::UnionInstance;
use ix_stage4_trace::{
  F128JaggedMatrixIdV1, F128MergedPcsFrontendTraceV1, F128MergedPcsRoundV1,
  F128MultipointRoundV1, F128MultipointTwistedAssistTraceV1,
  F128RingSwitchTraceV1, F128WiringTraceV1,
};

pub(crate) struct PcsBlueprint {
  pub(crate) frontend: F128MergedPcsFrontendTraceV1,
  pub(crate) multipoint: F128MultipointTwistedAssistTraceV1,
}

pub(crate) fn compile_pcs(
  setup: &impl VerifierSetup,
  wiring: &F128WiringTraceV1,
  boolean: &BooleanBlueprint,
) -> Result<PcsBlueprint> {
  let shape = setup.verifier_shape();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  ensure!(union.num_boolean() != 0, "a Boolean class is required");
  let params = setup.pcs_params();
  let dense = params
    .m
    .checked_sub(7)
    .ok_or_else(|| anyhow::anyhow!("PCS dense dimension"))?;
  let heights = union.jagged_heights();
  ensure!(
    !heights.is_empty() && heights.len().is_power_of_two(),
    "jagged height table dimension"
  );
  let row_variables = u32::try_from(union.n_log())?;
  let column_variables = heights.len().ilog2();
  let packed_variables = row_variables + column_variables;
  ensure!(
    wiring.packed_claim_variables == packed_variables
      && boolean.pcs_claims.len() == 2
      && boolean
        .pcs_claims
        .iter()
        .all(|claim| { claim.x_outer.len() == 1 + packed_variables as usize }),
    "PCS Boolean/gather point dimensions"
  );
  let element = super::element::compile_element(setup, boolean)?;
  let mut address = boolean.end;
  // Closing wiring digests are observed on the parent after its Boolean
  // branch. The child's two closing squeezes are already in boolean.end.
  address.observe_index();
  address.observe_index();
  if let Some(element) = &element {
    address = element.end;
  }
  let element_claims = 2 * usize::from(union.has_element());
  let groups = 1 + usize::from(union.has_element());
  let jagged_claims = 3 + element_claims;
  let ring_switches = (0..2)
    .map(|_| F128RingSwitchTraceV1 {
      s_hat_v_observations: (0..128).map(|_| address.observe_index()).collect(),
      r_dprime_challenges: (0..7).map(|_| address.challenge_index()).collect(),
    })
    .collect();
  let packed_direct_observations = (0..element_claims
    + wiring.gather_observations.len())
    .map(|_| address.observe_index())
    .collect::<Vec<_>>();
  ensure!(
    packed_direct_observations[element_claims..] == wiring.gather_observations,
    "PCS/wiring gather schedule"
  );
  let batching_challenges = (0..2 + packed_direct_observations.len())
    .map(|_| address.challenge_index())
    .collect();
  let merged_rounds = (0..dense)
    .map(|_| F128MergedPcsRoundV1 {
      one_observation: address.observe_index(),
      infinity_observation: address.observe_index(),
      challenge: address.challenge_index(),
    })
    .collect();

  // At the assist fork the parent squeezes two seed words. The child is
  // inlined here, observes the seeds, then runs its two complete sumchecks.
  address.challenge_index();
  address.challenge_index();
  address.observe_index();
  address.observe_index();
  let dual_value_observations = (0..2)
    .map(|_| (0..128).map(|_| address.observe_index()).collect())
    .collect();
  let group_value_observations =
    (0..groups).map(|_| address.observe_index()).collect();
  let gamma_challenge = address.challenge_index();
  let multipoint_rounds =
    (0..dense).map(|_| multipoint_round(&mut address)).collect();
  let anchor_value_observation = address.observe_index();
  let anchor_dimensions = 2 * (dense + 1);
  let anchor_rounds =
    (0..anchor_dimensions).map(|_| multipoint_round(&mut address)).collect();
  address.challenge_index();
  address.challenge_index();
  // The inner opening starts on the parent BEFORE it merges the assist's
  // digest. Its first scalar is q_eval; no merge observations precede it.
  let q_eval_observation = address.observe_index();

  let cap_nodes = 1u32
    .checked_shl(u32::try_from(params.l0_cap_depth())?)
    .ok_or_else(|| anyhow::anyhow!("PCS CAP dimension"))?;
  let frontend = F128MergedPcsFrontendTraceV1 {
    commitment_variables: u32::try_from(params.m)?,
    commitment_cap_payload: 2,
    commitment_cap_nodes: cap_nodes,
    row_variables,
    column_variables,
    jagged_heights: heights,
    boolean_claims: boolean.pcs_claims.clone(),
    ring_switches,
    packed_direct_observations,
    batching_challenges,
    merged_rounds,
    q_eval_observation,
  };
  let group_column_addresses = wiring
    .gather_high_bits
    .iter()
    .map(|bits| {
      bits.iter().enumerate().try_fold(0u32, |result, (bit, &set)| {
        let mask = 1u32
          .checked_shl(u32::try_from(bit)?)
          .ok_or_else(|| anyhow::anyhow!("gather address dimension"))?;
        Ok(result | if set { mask } else { 0 })
      })
    })
    .collect::<Result<Vec<_>>>()?;
  let multipoint = F128MultipointTwistedAssistTraceV1 {
    element_claims: union.has_element(),
    frontend_topology_digest: frontend.topology_digest(),
    matrix: F128JaggedMatrixIdV1 {
      circuit_digest: setup.circuit_digest(),
      row_variables: column_variables,
      column_variables: u32::try_from(anchor_dimensions)?,
    },
    witness_row_variables: row_variables,
    dense_variables: u32::try_from(dense)?,
    family_h: crate::replay::family_h_constants(),
    dual_value_observations,
    group_value_observations,
    gamma_challenge,
    multipoint_rounds,
    anchor_value_observation,
    anchor_rounds,
    group_column_addresses,
    jagged_claim_private_values: (0..jagged_claims).map(|i| i as u64).collect(),
  };
  frontend.validate(
    0,
    usize::try_from(address.observed)?,
    usize::try_from(address.challenges)?,
    2 * union.num_boolean(),
    boolean.trace.operations.len(),
    &[32, 8 * shape.counts.len(), cap_nodes as usize * 32, 32, 32],
    &vec![
      packed_variables as usize;
      element_claims + wiring.gather_observations.len()
    ],
  )?;
  multipoint.validate(
    usize::try_from(address.observed)?,
    usize::try_from(address.challenges)?,
    jagged_claims,
  )?;
  Ok(PcsBlueprint { frontend, multipoint })
}

fn multipoint_round(address: &mut Addresses) -> F128MultipointRoundV1 {
  F128MultipointRoundV1 {
    one_observation: address.observe_index(),
    infinity_observation: address.observe_index(),
    challenge: address.challenge_index(),
  }
}
