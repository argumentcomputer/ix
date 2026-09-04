//! Box-independent end-to-end smoke for the terminal guest.
//!
//! This builds a tiny Aiur proof with the same fixed 18-word claim framing as
//! `ix_aggr`, then verifies it inside the real SP1 guest in execute mode. It is
//! intentionally synthetic: production aggregate roots enter through
//! `ix compress-root`.

use aiur::{
  G,
  bytecode::{Block, Ctrl, Function, FunctionLayout, Toplevel},
  execute::IOBuffer,
  synthesis::AiurSystem,
  vk_codec::aiur_system_to_bytes,
};
use anyhow::{Context, Result};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::{CommitmentParameters, FriParameters},
};
use sp1_compress_host::{Mode, OUTER_CLAIM_ELEMENTS, run_sp1};

fn root_format_toplevel() -> Toplevel {
  Toplevel {
    functions: vec![Function {
      body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![]) },
      layout: FunctionLayout {
        input_size: OUTER_CLAIM_ELEMENTS - 2,
        selectors: 1,
        auxiliaries: 1,
        lookups: 1,
      },
      entry: true,
      constrained: true,
    }],
    memory_sizes: vec![],
  }
}

#[tokio::main]
async fn main() -> Result<()> {
  sp1_sdk::utils::setup_logger();
  let commitment = CommitmentParameters { log_blowup: 1, cap_height: 0 };
  let fri = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 4,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let system = AiurSystem::build(root_format_toplevel(), commitment, fri);
  let input =
    (1..=OUTER_CLAIM_ELEMENTS - 2).map(G::from_usize).collect::<Vec<_>>();
  let mut io = IOBuffer { data: Default::default(), map: Default::default() };
  let (claim, proof) = system.prove(0, &input, &mut io);
  system
    .verify(&claim, &proof)
    .map_err(|error| anyhow::anyhow!("native smoke proof failed: {error:?}"))?;
  assert_eq!(claim.len(), OUTER_CLAIM_ELEMENTS);

  let vk_bytes = aiur_system_to_bytes(&system)
    .map_err(|error| anyhow::anyhow!("encode smoke vk: {error}"))?;
  let claim_bytes = claim
    .iter()
    .flat_map(|value| value.as_canonical_u64().to_le_bytes())
    .collect();
  let proof_bytes = proof.to_bytes().context("encode smoke proof")?;
  run_sp1(vk_bytes, claim_bytes, proof_bytes, &fri, Mode::Execute, None, None)
    .await
}
