//! The `AiurRun` statement of an Aiur join (`ix_aggr` shapes 17 and 18): an
//! environment's unconditional `CheckEnv` statement, two of its subjects (a
//! refinement theorem and the binding naming the program key), and an Aiur
//! proof's verifying key and serialized claims.

use ix_common::address::Address;
use ixon::Claim;
use rustc_hash::FxHashMap;

use crate::{advice::path_payload, statement::Statement};

pub struct AiurRun {
  pub claim: Claim,
  pub claim_bytes: Vec<u8>,
  /// Discharge-format Merkle paths of the theorem and the binding into the
  /// environment's subject root.
  pub theorem_path: Vec<u8>,
  pub binding_path: Vec<u8>,
}

impl AiurRun {
  pub fn new(
    env: &Statement,
    owner_by_address: &FxHashMap<Address, usize>,
    theorem: &Address,
    binding: &Address,
    aiur_key: &[u8],
    aiur_claims: &[u8],
  ) -> Result<Self, String> {
    let Claim::CheckEnv { ctx, root, assumptions } = &env.claim else {
      return Err("an Aiur join's environment claim is a CheckEnv".into());
    };
    if assumptions.is_some() || ctx.binding_assumed {
      return Err(
        "an Aiur join's environment claim must be unconditional and validate its binding"
          .into(),
      );
    }
    let path = |constant: &Address, what: &str| -> Result<Vec<u8>, String> {
      let owner = owner_by_address
        .get(constant)
        .ok_or_else(|| format!("the {what} {} is not a subject", constant.hex()))?;
      let path = env
        .subjects
        .merkle_proof(constant, *owner)
        .ok_or_else(|| format!("no Merkle path for the {what}"))?;
      path_payload(Some(&path))
    };
    let theorem_path = path(theorem, "theorem")?;
    let binding_path = path(binding, "binding")?;
    let claim = Claim::AiurRun {
      env: Address::hash(&env.claim_bytes),
      root: root.clone(),
      theorem: theorem.clone(),
      binding: binding.clone(),
      key: Address::hash(aiur_key),
      claims: Address::hash(aiur_claims),
    };
    let (_, claim_bytes) = claim.commit();
    Ok(Self { claim, claim_bytes, theorem_path, binding_path })
  }
}
