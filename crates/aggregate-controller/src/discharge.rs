//! Binding discharge (`ix_aggr` shapes 13 and 14). Claims proven with
//! `assume_binding` state their typing only if the environment's role
//! binding meets the specifications; an IxVM proof of the `Binding` claim
//! states that once. The discharge joins it to an aggregate of such claims
//! into the same statement validating the binding
//! (`Statement::discharged`). The controller applies it once, to the root,
//! before any root wrap.

use std::{path::Path, sync::Arc};

use ix_common::address::Address;
use ixon::{Claim, ClaimContext};
use record_pool::RecordReservation;

use crate::{
  backend::{Backend, BackendSlot, ChildProof, ExtraNode, Run},
  protocol::ChildKind,
  store::{
    decode_wrapper, load_cached_claim, persist_cached_claim, read_store,
  },
};

/// A natively verified proof of an environment's `Binding` claim.
pub struct BindingProof<B: Backend> {
  pub claim_bytes: Vec<u8>,
  /// The serialized claim list of its IxVM outer claim.
  pub claims_bytes: Vec<u8>,
  pub proof: B::Proof,
  pub address: Address,
}

/// The `Binding` claim of `env`'s own role binding under this specification
/// set: what `ix prove-binding` proves for it.
pub fn binding_claim(env: &ixon::Env) -> Result<Claim, String> {
  let ctx = ClaimContext::for_env(env)?;
  Ok(Claim::Binding { spec: ctx.spec, binding: ctx.binding })
}

/// Where a binding proof's wrapper comes from.
#[derive(Clone, Debug)]
pub enum BindingSource {
  /// The wrapper's store address.
  Stored(Address),
  /// The encoded wrapper itself, for a run that must not write the store
  /// and so cannot take the proof by address.
  Bytes(Vec<u8>),
}

/// The binding proof wrapper `source` names, which must prove `env`'s
/// binding claim and verify natively.
pub fn load_binding<B: Backend>(
  backend: &B,
  store_dir: &Path,
  source: &BindingSource,
  env: &ixon::Env,
) -> Result<BindingProof<B>, String> {
  let read;
  let (address, bytes) = match source {
    BindingSource::Stored(address) => {
      read = read_store(store_dir, address)?;
      if Address::hash(&read) != *address {
        return Err(format!(
          "binding proof {}: the store object has another digest",
          address.hex()
        ));
      }
      (address.clone(), read.as_slice())
    },
    BindingSource::Bytes(bytes) => (Address::hash(bytes), bytes.as_slice()),
  };
  let name = format!("binding proof {}", address.hex());
  let wrapper = decode_wrapper(bytes).map_err(|e| format!("{name}: {e}"))?;
  let expected = binding_claim(env)?;
  if wrapper.claim != expected {
    return Err(format!(
      "{name} states {:?}, not the environment's binding claim {expected:?}",
      wrapper.claim
    ));
  }
  let mut claim_bytes = Vec::new();
  expected.put(&mut claim_bytes);
  let proof = backend
    .decode_proof(&wrapper.proof)
    .map_err(|e| format!("{name} does not decode: {e}"))?;
  let outer = backend.outer_claim(ChildKind::Ixvm, &claim_bytes);
  backend
    .verify(ChildKind::Ixvm, &outer, &proof)
    .map_err(|e| format!("{name} fails native verification: {e}"))?;
  Ok(BindingProof {
    claim_bytes,
    claims_bytes: backend.claims_bytes(&outer),
    proof,
    address,
  })
}

/// Discharges `root`'s binding assumption with `binding` on `lane`: a proof
/// of `root.statement.discharged()`, found in the aggregate cache or proven
/// and published there.
pub fn discharge<B: Backend>(
  backend: &B,
  lane: &B::Lane,
  run: Run<'_, B::Claim>,
  root: &BackendSlot<B>,
  binding: &BindingProof<B>,
  reservation: &RecordReservation,
) -> Result<Arc<BackendSlot<B>>, String> {
  const LABEL: &str = "binding discharge";
  let output = root.statement.discharged()?;
  let outer = backend.outer_claim(ChildKind::Aggr, &output.claim_bytes);
  let key = backend.cache_key(&outer);
  let cached = load_cached_claim(
    run.store_dir,
    run.cache_dir,
    LABEL,
    &key,
    &output.claim,
    &outer,
    |bytes| backend.decode_proof(bytes),
    |outer, proof| backend.verify(ChildKind::Aggr, outer, proof),
  );
  let (proof, proof_address) = match cached {
    Some((proof, address)) => (proof, Some(address)),
    None => {
      let node = ExtraNode::Discharge {
        child: ChildProof {
          kind: root.kind,
          claim_bytes: &root.statement.claim_bytes,
          claims_bytes: &root.claims_bytes,
          proof: &root.proof,
        },
        binding: ChildProof {
          kind: ChildKind::Ixvm,
          claim_bytes: &binding.claim_bytes,
          claims_bytes: &binding.claims_bytes,
          proof: &binding.proof,
        },
        output: &output.claim_bytes,
      };
      let proof = backend.prove_extra(lane, node, reservation)?;
      let address = persist_cached_claim(
        run.store_dir,
        run.cache_dir,
        run.write_outputs,
        LABEL,
        &key,
        &output.claim,
        &output.claim_bytes,
        || backend.encode_proof(&proof),
      )?;
      (proof, address)
    },
  };
  eprintln!(
    "[aggregate] binding {} discharged with {}",
    output.ctx.binding.hex(),
    binding.address.hex()
  );
  Ok(Arc::new(BackendSlot::<B> {
    kind: ChildKind::Aggr,
    statement: output,
    claims_bytes: backend.claims_bytes(&outer),
    outer_claim: outer,
    proof,
    proof_address,
  }))
}
