//! What a proof system supplies to the controller.
//!
//! The controller decides what to prove and when: the plan, admission,
//! priority, retries, cancellation, bisection, resumption, root wrapping and
//! progress. A backend executes, proves, verifies and encodes one unit of
//! work. Execution runs on the controller's executor threads under a bound
//! [`RecordReservation`]; proving runs on the prover thread of one lane.

use std::{fmt::Debug, path::Path, sync::Arc};

use ix_common::address::Address;
use record_pool::RecordReservation;
use rustc_hash::FxHashMap;

use crate::{
  plan::SlotSpec,
  prepare::PreparedShard,
  protocol::ChildKind,
  statement::{CanonicalTree, Statement},
};

/// The claims a backend's proofs are about, and the cache keys of those
/// proofs. Pure functions of the claim bytes, so a plan can be built without
/// a prover.
pub trait Identity {
  /// An outer claim: what a proof of one child kind publicly proves.
  type Claim: Clone + PartialEq + Debug + Send + Sync;
  /// The outer claim a proof of `kind` makes about an `ixon` claim.
  fn outer_claim(&self, kind: ChildKind, claim_bytes: &[u8]) -> Self::Claim;
  /// The serialized claim list a parent's advice carries for a child.
  fn claims_bytes(&self, outer: &Self::Claim) -> Vec<u8>;
  /// The aggregate-cache key of a proof of `outer`.
  fn cache_key(&self, outer: &Self::Claim) -> Address;
}

/// A proven plan slot, or a proven claim standing in for one.
pub struct Slot<C, P> {
  pub kind: ChildKind,
  pub statement: Arc<Statement>,
  pub outer_claim: C,
  pub proof: P,
  pub proof_address: Option<Address>,
  pub claims_bytes: Vec<u8>,
}

/// A backend's proven slot.
pub type BackendSlot<B> = Slot<<B as Identity>::Claim, <B as Backend>::Proof>;

/// Why an execution did not produce a record: it reached the per-record
/// ceiling (a claim can be bisected), it was cancelled to resolve memory
/// contention (it is requeued), or anything else (the pass fails).
#[derive(Debug)]
pub enum PrepareFailure {
  OverRecordCap { bytes: usize, cap: usize },
  MemoryContention,
  Other(String),
}

impl From<String> for PrepareFailure {
  fn from(message: String) -> Self {
    Self::Other(message)
  }
}

impl From<&str> for PrepareFailure {
  fn from(message: &str) -> Self {
    Self::Other(message.to_string())
  }
}

impl From<PrepareFailure> for String {
  fn from(failure: PrepareFailure) -> Self {
    match failure {
      PrepareFailure::OverRecordCap { bytes, cap } => {
        format!("record reached {bytes} B, over the {cap} B record cap")
      },
      PrepareFailure::MemoryContention => {
        "record cancelled to resolve memory contention".into()
      },
      PrepareFailure::Other(message) => message,
    }
  }
}

/// The run state a backend reads while executing or proving a slot.
pub struct Run<'a, C> {
  pub specs: &'a [SlotSpec<C>],
  pub prepared: &'a [PreparedShard],
  pub owner_by_address: &'a FxHashMap<Address, usize>,
  pub store_dir: &'a Path,
  pub cache_dir: Option<&'a Path>,
  pub write_outputs: bool,
  /// The prover budget of one slot when its execution is proven as trace
  /// shards; `None` proves unsharded and unbudgeted.
  pub wrap_budget: Option<usize>,
  /// A slot to prove again although the aggregate cache holds it.
  pub reprove_slot: Option<usize>,
}

impl<C> Clone for Run<'_, C> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<C> Copy for Run<'_, C> {}

/// One child proof of an [`ExtraNode`].
pub struct ChildProof<'a, P> {
  pub kind: ChildKind,
  /// The child's `ixon` claim, serialized.
  pub claim_bytes: &'a [u8],
  /// The serialized claim list of the child's outer claim.
  pub claims_bytes: &'a [u8],
  pub proof: &'a P,
}

impl<P> Clone for ChildProof<'_, P> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<P> Copy for ChildProof<'_, P> {}

/// An `ix_aggr` node outside a manifest's fold plan.
pub enum ExtraNode<'a, P> {
  /// Shapes 13 and 14: `child` assumes its role binding and `binding`, an
  /// IxVM proof of the `Binding` claim, discharges it; `output` is the
  /// child's claim validating the binding.
  Discharge {
    child: ChildProof<'a, P>,
    binding: ChildProof<'a, P>,
    output: &'a [u8],
  },
  /// Shapes 15 and 16: a catalog join (`crate::catalog`) of two aggregate
  /// proofs into `output`, with the node's preimages and trees.
  Catalog {
    shape: u8,
    children: [ChildProof<'a, P>; 2],
    output: &'a [u8],
    preimages: &'a [Vec<u8>],
    trees: &'a [&'a CanonicalTree],
  },
}

impl<'a, P> ExtraNode<'a, P> {
  /// The serialized claim the node proves.
  pub fn output(&self) -> &'a [u8] {
    match *self {
      Self::Discharge { output, .. } | Self::Catalog { output, .. } => output,
    }
  }
}

/// A claim proven on a lane, before it is persisted.
pub struct ProvenClaim<P> {
  /// The claim the execution proved, as the witness builder produced it.
  pub claim: ixon::Claim,
  pub claim_bytes: Vec<u8>,
  pub proof: P,
}

pub trait Backend: Identity + Sync {
  /// One resident prover: a device, or a CPU lane.
  type Lane: Sync;
  type Proof: Send + Sync;
  /// An executed claim waiting for a lane.
  type ClaimRecord: Send;
  /// An executed join or root waiting for a lane.
  type Staged: Send;
  /// Keeps a reservation bound to the executing thread while it lives.
  type Binding;

  /// `count` resident provers with the same verifying keys.
  fn lanes(&self, count: usize) -> Result<Vec<Self::Lane>, String>;

  /// Host memory the backend keeps resident for the whole run (programs,
  /// fixed tables), set aside before any record is admitted. Measured once
  /// the lanes exist.
  fn resident_bytes(&self) -> usize {
    0
  }

  /// The host workspace one lane proves within, for shards of at most
  /// `cells` committed cells; `None` when it overflows.
  fn lane_workspace_bytes(&self, cells: usize) -> Option<usize> {
    crate::lanes::cell_workspace(cells)
  }

  /// Routes the records the current thread executes to `reservation`.
  fn bind(&self, reservation: &RecordReservation) -> Self::Binding;

  /// Executes the claim over `owned`, which must be `expected`, planned
  /// within `budget` and charged to `reservation`. Runs on an executor
  /// thread against the executors' lane, with `reservation` bound.
  fn execute_claim(
    &self,
    lane: &Self::Lane,
    env: &ixon::Env,
    owned: &[Address],
    expected: &ixon::Claim,
    budget: Option<usize>,
    reservation: &RecordReservation,
  ) -> Result<Self::ClaimRecord, PrepareFailure>;

  /// Executes plan slot `slot` (a join, or the root) over its proven
  /// children, or finds its proof in the cache.
  fn execute_aggregate(
    &self,
    lane: &Self::Lane,
    run: Run<'_, Self::Claim>,
    slot: usize,
    children: &[Arc<BackendSlot<Self>>],
    reservation: &RecordReservation,
  ) -> Result<Self::Staged, PrepareFailure>;

  /// Proves an executed claim on `lane`.
  fn prove_claim(
    &self,
    lane: &Self::Lane,
    record: Self::ClaimRecord,
  ) -> Result<ProvenClaim<Self::Proof>, String>;

  /// Proves an executed slot on `lane`, persisting it in the cache.
  fn prove_aggregate(
    &self,
    lane: &Self::Lane,
    run: Run<'_, Self::Claim>,
    slot: usize,
    staged: Self::Staged,
  ) -> Result<Arc<BackendSlot<Self>>, String>;

  /// One more aggregation over `proof`, a proof of `root`'s claim, so a
  /// root of several trace shards ends as a smaller proof of the same claim.
  fn wrap_root(
    &self,
    lane: &Self::Lane,
    run: Run<'_, Self::Claim>,
    root: &BackendSlot<Self>,
    proof: &Self::Proof,
    reservation: &RecordReservation,
  ) -> Result<Self::Proof, String>;

  /// Executes and proves `node` on `lane`, charged to `reservation`: an
  /// aggregate proof of `node.output()`.
  fn prove_extra(
    &self,
    lane: &Self::Lane,
    node: ExtraNode<'_, Self::Proof>,
    reservation: &RecordReservation,
  ) -> Result<Self::Proof, String>;

  /// Native verification with the backend's own verifier.
  fn verify(
    &self,
    kind: ChildKind,
    outer: &Self::Claim,
    proof: &Self::Proof,
  ) -> Result<(), String>;

  /// Native verification with `lane`'s verifier.
  fn verify_on(
    &self,
    lane: &Self::Lane,
    kind: ChildKind,
    outer: &Self::Claim,
    proof: &Self::Proof,
  ) -> Result<(), String>;

  /// The trace shards `proof` consists of.
  fn trace_shards(&self, proof: &Self::Proof) -> usize;

  /// The proof bytes an `ixon` proof wrapper carries.
  fn encode_proof(&self, proof: &Self::Proof) -> Result<Vec<u8>, String>;

  fn decode_proof(&self, bytes: &[u8]) -> Result<Self::Proof, String>;
}
