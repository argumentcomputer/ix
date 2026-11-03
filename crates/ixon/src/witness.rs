//! Backend-independent advice recipe for IxVM `verify_claim` executions.
//!
//! A [`ClaimWitness`] is the claim together with the advice streams the
//! IxVM kernel reads while checking it, as `(channel, key, payload)`
//! triples whose payloads are still bytes or numeric tags. Converting the
//! payloads to field elements, and laying them out in arenas, is left to
//! the consumer: the legacy prover fills an `IOBuffer`, the formal prover
//! binds the streams to its hint providers. Keeping the recipe here, next
//! to the environment and claim conventions, keeps both backends on one
//! definition of what a witness contains.
//!
//! # Channels
//!
//! | ch | payload                         | key                         |
//! |----|---------------------------------|-----------------------------|
//! | 0  | claim wire bytes                | packed `blake3(claim)` (8 words) |
//! | 1  | assumption tree serialization   | tree root (32 bytes)        |
//! | 2  | constant wire bytes             | constant address            |
//! | 3  | reducibility hint, numeric tag  | definition address          |
//! | 4  | blob bytes                      | blob address                |
//! | 6  | role binding bytes              | binding address             |
//!
//! Constant and blob addresses share a hash codomain, so one address can
//! be seeded on both channel 2 and channel 4. The kernel decides which
//! table a reference means from its Expr context (`Ref`/`Prj` against
//! `Str`/`Nat`), so the two channels are filled independently and no
//! discriminator is shipped.
//!
//! Reducibility hints keep their numeric encoding ([`hint_tag`]); a tag
//! can exceed one byte and must not be truncated to a byte payload.
//!
//! # Stream order
//!
//! Arena offsets are assigned per channel in stream order and are visible
//! in execution records, so the order is part of the recipe:
//!
//! 1. channels ascend: 0, 1, 2, 3, 4, 6;
//! 2. channel 1 follows the claim's fields: the subject tree of a
//!    `CheckEnv` claim, then its assumption tree when present;
//! 3. channels 2, 3 and 4 ascend by address bytes.
//!
//! The order depends only on the environment and the request, never on
//! hash-set iteration, so building twice yields identical streams.
//!
//! # Role binding
//!
//! Every claim is made relative to the environment's own role binding
//! ([`ClaimContext::for_env`]), which the kernel reads from channel 6. Its
//! bound roles and proof evidence ([`binding_roots`]) are walked as extra
//! roots of the byte scope, so the kernel finds every record it validates
//! the binding against. This is what `IxVM.ClaimHarness.buildClaimWitness`
//! and `buildShardCheckEnvWitness` emit.
//!
//! # Scopes
//!
//! The thin frontier committed by a shard claim and the byte scope shipped
//! to the kernel are different sets; see [`crate::shard_claim`]. The byte
//! scope is [`witness_scope`]: the full structural closure of the roots,
//! including the projection wrappers the kernel synthesizes for every
//! `Muts` block it reaches, together with every primitive the kernel may
//! fabricate references to while reducing, and the binding's roots.

use std::fmt;

use ix_common::address::Address;
use ix_common::env::ReducibilityHints;
use ix_common::prim_addrs::PrimAddrs;
use rustc_hash::FxHashSet;

use crate::assumption_tree::AssumptionTree;
use crate::env::Env;
use crate::lazy::BytesSource;
use crate::proof::{Claim, ClaimContext, spec_digest};
use crate::role_table::RoleTable;
use crate::shard_claim::shard_check_env_claim;

pub const CLAIM_CHANNEL: u8 = 0;
pub const TREE_CHANNEL: u8 = 1;
pub const CONSTANT_CHANNEL: u8 = 2;
pub const HINT_CHANNEL: u8 = 3;
pub const BLOB_CHANNEL: u8 = 4;
pub const ROLE_CHANNEL: u8 = 6;

/// The key a stream is stored under.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StreamKey {
  /// A claim digest, keyed as the eight packed words `verify_claim`
  /// receives as its public input.
  ClaimDigest(Address),
  /// A content address, keyed as its 32 bytes.
  Address(Address),
}

impl StreamKey {
  /// The key as field-sized words: eight packed little-endian `u32`s for
  /// a claim digest, one word per byte for an address.
  pub fn words(&self) -> Vec<u64> {
    match self {
      StreamKey::ClaimDigest(digest) => packed_digest_words(digest).to_vec(),
      StreamKey::Address(addr) => {
        addr.as_bytes().iter().map(|b| u64::from(*b)).collect()
      },
    }
  }
}

/// An address as eight little-endian packed `u32` words: the
/// `verify_claim` public input and the channel 0 key. Matches the
/// in-circuit `b3_pack`.
pub fn packed_digest_words(addr: &Address) -> [u64; 8] {
  let words = addr.as_bytes().as_chunks::<4>().0;
  std::array::from_fn(|i| u64::from(u32::from_le_bytes(words[i])))
}

/// A stream payload before field-element expansion.
#[derive(Clone, Debug)]
pub enum Payload {
  /// One value per byte. Constant payloads share the environment's
  /// backing storage.
  Bytes(BytesSource),
  /// A single numeric value.
  Tag(u64),
}

impl Payload {
  /// Number of field values the payload expands to.
  pub fn len(&self) -> usize {
    match self {
      Payload::Bytes(bytes) => bytes.len(),
      Payload::Tag(_) => 1,
    }
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// The payload's values, one `u64` per field element.
  pub fn values(&self) -> Vec<u64> {
    match self {
      Payload::Bytes(bytes) => {
        bytes.as_slice().iter().map(|b| u64::from(*b)).collect()
      },
      Payload::Tag(tag) => vec![*tag],
    }
  }
}

#[derive(Clone, Debug)]
pub struct AdviceStream {
  pub channel: u8,
  pub key: StreamKey,
  pub payload: Payload,
}

/// A claim and the advice its `verify_claim` execution reads, in the
/// module's stream order.
#[derive(Clone, Debug)]
pub struct ClaimWitness {
  pub claim: Claim,
  pub claim_bytes: Vec<u8>,
  /// `blake3(claim_bytes)`.
  pub digest: Address,
  pub streams: Vec<AdviceStream>,
}

impl ClaimWitness {
  /// The `verify_claim` public input.
  pub fn digest_words(&self) -> [u64; 8] {
    packed_digest_words(&self.digest)
  }
}

/// A claim form whose advice is prepared from the environment alone. The
/// typing claims are made under the environment's own binding, assumed
/// rather than validated with `assume_binding`.
#[derive(Clone, Copy, Debug)]
pub enum WitnessRequest<'a> {
  /// `Check { ctx, const_addr, assumptions: None }`.
  Check { target: &'a Address, assume_binding: bool },
  /// A shard `CheckEnv` over the given owned constants, with the thin
  /// frontier of [`crate::shard_claim`] as its assumptions.
  ShardCheckEnv { owned: &'a [Address], assume_binding: bool },
  /// `Binding { spec, binding }` for the environment's own binding.
  Binding,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessError {
  EmptyOwned,
  /// The environment carries no role binding.
  Unbound,
  /// A canonical tree's root disagrees with the claim computed from the
  /// same leaves.
  TreeMismatch,
  /// The claim recomputed from the request is not the expected claim.
  ClaimMismatch {
    expected: Box<Claim>,
    computed: Box<Claim>,
  },
}

impl fmt::Display for WitnessError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      WitnessError::EmptyOwned => write!(f, "shard owns no constants"),
      WitnessError::Unbound => {
        write!(f, "the environment carries no role binding")
      },
      WitnessError::TreeMismatch => {
        write!(f, "canonical tree root disagrees with the shard claim")
      },
      WitnessError::ClaimMismatch { expected, computed } => write!(
        f,
        "recomputed claim {computed:?} differs from expected claim {expected:?}"
      ),
    }
  }
}

impl std::error::Error for WitnessError {}

/// Recompute the claim for `request`, require it to equal `expected`, and
/// only then build its advice. The expected claim is never replaced: on a
/// mismatch no advice is produced.
pub fn prepare(
  env: &Env,
  request: WitnessRequest<'_>,
  expected: &Claim,
) -> Result<ClaimWitness, WitnessError> {
  let statement = Statement::new(env, request)?;
  if &statement.claim != expected {
    return Err(WitnessError::ClaimMismatch {
      expected: Box::new(expected.clone()),
      computed: Box::new(statement.claim),
    });
  }
  statement.into_witness(env)
}

/// The claim [`prepare`] would compare against, without building advice.
pub fn claim(
  env: &Env,
  request: WitnessRequest<'_>,
) -> Result<Claim, WitnessError> {
  Ok(Statement::new(env, request)?.claim)
}

/// The witness of `request`, whatever claim it recomputes.
pub fn witness(
  env: &Env,
  request: WitnessRequest<'_>,
) -> Result<ClaimWitness, WitnessError> {
  Statement::new(env, request)?.into_witness(env)
}

/// The context of a typing claim over `env`'s own role binding.
pub fn claim_context(
  env: &Env,
  assume_binding: bool,
) -> Result<ClaimContext, WitnessError> {
  let ctx = ClaimContext::for_env(env).map_err(|_unbound| WitnessError::Unbound)?;
  Ok(if assume_binding { ctx.assuming_binding() } else { ctx })
}

struct Statement<'a> {
  claim: Claim,
  roots: &'a [Address],
  trees: Vec<AssumptionTree>,
}

impl<'a> Statement<'a> {
  fn new(env: &Env, request: WitnessRequest<'a>) -> Result<Self, WitnessError> {
    match request {
      WitnessRequest::Check { target, assume_binding } => {
        Ok(Self::check(claim_context(env, assume_binding)?, target))
      },
      WitnessRequest::ShardCheckEnv { owned, assume_binding } => {
        Self::shard(&claim_context(env, assume_binding)?, env, owned)
      },
      WitnessRequest::Binding => Self::binding(env),
    }
  }

  fn check(ctx: ClaimContext, target: &'a Address) -> Self {
    Self {
      claim: Claim::Check {
        ctx,
        const_addr: target.clone(),
        assumptions: None,
      },
      roots: std::slice::from_ref(target),
      trees: Vec::new(),
    }
  }

  /// The scope of a binding claim is the primitives and the binding's
  /// roots alone, which [`witness_scope`] adds to every scope.
  fn binding(env: &Env) -> Result<Self, WitnessError> {
    let binding =
      env.role_binding.as_ref().ok_or(WitnessError::Unbound)?.address.clone();
    Ok(Self {
      claim: Claim::Binding { spec: spec_digest(), binding },
      roots: &[],
      trees: Vec::new(),
    })
  }

  fn shard(
    ctx: &ClaimContext,
    env: &Env,
    owned: &'a [Address],
  ) -> Result<Self, WitnessError> {
    let (claim, frontier) = shard_check_env_claim(ctx, env, owned)
      .ok_or(WitnessError::EmptyOwned)?;
    let subject =
      AssumptionTree::canonical(owned).ok_or(WitnessError::EmptyOwned)?;
    let assumptions = AssumptionTree::canonical(&frontier);
    let consistent = matches!(
      &claim,
      Claim::CheckEnv { root, assumptions: asm, .. }
        if *root == subject.root()
          && *asm == assumptions.as_ref().map(AssumptionTree::root)
    );
    if !consistent {
      return Err(WitnessError::TreeMismatch);
    }
    let mut trees = vec![subject];
    trees.extend(assumptions);
    Ok(Self { claim, roots: owned, trees })
  }

  fn into_witness(self, env: &Env) -> Result<ClaimWitness, WitnessError> {
    let binding = env.role_binding.as_ref().ok_or(WitnessError::Unbound)?;
    let mut claim_bytes = Vec::new();
    self.claim.put(&mut claim_bytes);
    let digest = Address::hash(&claim_bytes);
    let mut streams = vec![AdviceStream {
      channel: CLAIM_CHANNEL,
      key: StreamKey::ClaimDigest(digest.clone()),
      payload: Payload::Bytes(claim_bytes.clone().into()),
    }];
    streams.extend(self.trees.iter().map(tree_stream));
    streams.extend(scope_streams(env, &witness_scope(env, self.roots)));
    streams.push(AdviceStream {
      channel: ROLE_CHANNEL,
      key: StreamKey::Address(binding.address.clone()),
      payload: Payload::Bytes(BytesSource::Heap(binding.bytes.clone())),
    });
    Ok(ClaimWitness { claim: self.claim, claim_bytes, digest, streams })
  }
}

/// An assumption tree's channel 1 stream, keyed by its root.
pub fn tree_stream(tree: &AssumptionTree) -> AdviceStream {
  AdviceStream {
    channel: TREE_CHANNEL,
    key: StreamKey::Address(tree.root()),
    payload: Payload::Bytes(tree.ser().into()),
  }
}

/// Numeric reducibility hint: `Opaque → 0`, `Abbrev → 0xFFFF_FFFF`,
/// `Regular n → min(1 + n, 0xFFFF_FFFE)`, as the kernel's
/// `load_constant_hint` decodes it.
pub fn hint_tag(hint: &ReducibilityHints) -> u64 {
  match hint {
    ReducibilityHints::Opaque => 0,
    ReducibilityHints::Abbrev => 0xFFFF_FFFF,
    ReducibilityHints::Regular(n) => (1 + u64::from(*n)).min(0xFFFF_FFFE),
  }
}

/// Every primitive address the kernel can name: the Lean parity table and
/// the reserved reduction markers.
pub fn primitive_addresses() -> Vec<Address> {
  let mut addrs: Vec<Address> = PrimAddrs::lean_parity_table()
    .iter()
    .map(|(name, hex)| {
      Address::from_hex(hex)
        .unwrap_or_else(|| panic!("primitive {name}: invalid address hex"))
    })
    .collect();
  addrs.extend(
    PrimAddrs::reserved_marker_addrs().into_iter().map(|(_, addr)| addr),
  );
  addrs
}

/// The constants the role binding names: every bound role and every proof
/// evidence theorem, as far as the environment carries them. An absent or
/// unparsable binding names none. Mirrors `IxVM.ClaimHarness.bindingRoots`.
pub fn binding_roots(env: &Env) -> Vec<Address> {
  let Some(binding) = &env.role_binding else { return Vec::new() };
  let Ok(table) = RoleTable::from_bytes(&binding.bytes) else {
    return Vec::new();
  };
  table.records().filter(|a| env.consts.contains_key(*a)).cloned().collect()
}

/// The byte scope of a witness for `roots`: [`Env::bfs_closure`] of the
/// roots together with every primitive present in the environment and the
/// role binding's roots ([`binding_roots`]).
///
/// `bfs_closure` follows `refs`, each projection's block, and every
/// member and constructor wrapper a `Muts` block derives. The kernel's
/// `get_ci` synthesizes those wrapper addresses itself and faults their
/// bytes, so they ship even when no `refs` edge names them.
///
/// Primitives are walked as additional roots because the kernel fabricates
/// references to them while reducing (`Nat.succ`, `Bool.true`, string
/// literal constructors, ...), and definitional equality may unfold their
/// bodies, whose references are reachable from nowhere else.
pub fn witness_scope(env: &Env, roots: &[Address]) -> FxHashSet<Address> {
  let mut all_roots = roots.to_vec();
  all_roots.extend(
    primitive_addresses().into_iter().filter(|a| env.consts.contains_key(a)),
  );
  all_roots.extend(binding_roots(env));
  env.bfs_closure(&all_roots)
}

/// Channel 2, 3 and 4 streams for every address of `scope` the
/// environment carries, in stream order. Addresses the environment does
/// not carry produce no stream.
pub fn scope_streams(
  env: &Env,
  scope: &FxHashSet<Address>,
) -> Vec<AdviceStream> {
  let mut addrs: Vec<&Address> = scope.iter().collect();
  addrs.sort_unstable();
  let stream = |channel, addr: &Address, payload| AdviceStream {
    channel,
    key: StreamKey::Address(addr.clone()),
    payload,
  };
  let mut streams = Vec::new();
  for addr in &addrs {
    if let Some(constant) = env.consts.get(*addr) {
      let bytes = constant.bytes_source().clone();
      streams.push(stream(CONSTANT_CHANNEL, addr, Payload::Bytes(bytes)));
    }
  }
  for addr in &addrs {
    if let Some(hint) = env.anon_hints.get(*addr) {
      streams.push(stream(HINT_CHANNEL, addr, Payload::Tag(hint_tag(&hint))));
    }
  }
  for addr in &addrs {
    if let Some(blob) = env.blobs.get(*addr) {
      let bytes = BytesSource::from(blob.value().clone());
      streams.push(stream(BLOB_CHANNEL, addr, Payload::Bytes(bytes)));
    }
  }
  streams
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::constant::{
    Axiom, Constant, ConstantInfo, DefKind, Definition, MutConst,
  };
  use crate::expr::Expr;
  use ix_common::env::DefinitionSafety;
  use std::sync::Arc;

  fn axiom_using(refs: Vec<Address>) -> Constant {
    let mut typ: Arc<Expr> = Arc::new(Expr::Sort(0));
    for i in 0..refs.len() {
      typ = Arc::new(Expr::App(typ, Arc::new(Expr::Ref(i as u64, vec![]))));
    }
    Constant::with_tables(
      ConstantInfo::Axio(Axiom { is_unsafe: false, lvls: 0, typ }),
      Vec::new(),
      refs,
      Vec::new(),
    )
  }

  /// a -> b -> c, with `b` a dual-use constant/blob address and `c`
  /// carrying a hint, bound to a role table that binds `Nat` to `r`, a
  /// constant no other constant reaches.
  fn chain() -> (Env, Address, Address, Address, Address) {
    let mut env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    let r = Address::hash(b"r");
    env.store_const(a.clone(), axiom_using(vec![b.clone()]));
    env.store_const(b.clone(), axiom_using(vec![c.clone()]));
    env.store_const(c.clone(), axiom_using(vec![]));
    env.store_const(r.clone(), axiom_using(vec![]));
    env.blobs.insert(b.clone(), vec![7, 8, 9]);
    env.anon_hints.insert(c.clone(), ReducibilityHints::Regular(300));
    let bytes = RoleTable {
      version: 2,
      bound: vec![(crate::role_table::Role::Nat, r.clone())],
      evidence: vec![],
    }
    .to_bytes()
    .unwrap();
    env.role_binding = Some(crate::env::RoleBinding {
      address: Address::hash(&bytes),
      bytes: bytes.into(),
    });
    (env, a, b, c, r)
  }

  fn shard(owned: &[Address]) -> WitnessRequest<'_> {
    WitnessRequest::ShardCheckEnv { owned, assume_binding: false }
  }

  fn layout(w: &ClaimWitness) -> Vec<(u8, Vec<u64>, Vec<u64>)> {
    w.streams
      .iter()
      .map(|s| (s.channel, s.key.words(), s.payload.values()))
      .collect()
  }

  #[test]
  fn packed_digest_words_are_little_endian_u32() {
    let addr = Address::hash(b"digest");
    let words = packed_digest_words(&addr);
    let bytes = addr.as_bytes();
    assert_eq!(
      words[1],
      u64::from(bytes[4])
        | u64::from(bytes[5]) << 8
        | u64::from(bytes[6]) << 16
        | u64::from(bytes[7]) << 24
    );
  }

  #[test]
  fn hint_tags_keep_numeric_encoding() {
    assert_eq!(hint_tag(&ReducibilityHints::Opaque), 0);
    assert_eq!(hint_tag(&ReducibilityHints::Abbrev), 0xFFFF_FFFF);
    assert_eq!(hint_tag(&ReducibilityHints::Regular(300)), 301);
    assert_eq!(hint_tag(&ReducibilityHints::Regular(u32::MAX)), 0xFFFF_FFFE);
  }

  #[test]
  fn shard_witness_streams_follow_documented_order() {
    let (env, a, b, c, r) = chain();
    let owned = [a.clone()];
    let w = witness(&env, shard(&owned)).unwrap();
    let Claim::CheckEnv { ctx, root, assumptions: Some(asm) } = &w.claim else {
      panic!("unexpected claim {:?}", w.claim);
    };
    assert_eq!(*ctx, ClaimContext::for_env(&env).unwrap());
    let channels: Vec<u8> = w.streams.iter().map(|s| s.channel).collect();
    assert!(channels.is_sorted());
    assert_eq!(w.streams[0].key, StreamKey::ClaimDigest(w.digest.clone()));
    assert_eq!(w.streams[1].key, StreamKey::Address(root.clone()));
    assert_eq!(w.streams[2].key, StreamKey::Address(asm.clone()));
    let constants: Vec<&StreamKey> = w
      .streams
      .iter()
      .filter(|s| s.channel == CONSTANT_CHANNEL)
      .map(|s| &s.key)
      .collect();
    // The bound role `r` ships although nothing the shard owns reaches it.
    let mut sorted = vec![a.clone(), b.clone(), c.clone(), r];
    sorted.sort();
    let expected: Vec<StreamKey> =
      sorted.into_iter().map(StreamKey::Address).collect();
    assert_eq!(constants, expected.iter().collect::<Vec<_>>());
    // The dual-use address is seeded as both a constant and a blob, and
    // the scope reaches below the thin frontier ({b}) to c's hint.
    assert!(w.streams.iter().any(|s| s.channel == BLOB_CHANNEL
      && s.key == StreamKey::Address(b.clone())
      && s.payload.values() == vec![7, 8, 9]));
    assert!(w.streams.iter().any(|s| s.channel == HINT_CHANNEL
      && s.key == StreamKey::Address(c.clone())
      && s.payload.values() == vec![301]));
    let binding = env.role_binding.as_ref().unwrap();
    let last = w.streams.last().unwrap();
    assert_eq!(last.channel, ROLE_CHANNEL);
    assert_eq!(last.key, StreamKey::Address(binding.address.clone()));
    assert_eq!(
      last.payload.values(),
      binding.bytes.iter().map(|b| u64::from(*b)).collect::<Vec<_>>()
    );
    assert_eq!(layout(&w), layout(&witness(&env, shard(&owned)).unwrap()));
  }

  #[test]
  fn constant_payloads_share_environment_storage() {
    let (env, a, _, _, _) = chain();
    let w = witness(
      &env,
      WitnessRequest::Check { target: &a, assume_binding: false },
    )
    .unwrap();
    let stream = w
      .streams
      .iter()
      .find(|s| {
        s.channel == CONSTANT_CHANNEL && s.key == StreamKey::Address(a.clone())
      })
      .unwrap();
    let Payload::Bytes(bytes) = &stream.payload else { panic!() };
    assert_eq!(
      bytes.as_slice().as_ptr(),
      env.consts.get(&a).unwrap().raw_bytes().as_ptr()
    );
  }

  #[test]
  fn prepare_rejects_a_different_expected_claim() {
    let (env, a, b, _, _) = chain();
    let ctx = ClaimContext::for_env(&env).unwrap();
    let check = WitnessRequest::Check { target: &a, assume_binding: false };
    let expected =
      Claim::Check { ctx: ctx.clone(), const_addr: b, assumptions: None };
    let err = prepare(&env, check, &expected).unwrap_err();
    assert!(matches!(err, WitnessError::ClaimMismatch { .. }));

    let owned = [a.clone()];
    let computed = claim(&env, shard(&owned)).unwrap();
    let Claim::CheckEnv { root, .. } = computed.clone() else { panic!() };
    let without_assumptions =
      Claim::CheckEnv { ctx: ctx.clone(), root, assumptions: None };
    assert!(prepare(&env, shard(&owned), &without_assumptions).is_err());
    // An assumed binding is part of the claim.
    let assumed =
      WitnessRequest::ShardCheckEnv { owned: &owned, assume_binding: true };
    assert!(prepare(&env, assumed, &computed).is_err());
    let w = prepare(&env, shard(&owned), &computed).unwrap();
    assert_eq!(w.claim, computed);
    assert_eq!(
      prepare(&env, shard(&[]), &computed).unwrap_err(),
      WitnessError::EmptyOwned
    );
    let mut unbound = env.clone();
    unbound.role_binding = None;
    assert_eq!(
      claim(&unbound, shard(&owned)).unwrap_err(),
      WitnessError::Unbound
    );
  }

  #[test]
  fn binding_witness_ships_the_binding_roots() {
    let (env, a, _, _, r) = chain();
    let w = witness(&env, WitnessRequest::Binding).unwrap();
    let binding = env.role_binding.as_ref().unwrap().address.clone();
    assert_eq!(w.claim, Claim::Binding { spec: spec_digest(), binding });
    let has = |x: &Address| {
      w.streams.iter().any(|s| {
        s.channel == CONSTANT_CHANNEL && s.key == StreamKey::Address(x.clone())
      })
    };
    assert!(has(&r) && !has(&a));
    assert!(!w.streams.iter().any(|s| s.channel == TREE_CHANNEL));
  }

  /// The kernel faults the wrapper addresses of every `Muts` block it
  /// loads, so the scope must carry them although no `refs` edge names
  /// them.
  #[test]
  fn scope_carries_synthesized_projection_wrappers() {
    let (env, _, _, _, _) = chain();
    let block = Address::hash(b"block");
    let defn = Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Arc::new(Expr::Sort(0)),
      value: Arc::new(Expr::Sort(0)),
    };
    env.store_const(
      block.clone(),
      Constant::new(ConstantInfo::Muts(vec![MutConst::Defn(defn)])),
    );
    let wrapper = crate::constant::defn_proj_address(0, &block);
    env.store_const(
      wrapper.clone(),
      crate::constant::defn_proj_constant(0, block.clone()),
    );
    let w = witness(
      &env,
      WitnessRequest::Check { target: &block, assume_binding: false },
    )
    .unwrap();
    assert!(w.streams.iter().any(|s| s.channel == CONSTANT_CHANNEL
      && s.key == StreamKey::Address(wrapper.clone())));
  }
}
