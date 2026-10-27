//! Native role admission. Wire decoding, candidate preparation and semantic
//! admission are distinct boundaries: a prepared source authenticates its
//! binding and every bound record, and only the group validators in
//! `groups` admit roles, a whole specification group at a time.
//!
//! # The certified checker's frontend, as this kernel reads it
//!
//! The certified checker reads an artifact as a stream folded in order, with
//! a committed prelude in front. Its frontend has six checks this kernel must
//! match. This kernel reads an artifact as content-addressed units checked
//! independently, with the bound roles admitted first, so each check is
//! either enforced here or ruled out by that representation:
//!
//! - **The prelude's shape** (the prelude names the pinned prelude roles) and
//!   **the prelude copy** (a stream may not hold, at a prelude key, anything
//!   but the prelude's entry): every prelude role ([`PRELUDE`]) must be bound
//!   and its group admitted, or no unit of the artifact is checked
//!   ([`ArtifactSource::prelude_refusal`]). The prelude's records are not
//!   compared with a committed copy: the group validators compare them with
//!   the same specifications the committed prelude was checked against, and
//!   a bound address holds exactly one record.
//! - **The rest-only hoist** and **the hoist guard** reorder a stream so that a
//!   `Nat` operation's ground precedes it, outside the prelude and without
//!   splitting a unit. Nothing here depends on order: groups are admitted in
//!   dependency order before any unit is checked, whatever order the records
//!   come in, and units are never split or merged.
//! - **The units check** declines a basis record of the fold's own, a unit out
//!   of shape, a prelude role declared past the front, and two units declaring
//!   a common base. This kernel has no fold-own records and no generated model
//!   records; a unit is a serialized record, whose recursive targets come from
//!   the unit itself; a role's records are its bound addresses, one record
//!   each; and a projection is authenticated against the one owner its address
//!   commits to, so no two units declare one declaration.
//! - **The inferer's fuel** bounds the checker's untyped inference over model
//!   records. This kernel has no untyped inference: every inference and
//!   reduction is typed and bounded by fuel, the WHNF step limit and the stack
//!   check, so a non-terminating head β in a declared type declines.

use std::sync::{Arc, OnceLock};

use ix_common::address::Address;
use ix_common::env::DefinitionSafety;
use ixon::constant::{Constant, ConstantInfo, DefKind, Definition, MutConst};
use ixon::env::{Env, RoleBinding};
use ixon::lazy::LazyConstant;
use ixon::role_table::{Evidence, Role, RoleTable};
use rustc_hash::{FxHashMap, FxHashSet};

/// Current IxC specification version; the wire codec deliberately accepts more.
pub const SPEC_VERSION: u8 = 2;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
  Binding(String),
  Unbound,
  MissingRole(Role),
  MissingRecord(Address),
  Record(Address, String),
  Member(Address, &'static str),
  NotTheorem(Address),
  MissingBlob(Address),
  BlobHash(Address),
}

impl std::fmt::Display for Error {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Binding(reason) => write!(f, "role binding: {reason}"),
      Self::Unbound => write!(f, "artifact has no role binding"),
      Self::MissingRole(role) => write!(f, "role binding: missing {role:?}"),
      Self::MissingRecord(a) => {
        write!(f, "role source: missing record {}", a.hex())
      },
      Self::Record(a, reason) => {
        write!(f, "role source: record {}: {reason}", a.hex())
      },
      Self::Member(a, reason) => {
        write!(f, "role source: member {}: {reason}", a.hex())
      },
      Self::NotTheorem(a) => {
        write!(f, "role source: proof {} is not a safe theorem", a.hex())
      },
      Self::MissingBlob(a) => {
        write!(f, "role source: missing blob {}", a.hex())
      },
      Self::BlobHash(a) => {
        write!(f, "role source: blob {} hash mismatch", a.hex())
      },
    }
  }
}
impl std::error::Error for Error {}

static ALL_ROLES: [Role; 59] = Role::ALL;

// Exactly Role.block/deps and Spec.evidenceKinds in IxC/Kernel/Roles.lean.
// These describe candidate well-formedness, not declaration specifications.
fn block(role: Role) -> &'static [Role] {
  use Role::{
    And, AndIntro, AndRec, Bool, BoolFalse, BoolRec, BoolTrue, Empty, EmptyRec,
    Eq, EqRec, EqRefl, False, FalseRec, Iff, IffIntro, IffRec, List, ListCons,
    ListNil, Nat, NatRec, NatSucc, NatZero, Nonempty, NonemptyIntro,
    NonemptyRec, PUnit, PUnitRec, PUnitUnit, Quot, QuotInd, QuotLift, QuotMk,
    QuotSound, True, TrueIntro,
  };
  match role {
    Nat | NatZero | NatSucc | NatRec => &[Nat, NatZero, NatSucc, NatRec],
    Bool | BoolFalse | BoolTrue | BoolRec => {
      &[Bool, BoolFalse, BoolTrue, BoolRec]
    },
    Eq | EqRefl | EqRec => &[Eq, EqRefl, EqRec],
    PUnit | PUnitUnit | PUnitRec => &[PUnit, PUnitUnit, PUnitRec],
    Empty | EmptyRec => &[Empty, EmptyRec],
    False | FalseRec => &[False, FalseRec],
    True | TrueIntro => &[True, TrueIntro],
    And | AndIntro | AndRec => &[And, AndIntro, AndRec],
    Iff | IffIntro | IffRec => &[Iff, IffIntro, IffRec],
    Nonempty | NonemptyIntro | NonemptyRec => {
      &[Nonempty, NonemptyIntro, NonemptyRec]
    },
    List | ListNil | ListCons => &[List, ListNil, ListCons],
    Quot | QuotMk | QuotLift | QuotInd | QuotSound => {
      &[Quot, QuotMk, QuotLift, QuotInd, QuotSound]
    },
    _ => &ALL_ROLES[usize::from(role.index())..=usize::from(role.index())],
  }
}

fn dependencies(role: Role) -> &'static [Role] {
  use Role::{
    Bool, Char, CharOfNat, Choice, Eq, Iff, List, Nat, NatAdd, NatBeq, NatBle,
    NatDiv, NatGcd, NatLand, NatLor, NatMod, NatMul, NatPow, NatPred,
    NatShiftLeft, NatShiftRight, NatSub, NatXor, Nonempty, Propext, Quot,
    QuotInd, QuotLift, QuotMk, QuotSound, String, StringOfList,
  };
  match role {
    Quot | QuotMk | QuotLift | QuotInd | QuotSound => &[Eq],
    StringOfList => &[List, Char, String],
    CharOfNat => &[Nat, Char],
    NatPred | NatAdd => &[Nat],
    NatSub => &[Nat, NatPred],
    NatMul => &[Nat, NatAdd],
    NatPow => &[Nat, NatAdd, NatMul],
    NatBeq | NatBle => &[Nat, Bool],
    NatDiv | NatMod => &[Nat, NatPred, NatSub, NatBle, Bool, Eq],
    NatGcd => &[Nat, NatBle, NatMod, Bool, Eq],
    NatLand | NatXor => {
      &[Nat, NatAdd, NatMul, NatBle, NatDiv, NatMod, Bool, Eq]
    },
    NatLor => &[Nat, NatAdd, NatSub, NatMul, NatBle, NatDiv, NatMod, Bool, Eq],
    NatShiftLeft => &[Nat, NatSub, NatMul, NatBle, Bool, Eq],
    NatShiftRight => &[Nat, NatSub, NatBle, NatDiv, Bool, Eq],
    Propext => &[Iff, Eq],
    Choice => &[Nonempty],
    _ => &[],
  }
}

fn evidence_shape(role: Role) -> (usize, bool) {
  use Role::{
    NatAdd, NatBeq, NatBle, NatDiv, NatGcd, NatLand, NatLor, NatMod, NatMul,
    NatPow, NatPred, NatShiftLeft, NatShiftRight, NatSub, NatXor,
  };
  match role {
    NatPred | NatAdd | NatSub | NatMul | NatPow => (2, true),
    NatBeq => (4, true),
    NatBle => (3, true),
    NatDiv | NatMod => (3, false),
    NatGcd | NatLand | NatLor | NatXor | NatShiftLeft | NatShiftRight => {
      (2, false)
    },
    _ => (0, false),
  }
}

/// Authentication and table well-formedness only. There is no public unchecked
/// constructor, and obtaining this value does not authorize any native rule.
#[derive(Debug)]
pub struct BindingCandidate {
  raw: RoleBinding,
  table: RoleTable,
}

impl BindingCandidate {
  fn prepare(raw: RoleBinding) -> Result<Self, Error> {
    raw.check_hash().map_err(Error::Binding)?;
    let table = RoleTable::from_bytes(&raw.bytes).map_err(Error::Binding)?;
    if table.version != SPEC_VERSION {
      return Err(Error::Binding(format!(
        "unsupported specification version {}",
        table.version
      )));
    }
    let mut roles = FxHashSet::default();
    let mut addresses = FxHashSet::default();
    for (role, address) in &table.bound {
      if !roles.insert(*role) || !addresses.insert(address) {
        return Err(Error::Binding("repeated bound role or address".into()));
      }
    }
    for (role, _) in &table.bound {
      for required in block(*role).iter().chain(dependencies(*role)) {
        if !roles.contains(required) {
          return Err(Error::Binding(format!(
            "{role:?} requires {required:?}"
          )));
        }
      }
    }
    let mut evidence_roles = FxHashSet::default();
    for (role, evidence) in &table.evidence {
      let (count, defeq) = evidence_shape(*role);
      if !roles.contains(role)
        || !evidence_roles.insert(*role)
        || count == 0
        || evidence.len() != count
        || evidence
          .iter()
          .any(|entry| matches!(entry, Evidence::DefEq) != defeq)
      {
        return Err(Error::Binding(format!(
          "evidence does not match {role:?}'s specification"
        )));
      }
    }
    for role in roles {
      if evidence_shape(role).0 != 0 && !evidence_roles.contains(&role) {
        return Err(Error::Binding(format!(
          "operation {role:?} has no evidence"
        )));
      }
    }
    Ok(Self { raw, table })
  }

  pub fn address(&self) -> &Address {
    &self.raw.address
  }
  pub fn bytes(&self) -> &[u8] {
    &self.raw.bytes
  }
  pub fn role(&self, role: Role) -> Option<&Address> {
    self.table.bound.iter().find_map(|(r, a)| (*r == role).then_some(a))
  }
  pub fn required(&self, role: Role) -> Result<&Address, Error> {
    self.role(role).ok_or(Error::MissingRole(role))
  }
  pub fn evidence(&self, role: Role) -> Option<&[Evidence]> {
    self
      .table
      .evidence
      .iter()
      .find_map(|(r, es)| (*r == role).then_some(es.as_slice()))
  }
}

#[derive(Debug)]
struct Source {
  env: Env,
  blobs: FxHashMap<Address, Arc<Vec<u8>>>,
  candidate: Option<BindingCandidate>,
  lookups: OnceLock<Arc<crate::ingress::IxonIngressLookups>>,
  owners: OnceLock<Result<FxHashMap<Address, Vec<Role>>, Error>>,
  /// Addresses whose carried record (and, for a projection, its owner and
  /// position) has been authenticated. Authentication is a function of this
  /// immutable source alone, so a success is shared by every worker.
  references: dashmap::DashSet<Address>,
  /// The roles this source's binding has admitted, computed once by the
  /// group validators (see [`ArtifactSource::admission`]).
  admission: OnceLock<Admission>,
}

/// The stack of the thread that validates a source's groups.
const ADMISSION_STACK_SIZE: usize = 256 * 1024 * 1024;

/// The outcome of admitting a source's bound roles: each group is admitted
/// whole, only after its validator has checked it, or not at all.
#[derive(Debug, Default)]
pub struct Admission {
  roles: FxHashMap<Role, Address>,
  refused: Vec<(Role, String)>,
}

impl Admission {
  /// The bound address of `role`, if its group was admitted.
  pub fn address(&self, role: Role) -> Option<&Address> {
    self.roles.get(&role)
  }
  /// The number of admitted roles.
  pub fn admitted_count(&self) -> usize {
    self.roles.len()
  }
  /// Every admitted role with its bound address.
  pub(crate) fn roles(&self) -> &FxHashMap<Role, Address> {
    &self.roles
  }
  /// Each bound group that was not admitted, by its first role, with the
  /// reason.
  pub fn refused(&self) -> &[(Role, String)] {
    &self.refused
  }
}

/// The prelude's roles: the certified checker's prelude shape, the blocks of
/// its committed prelude (Eq, Nat, PUnit, Empty, False, the quotient package,
/// And and Bool). A bound artifact must bind and admit all of them.
pub const PRELUDE: [Role; 26] = [
  Role::Eq,
  Role::EqRefl,
  Role::EqRec,
  Role::Nat,
  Role::NatZero,
  Role::NatSucc,
  Role::NatRec,
  Role::PUnit,
  Role::PUnitUnit,
  Role::PUnitRec,
  Role::Empty,
  Role::EmptyRec,
  Role::False,
  Role::FalseRec,
  Role::Quot,
  Role::QuotMk,
  Role::QuotLift,
  Role::QuotInd,
  Role::QuotSound,
  Role::And,
  Role::AndIntro,
  Role::AndRec,
  Role::Bool,
  Role::BoolFalse,
  Role::BoolTrue,
  Role::BoolRec,
];

/// One privately owned input, shared cheaply between workers. No Env reference
/// escapes this API: its DashMaps must not become a mutable admission input.
/// Record backing buffers retain the loader's immutable heap/mmap contract.
#[derive(Clone, Debug)]
pub struct ArtifactSource(Arc<Source>);

impl ixon::resource::addressed::RawSource for ArtifactSource {
  fn constants(&self) -> Vec<(Address, LazyConstant)> {
    self
      .0
      .env
      .consts
      .iter()
      .map(|entry| (entry.key().clone(), entry.value().clone()))
      .collect()
  }
  fn blobs(&self) -> Vec<(Address, Vec<u8>)> {
    self
      .0
      .blobs
      .iter()
      .map(|(address, bytes)| (address.clone(), bytes.as_ref().clone()))
      .collect()
  }
}

impl ArtifactSource {
  pub fn prepare(mut env: Env) -> Result<Self, Error> {
    let candidate =
      env.role_binding.clone().map(BindingCandidate::prepare).transpose()?;
    let blobs = std::mem::take(&mut env.blobs)
      .into_iter()
      .map(|(address, bytes)| (address, Arc::new(bytes)))
      .collect();
    let source = Self(Arc::new(Source {
      env,
      blobs,
      candidate,
      lookups: OnceLock::new(),
      owners: OnceLock::new(),
      references: dashmap::DashSet::new(),
      admission: OnceLock::new(),
    }));
    if let Some(binding) = source.binding() {
      for (_, address) in &binding.table.bound {
        source.member(address)?;
      }
      for (_, entries) in &binding.table.evidence {
        for entry in entries {
          if let Evidence::Proof(address) = entry {
            source.proof_record(address)?;
          }
        }
      }
    }
    Ok(source)
  }

  /// Capture a borrowed input once, before sharing the result. The caller must
  /// prevent concurrent map mutation during Env::clone; afterwards maps are
  /// independent, constant buffers shared, and blob vectors copied only once.
  pub fn snapshot(env: &Env) -> Result<Self, Error> {
    Self::prepare(env.clone())
  }
  pub fn binding(&self) -> Option<&BindingCandidate> {
    self.0.candidate.as_ref()
  }
  pub fn same_source(&self, other: &Self) -> bool {
    Arc::ptr_eq(&self.0, &other.0)
  }
  pub fn required_role(&self, role: Role) -> Result<&Address, Error> {
    self.binding().ok_or(Error::Unbound)?.required(role)
  }

  /// The roles admitted for this source. Computed once, by validating each
  /// bound group in dependency order with only the groups admitted before
  /// it available; every worker sharing this source reads the result.
  pub fn admission(&self) -> &Admission {
    self.0.admission.get_or_init(|| {
      // Validation runs the kernel; give it the stack a check gets.
      std::thread::scope(|scope| {
        std::thread::Builder::new()
          .name("role-admission".into())
          .stack_size(ADMISSION_STACK_SIZE)
          .spawn_scoped(scope, || groups::admit(self))
          .expect("spawn the role admission thread")
          .join()
          .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
      })
    })
  }
  /// Whether `role`'s group has been admitted.
  pub fn is_admitted(&self, role: Role) -> bool {
    self.admission().address(role).is_some()
  }
  /// Why a bound artifact's units may not be checked, if they may not: a
  /// prelude role ([`PRELUDE`]) that is unbound, or whose group was refused.
  pub fn prelude_refusal(&self) -> Option<String> {
    let binding = self.binding()?;
    let role = PRELUDE.into_iter().find(|role| !self.is_admitted(*role))?;
    Some(if binding.role(role).is_none() {
      format!("the binding does not bind the prelude role {}", role.lean_name())
    } else {
      format!("the prelude role {} is not admitted", role.lean_name())
    })
  }
  /// The capability to use `role`'s rules, issued only for an admitted role.
  pub fn capability(&self, role: Role) -> Option<AdmittedRole> {
    self.is_admitted(role).then(|| AdmittedRole { source: self.clone(), role })
  }

  // Metadata is taken from the same captured input. These narrow views do not
  // expose an Env/DashMap that could mutate admission's source or read caches.
  pub(crate) fn contains_record(&self, address: &Address) -> bool {
    self.0.env.consts.contains_key(address)
  }
  pub(crate) fn addresses(&self) -> Vec<Address> {
    self.0.env.consts.iter().map(|entry| entry.key().clone()).collect()
  }
  pub(crate) fn record_tag(
    &self,
    address: &Address,
  ) -> Result<ixon::lazy::ConstVariantTag, Error> {
    self
      .raw_record(address)?
      .peek_variant()
      .map_err(|reason| Error::Record(address.clone(), reason))
  }
  pub(crate) fn named(
    &self,
    name: &ix_common::env::Name,
  ) -> Option<ixon::env::Named> {
    self.0.env.lookup_name(name)
  }
  pub(crate) fn name(&self, address: &Address) -> Option<ix_common::env::Name> {
    self.0.env.get_name(address)
  }
  pub(crate) fn hint(
    &self,
    address: &Address,
  ) -> Option<ix_common::env::ReducibilityHints> {
    self.0.env.anon_hints.get(address).map(|entry| *entry)
  }
  pub(crate) fn lookups(&self) -> Arc<crate::ingress::IxonIngressLookups> {
    Arc::clone(self.0.lookups.get_or_init(|| {
      Arc::new(crate::ingress::build_ixon_ingress_lookups(&self.0.env))
    }))
  }
  pub(crate) fn unit_roles(&self, address: &Address) -> Result<&[Role], Error> {
    let owners = self
      .0
      .owners
      .get_or_init(|| {
        let mut owners: FxHashMap<Address, Vec<Role>> = FxHashMap::default();
        if let Some(binding) = self.binding() {
          for (role, address) in &binding.table.bound {
            let member = self.member(address)?;
            let owner =
              member.owner().unwrap_or(member.record()).address().clone();
            owners.entry(owner).or_default().push(*role);
          }
        }
        Ok(owners)
      })
      .as_ref()
      .map_err(Clone::clone)?;
    let record = self.record(address)?;
    let owner = match &record.constant().info {
      ConstantInfo::IPrj(p) => &p.block,
      ConstantInfo::CPrj(p) => &p.block,
      ConstantInfo::RPrj(p) => &p.block,
      ConstantInfo::DPrj(p) => &p.block,
      _ => address,
    };
    Ok(owners.get(owner).map_or(&[][..], Vec::as_slice))
  }
  pub fn block_of(&self, address: &Address) -> Result<Address, Error> {
    let record = self.record(address)?;
    Ok(match &record.constant().info {
      ConstantInfo::IPrj(p) => p.block.clone(),
      ConstantInfo::CPrj(p) => p.block.clone(),
      ConstantInfo::RPrj(p) => p.block.clone(),
      ConstantInfo::DPrj(p) => p.block.clone(),
      _ => address.clone(),
    })
  }
  pub fn closure(
    &self,
    roots: &[Address],
  ) -> Result<FxHashSet<Address>, Error> {
    let mut pending = roots.to_vec();
    let mut seen = FxHashSet::default();
    while let Some(address) = pending.pop() {
      if !seen.insert(address.clone()) {
        continue;
      }
      if self.contains_record(&address) {
        let record = self.record(&address)?;
        Env::closure_edges(&address, record.constant(), &mut pending);
      }
      if self.0.blobs.contains_key(&address) {
        self.blob(&address)?;
      }
    }
    Ok(seen)
  }

  /// Every later admission read, including transitive support, enters here.
  /// Authenticate exact raw bytes and decode them without LazyConstant::get,
  /// even if the compiler supplied an already materialized Constant cache.
  fn raw_record(&self, address: &Address) -> Result<LazyConstant, Error> {
    let raw = self
      .0
      .env
      .consts
      .get(address)
      .map(|entry| entry.value().clone())
      .ok_or_else(|| Error::MissingRecord(address.clone()))?;
    if Address::hash(raw.raw_bytes()) != *address {
      return Err(Error::Record(address.clone(), "hash mismatch".into()));
    }
    Ok(raw)
  }

  pub fn record(&self, address: &Address) -> Result<Record, Error> {
    let raw = self.raw_record(address)?;
    let bytes = raw.raw_bytes();
    let fail = |reason| Error::Record(address.clone(), reason);
    let mut input = bytes;
    let value = Constant::get(&mut input).map_err(fail)?;
    let mut canonical = Vec::new();
    value.put(&mut canonical);
    if !input.is_empty() || canonical != bytes {
      return Err(fail("noncanonical bytes".into()));
    }
    Ok(Record { address: address.clone(), raw, value })
  }

  pub fn blob(&self, address: &Address) -> Result<Blob, Error> {
    let bytes = self
      .0
      .blobs
      .get(address)
      .ok_or_else(|| Error::MissingBlob(address.clone()))?;
    if Address::hash(bytes) != *address {
      return Err(Error::BlobHash(address.clone()));
    }
    Ok(Blob { address: address.clone(), bytes: Arc::clone(bytes) })
  }

  /// Resolve physical projection/owner provenance, not semantic role identity.
  pub fn member(&self, address: &Address) -> Result<Member, Error> {
    let record = self.record(address)?;
    let fail = |reason| Error::Member(address.clone(), reason);
    use ConstantInfo as C;
    let (owner, index, ctor, kind) = match &record.value.info {
      C::IPrj(p) => (&p.block, p.idx, None, 0),
      C::CPrj(p) => (&p.block, p.idx, Some(p.cidx), 0),
      C::RPrj(p) => (&p.block, p.idx, None, 1),
      C::DPrj(p) => (&p.block, p.idx, None, 2),
      C::Muts(_) => return Err(fail("a block is not a member")),
      _ => {
        return Ok(Member {
          record,
          owner: None,
          index: None,
          constructor: None,
        });
      },
    };
    if !record.value.refs.is_empty()
      || !record.value.sharing.is_empty()
      || !record.value.univs.is_empty()
    {
      return Err(fail("projection carries nonempty tables"));
    }
    let index = usize::try_from(index)
      .map_err(|_error| fail("member index overflows"))?;
    let constructor = ctor
      .map(usize::try_from)
      .transpose()
      .map_err(|_error| fail("constructor index overflows"))?;
    let owner = self.record(owner)?;
    let C::Muts(members) = &owner.value.info else {
      return Err(fail("owner is not a mutual block"));
    };
    match (kind, members.get(index)) {
      (0, Some(MutConst::Indc(inductive))) => {
        if let Some(i) = constructor {
          let Some(c) = inductive.ctors.get(i) else {
            return Err(fail("constructor is missing"));
          };
          if Some(c.cidx) != ctor {
            return Err(fail("constructor index differs"));
          }
        }
      },
      (1, Some(MutConst::Recr(_))) | (2, Some(MutConst::Defn(_))) => {},
      _ => return Err(fail("projection kind/index differs from owner")),
    }
    Ok(Member { record, owner: Some(owner), index: Some(index), constructor })
  }

  /// Authenticate the carried record a reference names: its bytes hash to
  /// the address and decode canonically, and a projection is the member of
  /// its owner at its index (see [`Self::member`]). Key presence alone is not
  /// enough: a worker may already hold a declaration for the address, built
  /// from an owner payload, which must not stand in for a corrupted record.
  pub(crate) fn authenticate_reference(
    &self,
    address: &Address,
  ) -> Result<(), Error> {
    if self.0.references.contains(address) {
      return Ok(());
    }
    self.member(address)?;
    self.0.references.insert(address.clone());
    Ok(())
  }

  /// Only raw theorem-kind/owner coverage is established here. Its value and
  /// certificate statement still require isolated semantic admission.
  pub fn proof_record(&self, address: &Address) -> Result<Member, Error> {
    let member = self.member(address)?;
    if !member.definition().is_some_and(|d| {
      d.kind == DefKind::Theorem && d.safety == DefinitionSafety::Safe
    }) {
      return Err(Error::NotTheorem(address.clone()));
    }
    Ok(member)
  }
}

/// Genuine canonical bytes and their decoded payload. Neither type nor value
/// has been checked. The raw buffer is retained alongside its claimed key.
#[derive(Debug)]
pub struct Record {
  address: Address,
  raw: LazyConstant,
  value: Constant,
}
impl Record {
  pub fn address(&self) -> &Address {
    &self.address
  }
  pub fn bytes(&self) -> &[u8] {
    self.raw.raw_bytes()
  }
  pub fn constant(&self) -> &Constant {
    &self.value
  }
  pub(crate) fn into_constant(self) -> Constant {
    self.value
  }
}

#[derive(Debug)]
pub struct Blob {
  address: Address,
  bytes: Arc<Vec<u8>>,
}
impl Blob {
  pub fn address(&self) -> &Address {
    &self.address
  }
  pub fn bytes(&self) -> &[u8] {
    &self.bytes
  }
}

#[derive(Debug)]
pub struct Member {
  record: Record,
  owner: Option<Record>,
  index: Option<usize>,
  constructor: Option<usize>,
}
impl Member {
  pub fn record(&self) -> &Record {
    &self.record
  }
  pub fn owner(&self) -> Option<&Record> {
    self.owner.as_ref()
  }
  pub fn index(&self) -> Option<usize> {
    self.index
  }
  pub fn constructor_index(&self) -> Option<usize> {
    self.constructor
  }
  pub fn definition(&self) -> Option<&Definition> {
    if self.constructor.is_some() {
      return None;
    }
    match (&self.owner, self.index, &self.record.value.info) {
      (None, None, ConstantInfo::Defn(d)) => Some(d),
      (Some(owner), Some(i), _) => match &owner.value.info {
        ConstantInfo::Muts(ms) => match ms.get(i) {
          Some(MutConst::Defn(d)) => Some(d),
          _ => None,
        },
        _ => None,
      },
      _ => None,
    }
  }
}

/// The capability to use one role's rules for one source. Only
/// [`ArtifactSource::capability`] issues it, and only for a role whose group
/// its validator admitted; there is no other constructor, no
/// Default/deserialize implementation and no public field, so a decoded or
/// authenticated candidate cannot create one.
/// ```compile_fail
/// use ix_kernel::role_admission::AdmittedRole;
/// let rule: AdmittedRole = Default::default();
/// ```
/// ```compile_fail
/// use ix_kernel::role_admission::{AdmittedRole, ArtifactSource};
/// use ixon::{env::Env, role_table::Role};
/// let source = ArtifactSource::prepare(Env::new()).unwrap();
/// let rule = AdmittedRole { source, role: Role::Nat };
/// ```
pub struct AdmittedRole {
  source: ArtifactSource,
  role: Role,
}
impl AdmittedRole {
  pub fn role(&self) -> Role {
    self.role
  }
  pub fn belongs_to(&self, source: &ArtifactSource) -> bool {
    self.source.same_source(source)
  }
}

mod groups;

#[cfg(test)]
mod tests;
