//! Group validators. Each admits one specification group of a binding (a
//! basis block: an inductive with its constructors and recursor) for a
//! source, or refuses it with a reason.
//!
//! A group is admitted only when
//! 1. every bound role of the group authenticates as a member of one
//!    carried owner unit, at the positions the specification fixes, and the
//!    unit holds nothing else;
//! 2. the unit's declarations, read in a fresh anonymous environment, are
//!    exactly the specified ones (the certified checker's basis blocks)
//!    built from the bound addresses; and
//! 3. the kernel checks the whole unit in that environment, with only the
//!    groups admitted before this one available, so none of the group's
//!    own rules can be used to check it.
//!
//! The roles are then admitted together. Nothing outside this module
//! creates an admission.

use ix_common::address::Address;
use ixon::constant::{ConstantInfo, MutConst};
use ixon::role_table::Role;

use super::{Admission, ArtifactSource};
use crate::constant::KConst;
use crate::env::KEnv;
use crate::expr::KExpr;
use crate::id::KId;
use crate::ingress::{IxonIngressLookups, ingress_anon_addr_shallow_input};
use crate::input::Input;
use crate::level::KUniv;
use crate::mode::Anon;
use crate::primitive_context::PrimitiveContext;
use crate::tc::TypeChecker;

type E = KExpr<Anon>;
type U = KUniv<Anon>;

/// One specification group.
struct Group {
  /// Its roles, the inductive first.
  roles: &'static [Role],
  /// The lead roles of the groups its specification mentions.
  needs: &'static [Role],
  validate: fn(&ArtifactSource, &Admission) -> Result<(), String>,
}

/// The groups, in an order that lists every group after those it needs.
const GROUPS: &[Group] = &[Group {
  roles: &[Role::Nat, Role::NatZero, Role::NatSucc, Role::NatRec],
  needs: &[],
  validate: validate_nat,
}];

/// Admit every bound group of `source` that its validator accepts.
pub(super) fn admit(source: &ArtifactSource) -> Admission {
  let mut admission = Admission::default();
  let Some(binding) = source.binding() else {
    return admission;
  };
  for group in GROUPS {
    let lead = group.roles[0];
    if binding.role(lead).is_none() {
      continue;
    }
    let missing: Vec<Role> = group
      .needs
      .iter()
      .copied()
      .filter(|role| admission.address(*role).is_none())
      .collect();
    let outcome = if missing.is_empty() {
      (group.validate)(source, &admission)
    } else {
      Err(format!("needs the unadmitted group(s) {missing:?}"))
    };
    match outcome {
      Ok(()) => {
        for role in group.roles {
          if let Some(address) = binding.role(*role) {
            admission.roles.insert(*role, address.clone());
          }
        }
      },
      Err(reason) => admission.refused.push((lead, reason)),
    }
  }
  admission
}

fn bound<const N: usize>(
  source: &ArtifactSource,
  roles: [Role; N],
) -> Result<[Address; N], String> {
  let mut out = Vec::with_capacity(N);
  for role in roles {
    out.push(
      source.required_role(role).map_err(|error| error.to_string())?.clone(),
    );
  }
  out.try_into().map_err(|_error| "role count".to_string())
}

/// Locate the carried records of an inductive basis block. `inductive` is
/// member `i` of an owner unit holding only it and any of `recursors` that
/// are members (a recursor may instead be its own standalone record), and
/// `constructors[c]` is constructor `c` of member `i`.
fn locate_inductive_unit(
  source: &ArtifactSource,
  inductive: &Address,
  constructors: &[&Address],
  recursors: &[&Address],
) -> Result<(), String> {
  let fail = |what: &str| Err(format!("{what} ({})", inductive.hex()));
  let member = source.member(inductive).map_err(|e| e.to_string())?;
  let (Some(owner), Some(index), None) =
    (member.owner(), member.index(), member.constructor_index())
  else {
    return fail("the inductive is not a member of a carried unit");
  };
  let owner_address = owner.address().clone();
  let ConstantInfo::Muts(members) = &owner.constant().info else {
    return fail("the inductive's owner is not a mutual unit");
  };
  let Some(MutConst::Indc(declared)) = members.get(index) else {
    return fail("the inductive's member is not an inductive");
  };
  if declared.ctors.len() != constructors.len() {
    return fail("the inductive's constructor count differs");
  }
  for (cidx, constructor) in constructors.iter().enumerate() {
    let member = source.member(constructor).map_err(|e| e.to_string())?;
    if member.owner().map(super::Record::address) != Some(&owner_address)
      || member.index() != Some(index)
      || member.constructor_index() != Some(cidx)
    {
      return fail(&format!("constructor {cidx} is not at its position"));
    }
  }
  let mut in_unit = Vec::new();
  for recursor in recursors {
    let member = source.member(recursor).map_err(|e| e.to_string())?;
    match (member.owner(), member.index()) {
      (None, None)
        if matches!(member.record().constant().info, ConstantInfo::Recr(_)) => {
      },
      (Some(owner), Some(at))
        if owner.address() == &owner_address
          && member.constructor_index().is_none()
          && matches!(members.get(at), Some(MutConst::Recr(_)))
          && !in_unit.contains(&at) =>
      {
        in_unit.push(at);
      },
      _ => return fail("a recursor is neither standalone nor in the unit"),
    }
  }
  if members.len() != 1 + in_unit.len() {
    return fail("the unit holds members outside the specification");
  }
  Ok(())
}

/// Read the declarations at `addresses` (with their units) into a fresh
/// anonymous environment.
fn ingress_records(
  source: &ArtifactSource,
  addresses: &[&Address],
) -> Result<KEnv<Anon>, String> {
  let mut kenv = KEnv::<Anon>::new();
  for address in addresses {
    if !ingress_anon_addr_shallow_input(
      &mut kenv,
      Input::Artifact(source),
      address,
    )? {
      return Err(format!("no carried record at {}", address.hex()));
    }
  }
  Ok(kenv)
}

/// Check the whole unit of each of `members` with only the groups in
/// `admitted`.
fn check_units(
  source: &ArtifactSource,
  admitted: &Admission,
  kenv: &mut KEnv<Anon>,
  members: &[&Address],
) -> Result<(), String> {
  let context =
    PrimitiveContext::bound(source.clone(), admitted.roles(), |_| None);
  let lookups = IxonIngressLookups::default();
  let mut checker =
    TypeChecker::for_artifact_anon(kenv, source, &lookups, context);
  for member in members {
    checker
      .check_ixon_const(&KId::new((*member).clone(), ()))
      .map_err(|error| format!("{} does not check: {error}", member.hex()))?;
  }
  Ok(())
}

// -----------------------------------------------------------------------
// Expected declarations
// -----------------------------------------------------------------------

fn cnst(address: &Address, levels: &[U]) -> E {
  KExpr::cnst(KId::new(address.clone(), ()), levels.to_vec().into())
}
fn var(index: u64) -> E {
  KExpr::var(index, ())
}
fn app(f: E, a: E) -> E {
  KExpr::app(f, a)
}
fn apps(f: E, args: Vec<E>) -> E {
  args.into_iter().fold(f, app)
}
fn pi(ty: E, body: E) -> E {
  KExpr::all((), (), ty, body)
}
fn lam(ty: E, body: E) -> E {
  KExpr::lam((), (), ty, body)
}
fn sort(level: U) -> E {
  KExpr::sort(level)
}
fn param(index: u64) -> U {
  KUniv::param(index, ())
}
fn type1() -> E {
  sort(KUniv::succ(KUniv::zero()))
}

/// The specified shape of an inductive type.
struct InductiveSpec {
  lvls: u64,
  params: u64,
  indices: u64,
  ty: E,
  constructors: Vec<Address>,
}

/// The specified shape of a constructor.
struct ConstructorSpec {
  lvls: u64,
  cidx: u64,
  params: u64,
  fields: u64,
  ty: E,
}

/// The specified shape of a recursor, with each rule's field count and
/// right-hand side.
struct RecursorSpec {
  lvls: u64,
  params: u64,
  indices: u64,
  motives: u64,
  minors: u64,
  k: bool,
  ty: E,
  rules: Vec<(u64, E)>,
}

fn declared(
  kenv: &KEnv<Anon>,
  address: &Address,
) -> Result<KConst<Anon>, String> {
  kenv
    .get(&KId::new(address.clone(), ()))
    .ok_or_else(|| format!("no declaration at {}", address.hex()))
}

fn differs(address: &Address, what: &str) -> String {
  format!("{} differs from the specification: {what}", address.hex())
}

fn expect_inductive(
  kenv: &KEnv<Anon>,
  address: &Address,
  spec: &InductiveSpec,
) -> Result<(), String> {
  let KConst::Indc { lvls, params, indices, is_unsafe, ty, ctors, .. } =
    declared(kenv, address)?
  else {
    return Err(differs(address, "not an inductive"));
  };
  let found: Vec<&Address> = ctors.iter().map(|id| &id.addr).collect();
  let wanted: Vec<&Address> = spec.constructors.iter().collect();
  if lvls != spec.lvls
    || params != spec.params
    || indices != spec.indices
    || is_unsafe
  {
    return Err(differs(address, "arity or safety"));
  }
  if ty != spec.ty {
    return Err(differs(address, "type"));
  }
  if found != wanted {
    return Err(differs(address, "constructors"));
  }
  Ok(())
}

fn expect_constructor(
  kenv: &KEnv<Anon>,
  address: &Address,
  inductive: &Address,
  spec: &ConstructorSpec,
) -> Result<(), String> {
  let KConst::Ctor {
    lvls, is_unsafe, induct, cidx, params, fields, ty, ..
  } = declared(kenv, address)?
  else {
    return Err(differs(address, "not a constructor"));
  };
  if lvls != spec.lvls
    || is_unsafe
    || &induct.addr != inductive
    || cidx != spec.cidx
    || params != spec.params
    || fields != spec.fields
  {
    return Err(differs(address, "arity, owner or index"));
  }
  if ty != spec.ty {
    return Err(differs(address, "type"));
  }
  Ok(())
}

fn expect_recursor(
  kenv: &KEnv<Anon>,
  address: &Address,
  spec: &RecursorSpec,
) -> Result<(), String> {
  let KConst::Recr {
    k,
    is_unsafe,
    lvls,
    params,
    indices,
    motives,
    minors,
    ty,
    rules,
    ..
  } = declared(kenv, address)?
  else {
    return Err(differs(address, "not a recursor"));
  };
  if lvls != spec.lvls
    || params != spec.params
    || indices != spec.indices
    || motives != spec.motives
    || minors != spec.minors
    || k != spec.k
    || is_unsafe
  {
    return Err(differs(address, "arity, K-flag or safety"));
  }
  if ty != spec.ty {
    return Err(differs(address, "type"));
  }
  if rules.len() != spec.rules.len()
    || rules
      .iter()
      .zip(&spec.rules)
      .any(|(rule, (fields, rhs))| rule.fields != *fields || &rule.rhs != rhs)
  {
    return Err(differs(address, "computation rules"));
  }
  Ok(())
}

// -----------------------------------------------------------------------
// The Nat basis
// -----------------------------------------------------------------------

/// `Nat : Type` with `Nat.zero : Nat`, `Nat.succ : Nat → Nat` and
/// `Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero)
/// (succ : ∀ n, motive n → motive (Nat.succ n)) (t : Nat) : motive t`, whose
/// rules return `zero` and `succ n (Nat.rec motive zero succ n)`.
fn validate_nat(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let [nat, zero, succ, rec] =
    bound(source, [Role::Nat, Role::NatZero, Role::NatSucc, Role::NatRec])?;
  locate_inductive_unit(source, &nat, &[&zero, &succ], &[&rec])?;
  let mut kenv = ingress_records(source, &[&nat, &rec])?;

  let nat_t = || cnst(&nat, &[]);
  expect_inductive(
    &kenv,
    &nat,
    &InductiveSpec {
      lvls: 0,
      params: 0,
      indices: 0,
      ty: type1(),
      constructors: vec![zero.clone(), succ.clone()],
    },
  )?;
  expect_constructor(
    &kenv,
    &zero,
    &nat,
    &ConstructorSpec { lvls: 0, cidx: 0, params: 0, fields: 0, ty: nat_t() },
  )?;
  expect_constructor(
    &kenv,
    &succ,
    &nat,
    &ConstructorSpec {
      lvls: 0,
      cidx: 1,
      params: 0,
      fields: 1,
      ty: pi(nat_t(), nat_t()),
    },
  )?;

  let u = param(0);
  // In the `motive` binder context.
  let zero_minor = || app(var(0), cnst(&zero, &[]));
  // In the `motive`, `zero` binder context.
  let succ_minor = || {
    pi(
      nat_t(),
      pi(app(var(2), var(0)), app(var(3), app(cnst(&succ, &[]), var(1)))),
    )
  };
  let motive = || pi(nat_t(), sort(u.clone()));
  let ty = pi(
    motive(),
    pi(zero_minor(), pi(succ_minor(), pi(nat_t(), app(var(3), var(0))))),
  );
  let zero_rule = lam(motive(), lam(zero_minor(), lam(succ_minor(), var(1))));
  let succ_rule = lam(
    motive(),
    lam(
      zero_minor(),
      lam(
        succ_minor(),
        lam(
          nat_t(),
          app(
            app(var(1), var(0)),
            apps(
              cnst(&rec, std::slice::from_ref(&u)),
              vec![var(3), var(2), var(1), var(0)],
            ),
          ),
        ),
      ),
    ),
  );
  expect_recursor(
    &kenv,
    &rec,
    &RecursorSpec {
      lvls: 1,
      params: 0,
      indices: 0,
      motives: 1,
      minors: 2,
      k: false,
      ty,
      rules: vec![(0, zero_rule), (1, succ_rule)],
    },
  )?;
  check_units(source, admitted, &mut kenv, &[&nat, &rec])
}
