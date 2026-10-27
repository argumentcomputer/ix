//! Group validators. Each admits one specification group of a binding for a
//! source, or refuses it with a reason. The groups and their specifications
//! are the certified checker's:
//!
//! - a basis block (`Nat`, `Eq`, `PUnit`, `Empty`, `False`, `Quot`) is
//!   admitted only when every bound role authenticates as the carried record
//!   at the position the specification fixes (an inductive's unit holding
//!   nothing else, its constructors by index, the quotient records by kind);
//!   the declarations, read into a fresh anonymous environment, are exactly
//!   the specified ones built from the bound addresses; and the kernel checks
//!   them there with only the groups admitted before this one;
//! - an anchor (the literal support) is admitted only when its record
//!   authenticates, is not unsafe, has exactly the specified level count and
//!   type, and that type checks as a type with only the groups admitted
//!   before it. An anchor is specified by its type alone; its declaration is
//!   checked like any other once admitted.
//!
//! A group is admitted whole or not at all, after the groups it needs.
//! Nothing outside this module creates an admission.

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, QuotKind};
use ixon::constant::DefKind;
use ixon::constant::{ConstantInfo, MutConst};
use ixon::role_table::{Evidence, Role};
use rustc_hash::{FxHashMap, FxHashSet};

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
  /// Its roles, the lead first.
  roles: &'static [Role],
  /// The lead roles of the groups its specification mentions.
  needs: &'static [Role],
  validate: fn(&ArtifactSource, &Admission) -> Result<(), String>,
}

/// The groups, in an order that lists every group after those it needs.
const GROUPS: &[Group] = &[
  Group {
    roles: &[Role::Nat, Role::NatZero, Role::NatSucc, Role::NatRec],
    needs: &[],
    validate: validate_nat,
  },
  Group {
    roles: &[Role::Eq, Role::EqRefl, Role::EqRec],
    needs: &[],
    validate: validate_eq,
  },
  Group {
    roles: &[Role::PUnit, Role::PUnitUnit, Role::PUnitRec],
    needs: &[],
    validate: validate_punit,
  },
  Group {
    roles: &[Role::Empty, Role::EmptyRec],
    needs: &[],
    validate: |source, admitted| {
      validate_empty_like(
        source,
        admitted,
        [Role::Empty, Role::EmptyRec],
        type1(),
      )
    },
  },
  Group {
    roles: &[Role::False, Role::FalseRec],
    needs: &[],
    validate: |source, admitted| {
      validate_empty_like(
        source,
        admitted,
        [Role::False, Role::FalseRec],
        prop(),
      )
    },
  },
  Group {
    roles: &[
      Role::Quot,
      Role::QuotMk,
      Role::QuotLift,
      Role::QuotInd,
      Role::QuotSound,
    ],
    needs: &[Role::Eq],
    validate: validate_quot,
  },
  Group { roles: &[Role::Char], needs: &[], validate: validate_char },
  Group { roles: &[Role::String], needs: &[], validate: validate_string },
  Group {
    roles: &[Role::List, Role::ListNil, Role::ListCons],
    needs: &[],
    validate: validate_list,
  },
  Group {
    roles: &[Role::CharOfNat],
    needs: &[Role::Nat, Role::Char],
    validate: validate_char_of_nat,
  },
  Group {
    roles: &[Role::StringOfList],
    needs: &[Role::List, Role::Char, Role::String],
    validate: validate_string_of_list,
  },
  Group {
    roles: &[Role::Bool, Role::BoolFalse, Role::BoolTrue, Role::BoolRec],
    needs: &[],
    validate: validate_bool,
  },
  Group {
    roles: &[Role::NatPred],
    needs: &[Role::Nat],
    validate: |source, admitted| {
      validate_structural_op(source, admitted, Role::NatPred)
    },
  },
  Group {
    roles: &[Role::NatAdd],
    needs: &[Role::Nat],
    validate: |source, admitted| {
      validate_structural_op(source, admitted, Role::NatAdd)
    },
  },
  Group {
    roles: &[Role::NatSub],
    needs: &[Role::Nat, Role::NatPred],
    validate: |source, admitted| {
      validate_structural_op(source, admitted, Role::NatSub)
    },
  },
  Group {
    roles: &[Role::NatMul],
    needs: &[Role::Nat, Role::NatAdd],
    validate: |source, admitted| {
      validate_structural_op(source, admitted, Role::NatMul)
    },
  },
  Group {
    roles: &[Role::NatPow],
    needs: &[Role::Nat, Role::NatAdd, Role::NatMul],
    validate: |source, admitted| {
      validate_structural_op(source, admitted, Role::NatPow)
    },
  },
  Group {
    roles: &[Role::NatBeq],
    needs: &[Role::Nat, Role::Bool],
    validate: |source, admitted| {
      validate_structural_op(source, admitted, Role::NatBeq)
    },
  },
  Group {
    roles: &[Role::NatBle],
    needs: &[Role::Nat, Role::Bool],
    validate: |source, admitted| {
      validate_structural_op(source, admitted, Role::NatBle)
    },
  },
];

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
  check_units_with(source, admitted, &FxHashMap::default(), kenv, members)
}

/// [`check_units`], with the group's own `candidates` also in the
/// primitive table but not admitted: the kernel recognises a quotient
/// record only at its table address.
fn check_units_with(
  source: &ArtifactSource,
  admitted: &Admission,
  candidates: &FxHashMap<Role, Address>,
  kenv: &mut KEnv<Anon>,
  members: &[&Address],
) -> Result<(), String> {
  let mut table = admitted.roles().clone();
  table
    .extend(candidates.iter().map(|(role, address)| (*role, address.clone())));
  let roles: FxHashSet<Role> = admitted.roles().keys().copied().collect();
  let context =
    PrimitiveContext::bound_with_table(source.clone(), &table, roles, |_| None);
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
fn prop() -> E {
  sort(KUniv::zero())
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

// -----------------------------------------------------------------------
// The Eq, PUnit, Empty and False bases
// -----------------------------------------------------------------------

/// `Eq.{u} {α : Sort u} (a : α) : α → Prop` with
/// `Eq.refl.{u} {α : Sort u} (a : α) : Eq a a` and
/// `Eq.rec.{u_1, u} {α : Sort u} {a : α}
/// {motive : (b : α) → Eq a b → Sort u_1} (refl : motive a (Eq.refl a))
/// {b : α} (t : Eq a b) : motive b t`, a K-like recursor whose rule returns
/// `refl`.
fn validate_eq(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let [eq, refl, rec] = bound(source, [Role::Eq, Role::EqRefl, Role::EqRec])?;
  locate_inductive_unit(source, &eq, &[&refl], &[&rec])?;
  let mut kenv = ingress_records(source, &[&eq, &rec])?;

  // `Eq` and `Eq.refl` at their own level `u`.
  let u = param(0);
  expect_inductive(
    &kenv,
    &eq,
    &InductiveSpec {
      lvls: 1,
      params: 2,
      indices: 1,
      ty: pi(sort(u.clone()), pi(var(0), pi(var(1), prop()))),
      constructors: vec![refl.clone()],
    },
  )?;
  expect_constructor(
    &kenv,
    &refl,
    &eq,
    &ConstructorSpec {
      lvls: 1,
      cidx: 0,
      params: 2,
      fields: 0,
      ty: pi(
        sort(u.clone()),
        pi(var(0), apps(cnst(&eq, &[u]), vec![var(1), var(0), var(0)])),
      ),
    },
  )?;

  // `Eq.rec.{u_1, u}`: `u_1` is level 0, `u` level 1.
  let (u1, u) = (param(0), param(1));
  let eq_u = || cnst(&eq, std::slice::from_ref(&u));
  // In the `α`, `a` binder context.
  let motive = || {
    pi(var(1), pi(apps(eq_u(), vec![var(2), var(1), var(0)]), sort(u1.clone())))
  };
  // In the `α`, `a`, `motive` binder context.
  let minor = || {
    app(
      app(var(0), var(1)),
      apps(cnst(&refl, std::slice::from_ref(&u)), vec![var(2), var(1)]),
    )
  };
  let ty = pi(
    sort(u.clone()),
    pi(
      var(0),
      pi(
        motive(),
        pi(
          minor(),
          pi(
            var(3),
            pi(
              apps(eq_u(), vec![var(4), var(3), var(0)]),
              app(app(var(3), var(1)), var(0)),
            ),
          ),
        ),
      ),
    ),
  );
  let rule =
    lam(sort(u.clone()), lam(var(0), lam(motive(), lam(minor(), var(0)))));
  expect_recursor(
    &kenv,
    &rec,
    &RecursorSpec {
      lvls: 2,
      params: 2,
      indices: 1,
      motives: 1,
      minors: 1,
      k: true,
      ty,
      rules: vec![(0, rule)],
    },
  )?;
  check_units(source, admitted, &mut kenv, &[&eq, &rec])
}

/// `PUnit.{u} : Sort u` with `PUnit.unit.{u} : PUnit.{u}` and
/// `PUnit.rec.{u_1, u} {motive : PUnit.{u} → Sort u_1}
/// (unit : motive PUnit.unit) (t : PUnit.{u}) : motive t`, whose rule
/// returns `unit`.
fn validate_punit(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let [punit, unit, rec] =
    bound(source, [Role::PUnit, Role::PUnitUnit, Role::PUnitRec])?;
  locate_inductive_unit(source, &punit, &[&unit], &[&rec])?;
  let mut kenv = ingress_records(source, &[&punit, &rec])?;

  let u = param(0);
  expect_inductive(
    &kenv,
    &punit,
    &InductiveSpec {
      lvls: 1,
      params: 0,
      indices: 0,
      ty: sort(u.clone()),
      constructors: vec![unit.clone()],
    },
  )?;
  expect_constructor(
    &kenv,
    &unit,
    &punit,
    &ConstructorSpec {
      lvls: 1,
      cidx: 0,
      params: 0,
      fields: 0,
      ty: cnst(&punit, &[u]),
    },
  )?;

  // `PUnit.rec.{u_1, u}`: `u_1` is level 0, `u` level 1.
  let (u1, u) = (param(0), param(1));
  let punit_t = || cnst(&punit, std::slice::from_ref(&u));
  let motive = || pi(punit_t(), sort(u1.clone()));
  let minor = || app(var(0), cnst(&unit, std::slice::from_ref(&u)));
  let ty = pi(motive(), pi(minor(), pi(punit_t(), app(var(2), var(0)))));
  let rule = lam(motive(), lam(minor(), var(0)));
  expect_recursor(
    &kenv,
    &rec,
    &RecursorSpec {
      lvls: 2,
      params: 0,
      indices: 0,
      motives: 1,
      minors: 1,
      k: false,
      ty,
      rules: vec![(0, rule)],
    },
  )?;
  check_units(source, admitted, &mut kenv, &[&punit, &rec])
}

/// An inductive with no constructors and no parameters in sort `sort`
/// (`Empty : Type`, `False : Prop`), with its recursor
/// `rec.{u} (motive : T → Sort u) (t : T) : motive t`, which has no rules.
fn validate_empty_like(
  source: &ArtifactSource,
  admitted: &Admission,
  roles: [Role; 2],
  sort_of_type: E,
) -> Result<(), String> {
  let [ty_address, rec] = bound(source, roles)?;
  locate_inductive_unit(source, &ty_address, &[], &[&rec])?;
  let mut kenv = ingress_records(source, &[&ty_address, &rec])?;
  expect_inductive(
    &kenv,
    &ty_address,
    &InductiveSpec {
      lvls: 0,
      params: 0,
      indices: 0,
      ty: sort_of_type,
      constructors: vec![],
    },
  )?;
  let t = || cnst(&ty_address, &[]);
  expect_recursor(
    &kenv,
    &rec,
    &RecursorSpec {
      lvls: 1,
      params: 0,
      indices: 0,
      motives: 1,
      minors: 0,
      k: false,
      ty: pi(pi(t(), sort(param(0))), pi(t(), app(var(1), var(0)))),
      rules: vec![],
    },
  )?;
  check_units(source, admitted, &mut kenv, &[&ty_address, &rec])
}

// -----------------------------------------------------------------------
// The Quot basis
// -----------------------------------------------------------------------

/// The four quotient records (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`)
/// of the kinds and types Lean installs, and the axiom `Quot.sound`.
fn validate_quot(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let [quot, mk, lift, ind, sound] = bound(
    source,
    [Role::Quot, Role::QuotMk, Role::QuotLift, Role::QuotInd, Role::QuotSound],
  )?;
  for (address, kind) in [
    (&quot, QuotKind::Type),
    (&mk, QuotKind::Ctor),
    (&lift, QuotKind::Lift),
    (&ind, QuotKind::Ind),
  ] {
    let member = source.member(address).map_err(|e| e.to_string())?;
    if member.owner().is_some()
      || !matches!(&member.record().constant().info,
        ConstantInfo::Quot(record) if record.kind == kind)
    {
      return Err(differs(address, &format!("not a {kind:?} quotient record")));
    }
  }
  let member = source.member(&sound).map_err(|e| e.to_string())?;
  if member.owner().is_some()
    || !matches!(member.record().constant().info, ConstantInfo::Axio(_))
  {
    return Err(differs(&sound, "not an axiom"));
  }
  let mut kenv = ingress_records(source, &[&quot, &mk, &lift, &ind, &sound])?;

  let (u, v) = (param(0), param(1));
  let quot_u = || cnst(&quot, std::slice::from_ref(&u));
  let mk_u = || cnst(&mk, std::slice::from_ref(&u));
  // `α → α → Prop`, in the `α` binder context.
  let relation = || pi(var(0), pi(var(1), prop()));
  let quot_ty = pi(sort(u.clone()), pi(relation(), sort(u.clone())));
  let mk_ty = pi(
    sort(u.clone()),
    pi(relation(), pi(var(1), apps(quot_u(), vec![var(2), var(1)]))),
  );
  // `Quot.lift.{u, v} {α} {r} {β : Sort v} (f : α → β)
  // (h : ∀ a b, r a b → f a = f b) (q : Quot r) : β`.
  let lift_f = pi(var(2), var(1));
  let lift_h = pi(
    var(3),
    pi(
      var(4),
      pi(
        apps(var(4), vec![var(1), var(0)]),
        apps(
          cnst(&admitted_eq(admitted)?, std::slice::from_ref(&v)),
          vec![var(4), app(var(3), var(2)), app(var(3), var(1))],
        ),
      ),
    ),
  );
  let lift_ty = pi(
    sort(u.clone()),
    pi(
      relation(),
      pi(
        sort(v.clone()),
        pi(
          lift_f,
          pi(lift_h, pi(apps(quot_u(), vec![var(4), var(3)]), var(3))),
        ),
      ),
    ),
  );
  // `Quot.ind.{u} {α} {r} {β : Quot r → Prop}
  // (mk : ∀ a, β (Quot.mk r a)) (q : Quot r) : β q`.
  let ind_motive = pi(apps(quot_u(), vec![var(1), var(0)]), prop());
  let ind_minor =
    pi(var(2), app(var(1), apps(mk_u(), vec![var(3), var(2), var(0)])));
  let ind_ty = pi(
    sort(u.clone()),
    pi(
      relation(),
      pi(
        ind_motive,
        pi(
          ind_minor,
          pi(apps(quot_u(), vec![var(3), var(2)]), app(var(2), var(0))),
        ),
      ),
    ),
  );
  // `Quot.sound.{u} {α} {r} {a b : α} : r a b → Quot.mk r a = Quot.mk r b`.
  let sound_ty = pi(
    sort(u.clone()),
    pi(
      relation(),
      pi(
        var(1),
        pi(
          var(2),
          pi(
            apps(var(2), vec![var(1), var(0)]),
            apps(
              cnst(&admitted_eq(admitted)?, std::slice::from_ref(&u)),
              vec![
                apps(quot_u(), vec![var(4), var(3)]),
                apps(mk_u(), vec![var(4), var(3), var(2)]),
                apps(mk_u(), vec![var(4), var(3), var(1)]),
              ],
            ),
          ),
        ),
      ),
    ),
  );
  for (address, kind, lvls, ty) in [
    (&quot, QuotKind::Type, 1, quot_ty),
    (&mk, QuotKind::Ctor, 1, mk_ty),
    (&lift, QuotKind::Lift, 2, lift_ty),
    (&ind, QuotKind::Ind, 1, ind_ty),
  ] {
    match declared(&kenv, address)? {
      KConst::Quot { kind: found, lvls: found_lvls, ty: found_ty, .. }
        if found == kind && found_lvls == lvls =>
      {
        if found_ty != ty {
          return Err(differs(address, "type"));
        }
      },
      _ => return Err(differs(address, "kind or level count")),
    }
  }
  match declared(&kenv, &sound)? {
    KConst::Axio { is_unsafe: false, lvls: 1, ty, .. } if ty == sound_ty => {},
    _ => return Err(differs(&sound, "safety, level count or type")),
  }

  let candidates: FxHashMap<Role, Address> = [
    (Role::Quot, quot.clone()),
    (Role::QuotMk, mk.clone()),
    (Role::QuotLift, lift.clone()),
    (Role::QuotInd, ind.clone()),
  ]
  .into_iter()
  .collect();
  check_units_with(
    source,
    admitted,
    &candidates,
    &mut kenv,
    &[&quot, &mk, &lift, &ind, &sound],
  )
}

fn admitted_eq(admitted: &Admission) -> Result<Address, String> {
  admitted.address(Role::Eq).cloned().ok_or_else(|| "Eq is not admitted".into())
}

// -----------------------------------------------------------------------
// The literal-support anchors
// -----------------------------------------------------------------------

/// Whether a declaration is unsafe.
fn is_unsafe(constant: &KConst<Anon>) -> bool {
  match constant {
    KConst::Defn { safety, .. } => *safety == DefinitionSafety::Unsafe,
    KConst::Recr { is_unsafe, .. }
    | KConst::Axio { is_unsafe, .. }
    | KConst::Indc { is_unsafe, .. }
    | KConst::Ctor { is_unsafe, .. } => *is_unsafe,
    KConst::Quot { .. } => false,
  }
}

/// Admit anchors `(role, level count, type)`, which are specified by their
/// types alone: each bound record authenticates, is not unsafe, has the
/// level count and exactly the type, and that type is a type with only the
/// groups admitted before.
fn validate_anchors(
  source: &ArtifactSource,
  admitted: &Admission,
  anchors: &[(Role, u64, E)],
) -> Result<(), String> {
  let mut addresses = Vec::with_capacity(anchors.len());
  for (role, _, _) in anchors {
    let address =
      source.required_role(*role).map_err(|error| error.to_string())?.clone();
    source.member(&address).map_err(|error| error.to_string())?;
    addresses.push(address);
  }
  let references: Vec<&Address> = addresses.iter().collect();
  let mut kenv = ingress_records(source, &references)?;
  for ((_, lvls, ty), address) in anchors.iter().zip(&addresses) {
    let constant = declared(&kenv, address)?;
    if is_unsafe(&constant) {
      return Err(differs(address, "unsafe"));
    }
    if constant.lvls() != *lvls {
      return Err(differs(address, "level count"));
    }
    if constant.ty() != ty {
      return Err(differs(address, "type"));
    }
  }
  let context =
    PrimitiveContext::bound(source.clone(), admitted.roles(), |_| None);
  let lookups = IxonIngressLookups::default();
  let mut checker =
    TypeChecker::for_artifact_anon(&mut kenv, source, &lookups, context);
  for ((_, _, ty), address) in anchors.iter().zip(&addresses) {
    checker.reset();
    let sort = checker.infer(ty).map_err(|error| {
      format!("{}: the specified type does not check: {error}", address.hex())
    })?;
    checker.ensure_sort(&sort).map_err(|error| {
      format!("{}: the specified type is not a type: {error}", address.hex())
    })?;
  }
  Ok(())
}

/// `Char : Type`.
fn validate_char(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  validate_anchors(source, admitted, &[(Role::Char, 0, type1())])
}

/// `String : Type`.
fn validate_string(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  validate_anchors(source, admitted, &[(Role::String, 0, type1())])
}

/// `List.{u} : Type u → Type u`, `List.nil.{u} (α : Type u) : List α` and
/// `List.cons.{u} (α : Type u) (head : α) (tail : List α) : List α`.
fn validate_list(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let list = source
    .required_role(Role::List)
    .map_err(|error| error.to_string())?
    .clone();
  let type_u = || sort(KUniv::succ(param(0)));
  let list_u = || cnst(&list, &[param(0)]);
  validate_anchors(
    source,
    admitted,
    &[
      (Role::List, 1, pi(type_u(), type_u())),
      (Role::ListNil, 1, pi(type_u(), app(list_u(), var(0)))),
      (
        Role::ListCons,
        1,
        pi(
          type_u(),
          pi(var(0), pi(app(list_u(), var(1)), app(list_u(), var(2)))),
        ),
      ),
    ],
  )
}

/// `Char.ofNat : Nat → Char`.
fn validate_char_of_nat(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let nat = admitted.address(Role::Nat).ok_or("Nat is not admitted")?;
  let char_t = admitted.address(Role::Char).ok_or("Char is not admitted")?;
  validate_anchors(
    source,
    admitted,
    &[(Role::CharOfNat, 0, pi(cnst(nat, &[]), cnst(char_t, &[])))],
  )
}

/// `String.ofList : List.{0} Char → String`.
fn validate_string_of_list(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let list = admitted.address(Role::List).ok_or("List is not admitted")?;
  let char_t = admitted.address(Role::Char).ok_or("Char is not admitted")?;
  let string =
    admitted.address(Role::String).ok_or("String is not admitted")?;
  validate_anchors(
    source,
    admitted,
    &[(
      Role::StringOfList,
      0,
      pi(
        app(cnst(list, &[KUniv::zero()]), cnst(char_t, &[])),
        cnst(string, &[]),
      ),
    )],
  )
}

// -----------------------------------------------------------------------
// Bool and the structural Nat operations
// -----------------------------------------------------------------------

/// `Bool : Type`, `Bool.false Bool.true : Bool` and
/// `Bool.rec.{u} {motive : Bool → Sort u} (false : motive false)
/// (true : motive true) (t : Bool) : motive t`, anchors specified by type.
fn validate_bool(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let [bool_t, false_c, true_c] =
    bound(source, [Role::Bool, Role::BoolFalse, Role::BoolTrue])?;
  let bool_c = || cnst(&bool_t, &[]);
  let rec_ty = pi(
    pi(bool_c(), sort(param(0))),
    pi(
      app(var(0), cnst(&false_c, &[])),
      pi(app(var(1), cnst(&true_c, &[])), pi(bool_c(), app(var(3), var(0)))),
    ),
  );
  validate_anchors(
    source,
    admitted,
    &[
      (Role::Bool, 0, type1()),
      (Role::BoolFalse, 0, bool_c()),
      (Role::BoolTrue, 0, bool_c()),
      (Role::BoolRec, 1, rec_ty),
    ],
  )
}

fn admitted_role(admitted: &Admission, role: Role) -> Result<E, String> {
  admitted
    .address(role)
    .map(|address| cnst(address, &[]))
    .ok_or_else(|| format!("{} is not admitted", role.lean_name()))
}

/// The type and recurrence equations of a structural `Nat` operation, the
/// certified checker's: each equation over `x` (`#1`) and `y` (`#0`), with
/// the operation itself as `op`.
fn structural_spec(
  role: Role,
  admitted: &Admission,
  op: &E,
) -> Result<(E, Vec<(E, E)>), String> {
  let nat = || admitted_role(admitted, Role::Nat);
  let zero = admitted_role(admitted, Role::NatZero)?;
  let succ = admitted_role(admitted, Role::NatSucc)?;
  let (x, y) = (var(1), var(0));
  let s = |e: E| app(succ.clone(), e);
  let op2 = |a: E, b: E| apps(op.clone(), vec![a, b]);
  let binary =
    |cod: E| -> Result<E, String> { Ok(pi(nat()?, pi(nat()?, cod))) };
  Ok(match role {
    Role::NatPred => (
      pi(nat()?, nat()?),
      vec![
        (app(op.clone(), zero.clone()), zero),
        (app(op.clone(), s(x.clone())), x),
      ],
    ),
    Role::NatAdd => (
      binary(nat()?)?,
      vec![
        (op2(x.clone(), zero), x.clone()),
        (op2(x.clone(), s(y.clone())), s(op2(x, y))),
      ],
    ),
    Role::NatSub => {
      let pred = admitted_role(admitted, Role::NatPred)?;
      (
        binary(nat()?)?,
        vec![
          (op2(x.clone(), zero), x.clone()),
          (op2(x.clone(), s(y.clone())), app(pred, op2(x, y))),
        ],
      )
    },
    Role::NatMul => {
      let add = admitted_role(admitted, Role::NatAdd)?;
      (
        binary(nat()?)?,
        vec![
          (op2(x.clone(), zero.clone()), zero),
          (op2(x.clone(), s(y.clone())), apps(add, vec![op2(x.clone(), y), x])),
        ],
      )
    },
    Role::NatPow => {
      let mul = admitted_role(admitted, Role::NatMul)?;
      (
        binary(nat()?)?,
        vec![
          (op2(x.clone(), zero.clone()), s(zero)),
          (op2(x.clone(), s(y.clone())), apps(mul, vec![op2(x.clone(), y), x])),
        ],
      )
    },
    Role::NatBeq => {
      let bool_t = admitted_role(admitted, Role::Bool)?;
      let true_c = admitted_role(admitted, Role::BoolTrue)?;
      let false_c = admitted_role(admitted, Role::BoolFalse)?;
      (
        binary(bool_t)?,
        vec![
          (op2(zero.clone(), zero.clone()), true_c),
          (op2(zero.clone(), s(y.clone())), false_c.clone()),
          (op2(s(x.clone()), zero), false_c),
          (op2(s(x.clone()), s(y.clone())), op2(x, y)),
        ],
      )
    },
    Role::NatBle => {
      let bool_t = admitted_role(admitted, Role::Bool)?;
      let true_c = admitted_role(admitted, Role::BoolTrue)?;
      let false_c = admitted_role(admitted, Role::BoolFalse)?;
      (
        binary(bool_t)?,
        vec![
          (op2(zero.clone(), y.clone()), true_c),
          (op2(s(x.clone()), zero), false_c),
          (op2(s(x.clone()), s(y.clone())), op2(x, y)),
        ],
      )
    },
    _ => return Err(format!("{role:?} is not a structural operation")),
  })
}

/// A structural `Nat` operation: a safe, level-monomorphic definition of
/// the specified type that checks, whose role evidence is one definitional
/// entry per recurrence equation, and whose equations hold by definitional
/// equality with its own references replaced by its value, checked with
/// only the groups admitted before (so its own fast path cannot discharge
/// them).
fn validate_structural_op(
  source: &ArtifactSource,
  admitted: &Admission,
  role: Role,
) -> Result<(), String> {
  let address =
    source.required_role(role).map_err(|error| error.to_string())?.clone();
  source.member(&address).map_err(|error| error.to_string())?;
  let mut kenv = ingress_records(source, &[&address])?;
  let KConst::Defn {
    kind: DefKind::Definition,
    safety: DefinitionSafety::Safe,
    lvls: 0,
    ty,
    val,
    ..
  } = declared(&kenv, &address)?
  else {
    return Err(differs(&address, "not a safe level-monomorphic definition"));
  };
  let (spec_ty, equations) = structural_spec(role, admitted, &val)?;
  if ty != spec_ty {
    return Err(differs(&address, "type"));
  }
  let evidence =
    source.binding().and_then(|binding| binding.evidence(role)).unwrap_or(&[]);
  if evidence.len() != equations.len()
    || evidence.iter().any(|entry| !matches!(entry, Evidence::DefEq))
  {
    return Err(format!(
      "{}: the evidence is not one definitional entry per equation",
      address.hex()
    ));
  }
  check_units(source, admitted, &mut kenv, &[&address])?;

  let nat = admitted_role(admitted, Role::Nat)?;
  let context =
    PrimitiveContext::bound(source.clone(), admitted.roles(), |_| None);
  let lookups = IxonIngressLookups::default();
  let mut checker =
    TypeChecker::for_artifact_anon(&mut kenv, source, &lookups, context);
  for (index, (lhs, rhs)) in equations.into_iter().enumerate() {
    let close = |e: E| lam(nat.clone(), lam(nat.clone(), e));
    checker.reset();
    let holds =
      checker.is_def_eq(&close(lhs), &close(rhs)).map_err(|error| {
        format!("{}: equation {index} does not check: {error}", address.hex())
      })?;
    if !holds {
      return Err(format!("{}: equation {index} does not hold", address.hex()));
    }
  }
  Ok(())
}
