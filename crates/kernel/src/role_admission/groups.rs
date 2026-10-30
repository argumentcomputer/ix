//! Group validators. Each admits one specification group of a binding for a
//! source, or refuses it with a reason. The groups and their specifications
//! are the certified checker's:
//!
//! - a basis block (`Nat`, `Eq`, `PUnit`, `Empty`, `False`, `Quot`) or a
//!   standard axiom's family (`Iff`, `Nonempty`) is admitted only when
//!   every bound role authenticates as the carried record at the position
//!   the specification fixes (an inductive's unit holding nothing else, its
//!   constructors by index, the quotient records by kind); the
//!   declarations, read into a fresh anonymous environment, are exactly the
//!   specified ones built from the bound addresses; and the kernel checks
//!   them there with only the groups admitted before this one. Every role a
//!   standard axiom's type mentions is such a block: an admitted axiom is
//!   true only of the declarations it quantifies over, so a type does not
//!   pin them;
//! - an anchor (the literal support, `Bool`, `True`, `And`) is admitted only
//!   when its record authenticates, is not unsafe, has exactly the specified
//!   level count and type, and that type checks as a type with only the
//!   groups admitted before it. An anchor is specified by its type alone;
//!   its declaration is checked like any other once admitted;
//! - an axiom (`propext`, `Classical.choice`, the inert `sorryAx`) is
//!   admitted only when its record is a safe axiom of exactly the specified
//!   level count and type over the admitted groups, and checks.
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

#[path = "equations.rs"]
mod equations;
#[path = "specs.rs"]
mod specs;

/// One specification group.
struct Group {
  /// Its roles, the lead first.
  roles: &'static [Role],
  /// The lead roles of the groups its specification mentions.
  needs: &'static [Role],
  validate: fn(&ArtifactSource, &Admission) -> Result<(), String>,
}

/// Validators with declaration-shape or recurrence-specific checks. The
/// generated group order also includes definitions checked by their equations.
const SPECIALIZED_GROUPS: &[Group] = &[
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
  Group {
    roles: &[Role::True, Role::TrueIntro],
    needs: &[],
    validate: validate_true,
  },
  Group {
    roles: &[Role::And, Role::AndIntro, Role::AndRec],
    needs: &[],
    validate: validate_and,
  },
  Group {
    roles: &[Role::Iff, Role::IffIntro, Role::IffRec],
    needs: &[],
    validate: validate_iff,
  },
  Group {
    roles: &[Role::Nonempty, Role::NonemptyIntro, Role::NonemptyRec],
    needs: &[],
    validate: validate_nonempty,
  },
  Group {
    roles: &[Role::Propext],
    needs: &[Role::Iff, Role::Eq],
    validate: validate_propext,
  },
  Group {
    roles: &[Role::Choice],
    needs: &[Role::Nonempty],
    validate: validate_choice,
  },
  Group {
    roles: &[Role::SorryAx],
    needs: &[Role::Bool],
    validate: validate_sorry,
  },
  Group {
    roles: &[Role::NatDiv],
    needs: &[
      Role::Nat,
      Role::NatPred,
      Role::NatSub,
      Role::NatBle,
      Role::Bool,
      Role::Eq,
    ],
    validate: |source, admitted| validate_wf_op(source, admitted, Role::NatDiv),
  },
  Group {
    roles: &[Role::NatMod],
    needs: &[
      Role::Nat,
      Role::NatPred,
      Role::NatSub,
      Role::NatBle,
      Role::Bool,
      Role::Eq,
    ],
    validate: |source, admitted| validate_wf_op(source, admitted, Role::NatMod),
  },
  Group {
    roles: &[Role::NatGcd],
    needs: &[Role::Nat, Role::NatBle, Role::NatMod, Role::Bool, Role::Eq],
    validate: |source, admitted| validate_wf_op(source, admitted, Role::NatGcd),
  },
  Group {
    roles: &[Role::NatLand],
    needs: &[
      Role::Nat,
      Role::NatAdd,
      Role::NatMul,
      Role::NatBle,
      Role::NatDiv,
      Role::NatMod,
      Role::Bool,
      Role::Eq,
    ],
    validate: |source, admitted| {
      validate_wf_op(source, admitted, Role::NatLand)
    },
  },
  Group {
    roles: &[Role::NatLor],
    needs: &[
      Role::Nat,
      Role::NatAdd,
      Role::NatSub,
      Role::NatMul,
      Role::NatBle,
      Role::NatDiv,
      Role::NatMod,
      Role::Bool,
      Role::Eq,
    ],
    validate: |source, admitted| validate_wf_op(source, admitted, Role::NatLor),
  },
  Group {
    roles: &[Role::NatXor],
    needs: &[
      Role::Nat,
      Role::NatAdd,
      Role::NatMul,
      Role::NatBle,
      Role::NatDiv,
      Role::NatMod,
      Role::Bool,
      Role::Eq,
    ],
    validate: |source, admitted| validate_wf_op(source, admitted, Role::NatXor),
  },
  Group {
    roles: &[Role::NatShiftLeft],
    needs: &[
      Role::Nat,
      Role::NatSub,
      Role::NatMul,
      Role::NatBle,
      Role::Bool,
      Role::Eq,
    ],
    validate: |source, admitted| {
      validate_wf_op(source, admitted, Role::NatShiftLeft)
    },
  },
  Group {
    roles: &[Role::NatShiftRight],
    needs: &[
      Role::Nat,
      Role::NatSub,
      Role::NatBle,
      Role::NatDiv,
      Role::Bool,
      Role::Eq,
    ],
    validate: |source, admitted| {
      validate_wf_op(source, admitted, Role::NatShiftRight)
    },
  },
];

/// Admit every bound group of `source` that its validator accepts.
pub(super) fn admit(source: &ArtifactSource) -> Admission {
  let mut admission = Admission::default();
  let Some(binding) = source.binding() else {
    return admission;
  };
  for group in specs::GROUPS {
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
      match SPECIALIZED_GROUPS
        .iter()
        .find(|existing| existing.roles == group.roles)
      {
        Some(existing) if existing.needs != group.needs => Err(
          "generated dependencies differ from the existing validator".into(),
        ),
        Some(existing) => (existing.validate)(source, &admission),
        None => equations::validate_group(source, &admission, group.roles),
      }
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
    (Role::QuotSound, sound.clone()),
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

// -----------------------------------------------------------------------
// The well-founded Nat operations
// -----------------------------------------------------------------------

/// The admitted constants a certificate statement mentions.
struct Vocabulary {
  nat: E,
  zero: E,
  succ: E,
  boolean: E,
  true_c: E,
  false_c: E,
  eq: E,
  ble: E,
  sub: Option<E>,
  add: Option<E>,
  mul: Option<E>,
  div: Option<E>,
  modulo: Option<E>,
}

impl Vocabulary {
  fn of(admitted: &Admission) -> Result<Self, String> {
    let optional = |role| admitted_role(admitted, role).ok();
    Ok(Self {
      nat: admitted_role(admitted, Role::Nat)?,
      zero: admitted_role(admitted, Role::NatZero)?,
      succ: admitted_role(admitted, Role::NatSucc)?,
      boolean: admitted_role(admitted, Role::Bool)?,
      true_c: admitted_role(admitted, Role::BoolTrue)?,
      false_c: admitted_role(admitted, Role::BoolFalse)?,
      eq: cnst(&admitted_eq(admitted)?, &[KUniv::succ(KUniv::zero())]),
      ble: admitted_role(admitted, Role::NatBle)?,
      sub: optional(Role::NatSub),
      add: optional(Role::NatAdd),
      mul: optional(Role::NatMul),
      div: optional(Role::NatDiv),
      modulo: optional(Role::NatMod),
    })
  }
}

fn needed(constant: &Option<E>, name: &str) -> Result<E, String> {
  constant.clone().ok_or_else(|| format!("{name} is not admitted"))
}

/// The certificate statements of a well-founded `Nat` operation, the
/// certified checker's: per certificate its hypotheses and its equation,
/// over `x` and `y`, with the operation itself as `op`. Guards are spelled
/// with `Nat.ble` and `1` as `Nat.succ Nat.zero`.
fn wf_statements(
  role: Role,
  v: &Vocabulary,
  op: &E,
  x: &E,
  y: &E,
) -> Result<Vec<(Vec<E>, E)>, String> {
  let s = |e: E| app(v.succ.clone(), e);
  let one = s(v.zero.clone());
  let two = s(one.clone());
  let bin = |f: &E, a: E, b: E| apps(f.clone(), vec![a, b]);
  let ble = |a: E, b: E| bin(&v.ble, a, b);
  let eq_bool = |a: E, b: E| apps(v.eq.clone(), vec![v.boolean.clone(), a, b]);
  let eq_nat = |a: E, b: E| apps(v.eq.clone(), vec![v.nat.clone(), a, b]);
  let holds = |guard: E| eq_bool(guard, v.true_c.clone());
  let fails = |guard: E| eq_bool(guard, v.false_c.clone());
  let lhs = bin(op, x.clone(), y.clone());
  let one_le = |e: &E| ble(one.clone(), e.clone());
  Ok(match role {
    Role::NatDiv | Role::NatMod => {
      let sub = needed(&v.sub, "Nat.sub")?;
      let rest = bin(op, bin(&sub, x.clone(), y.clone()), y.clone());
      let (recursive, base) = if role == Role::NatDiv {
        (s(rest), v.zero.clone())
      } else {
        (rest, x.clone())
      };
      vec![
        (
          vec![holds(ble(y.clone(), x.clone())), holds(one_le(y))],
          eq_nat(lhs.clone(), recursive),
        ),
        (
          vec![fails(ble(y.clone(), x.clone()))],
          eq_nat(lhs.clone(), base.clone()),
        ),
        (vec![fails(one_le(y))], eq_nat(lhs, base)),
      ]
    },
    Role::NatGcd => {
      let modulo = needed(&v.modulo, "Nat.mod")?;
      vec![
        (
          vec![holds(one_le(x))],
          eq_nat(
            lhs.clone(),
            bin(op, bin(&modulo, y.clone(), x.clone()), x.clone()),
          ),
        ),
        (vec![fails(one_le(x))], eq_nat(lhs, y.clone())),
      ]
    },
    Role::NatShiftLeft => {
      let (sub, mul) = (needed(&v.sub, "Nat.sub")?, needed(&v.mul, "Nat.mul")?);
      vec![
        (
          vec![holds(one_le(y))],
          eq_nat(
            lhs.clone(),
            bin(
              op,
              bin(&mul, two, x.clone()),
              bin(&sub, y.clone(), one.clone()),
            ),
          ),
        ),
        (vec![fails(one_le(y))], eq_nat(lhs, x.clone())),
      ]
    },
    Role::NatShiftRight => {
      let (sub, div) = (needed(&v.sub, "Nat.sub")?, needed(&v.div, "Nat.div")?);
      vec![
        (
          vec![holds(one_le(y))],
          eq_nat(
            lhs.clone(),
            bin(
              &div,
              bin(op, x.clone(), bin(&sub, y.clone(), one.clone())),
              two,
            ),
          ),
        ),
        (vec![fails(one_le(y))], eq_nat(lhs, x.clone())),
      ]
    },
    Role::NatLand | Role::NatLor | Role::NatXor => {
      let add = needed(&v.add, "Nat.add")?;
      let mul = needed(&v.mul, "Nat.mul")?;
      let div = needed(&v.div, "Nat.div")?;
      let modulo = needed(&v.modulo, "Nat.mod")?;
      let halves = bin(
        op,
        bin(&div, x.clone(), two.clone()),
        bin(&div, y.clone(), two.clone()),
      );
      let x_bit = bin(&modulo, x.clone(), two.clone());
      let y_bit = bin(&modulo, y.clone(), two.clone());
      let low = match role {
        Role::NatLand => bin(&mul, x_bit, y_bit),
        Role::NatLor => {
          let sub = needed(&v.sub, "Nat.sub")?;
          bin(
            &sub,
            bin(&add, x_bit.clone(), y_bit.clone()),
            bin(&mul, x_bit, y_bit),
          )
        },
        _ => bin(&modulo, bin(&add, x_bit, y_bit), two.clone()),
      };
      let base = if role == Role::NatLand { v.zero.clone() } else { y.clone() };
      vec![
        (
          vec![holds(one_le(x))],
          eq_nat(lhs.clone(), bin(&add, bin(&mul, two, halves), low)),
        ),
        (vec![fails(one_le(x))], eq_nat(lhs, base)),
      ]
    },
    _ => return Err(format!("{role:?} is not a well-founded operation")),
  })
}

/// Replace every occurrence of the level-monomorphic constant `target` in
/// `e` by the closed term `value`, under binders too (sharing preserved).
fn replace_constant(
  e: &E,
  target: &Address,
  value: &E,
  memo: &mut FxHashMap<u64, E>,
) -> E {
  if let Some(done) = memo.get(&e.hash_key()) {
    return done.clone();
  }
  let mut go = |e: &E| replace_constant(e, target, value, memo);
  let out = match e.data() {
    crate::expr::ExprData::Const(id, levels, _)
      if &id.addr == target && levels.is_empty() =>
    {
      value.clone()
    },
    crate::expr::ExprData::App(f, a, _) => KExpr::app(go(f), go(a)),
    // Anonymous mode: names and binder infos are `()`.
    crate::expr::ExprData::Lam((), (), contract, ty, body, _) => {
      KExpr::lam_contract((), (), *contract, go(ty), go(body))
    },
    crate::expr::ExprData::All((), (), contract, result, ty, body, _) => {
      KExpr::all_contract((), (), *contract, *result, go(ty), go(body))
    },
    crate::expr::ExprData::Let((), ty, val, body, contract, _) => {
      KExpr::let_contract((), *contract, go(ty), go(val), go(body))
    },
    crate::expr::ExprData::Prj(id, field, val, _) => {
      KExpr::prj(id.clone(), *field, go(val))
    },
    _ => e.clone(),
  };
  memo.insert(e.hash_key(), out.clone());
  out
}

/// The records reachable from `roots` through carried references: a
/// projection reaches its unit, a unit everything its members mention. A
/// unit is the granularity at which records are carried and checked.
fn reference_closure(
  source: &ArtifactSource,
  roots: Vec<Address>,
) -> FxHashSet<Address> {
  let mut seen = FxHashSet::default();
  let mut todo = roots;
  while let Some(address) = todo.pop() {
    if !seen.insert(address.clone()) {
      continue;
    }
    // Literal blobs are references but not records.
    let Ok(record) = source.record(&address) else { continue };
    let constant = record.constant();
    if let Some(block) = projection_unit(&constant.info) {
      todo.push(block.clone());
    }
    todo.extend(constant.refs.iter().cloned());
  }
  seen
}

fn projection_unit(info: &ConstantInfo) -> Option<&Address> {
  match info {
    ConstantInfo::IPrj(p) => Some(&p.block),
    ConstantInfo::CPrj(p) => Some(&p.block),
    ConstantInfo::RPrj(p) => Some(&p.block),
    ConstantInfo::DPrj(p) => Some(&p.block),
    _ => None,
  }
}

/// Evidence may mention only the operation and the reference closure of its
/// definition and dependency groups. The theorem and its body are checked
/// separately by the operation's validator.
fn check_evidence_locality(
  source: &ArtifactSource,
  admitted: &Admission,
  role: Role,
  address: &Address,
  evidence: &[Address],
) -> Result<(), String> {
  let mut roots: Vec<Address> = vec![address.clone()];
  for dependency in super::dependencies(role) {
    for member in super::block(*dependency) {
      roots.extend(admitted.address(*member).cloned());
    }
  }
  let closure = reference_closure(source, roots);
  let local = |reference: &Address| {
    closure.contains(reference)
      || source.record(reference).ok().is_some_and(|r| {
        projection_unit(&r.constant().info).is_some_and(|b| closure.contains(b))
      })
  };
  for proof in evidence {
    let proof_record =
      source.proof_record(proof).map_err(|error| error.to_string())?;
    for reference in &proof_record.record().constant().refs {
      if reference != address
        && source.record(reference).is_ok()
        && !local(reference)
      {
        return Err(format!(
          "{}: evidence {} mentions {} outside the operation's closure",
          address.hex(),
          proof.hex(),
          reference.hex()
        ));
      }
    }
  }
  Ok(())
}

/// A well-founded `Nat` operation: a safe, level-monomorphic definition of
/// type `Nat → Nat → Nat` that checks, whose role evidence is one proof per
/// certificate statement. Each local proof, with the operation's references
/// replaced by its value, must prove its equation over the statement's
/// variables and hypotheses, with only the groups admitted before.
fn validate_wf_op(
  source: &ArtifactSource,
  admitted: &Admission,
  role: Role,
) -> Result<(), String> {
  let address =
    source.required_role(role).map_err(|error| error.to_string())?.clone();
  source.member(&address).map_err(|error| error.to_string())?;
  let evidence: Vec<Address> = source
    .binding()
    .and_then(|binding| binding.evidence(role))
    .unwrap_or(&[])
    .iter()
    .map(|entry| match entry {
      Evidence::Proof(proof) => Ok(proof.clone()),
      Evidence::DefEq => Err(format!(
        "{}: definitional evidence for a well-founded operation",
        address.hex()
      )),
    })
    .collect::<Result<_, _>>()?;
  let mut references: Vec<&Address> = vec![&address];
  references.extend(evidence.iter());
  let mut kenv = ingress_records(source, &references)?;
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
  let vocabulary = Vocabulary::of(admitted)?;
  let nat = vocabulary.nat.clone();
  if ty != pi(nat.clone(), pi(nat.clone(), nat.clone())) {
    return Err(differs(&address, "type"));
  }
  let statement_count =
    wf_statements(role, &vocabulary, &val, &var(1), &var(0))?.len();
  if evidence.len() != statement_count {
    return Err(format!(
      "{}: the evidence is not one proof per certificate statement",
      address.hex()
    ));
  }
  check_units(source, admitted, &mut kenv, &references)?;

  // Locality: the closure of the operation (its unit's references) and of
  // the roles, with their blocks, that its specification depends on.

  check_evidence_locality(source, admitted, role, &address, &evidence)?;

  let context =
    PrimitiveContext::bound(source.clone(), admitted.roles(), |_| None);
  let lookups = IxonIngressLookups::default();
  let mut checker =
    TypeChecker::for_artifact_anon(&mut kenv, source, &lookups, context);
  for (index, proof) in evidence.iter().enumerate() {
    let fail = |what: String| {
      format!("{}: certificate {index} ({}) {what}", address.hex(), proof.hex())
    };
    let theorem = checker
      .get_const(&KId::new(proof.clone(), ()))
      .map_err(|error| fail(error.to_string()))?;
    let KConst::Defn {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      val: value,
      ..
    } = &theorem
    else {
      return Err(fail("is not a safe level-monomorphic theorem".into()));
    };
    checker
      .validate_const_well_scoped(&theorem)
      .map_err(|error| fail(error.to_string()))?;
    checker
      .check_no_unsafe_refs(value, DefinitionSafety::Safe)
      .map_err(|error| fail(error.to_string()))?;
    let proof_term =
      replace_constant(value, &address, &val, &mut FxHashMap::default());

    // λ (x y : Nat) (h₁ … hₙ), proof x y h₁ … hₙ, against
    // Π (x y : Nat) (h₁ … hₙ), equation.
    let (hypotheses, _) =
      &wf_statements(role, &vocabulary, &val, &var(1), &var(0))?[index];
    let count = u64::try_from(hypotheses.len()).map_err(|e| e.to_string())?;
    let at_depth = |depth: u64| {
      wf_statements(role, &vocabulary, &val, &var(depth + 1), &var(depth))
        .map(|statements| statements[index].clone())
    };
    let mut arguments = vec![var(count + 1), var(count)];
    arguments.extend((0..count).rev().map(var));
    let mut lambda = apps(proof_term, arguments);
    let (_, mut pi_type) = at_depth(count)?;
    for i in (0..count).rev() {
      let (hypotheses, _) = at_depth(i)?;
      let hypothesis =
        hypotheses[usize::try_from(i).map_err(|e| e.to_string())?].clone();
      lambda = lam(hypothesis.clone(), lambda);
      pi_type = pi(hypothesis, pi_type);
    }
    for _ in 0..2 {
      lambda = lam(nat.clone(), lambda);
      pi_type = pi(nat.clone(), pi_type);
    }
    checker.reset();
    let inferred =
      checker.infer(&lambda).map_err(|error| fail(error.to_string()))?;
    let proves = checker
      .is_def_eq(&inferred, &pi_type)
      .map_err(|error| fail(error.to_string()))?;
    if !proves {
      return Err(fail("does not prove its statement".into()));
    }
  }
  Ok(())
}

// -----------------------------------------------------------------------
// The standard axioms and their families
// -----------------------------------------------------------------------

/// `True : Prop` and `True.intro : True`.
fn validate_true(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let true_t = source
    .required_role(Role::True)
    .map_err(|error| error.to_string())?
    .clone();
  validate_anchors(
    source,
    admitted,
    &[(Role::True, 0, prop()), (Role::TrueIntro, 0, cnst(&true_t, &[]))],
  )
}

/// `And (a b : Prop) : Prop`, `And.intro {a b : Prop} (left : a)
/// (right : b) : And a b` and `And.rec.{u} {a b : Prop}
/// {motive : And a b → Sort u} (intro : (left : a) → (right : b) →
/// motive (And.intro left right)) (t : And a b) : motive t`.
fn validate_and(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let [and, intro] = bound(source, [Role::And, Role::AndIntro])?;
  let and2 = |a: E, b: E| apps(cnst(&and, &[]), vec![a, b]);
  let intro_ty =
    pi(prop(), pi(prop(), pi(var(1), pi(var(1), and2(var(3), var(2))))));
  let rec_ty = pi(
    prop(),
    pi(
      prop(),
      pi(
        pi(and2(var(1), var(0)), sort(param(0))),
        pi(
          pi(
            var(2),
            pi(
              var(2),
              app(
                var(2),
                apps(cnst(&intro, &[]), vec![var(4), var(3), var(1), var(0)]),
              ),
            ),
          ),
          pi(and2(var(3), var(2)), app(var(2), var(0))),
        ),
      ),
    ),
  );
  validate_anchors(
    source,
    admitted,
    &[
      (Role::And, 0, pi(prop(), pi(prop(), prop()))),
      (Role::AndIntro, 0, intro_ty),
      (Role::AndRec, 1, rec_ty),
    ],
  )
}

/// `Iff (a b : Prop) : Prop` with `Iff.intro {a b : Prop} (mp : a → b)
/// (mpr : b → a) : Iff a b` and `Iff.rec.{u} {a b : Prop}
/// {motive : Iff a b → Sort u} (intro : ∀ mp mpr, motive (Iff.intro mp mpr))
/// (t : Iff a b) : motive t`, whose rule returns `intro mp mpr`. A block,
/// not an anchor: `propext` is true only of this inductive.
fn validate_iff(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let [iff, intro, rec] =
    bound(source, [Role::Iff, Role::IffIntro, Role::IffRec])?;
  locate_inductive_unit(source, &iff, &[&intro], &[&rec])?;
  let mut kenv = ingress_records(source, &[&iff, &rec])?;

  let iff2 = |a: E, b: E| apps(cnst(&iff, &[]), vec![a, b]);
  expect_inductive(
    &kenv,
    &iff,
    &InductiveSpec {
      lvls: 0,
      params: 2,
      indices: 0,
      ty: pi(prop(), pi(prop(), prop())),
      constructors: vec![intro.clone()],
    },
  )?;
  expect_constructor(
    &kenv,
    &intro,
    &iff,
    &ConstructorSpec {
      lvls: 0,
      cidx: 0,
      params: 2,
      fields: 2,
      ty: pi(
        prop(),
        pi(
          prop(),
          pi(pi(var(1), var(1)), pi(pi(var(1), var(3)), iff2(var(3), var(2)))),
        ),
      ),
    },
  )?;

  // In the `a`, `b` binder context.
  let motive = || pi(iff2(var(1), var(0)), sort(param(0)));
  // In the `a`, `b`, `motive` binder context.
  let minor = || {
    pi(
      pi(var(2), var(2)),
      pi(
        pi(var(2), var(4)),
        app(
          var(2),
          apps(cnst(&intro, &[]), vec![var(4), var(3), var(1), var(0)]),
        ),
      ),
    )
  };
  let ty = pi(
    prop(),
    pi(
      prop(),
      pi(motive(), pi(minor(), pi(iff2(var(3), var(2)), app(var(2), var(0))))),
    ),
  );
  let rule = lam(
    prop(),
    lam(
      prop(),
      lam(
        motive(),
        lam(
          minor(),
          lam(
            pi(var(3), var(3)),
            lam(pi(var(3), var(5)), app(app(var(2), var(1)), var(0))),
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
      params: 2,
      indices: 0,
      motives: 1,
      minors: 1,
      k: false,
      ty,
      rules: vec![(2, rule)],
    },
  )?;
  check_units(source, admitted, &mut kenv, &[&iff, &rec])
}

/// `Nonempty.{u} (α : Sort u) : Prop` with `Nonempty.intro.{u} {α : Sort u}
/// (val : α) : Nonempty α` and `Nonempty.rec.{u} {α : Sort u}
/// {motive : Nonempty α → Prop} (intro : ∀ val, motive (Nonempty.intro val))
/// (t : Nonempty α) : motive t`, whose rule returns `intro val`. A block, not
/// an anchor: `Classical.choice` is true only of this inductive.
fn validate_nonempty(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let [nonempty, intro, rec] =
    bound(source, [Role::Nonempty, Role::NonemptyIntro, Role::NonemptyRec])?;
  locate_inductive_unit(source, &nonempty, &[&intro], &[&rec])?;
  let mut kenv = ingress_records(source, &[&nonempty, &rec])?;

  let u = param(0);
  let nonempty_u = |e: E| app(cnst(&nonempty, std::slice::from_ref(&u)), e);
  expect_inductive(
    &kenv,
    &nonempty,
    &InductiveSpec {
      lvls: 1,
      params: 1,
      indices: 0,
      ty: pi(sort(u.clone()), prop()),
      constructors: vec![intro.clone()],
    },
  )?;
  expect_constructor(
    &kenv,
    &intro,
    &nonempty,
    &ConstructorSpec {
      lvls: 1,
      cidx: 0,
      params: 1,
      fields: 1,
      ty: pi(sort(u.clone()), pi(var(0), nonempty_u(var(1)))),
    },
  )?;

  // In the `α` binder context.
  let motive = || pi(nonempty_u(var(0)), prop());
  // In the `α`, `motive` binder context.
  let minor = || {
    pi(
      var(1),
      app(
        var(1),
        apps(cnst(&intro, std::slice::from_ref(&u)), vec![var(2), var(0)]),
      ),
    )
  };
  let ty = pi(
    sort(u.clone()),
    pi(motive(), pi(minor(), pi(nonempty_u(var(2)), app(var(2), var(0))))),
  );
  let rule = lam(
    sort(u.clone()),
    lam(motive(), lam(minor(), lam(var(2), app(var(1), var(0))))),
  );
  expect_recursor(
    &kenv,
    &rec,
    &RecursorSpec {
      lvls: 1,
      params: 1,
      indices: 0,
      motives: 1,
      minors: 1,
      k: false,
      ty,
      rules: vec![(1, rule)],
    },
  )?;
  check_units(source, admitted, &mut kenv, &[&nonempty, &rec])
}

/// An axiom of the specified level count and type, checked as a declaration
/// with only the groups admitted before (and itself as an axiom the policy
/// allows).
fn validate_axiom(
  source: &ArtifactSource,
  admitted: &Admission,
  role: Role,
  lvls: u64,
  ty: &E,
) -> Result<(), String> {
  let address =
    source.required_role(role).map_err(|error| error.to_string())?.clone();
  let member = source.member(&address).map_err(|error| error.to_string())?;
  if member.owner().is_some()
    || !matches!(member.record().constant().info, ConstantInfo::Axio(_))
  {
    return Err(differs(&address, "not an axiom"));
  }
  let mut kenv = ingress_records(source, &[&address])?;
  match declared(&kenv, &address)? {
    KConst::Axio { is_unsafe: false, lvls: found, ty: found_ty, .. }
      if found == lvls =>
    {
      if &found_ty != ty {
        return Err(differs(&address, "type"));
      }
    },
    _ => return Err(differs(&address, "safety or level count")),
  }
  let candidates: FxHashMap<Role, Address> =
    std::iter::once((role, address.clone())).collect();
  check_units_with(source, admitted, &candidates, &mut kenv, &[&address])
}

/// `propext {a b : Prop} : Iff a b → a = b`.
fn validate_propext(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let iff = admitted.address(Role::Iff).ok_or("Iff is not admitted")?;
  let eq = admitted_eq(admitted)?;
  let ty = pi(
    prop(),
    pi(
      prop(),
      pi(
        apps(cnst(iff, &[]), vec![var(1), var(0)]),
        apps(
          cnst(&eq, &[KUniv::succ(KUniv::zero())]),
          vec![prop(), var(2), var(1)],
        ),
      ),
    ),
  );
  validate_axiom(source, admitted, Role::Propext, 0, &ty)
}

/// `Classical.choice.{u} {α : Sort u} : Nonempty α → α`.
fn validate_choice(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let nonempty =
    admitted.address(Role::Nonempty).ok_or("Nonempty is not admitted")?;
  let u = param(0);
  let ty = pi(
    sort(u.clone()),
    pi(app(cnst(nonempty, std::slice::from_ref(&u)), var(0)), var(1)),
  );
  validate_axiom(source, admitted, Role::Choice, 1, &ty)
}

/// `sorryAx.{u} (α : Sort u) (synthetic : Bool) : α`: an inert axiom,
/// tolerated as a declaration and refused at every use. Its type fixes which
/// declaration is tolerated.
fn validate_sorry(
  source: &ArtifactSource,
  admitted: &Admission,
) -> Result<(), String> {
  let bool_t = admitted.address(Role::Bool).ok_or("Bool is not admitted")?;
  let ty = pi(sort(param(0)), pi(cnst(bool_t, &[]), var(1)));
  validate_axiom(source, admitted, Role::SorryAx, 1, &ty)
}

#[cfg(test)]
mod tests {
  use super::{Role, SPECIALIZED_GROUPS, specs};
  use rustc_hash::FxHashSet;

  #[test]
  fn the_groups_are_the_specification_blocks_in_dependency_order() {
    let mut seen: FxHashSet<Role> = FxHashSet::default();
    for group in specs::GROUPS {
      let lead = group.roles[0];
      assert_eq!(group.roles, super::super::block(lead), "{lead:?}");
      let needs: FxHashSet<Role> = group.needs.iter().copied().collect();
      let specified: FxHashSet<Role> = group
        .roles
        .iter()
        .flat_map(|role| super::super::dependencies(*role))
        .filter(|role| !group.roles.contains(role))
        .copied()
        .collect();
      assert_eq!(needs, specified, "{lead:?}");
      assert!(needs.iter().all(|need| seen.contains(need)), "{lead:?}");
      for role in group.roles {
        assert!(seen.insert(*role), "{role:?} is in two groups");
      }
    }
    assert_eq!(seen.len(), Role::ALL.len());
    for specialized in SPECIALIZED_GROUPS {
      let generated = specs::GROUPS
        .iter()
        .find(|group| group.roles == specialized.roles)
        .unwrap();
      assert_eq!(specialized.needs, generated.needs);
    }
  }
}
