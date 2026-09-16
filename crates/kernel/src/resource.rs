//! Combined resource and erased-type validation for addressed Ixon v3.
//! Kernel typechecking on its own makes no resource promise.

use crate::anon_work::build_anon_work;
use crate::env::KEnv;
use crate::id::KId;
use crate::mode::Anon;
use crate::primitive::PrimAddrs;
use crate::tc::TypeChecker;
use ixon::env::Env;
use ixon::resource::addressed::{AddressedProgram, Profile, check_resources};

/// Minimal built-in profile, restricted to interfaces present in the closure.
pub fn standard_profile(env: &Env) -> Profile {
  let p = PrimAddrs::new();
  let mut shareable_types: Vec<_> =
    [p.nat.clone(), p.bool_type.clone(), p.string.clone()]
      .into_iter()
      .filter(|a| env.consts.contains_key(a))
      .collect();
  shareable_types.sort_unstable();
  Profile {
    nat_type: env.consts.contains_key(&p.nat).then_some(p.nat),
    string_type: env.consts.contains_key(&p.string).then_some(p.string),
    shareable_types,
    ..Default::default()
  }
}

pub fn check_literal_profile(profile: &Profile) -> Result<(), String> {
  let p = PrimAddrs::new();
  for (selected, actual) in
    [(&profile.nat_type, &p.nat), (&profile.string_type, &p.string)]
  {
    if selected.as_ref().is_some_and(|selected| selected != actual) {
      return Err("resource validator: literal type differs from the kernel primitive identity".into());
    }
  }
  Ok(())
}

/// Validate both resources and erased types of the same canonical addressed
/// closure. A caller advertising a resource claim must bind the returned
/// profile address and this validator's identity to its subject.
pub fn validate(
  env: &Env,
  profile: &Profile,
) -> Result<AddressedProgram, String> {
  check_literal_profile(profile)?;
  let resolved = check_resources(env, profile)?;
  let work = build_anon_work(env)?;
  let mut kernel = KEnv::<Anon>::new();
  for item in work {
    let id = KId { addr: item.primary().clone(), name: () };
    let mut checker = TypeChecker::new_with_lazy_anon(&mut kernel, env);
    checker.check_const(&id).map_err(|error| {
      format!(
        "resource validator: erased typing failed at {}: {error:?}",
        item.primary().hex()
      )
    })?;
    // Retain structural declarations but keep reduction caches local to one
    // work item, as in the existing anonymous driver.
    kernel.clear_reduction_caches();
  }
  Ok(resolved)
}

pub fn check_claim(
  env: &Env,
  profile: &Profile,
  claim: &ixon::proof::Claim,
) -> Result<AddressedProgram, String> {
  let ixon::proof::Claim::Resource { root, profile: expected_profile } = claim
  else {
    return Err("resource validator: claim uses a different validator".into());
  };
  let leaves: Vec<_> =
    env.consts.iter().map(|entry| entry.key().clone()).collect();
  if ixon::merkle::merkle_root_canonical(&leaves).as_ref() != Some(root) {
    return Err("resource validator: claim subject differs from the complete constant set".into());
  }
  if &profile.address()? != expected_profile {
    return Err(
      "resource validator: claim profile differs from the supplied policy"
        .into(),
    );
  }
  validate(env, profile)
}

pub fn make_claim(
  env: &Env,
  profile: &Profile,
) -> Result<ixon::proof::Claim, String> {
  let leaves: Vec<_> =
    env.consts.iter().map(|entry| entry.key().clone()).collect();
  let root = ixon::merkle::merkle_root_canonical(&leaves)
    .ok_or("resource validator: empty claim subject")?;
  let claim =
    ixon::proof::Claim::Resource { root, profile: profile.address()? };
  check_claim(env, profile, &claim)?;
  Ok(claim)
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::address::Address;
  use ix_common::env::DefinitionSafety;
  use ixon::constant::{
    Constant, ConstantInfo, Constructor, DefKind, Definition, Inductive,
    MutConst, ctor_proj_constant, indc_proj_constant,
  };
  use ixon::contract::{BinderContract, ValueContract};
  use ixon::expr::{Expr, Uses};
  use ixon::univ::Univ;

  fn store(env: &Env, c: Constant) -> Address {
    let a = c.commit().0;
    env.store_const(a.clone(), c);
    a
  }

  #[test]
  fn cross_language_consumer_handoff() {
    let profile = Profile::from_bytes(include_bytes!(
      "../../../Tests/Fixtures/ixon-v3/handoff/profile.bin"
    ))
    .unwrap();
    let claim = ixon::proof::Claim::from_bytes(include_bytes!(
      "../../../Tests/Fixtures/ixon-v3/handoff/accepted.claim"
    ))
    .unwrap();
    let accepted = Env::get(
      &mut include_bytes!(
        "../../../Tests/Fixtures/ixon-v3/handoff/accepted.ixe"
      )
      .as_slice(),
    )
    .unwrap();
    let rejected = Env::get(
      &mut include_bytes!(
        "../../../Tests/Fixtures/ixon-v3/handoff/rejected-local-escape.ixe"
      )
      .as_slice(),
    )
    .unwrap();
    check_claim(&accepted, &profile, &claim).unwrap();
    assert!(check_claim(&rejected, &profile, &claim).is_err());
    assert!(validate(&rejected, &profile).is_err());
    // The counterexample is well typed after erasure; its rejection is
    // specifically a resource obligation, not a wire or Lean typing failure.
    let mut kernel = KEnv::<Anon>::new();
    for item in build_anon_work(&rejected).unwrap() {
      let id = KId { addr: item.primary().clone(), name: () };
      TypeChecker::new_with_lazy_anon(&mut kernel, &rejected)
        .check_const(&id)
        .unwrap();
    }
  }

  fn base() -> (Env, Address) {
    let env = Env::new();
    let block = store(
      &env,
      Constant::with_tables(
        ConstantInfo::Muts(vec![MutConst::Indc(Inductive {
          is_unsafe: false,
          lvls: 0,
          params: 0,
          indices: 0,
          typ: Expr::sort(0),
          ctors: vec![Constructor {
            is_unsafe: false,
            lvls: 0,
            cidx: 0,
            params: 0,
            fields: 0,
            typ: Expr::rec(0, vec![]),
          }],
        })]),
        vec![],
        vec![],
        vec![Univ::zero()],
      ),
    );
    let typ = store(&env, indc_proj_constant(0, block.clone()));
    store(&env, ctor_proj_constant(0, 0, block));
    (env, typ)
  }
  #[test]
  fn combines_independent_resource_and_type_checks() {
    let (env, typ) = base();
    let c = BinderContract {
      uses: Uses::Linear,
      value: ValueContract::local_shared(),
    };
    store(
      &env,
      Constant::with_tables(
        ConstantInfo::Defn(Definition {
          kind: DefKind::Definition,
          safety: DefinitionSafety::Safe,
          lvls: 0,
          typ: Expr::all_contract(
            c,
            ValueContract::local_shared(),
            Expr::reference(0, vec![]),
            Expr::reference(0, vec![]),
          ),
          value: Expr::lam_contract(
            c,
            Expr::reference(0, vec![]),
            Expr::var(0),
          ),
        }),
        vec![],
        vec![typ.clone()],
        vec![],
      ),
    );
    validate(&env, &Profile::default()).unwrap();
    let claim = make_claim(&env, &Profile::default()).unwrap();
    assert!(check_claim(&env, &Profile::default(), &claim).is_ok());
    let mut changed_profile = Profile::default();
    changed_profile.limits.steps += 1;
    assert!(check_claim(&env, &changed_profile, &claim).is_err());
    assert!(
      check_claim(
        &env,
        &Profile::default(),
        &ixon::proof::Claim::CheckEnv {
          root: Address::hash(b"subject"),
          assumptions: None
        }
      )
      .is_err()
    );
    assert!(
      validate(&env, &Profile { nat_type: Some(typ), ..Default::default() })
        .is_err()
    );
    let malformed = env.clone();
    store(
      &malformed,
      Constant::with_tables(
        ConstantInfo::Defn(Definition {
          kind: DefKind::Definition,
          safety: DefinitionSafety::Safe,
          lvls: 0,
          typ: Expr::sort(0),
          value: Expr::var(0),
        }),
        vec![],
        vec![],
        vec![Univ::zero()],
      ),
    );
    // This ordinary component has no resource annotation. It still must typecheck.
    assert!(check_resources(&malformed, &Profile::default()).is_ok());
    assert!(validate(&malformed, &Profile::default()).is_err());
  }
}
