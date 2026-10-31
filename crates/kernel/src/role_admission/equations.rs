//! Admit generated definition specifications through the ordinary checker.
//! The operation under validation is absent from the native primitive table;
//! only earlier admitted groups can participate in checking its equations.

use super::*;
use crate::expr::ExprData;

pub(super) struct SpecGroup {
  pub roles: &'static [Role],
  pub needs: &'static [Role],
}

pub(super) struct Equation {
  pub statement: E,
  /// Present exactly for an unconditional equation, closed over its variables.
  pub definitional_sides: Option<(E, E)>,
}

pub(super) enum Specification {
  Anchor { levels: u64, typ: E },
  Definition { levels: u64, typ: E, equations: Vec<Equation> },
}

pub(super) fn reference(
  source: &ArtifactSource,
  role: Role,
  levels: &[U],
) -> Result<E, String> {
  let address = source.required_role(role).map_err(|e| e.to_string())?;
  Ok(cnst(address, levels))
}

/// Check the generated terms independently of dependency metadata. Every
/// external reference must belong to a completely admitted group; the group
/// being checked may refer to its own candidates without accelerating them.
fn specification_references<'a>(
  source: &ArtifactSource,
  admitted: &Admission,
  group: &[Role],
  terms: impl IntoIterator<Item = &'a E>,
) -> Result<Vec<Address>, String> {
  let mut allowed = FxHashSet::default();
  for role in group {
    allowed
      .insert(source.required_role(*role).map_err(|e| e.to_string())?.clone());
  }
  for (role, address) in admitted.roles() {
    if super::super::block(*role).iter().all(|member| {
      source
        .required_role(*member)
        .is_ok_and(|bound| admitted.address(*member) == Some(bound))
    }) {
      allowed.insert(address.clone());
    }
  }
  let mut roots = FxHashSet::default();
  let mut seen = FxHashSet::default();
  let mut pending: Vec<_> = terms.into_iter().collect();
  while let Some(term) = pending.pop() {
    if !seen.insert(term.hash_key()) {
      continue;
    }
    if let ExprData::Const(id, ..) | ExprData::Prj(id, ..) = term.data() {
      if !allowed.contains(&id.addr) {
        return Err(format!(
          "generated specification references {} outside the admitted groups",
          id.addr.hex()
        ));
      }
      roots.insert(id.addr.clone());
    }
    match term.data() {
      ExprData::Const(..) | ExprData::Var(..) | ExprData::Sort(..) => {},
      ExprData::App(fun, arg, _) => pending.extend([fun, arg]),
      ExprData::Lam(_, _, _, domain, body, _)
      | ExprData::All(_, _, _, _, domain, body, _) => {
        pending.extend([domain, body])
      },
      ExprData::Let(_, typ, value, body, _, _) => {
        pending.extend([typ, value, body])
      },
      ExprData::Prj(_, _, value, _) => pending.push(value),
      ExprData::FVar(..) | ExprData::Nat(..) | ExprData::Str(..) => {
        return Err(
          "generated specification contains an open variable or literal".into(),
        );
      },
    }
  }
  Ok(roots.into_iter().collect())
}

pub(super) fn validate_group(
  source: &ArtifactSource,
  admitted: &Admission,
  roles: &[Role],
) -> Result<(), String> {
  let mut anchors = Vec::new();
  for role in roles {
    match specs::specification(*role, source)? {
      Some(Specification::Anchor { levels, typ }) => {
        anchors.push((*role, levels, typ));
      },
      Some(Specification::Definition { levels, typ, equations })
        if roles.len() == 1 =>
      {
        return validate_definition(
          source, admitted, *role, levels, &typ, equations,
        );
      },
      _ => {
        return Err(
          "the group has no supported generated specification".into(),
        );
      },
    }
  }
  if anchors.is_empty() {
    return Err("an empty specification group".into());
  }
  let mut roots = specification_references(
    source,
    admitted,
    roles,
    anchors.iter().map(|(_, _, typ)| typ),
  )?;
  validate_anchors(source, admitted, &anchors)?;
  // New support anchors are ordinary checked declarations as well as having
  // the specified type. They cannot introduce an axiom through the role table.
  let addresses = roles
    .iter()
    .map(|role| source.required_role(*role).map_err(|e| e.to_string()))
    .collect::<Result<Vec<_>, _>>()?;
  let mut env = ingress_records(source, &addresses)?;
  roots.extend(addresses.into_iter().cloned());
  check_support(source, admitted, &mut env, &roots)
}

fn validate_definition(
  source: &ArtifactSource,
  admitted: &Admission,
  role: Role,
  levels: u64,
  typ: &E,
  equations: Vec<Equation>,
) -> Result<(), String> {
  let address = source.required_role(role).map_err(|e| e.to_string())?;
  source.member(address).map_err(|e| e.to_string())?;
  let evidence =
    source.binding().and_then(|binding| binding.evidence(role)).unwrap_or(&[]);
  if evidence.len() != equations.len() {
    return Err(differs(address, "equation evidence count"));
  }
  let proofs: Vec<Address> = evidence
    .iter()
    .filter_map(|entry| match entry {
      Evidence::Proof(proof) => Some(proof.clone()),
      Evidence::DefEq => None,
    })
    .collect();
  let mut records = vec![address];
  records.extend(proofs.iter());
  let mut env = ingress_records(source, &records)?;
  let (ty, _) = expect_safe_definition(&env, address, levels)?;
  for proof in &proofs {
    expect_theorem_evidence(&env, proof, levels)?;
  }
  // A specified RHS can mention an anchor that the actual definition and
  // proof never reference. Include all generated terms, not only actual roots.
  let mut terms = vec![typ];
  for equation in &equations {
    terms.push(&equation.statement);
    if let Some((left, right)) = &equation.definitional_sides {
      terms.extend([left, right]);
    }
  }
  let mut roots = specification_references(source, admitted, &[role], terms)?;
  roots.extend(records.into_iter().cloned());
  check_support(source, admitted, &mut env, &roots)?;
  let context =
    PrimitiveContext::bound(source.clone(), admitted.roles(), |_| None);
  let lookups = IxonIngressLookups::default();
  let mut checker =
    TypeChecker::for_artifact_anon(&mut env, source, &lookups, context);
  let inferred = checker.infer(typ).map_err(|e| e.to_string())?;
  checker.ensure_sort(&inferred).map_err(|e| e.to_string())?;
  if !checker.is_def_eq(&ty, typ).map_err(|e| e.to_string())? {
    return Err(differs(address, "definition type"));
  }
  for (index, (equation, evidence)) in
    equations.into_iter().zip(evidence).enumerate()
  {
    let fail = |error| format!("{}: equation {index}: {error}", address.hex());
    checker.reset();
    let inferred =
      checker.infer(&equation.statement).map_err(|e| fail(e.to_string()))?;
    checker.ensure_sort(&inferred).map_err(|e| fail(e.to_string()))?;
    match evidence {
      Evidence::DefEq => {
        let Some((left, right)) = equation.definitional_sides else {
          return Err(fail(
            "a conditional equation needs proof evidence".into(),
          ));
        };
        let left_type =
          checker.infer(&left).map_err(|e| fail(e.to_string()))?;
        let right_type =
          checker.infer(&right).map_err(|e| fail(e.to_string()))?;
        if !checker
          .is_def_eq(&left_type, &right_type)
          .map_err(|e| fail(e.to_string()))?
          || !checker
            .is_def_eq(&left, &right)
            .map_err(|e| fail(e.to_string()))?
        {
          return Err(fail("the definitional equation does not hold".into()));
        }
      },
      Evidence::Proof(proof) => {
        let (ty, val) =
          load_checked_theorem(source, &mut checker, proof, levels)
            .map_err(&fail)?;
        if !checker
          .is_def_eq(&ty, &equation.statement)
          .map_err(|e| fail(e.to_string()))?
        {
          return Err(fail("the theorem has a different statement".into()));
        }
        if !check_proof_term(&mut checker, &val, &equation.statement)
          .map_err(&fail)?
        {
          return Err(fail("the proof has a different type".into()));
        }
      },
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::Name;
  use ixon::env::{Env, RoleBinding};
  use ixon::role_table::RoleTable;

  #[test]
  fn generated_references_require_complete_admitted_external_groups() {
    let mut input =
      include_bytes!("../../tests/fixtures/role_admission/basis.ixe")
        .as_slice();
    let mut env = Env::get(&mut input).unwrap();
    let nat_group = crate::role_admission::block(Role::Nat);
    let eq_group = crate::role_admission::block(Role::Eq);
    let bound: Vec<_> = nat_group
      .iter()
      .chain(eq_group)
      .map(|role| {
        let name =
          role.lean_name().split('.').fold(Name::anon(), |parent, part| {
            Name::str(parent, part.to_owned())
          });
        (*role, env.lookup_name(&name).unwrap().addr)
      })
      .collect();
    let table = RoleTable {
      version: crate::role_admission::SPEC_VERSION,
      bound,
      evidence: vec![],
    };
    let bytes = table.to_bytes().unwrap();
    env.role_binding =
      Some(RoleBinding { address: Address::hash(&bytes), bytes: bytes.into() });
    let source = ArtifactSource::prepare(env).unwrap();
    let term = reference(&source, Role::NatSucc, &[]).unwrap();
    let mut admitted = Admission::default();
    assert!(
      specification_references(&source, &admitted, eq_group, [&term]).is_err()
    );
    admitted.roles.insert(
      Role::NatSucc,
      source.required_role(Role::NatSucc).unwrap().clone(),
    );
    assert!(
      specification_references(&source, &admitted, eq_group, [&term]).is_err()
    );
    for role in nat_group {
      admitted
        .roles
        .insert(*role, source.required_role(*role).unwrap().clone());
    }
    assert!(
      specification_references(&source, &admitted, eq_group, [&term]).is_ok()
    );
    assert!(
      specification_references(
        &source,
        &Admission::default(),
        nat_group,
        [&term]
      )
      .is_ok()
    );
  }
}
