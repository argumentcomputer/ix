//! Admit generated definition specifications through the ordinary checker.
//! The operation under validation is absent from the native primitive table;
//! only earlier admitted groups can participate in checking its equations.

use super::*;

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
  validate_anchors(source, admitted, &anchors)?;
  // New support anchors are ordinary checked declarations as well as having
  // the specified type. They cannot introduce an axiom through the role table.
  let addresses = roles
    .iter()
    .map(|role| source.required_role(*role).map_err(|e| e.to_string()))
    .collect::<Result<Vec<_>, _>>()?;
  let mut env = ingress_records(source, &addresses)?;
  check_units(source, admitted, &mut env, &addresses)
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
  let operation = declared(&env, address)?;
  let KConst::Defn {
    kind: DefKind::Definition,
    safety: DefinitionSafety::Safe,
    lvls,
    ty,
    ..
  } = operation
  else {
    return Err(differs(address, "not a safe definition"));
  };
  if lvls != levels {
    return Err(differs(address, "universe parameter count"));
  }
  for proof in &proofs {
    let theorem = declared(&env, proof)?;
    if !matches!(theorem, KConst::Defn {
      kind: DefKind::Theorem, safety: DefinitionSafety::Safe, lvls, ..
    } if lvls == levels)
    {
      return Err(differs(
        proof,
        "not a safe theorem at the specified universes",
      ));
    }
  }
  // Definition equations may use ordinary theorem dependencies. Check their
  // complete carried support before admission so an unchecked helper's type
  // cannot justify a native rule. Old Nat certificates retain their separate
  // locality rule. Only earlier groups are accelerated during these checks.
  let roots: Vec<_> = records.iter().map(|a| (*a).clone()).collect();
  let mut support: Vec<_> =
    source.closure(&roots).map_err(|e| e.to_string())?.into_iter().collect();
  support.sort_unstable();
  let mut targets = Vec::new();
  for entry in &support {
    if source.contains_record(entry) {
      if source.record_tag(entry).map_err(|e| e.to_string())?
        != ixon::lazy::ConstVariantTag::Muts
      {
        targets.push(entry);
      }
    } else {
      source.blob(entry).map_err(|e| e.to_string())?;
    }
  }
  check_units(source, admitted, &mut env, &targets)?;
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
        let theorem = checker
          .get_const(&KId::new(proof.clone(), ()))
          .map_err(|e| fail(e.to_string()))?;
        let KConst::Defn { ty, val, .. } = theorem else {
          return Err(fail("evidence is not a checked theorem".into()));
        };
        if !checker
          .is_def_eq(&ty, &equation.statement)
          .map_err(|e| fail(e.to_string()))?
        {
          return Err(fail("the theorem has a different statement".into()));
        }
        let actual = checker.infer(&val).map_err(|e| fail(e.to_string()))?;
        if !checker
          .is_def_eq(&actual, &equation.statement)
          .map_err(|e| fail(e.to_string()))?
        {
          return Err(fail("the proof has a different type".into()));
        }
      },
    }
  }
  Ok(())
}
