use super::*;
use crate::compile::{CompileState, KernelCtx, block_txn};
use crate::mutual::{Def, Ind};
use ix_common::env::{
  BinderInfo, ConstructorVal, Env, InductiveVal, Level, RecursorRule,
  RecursorVal, ReducibilityHints,
};
use ixon::env::Named;
use ixon::metadata::ConstantMeta;
use std::sync::Arc;

fn n(value: &str) -> Name {
  value
    .split('.')
    .fold(Name::anon(), |prefix, part| Name::str(prefix, part.into()))
}

fn addr(value: &str) -> Address {
  Address::hash(value.as_bytes())
}

fn cv(name: &str, typ: Expr) -> ConstantVal {
  ConstantVal { name: n(name), level_params: vec![], typ }
}

fn definition(name: &str, value: Expr) -> MutConst {
  MutConst::Defn(Def {
    name: n(name),
    level_params: vec![],
    typ: Expr::sort(Level::succ(Level::zero())),
    kind: DefKind::Definition,
    value,
    hints: ReducibilityHints::Abbrev,
    safety: DefinitionSafety::Safe,
    all: vec![n(name)],
  })
}

fn declaration(input: &MutConst) -> ConstantInfo {
  input_declarations(input).remove(0)
}

fn state() -> CompileState {
  CompileState {
    aux_input_capture: Some(Default::default()),
    ..Default::default()
  }
}

fn publish(stt: &CompileState, inputs: &[MutConst]) {
  let classes = inputs.iter().map(|input| vec![input]).collect::<Vec<_>>();
  let ctx = MutConst::ctx(&classes);
  let prepared =
    prepare_inputs(inputs, &ctx, |name| stt.resolve_addr(name)).unwrap();
  for input in inputs.iter().flat_map(input_declarations) {
    let name = input.get_name();
    stt.register_named(
      name.clone(),
      Named::new(addr(&name.pretty()), ConstantMeta::default()),
    );
  }
  publish_inputs(stt, prepared, Clone::clone).unwrap();
}

fn check(
  stt: &CompileState,
  name: &Name,
  actual: &ConstantInfo,
) -> Result<(), String> {
  stt.aux_input_capture.as_ref().unwrap().check(
    name,
    &stt.env.lookup_name(name).unwrap().addr,
    actual,
    |reference| stt.env.lookup_name(reference).map(|named| named.addr),
  )
}

#[test]
fn frozen_bindings_accept_aliases_but_reject_later_source_rebinding() {
  let stt = state();
  let source = n("Source.rec");
  let private = n("Source._ix.rec");
  let old = addr("canonical recursor");
  stt.name_to_addr.insert(source.clone(), old.clone());
  let input =
    definition("Generated._ix.helper", Expr::cnst(source.clone(), vec![]));
  publish(&stt, std::slice::from_ref(&input));
  // The compiler later publishes the canonical reference under a private
  // name and the original source name acquires a different meaning.
  stt.register_named(source, Named::with_addr(addr("source image")));
  stt.register_named(private.clone(), Named::with_addr(old));
  let mut actual = declaration(&input);
  let ConstantInfo::DefnInfo(value) = &mut actual else { unreachable!() };
  value.value = Expr::cnst(private, vec![]);
  assert!(check(&stt, actual.get_name(), &actual).is_ok());
  assert!(check(&stt, actual.get_name(), &declaration(&input)).is_err());
}

#[test]
fn capture_and_every_reference_are_required() {
  let stt = state();
  let input =
    definition("Generated._ix.helper", Expr::cnst(n("Missing"), vec![]));
  assert!(
    prepare_inputs(std::slice::from_ref(&input), &Default::default(), |_| None)
      .is_err()
  );
  let input = definition("Generated._ix.helper", Expr::sort(Level::zero()));
  let actual = declaration(&input);
  assert!(
    stt
      .aux_input_capture
      .as_ref()
      .unwrap()
      .check(actual.get_name(), &addr("absent"), &actual, |_| None)
      .is_err()
  );
  publish(&stt, std::slice::from_ref(&input));
  assert!(check(&stt, actual.get_name(), &actual).is_ok());
  let mut corrupt = actual.clone();
  let ConstantInfo::DefnInfo(value) = &mut corrupt else { unreachable!() };
  value.value = Expr::cnst(n("Missing"), vec![]);
  assert!(check(&stt, actual.get_name(), &corrupt).is_err());
  assert!(
    stt
      .aux_input_capture
      .as_ref()
      .unwrap()
      .check(actual.get_name(), &addr("rebound"), &actual, |_| None)
      .is_err()
  );
  assert!(
    stt
      .aux_input_capture
      .as_ref()
      .unwrap()
      .alias(&n("Alias"), &n("Absent"))
      .is_err()
  );
}

#[test]
fn changed_type_value_kind_and_safety_fail() {
  let stt = state();
  let input = definition("Generated._ix.helper", Expr::sort(Level::zero()));
  publish(&stt, std::slice::from_ref(&input));
  let ConstantInfo::DefnInfo(base) = declaration(&input) else {
    unreachable!()
  };
  for field in 0..4 {
    let mut value = base.clone();
    match field {
      0 => value.cnst.typ = Expr::sort(Level::zero()),
      1 => value.value = Expr::sort(Level::succ(Level::zero())),
      2 => value.safety = DefinitionSafety::Unsafe,
      _ => value.safety = DefinitionSafety::Partial,
    }
    assert!(
      check(&stt, &base.cnst.name, &ConstantInfo::DefnInfo(value)).is_err()
    );
  }
  let theorem = ConstantInfo::ThmInfo(TheoremVal {
    cnst: base.cnst.clone(),
    value: base.value,
    all: base.all,
  });
  assert!(check(&stt, &base.cnst.name, &theorem).is_err());
}

#[test]
fn alias_metadata_may_name_the_target_but_never_an_unrelated_binding() {
  let stt = state();
  let input = definition("Generated._ix.helper", Expr::sort(Level::zero()));
  publish(&stt, std::slice::from_ref(&input));
  let alias = n("Alias._ix.helper");
  stt
    .register_named(alias.clone(), stt.env.lookup_name(&input.name()).unwrap());
  stt.aux_input_capture.as_ref().unwrap().alias(&alias, &input.name()).unwrap();
  let actual = declaration(&input);
  assert!(check(&stt, &alias, &actual).is_ok());
  stt.register_named(
    n("Unrelated"),
    Named::with_addr(addr("unrelated binding")),
  );
  let ConstantInfo::DefnInfo(mut value) = actual else { unreachable!() };
  value.cnst.name = n("Unrelated");
  assert!(check(&stt, &alias, &ConstantInfo::DefnInfo(value)).is_err());
}

#[test]
fn universe_renaming_preserves_positions_and_rejects_swaps() {
  let mut input =
    definition("Generated._ix.helper", Expr::sort(Level::param(n("u"))));
  let MutConst::Defn(value) = &mut input else { unreachable!() };
  value.level_params = vec![n("u"), n("v")];
  value.typ = Expr::sort(Level::succ(Level::param(n("u"))));
  let stt = state();
  publish(&stt, std::slice::from_ref(&input));
  let ConstantInfo::DefnInfo(mut actual) = declaration(&input) else {
    unreachable!()
  };
  actual.cnst.level_params = vec![n("a"), n("b")];
  actual.cnst.typ = Expr::sort(Level::succ(Level::param(n("a"))));
  actual.value = Expr::sort(Level::param(n("a")));
  let name = actual.cnst.name.clone();
  assert!(check(&stt, &name, &ConstantInfo::DefnInfo(actual.clone())).is_ok());
  actual.value = Expr::sort(Level::param(n("b")));
  assert!(check(&stt, &name, &ConstantInfo::DefnInfo(actual.clone())).is_err());
  actual.value = Expr::sort(Level::param(n("a")));
  actual.cnst.level_params.push(n("c"));
  assert!(check(&stt, &name, &ConstantInfo::DefnInfo(actual)).is_err());
}

#[test]
fn internal_references_and_constructors_are_captured() {
  let ctor = ConstructorVal {
    cnst: cv("Generated._ix.P.mk", Expr::cnst(n("Generated._ix.P"), vec![])),
    induct: n("Generated._ix.P"),
    cidx: 0u64.into(),
    num_params: 0u64.into(),
    num_fields: 0u64.into(),
    is_unsafe: false,
  };
  let ind = InductiveVal {
    cnst: cv("Generated._ix.P", Expr::sort(Level::zero())),
    num_params: 0u64.into(),
    num_indices: 0u64.into(),
    all: vec![n("Generated._ix.P")],
    ctors: vec![ctor.cnst.name.clone()],
    num_nested: 0u64.into(),
    is_rec: false,
    is_unsafe: false,
    is_reflexive: false,
  };
  let input =
    MutConst::Indc(Ind { ind: ind.clone(), ctors: vec![ctor.clone()] });
  let stt = state();
  publish(&stt, std::slice::from_ref(&input));
  assert_eq!(stt.aux_input_capture.as_ref().unwrap().names().len(), 2);
  assert!(
    check(&stt, &ind.cnst.name, &ConstantInfo::InductInfo(ind.clone())).is_ok()
  );
  assert!(
    check(&stt, &ctor.cnst.name, &ConstantInfo::CtorInfo(ctor.clone())).is_ok()
  );
  stt.register_named(n("Other"), Named::with_addr(addr("different owner")));
  let mut wrong_owner = ctor.clone();
  wrong_owner.induct = n("Other");
  assert!(
    check(&stt, &ctor.cnst.name, &ConstantInfo::CtorInfo(wrong_owner)).is_err()
  );
  let mut wrong_ctor = ind.clone();
  wrong_ctor.ctors = vec![n("Other")];
  assert!(
    check(&stt, &ind.cnst.name, &ConstantInfo::InductInfo(wrong_ctor)).is_err()
  );
  let mut wrong_header = ind.clone();
  wrong_header.is_rec = true;
  assert!(
    check(&stt, &ind.cnst.name, &ConstantInfo::InductInfo(wrong_header))
      .is_err()
  );
}

#[test]
fn recursor_headers_rule_owners_and_bodies_are_checked() {
  let stt = state();
  for ctor in ["P.mk", "Q.mk"] {
    stt.name_to_addr.insert(n(ctor), addr(ctor));
    stt.register_named(n(ctor), Named::with_addr(addr(ctor)));
  }
  let rec = RecursorVal {
    cnst: cv("Generated._ix.rec", Expr::sort(Level::zero())),
    all: vec![n("Generated._ix.rec")],
    num_params: 0u64.into(),
    num_indices: 0u64.into(),
    num_motives: 1u64.into(),
    num_minors: 1u64.into(),
    rules: vec![RecursorRule {
      ctor: n("P.mk"),
      n_fields: 0u64.into(),
      rhs: Expr::bvar(0u64.into()),
    }],
    k: false,
    is_unsafe: false,
  };
  publish(&stt, &[MutConst::Recr(rec.clone())]);
  assert!(
    check(&stt, &rec.cnst.name, &ConstantInfo::RecInfo(rec.clone())).is_ok()
  );
  for field in 0..7 {
    let mut actual = rec.clone();
    match field {
      0 => actual.num_motives = 2u64.into(),
      1 => actual.rules[0].ctor = n("Q.mk"),
      2 => actual.rules[0].rhs = Expr::bvar(1u64.into()),
      3 => actual.rules[0].n_fields = 1u64.into(),
      4 => actual.rules.clear(),
      5 => actual.k = true,
      _ => actual.is_unsafe = true,
    }
    assert!(
      check(&stt, &rec.cnst.name, &ConstantInfo::RecInfo(actual)).is_err(),
      "field {field}"
    );
  }
}

#[test]
fn publication_requires_every_internal_binding() {
  let stt = state();
  let input =
    definition("Generated._ix.helper", Expr::cnst(n("Internal"), vec![]));
  let ctx = [(n("Internal"), 0u64.into())].into_iter().collect();
  let prepared =
    prepare_inputs(std::slice::from_ref(&input), &ctx, |_| None).unwrap();
  stt.register_named(input.name(), Named::with_addr(addr("helper")));
  assert!(publish_inputs(&stt, prepared, Clone::clone).is_err());
}

#[test]
fn display_moves_and_failed_transactions_do_not_leave_stale_captures() {
  let stt = state();
  let input = definition("Original.rec", Expr::sort(Level::zero()));
  let capture = stt.aux_input_capture.as_ref().unwrap();
  block_txn::start();
  publish(&stt, std::slice::from_ref(&input));
  let target = n("Original._ix.rec");
  capture.move_to_display(&input.name(), &target).unwrap();
  assert_eq!(capture.names(), vec![target]);
  let txn = block_txn::take().unwrap();
  block_txn::rollback(&stt, &txn);
  assert!(capture.names().is_empty());
}

#[test]
fn duplicate_capture_cannot_change_body_or_address() {
  let stt = state();
  let input = definition("Generated._ix.helper", Expr::sort(Level::zero()));
  publish(&stt, std::slice::from_ref(&input));
  let capture = stt.aux_input_capture.as_ref().unwrap();
  let record = capture.declarations.get(&input.name()).unwrap().clone();
  capture.insert(&input.name(), record.clone()).unwrap();
  let mut bad = record.clone();
  bad.address = addr("wrong");
  assert!(capture.insert(&input.name(), bad).is_err());
  let mut bad = record;
  let ConstantInfo::DefnInfo(value) = &mut bad.input.declaration else {
    unreachable!()
  };
  value.value = Expr::sort(Level::succ(Level::zero()));
  assert!(capture.insert(&input.name(), bad).is_err());
}

#[test]
fn projection_references_are_compared_by_binding() {
  let stt = state();
  stt.name_to_addr.insert(n("P"), addr("P"));
  let input = definition(
    "Generated._ix.helper",
    Expr::proj(n("P"), 0u64.into(), Expr::bvar(0u64.into())),
  );
  publish(&stt, std::slice::from_ref(&input));
  stt.register_named(n("Q"), Named::with_addr(addr("P")));
  let ConstantInfo::DefnInfo(mut value) = declaration(&input) else {
    unreachable!()
  };
  value.value = Expr::proj(n("Q"), 0u64.into(), Expr::bvar(0u64.into()));
  assert!(
    check(&stt, &input.name(), &ConstantInfo::DefnInfo(value.clone())).is_ok()
  );
  stt.register_named(n("Q"), Named::with_addr(addr("Q")));
  assert!(check(&stt, &input.name(), &ConstantInfo::DefnInfo(value)).is_err());
}

#[test]
fn reference_memo_confirms_raw_input_on_hash_collision() {
  let hash = *Expr::bvar(0u64.into()).get_hash();
  let left = Expr(Arc::new(ExprData::Bvar(0u64.into(), hash)));
  let right = Expr(Arc::new(ExprData::Bvar(1u64.into(), hash)));
  let mut memo = FxHashMap::default();
  assert_eq!(
    reference_expr(&left, &Default::default(), &mut memo).unwrap(),
    left
  );
  assert_eq!(
    reference_expr(&right, &Default::default(), &mut memo).unwrap(),
    right
  );
}

#[test]
fn writer_capture_preserves_bytes_and_checks_standalone_and_mutual_outputs() {
  let u = n("u");
  let sort = Expr::sort(Level::param(u.clone()));
  let mut one = definition(
    "Generated._ix.one",
    Expr::lam(
      n("a"),
      sort.clone(),
      Expr::bvar(0u64.into()),
      BinderInfo::Default,
    ),
  );
  let MutConst::Defn(value) = &mut one else { unreachable!() };
  value.level_params = vec![u];
  value.typ = Expr::all(n("a"), sort.clone(), sort, BinderInfo::Default);
  let two = definition("Generated._ix.two", Expr::sort(Level::zero()));
  for inputs in [vec![one.clone()], vec![one, two]] {
    let mut results = Vec::new();
    for capture in [false, true] {
      let stt = CompileState {
        aux_input_capture: capture.then(Default::default),
        ..Default::default()
      };
      crate::compile::mutual::compile_aux_block_with_rename(
        &inputs,
        &Arc::new(Env::default()),
        &stt,
        &mut KernelCtx::new(),
        None,
        None,
        &[],
      )
      .unwrap();
      let restored = crate::decompile::decompile_env(&stt).unwrap();
      if capture {
        for name in stt.aux_input_capture.as_ref().unwrap().names() {
          let actual = restored.env.get(&name).unwrap();
          check(&stt, &name, actual.value()).unwrap();
        }
      }
      let mut bytes = Vec::new();
      stt.env.put(&mut bytes).unwrap();
      if capture {
        let fresh = CompileState {
          env: ixon::env::Env::get_demoted_named(&mut bytes.as_slice())
            .unwrap(),
          ..Default::default()
        };
        let restored = crate::decompile::decompile_env(&fresh).unwrap();
        let observations = stt.aux_input_capture.as_ref().unwrap();
        for name in observations.names() {
          let actual = restored.env.get(&name).unwrap();
          observations
            .check(
              &name,
              &fresh.env.lookup_name(&name).unwrap().addr,
              actual.value(),
              |reference| {
                fresh.env.lookup_name(reference).map(|named| named.addr)
              },
            )
            .unwrap();
        }
      }
      results.push(bytes);
    }
    assert_eq!(results[0], results[1]);
  }
}

#[test]
fn shared_inductive_alias_restores_constructor_aliases_and_recursive_flags() {
  let stt = state();
  let parent = n("Generated._ix.P");
  let ctor_name = n("Generated._ix.P.step");
  let typ = Expr::cnst(parent.clone(), vec![]);
  let ctor = ConstructorVal {
    cnst: cv(
      "Generated._ix.P.step",
      Expr::all(n("child"), typ.clone(), typ, BinderInfo::Default),
    ),
    induct: parent.clone(),
    cidx: 0u64.into(),
    num_params: 0u64.into(),
    num_fields: 1u64.into(),
    is_unsafe: false,
  };
  let input = MutConst::Indc(Ind {
    ind: InductiveVal {
      cnst: cv("Generated._ix.P", Expr::sort(Level::zero())),
      num_params: 0u64.into(),
      num_indices: 0u64.into(),
      all: vec![parent.clone()],
      ctors: vec![ctor_name.clone()],
      num_nested: 0u64.into(),
      is_rec: true,
      is_unsafe: false,
      is_reflexive: false,
    },
    ctors: vec![ctor],
  });
  crate::compile::mutual::compile_aux_block_with_rename(
    &[input],
    &Arc::new(Env::default()),
    &stt,
    &mut KernelCtx::new(),
    None,
    None,
    &[],
  )
  .unwrap();
  let alias_parent = n("Alias._ix.P");
  let alias_ctor = n("Alias._ix.P.step");
  let capture = stt.aux_input_capture.as_ref().unwrap();
  for (alias, target) in [(&alias_parent, &parent), (&alias_ctor, &ctor_name)] {
    crate::compile::compile_name(alias, &stt).unwrap();
    stt.register_named(alias.clone(), stt.env.lookup_name(target).unwrap());
    capture.alias(alias, target).unwrap();
  }
  let mut bytes = Vec::new();
  stt.env.put(&mut bytes).unwrap();
  let fresh = CompileState {
    env: ixon::env::Env::get_demoted_named(&mut bytes.as_slice()).unwrap(),
    ..Default::default()
  };
  for compiled in [&stt, &fresh] {
    let restored = crate::decompile::decompile_env(compiled).unwrap();
    for name in capture.names() {
      let actual = restored
        .env
        .get(&name)
        .unwrap_or_else(|| panic!("missing alias {}", name.pretty()));
      capture
        .check(
          &name,
          &compiled.env.lookup_name(&name).unwrap().addr,
          actual.value(),
          |reference| {
            compiled.env.lookup_name(reference).map(|named| named.addr)
          },
        )
        .unwrap();
    }
  }
  let named = fresh.env.lookup_name(&alias_ctor).unwrap();
  let mut meta = (*named.meta()).clone();
  let ixon::metadata::ConstantMetaInfo::Ctor { induct, .. } = &mut meta.info
  else {
    unreachable!()
  };
  *induct = crate::compile::compile_name(&alias_ctor, &fresh).unwrap();
  fresh.register_named(alias_ctor, Named::new(named.addr, meta));
  let error = crate::decompile::decompile_env(&fresh).unwrap_err();
  assert!(
    error.to_string().contains("owner refers to another inductive projection")
  );
}
