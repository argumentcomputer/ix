use super::*;
use ixon::expr::Uses;
use ixon::resource::{DeclKind, check_definition};
fn r(i: u64) -> Term {
  Expr::reference(i, vec![])
}
fn v(i: u64) -> Term {
  Expr::var(i)
}
fn arr(a: Term, b: Term) -> Term {
  Expr::all(a, b)
}
fn apps(f: Term, xs: Vec<Term>) -> Term {
  xs.into_iter().fold(f, Expr::app)
}
fn ty() -> Term {
  Expr::sort(0)
}
fn prop() -> Term {
  Expr::sort(1)
}
fn eq(head: u64, a: Term, x: Term, y: Term) -> Term {
  apps(r(head), vec![a, x, y])
}
fn eq_ty() -> Term {
  arr(Expr::sort(2), arr(v(0), arr(v(1), prop())))
}
fn refl_ty(head: u64) -> Term {
  arr(Expr::sort(2), arr(v(0), eq(head, v(1), v(0), v(0))))
}
fn transport_ty(head: u64) -> Term {
  arr(ty(), arr(ty(), arr(eq(head, ty(), v(1), v(0)), arr(v(2), v(2)))))
}
fn shared_fn() -> Term {
  arr(r(0), r(0))
}
fn unique_fn() -> Term {
  Expr::all_contract(
    BinderContract::default(),
    ValueContract::unique(),
    r(0),
    r(0),
  )
}
fn unique_input() -> BinderContract {
  BinderContract { uses: Uses::Many, value: ValueContract::unique() }
}
fn generic() -> Term {
  Expr::lam(
    ty(),
    Expr::lam(
      ty(),
      Expr::lam(
        eq(4, ty(), v(1), v(0)),
        Expr::lam(v(2), apps(r(6), vec![v(3), v(2), v(1), v(0)])),
      ),
    ),
  )
}
fn decl(typ: Term, body: Option<Term>) -> Declaration {
  Declaration {
    typ,
    kind: if body.is_some() {
      DeclKind::Definition
    } else {
      DeclKind::Assumption
    },
    body,
  }
}
fn program() -> Program {
  Program {
    prop_sort: Some(1),
    declarations: vec![
      decl(ty(), None),
      decl(ty(), None),
      decl(ty(), Some(shared_fn())),
      decl(ty(), Some(unique_fn())),
      decl(eq_ty(), None),
      decl(refl_ty(4), None),
      decl(transport_ty(4), None),
      decl(shared_fn(), Some(Expr::lam(r(0), v(0)))),
      decl(transport_ty(4), Some(generic())),
      decl(eq_ty(), None),
      decl(refl_ty(9), None),
      decl(transport_ty(9), None),
      decl(arr(ty(), ty()), Some(Expr::lam(ty(), v(0)))),
      decl(prop(), None),
      decl(r(13), None),
      decl(arr(ty(), prop()), None),
      decl(arr(ty(), arr(v(0), Expr::app(r(15), v(1)))), None),
      decl(r(0), None),
    ],
    ..Program::default()
  }
}
fn metadata(p: &Program) -> Metadata {
  Metadata {
    universes: vec![
      Univ::succ(Univ::zero()),
      Univ::zero(),
      Univ::succ(Univ::succ(Univ::zero())),
    ],
    kinds: p
      .declarations
      .iter()
      .map(|d| {
        if d.body.is_some() {
          Kind::Definition
        } else {
          Kind::Axiom { standard: false }
        }
      })
      .collect(),
    level_arities: vec![0; p.declarations.len()],
    resource_sensitive: resource_sensitivity(p, p, Limits::default()).unwrap(),
    ..Metadata::default()
  }
}
fn refl(head: u64, a: Term) -> Term {
  apps(r(head), vec![ty(), a])
}
fn cast(head: u64, a: Term, b: Term, h: Term, value: Term) -> Term {
  apps(r(head), vec![a, b, h, value])
}
#[test]
fn source_contract_transport_synthetic_controls() {
  let p = program();
  let m = metadata(&p);
  let linear =
    BinderContract { uses: Uses::Linear, ..BinderContract::default() };
  let unique_input_fn =
    Expr::all_contract(unique_input(), ValueContract::shared(), r(0), r(0));
  let cases = vec![
    (
      "direct shared-to-unique",
      cast(6, shared_fn(), unique_fn(), refl(5, shared_fn()), r(7)),
      unique_fn(),
      false,
    ),
    (
      "alias laundering",
      cast(6, r(2), r(3), refl(5, r(2)), r(7)),
      unique_fn(),
      false,
    ),
    (
      "unique input changed",
      cast(6, shared_fn(), unique_input_fn.clone(), refl(5, shared_fn()), r(7)),
      unique_input_fn,
      false,
    ),
    (
      "generic laundering",
      cast(8, shared_fn(), unique_fn(), refl(5, shared_fn()), r(7)),
      unique_fn(),
      false,
    ),
    (
      "custom equality",
      cast(11, shared_fn(), unique_fn(), refl(10, shared_fn()), r(7)),
      unique_fn(),
      false,
    ),
    (
      "same type",
      cast(6, shared_fn(), shared_fn(), refl(5, shared_fn()), r(7)),
      shared_fn(),
      true,
    ),
    ("generic proof", generic(), transport_ty(4), true),
    (
      "beta laundering",
      cast(
        6,
        Expr::app(r(12), shared_fn()),
        Expr::app(r(12), unique_fn()),
        refl(5, Expr::app(r(12), shared_fn())),
        r(7),
      ),
      unique_fn(),
      false,
    ),
    (
      "beta control",
      cast(
        6,
        Expr::app(r(12), shared_fn()),
        shared_fn(),
        refl(5, Expr::app(r(12), shared_fn())),
        r(7),
      ),
      shared_fn(),
      true,
    ),
    ("dishonest promise", Expr::lam(r(0), v(0)), unique_fn(), false),
    (
      "Nonempty dishonest witness",
      apps(r(16), vec![unique_fn(), Expr::lam(r(0), r(17))]),
      Expr::app(r(15), unique_fn()),
      false,
    ),
    (
      "Prop telescope",
      Expr::lam_contract(linear, r(0), r(14)),
      Expr::all_contract(linear, ValueContract::shared(), r(0), r(13)),
      true,
    ),
    (
      "linear proof telescope capture",
      Expr::lam_contract(
        linear,
        r(0),
        apps(r(16), vec![shared_fn(), Expr::lam(r(0), v(1))]),
      ),
      Expr::all_contract(
        linear,
        ValueContract::shared(),
        r(0),
        Expr::app(r(15), shared_fn()),
      ),
      false,
    ),
  ];
  for (name, term, expected, accepted) in cases {
    let result = TransportChecker::new(&p, &p, &m, Limits::default()).check(
      256,
      &vec![],
      &term,
      &expected,
      Coverage::Uncovered,
    );
    assert_eq!(result.is_ok(), accepted, "{name}: {result:?}");
  }
  assert!(
    !TransportChecker::new(&p, &p, &m, Limits::default())
      .compatible(256, &vec![], &ty(), &prop())
      .unwrap()
  );
  let overridden = Program { interfaces: vec![(7, unique_fn())], ..p.clone() };
  assert!(
    TransportChecker::new(&p, &overridden, &m, Limits::default())
      .check(256, &vec![], &r(7), &unique_fn(), Coverage::Uncovered)
      .is_err()
  );
  let mut keep = p.clone();
  let typ =
    Expr::all_contract(unique_input(), ValueContract::unique(), r(0), r(0));
  let body = Expr::lam_contract(unique_input(), r(0), v(0));
  keep.declarations.push(decl(typ.clone(), Some(body.clone())));
  assert!(
    check_definition(&keep, p.declarations.len(), Limits::default()).is_ok()
  );
  assert!(
    TransportChecker::new(&keep, &keep, &metadata(&keep), Limits::default())
      .check(256, &vec![], &body, &typ, Coverage::Runtime)
      .is_ok()
  );
}

#[test]
fn computational_witness_coverage_boundaries() {
  let unique = unique_input();
  let fn_type = Expr::all_contract(unique, ValueContract::unique(), r(0), r(0));
  let bad = Expr::lam_contract(unique, r(0), r(1));
  let good = Expr::lam_contract(unique, r(0), v(0));
  let expression = Expr::app(r(3), bad.clone());
  let p = Program {
    prop_sort: Some(1),
    declarations: vec![
      decl(ty(), None),
      decl(r(0), None),
      decl(Expr::sort(2), Some(ty())),
      decl(arr(fn_type.clone(), r(2)), None),
      decl(r(2), Some(expression.clone())),
      decl(prop(), None),
      decl(arr(shared_fn(), arr(shared_fn(), r(5))), None),
      decl(arr(fn_type.clone(), prop()), None),
    ],
    ..Program::default()
  };
  let mut m = metadata(&p);
  m.kinds[2] = Kind::Opaque;
  assert!(check_definition(&p, 4, Limits::default()).is_ok());
  let capture = Expr::lam(r(0), v(1));
  let identity = Expr::lam(r(0), v(0));
  let proof_type =
    Expr::all_contract(unique, ValueContract::shared(), r(0), r(5));
  let pair =
    |a: Term, b: Term| Expr::lam_contract(unique, r(0), apps(r(6), vec![a, b]));
  for (name, term, expected, coverage, accepted) in vec![
    (
      "honest identity",
      good.clone(),
      fn_type.clone(),
      Coverage::Uncovered,
      true,
    ),
    (
      "dishonest promise",
      bad.clone(),
      fn_type.clone(),
      Coverage::Uncovered,
      false,
    ),
    ("opaque fresh", expression.clone(), r(2), Coverage::Uncovered, false),
    ("opaque inherited", expression, r(2), Coverage::Runtime, false),
    (
      "paired shared capture",
      pair(capture.clone(), capture),
      proof_type.clone(),
      Coverage::Uncovered,
      false,
    ),
    (
      "paired no capture",
      pair(identity.clone(), identity),
      proof_type,
      Coverage::Uncovered,
      true,
    ),
    (
      "dishonest type index",
      Expr::app(r(7), bad),
      prop(),
      Coverage::Uncovered,
      false,
    ),
    (
      "honest type index",
      Expr::app(r(7), good),
      prop(),
      Coverage::Uncovered,
      true,
    ),
  ] {
    let result = TransportChecker::new(&p, &p, &m, Limits::default()).check(
      256,
      &vec![],
      &term,
      &expected,
      coverage,
    );
    assert_eq!(result.is_ok(), accepted, "{name}: {result:?}");
  }
}

/// Local bounded census over explicitly supplied authenticated v4 closures.
/// Every row is path-to-env TAB path-to-profile TAB accept|reject.
#[test]
#[ignore = "requires IX_TRANSPORT_CASES manifest of retained canonical closures"]
fn addressed_transport_census() {
  let manifest =
    std::env::var("IX_TRANSPORT_CASES").expect("explicit census manifest");
  let mut failures = vec![];
  for line in std::fs::read_to_string(manifest)
    .unwrap()
    .lines()
    .filter(|s| !s.is_empty() && !s.starts_with('#'))
  {
    let fields = line.split('\t').collect::<Vec<_>>();
    assert_eq!(fields.len(), 3);
    let bytes = std::fs::read(fields[0]).unwrap();
    let mut input = bytes.as_slice();
    let env = ixon::env::Env::get(&mut input).unwrap();
    assert!(input.is_empty());
    let profile = ixon::resource::addressed::Profile::from_bytes(
      &std::fs::read(fields[1]).unwrap(),
    )
    .unwrap();
    let result = super::super::validate(&env, &profile).map(|_| ());
    let expected = match fields[2] {
      "accept" => true,
      "reject" => false,
      _ => panic!("expected verdict"),
    };
    println!("{}: {:?}", fields[0], result);
    if result.is_ok() != expected {
      failures.push((fields[0].to_owned(), result));
    }
  }
  assert!(failures.is_empty(), "{failures:?}");
}

#[test]
fn replacement_traversal_controls() {
  let unique = unique_input();
  let f = Expr::all_contract(unique, ValueContract::unique(), r(0), r(0));
  let bad = Expr::lam_contract(unique, r(0), r(1));
  let good = Expr::lam_contract(unique, r(0), v(0));
  let mut ctor = decl(arr(f.clone(), r(0)), None);
  ctor.kind = DeclKind::Constructor;
  let p = Program {
    prop_sort: Some(1),
    declarations: vec![
      decl(ty(), None),
      decl(r(0), None),
      decl(prop(), None),
      decl(arr(f.clone(), r(2)), None),
      decl(arr(f.clone(), f.clone()), None),
      ctor,
      decl(
        Expr::all_contract(
          BinderContract { uses: Uses::Erased, ..Default::default() },
          ValueContract::shared(),
          f.clone(),
          r(0),
        ),
        None,
      ),
    ],
    ..Default::default()
  };
  let m = Metadata {
    universes: vec![Univ::succ(Univ::zero()), Univ::zero()],
    kinds: vec![Kind::Axiom { standard: false }; 7],
    level_arities: vec![0; 7],
    resource_sensitive: resource_sensitivity(&p, &p, Limits::default())
      .unwrap(),
    ..Default::default()
  };
  for (name, term, expected, headers, accept) in [
    ("bad callback", bad.clone(), f.clone(), 0, false),
    ("honest callback", good.clone(), f.clone(), 0, true),
    ("hidden proof", Expr::app(r(3), bad.clone()), r(2), 0, false),
    ("honest proof", Expr::app(r(3), good.clone()), r(2), 0, true),
    ("indirect callback", Expr::app(r(4), bad.clone()), f.clone(), 0, false),
    ("constructor field", Expr::app(r(5), bad.clone()), r(0), 0, false),
    ("erased argument", Expr::app(r(6), bad.clone()), r(0), 0, false),
    (
      "let alias",
      Expr::let_(false, f.clone(), bad.clone(), v(0)),
      f.clone(),
      0,
      false,
    ),
    ("bad nested lambda", Expr::lam(r(0), bad), arr(r(0), f.clone()), 1, false),
    ("honest nested lambda", Expr::lam(r(0), good), arr(r(0), f), 1, true),
  ] {
    let result = TransportChecker::new(&p, &p, &m, Limits::default()).check(
      256,
      &vec![],
      &term,
      &expected,
      Coverage::Replacement(headers),
    );
    assert_eq!(result.is_ok(), accept, "{name}: {result:?}");
  }
}

#[test]
fn exact_transport_cache_context_controls() {
  let unique = unique_input();
  let f = Expr::all_contract(unique, ValueContract::unique(), r(0), r(0));
  let sf = arr(r(0), r(0));
  let bad = Expr::lam_contract(unique, r(0), r(1));
  let capture = Expr::lam(r(0), v(1));
  let p = Program {
    prop_sort: Some(1),
    sharing: vec![Expr::sort(2)],
    declarations: vec![decl(ty(), None), decl(r(0), None)],
    ..Default::default()
  };
  let m = Metadata {
    universes: vec![Univ::succ(Univ::zero()), Univ::zero(), Univ::var(0)],
    kinds: vec![Kind::Axiom { standard: false }; 2],
    level_arities: vec![0; 2],
    resource_sensitive: resource_sensitivity(&p, &p, Limits::default())
      .unwrap(),
    ..Default::default()
  };
  let mut c = TransportChecker::new(&p, &p, &m, Limits::default());
  c.check(256, &vec![], &bad, &f, Coverage::Runtime).unwrap();
  assert!(c.check(256, &vec![], &bad, &f, Coverage::Uncovered).is_err());
  let mut c = TransportChecker::new(&p, &p, &m, Limits::default());
  c.check(
    256,
    &vec![(BinderContract::default(), r(0))],
    &capture,
    &sf,
    Coverage::Uncovered,
  )
  .unwrap();
  assert!(
    c.check(256, &vec![(unique, r(0))], &capture, &sf, Coverage::Uncovered)
      .is_err()
  );
  let mut c = TransportChecker::new(&p, &p, &m, Limits::default());
  c.check(
    256,
    &vec![
      (BinderContract::default(), r(0)),
      (BinderContract::default(), f.clone()),
    ],
    &v(0),
    &f,
    Coverage::Runtime,
  )
  .unwrap();
  assert!(
    c.check(
      256,
      &vec![
        (BinderContract::default(), f.clone()),
        (BinderContract::default(), r(0))
      ],
      &v(0),
      &f,
      Coverage::Runtime
    )
    .is_err()
  );
  let mut c = TransportChecker::new(&p, &p, &m, Limits::default());
  let ctx = vec![(BinderContract::default(), f.clone())];
  c.check(256, &ctx, &v(0), &f, Coverage::Runtime).unwrap();
  assert!(c.check(256, &ctx, &v(0), &sf, Coverage::Runtime).is_err());
  let mut c = TransportChecker::new(&p, &p, &m, Limits::default());
  let a = c.instantiate_levels(256, &Expr::share(0), &[Univ::zero()]).unwrap();
  let b = c
    .instantiate_levels(256, &Expr::share(0), &[Univ::succ(Univ::zero())])
    .unwrap();
  let (Expr::Sort(a), Expr::Sort(b)) = (a.as_ref(), b.as_ref()) else {
    panic!("sort instances")
  };
  assert!(c.universe_zero(256, *a).unwrap());
  assert!(!c.universe_zero(256, *b).unwrap());
}

#[test]
fn committed_transport_fixtures() {
  let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("../../Tests/Fixtures/ixon-v4/transport");
  for (name, profile_hash, accepts) in [
    (
      "bridge-bad",
      "3a3b136bebf70228abeb5e8b6c40ce127d9f204807333b2eaaae5c4a4070497c",
      false,
    ),
    (
      "bridge-good",
      "3a3b136bebf70228abeb5e8b6c40ce127d9f204807333b2eaaae5c4a4070497c",
      true,
    ),
    (
      "recursion-zero",
      "cbd928242de3d2ddc78e84caf86152cf22ca15e77b5bb679029f35ebb862c5e0",
      true,
    ),
    (
      "recursion-succ",
      "5cd663ef2216856ff1ba728c924675056dfa9219b655694711c54f6812a26b35",
      true,
    ),
  ] {
    let bytes = std::fs::read(directory.join(format!("{name}.ixe"))).unwrap();
    let mut input = bytes.as_slice();
    let env = ixon::env::Env::get(&mut input).unwrap();
    assert!(input.is_empty());
    let profile = ixon::resource::addressed::Profile::from_bytes(
      &std::fs::read(directory.join(format!("{name}.profile"))).unwrap(),
    )
    .unwrap();
    assert_eq!(profile.address().unwrap().hex(), profile_hash, "{name}");
    let result = super::super::validate(&env, &profile);
    assert_eq!(result.is_ok(), accepts, "{name}: {result:?}");
    if name == "bridge-bad" {
      let message = result.unwrap_err();
      assert!(
        message.starts_with("resource admission Some(")
          && message.ends_with(": SharedToUnique"),
        "{name}: {message}"
      );
    }
  }
}
