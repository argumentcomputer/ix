//! Independent synthetic ownership diagnostics, paired with ResourceCaseAdmission.lean.
//! These tests do not establish authenticated primitive-family admission.
use super::*;
fn r(i: u64) -> Term {
  Expr::reference(i, vec![])
}
fn v(i: u64) -> Term {
  Expr::var(i)
}
fn arr(a: Term, b: Term) -> Term {
  Expr::all(a, b)
}
fn family(x: Term) -> Term {
  Expr::app(r(2), x)
}
fn apps(f: Term, xs: Vec<Term>) -> Term {
  xs.into_iter().fold(f, Expr::app)
}
fn assumption(typ: Term) -> Declaration {
  Declaration { typ, body: None, kind: DeclKind::Assumption }
}
fn definition(typ: Term, body: Term) -> Declaration {
  Declaration { typ, body: Some(body), kind: DeclKind::Definition }
}
fn base() -> Program {
  Program {
    prop_sort: Some(1),
    cases: true,
    shareable_types: vec![0],
    declarations: vec![
      Declaration {
        typ: Expr::sort(0),
        body: None,
        kind: DeclKind::TypeConstructor,
      },
      Declaration { typ: r(0), body: None, kind: DeclKind::Constructor },
      assumption(arr(r(0), Expr::sort(0))),
      assumption(arr(r(0), family(v(0)))),
      assumption(arr(
        arr(r(0), Expr::sort(0)),
        arr(Expr::app(v(0), r(1)), arr(r(0), Expr::app(v(2), v(0)))),
      )),
      assumption(arr(family(r(1)), r(0))),
    ],
    recursors: vec![RecursorInfo {
      index: 4,
      params: 0,
      motives: 1,
      minors: 1,
      indices: 0,
      fields: vec![0],
      binders: vec![0],
    }],
    conversion_recursors: vec![ConversionRecursor {
      index: 4,
      leading: 2,
      major: 2,
      rules: vec![ConversionRule {
        constructor: 1,
        params: 0,
        fields: 0,
        rhs: Expr::lam(Expr::sort(0), Expr::lam(Expr::sort(0), v(0))),
      }],
    }],
    ..Program::default()
  }
}
fn ordinary(fixed: bool) -> Declaration {
  let index = if fixed { r(1) } else { v(0) };
  definition(
    arr(r(0), arr(family(index.clone()), r(0))),
    Expr::lam(
      r(0),
      Expr::lam(
        family(index),
        apps(
          r(4),
          vec![
            Expr::lam(r(0), arr(family(v(0)), r(0))),
            Expr::lam(family(r(1)), Expr::app(r(5), v(0))),
            if fixed { r(1) } else { v(1) },
            v(0),
          ],
        ),
      ),
    ),
  )
}
fn independent_major() -> Declaration {
  definition(
    arr(r(0), arr(r(0), arr(family(v(0)), r(0)))),
    Expr::lam(
      r(0),
      Expr::lam(
        r(0),
        Expr::lam(
          family(v(0)),
          apps(
            r(4),
            vec![
              Expr::lam(r(0), arr(family(v(0)), r(0))),
              Expr::lam(family(r(1)), Expr::app(r(5), v(0))),
              v(2),
              v(0),
            ],
          ),
        ),
      ),
    ),
  )
}
fn callback(result: ValueContract, index: Term) -> Term {
  let index = match index.as_ref() {
    Expr::Var(n) => v(n + 1),
    _ => index,
  };
  Expr::all_contract(BinderContract::default(), result, r(0), family(index))
}
fn higher_order() -> Declaration {
  let shared = ValueContract::shared();
  definition(
    arr(r(0), arr(callback(shared, v(0)), r(0))),
    Expr::lam(
      r(0),
      Expr::lam(
        callback(shared, v(0)),
        apps(
          r(4),
          vec![
            Expr::lam(r(0), arr(callback(shared, v(0)), r(0))),
            Expr::lam(callback(shared, r(1)), Expr::app(r(6), v(0))),
            v(1),
            v(0),
          ],
        ),
      ),
    ),
  )
}
fn expect(name: &str, mut p: Program, d: Declaration, accept: bool) {
  p.declarations.push(d);
  let result =
    check_definition(&p, p.declarations.len() - 1, Limits::default());
  if accept {
    assert_eq!(result, Ok(()), "{name}");
  } else {
    assert_eq!(result, Err(Error::TypeMismatch), "{name}");
  }
}
#[test]
fn lexical_case_admission_controls() {
  expect("fixed major", base(), ordinary(true), true);
  expect("variable major", base(), ordinary(false), true);
  expect("different lexical major", base(), independent_major(), false);
  let mut p = base();
  p.conversion_recursors.clear();
  expect("no refinement metadata", p, ordinary(false), false);
  let mut p = base();
  p.conversion_recursors[0].major = 1;
  expect("wrong major position", p, ordinary(false), false);
  let mut p = base();
  p.conversion_recursors[0].leading = 1;
  expect("wrong leading count", p, ordinary(false), false);
  let mut p = base();
  p.conversion_recursors[0].rules[0].params = 1;
  expect("wrong constructor parameters", p, ordinary(false), false);
  let mut p = base();
  p.conversion_recursors[0].rules[0].fields = 1;
  expect("wrong constructor fields", p, ordinary(false), false);
  for bad in [false, true] {
    let mut p = base();
    p.declarations.push(assumption(arr(
      callback(
        if bad { ValueContract::unique() } else { ValueContract::shared() },
        r(1),
      ),
      r(0),
    )));
    expect(
      if bad {
        "dependent callback result differs"
      } else {
        "dependent callback positive"
      },
      p,
      higher_order(),
      !bad,
    );
  }
}
