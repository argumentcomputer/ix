//! Whole-closure source-contract gate, subsequent to erased validation.
use super::*;
use ixon::resource::{DeclKind, dependency_graph, propagate, relevance};
#[derive(Clone, Debug, Default)]
pub(super) struct Request {
  pub roots: Vec<usize>,
  pub runtime_covered: Vec<usize>,
  pub assumptions: Vec<usize>,
  pub equations: Vec<(usize, usize)>,
}
pub(super) fn resource_sensitivity(
  logical: &Program,
  runtime: &Program,
  limits: Limits,
) -> Result<Vec<bool>, Error> {
  let (mut graph, mut marks) = dependency_graph(logical, limits)?;
  let (other, seeds) = dependency_graph(runtime, limits)?;
  if graph.len() != other.len() {
    return Err(Error::Unsupported(
      "transport: source/runtime declaration mismatch",
    ));
  }
  for i in 0..graph.len() {
    graph[i].extend(other[i].iter().copied());
    marks[i] |= seeds[i];
  }
  Ok(propagate(&graph, marks))
}
fn forward_closure(
  p: &Program,
  limits: Limits,
  roots: &[usize],
) -> Result<Vec<bool>, Error> {
  let (reverse, _) = dependency_graph(p, limits)?;
  let mut forward = vec![vec![]; p.declarations.len()];
  for (dependency, callers) in reverse.iter().enumerate() {
    for caller in callers {
      forward[*caller].push(dependency);
    }
  }
  let mut selected = vec![false; p.declarations.len()];
  for root in roots {
    *selected.get_mut(*root).ok_or(Error::BadReference(*root as u64))? = true;
  }
  Ok(propagate(&forward, selected))
}
fn primitive(kind: &Kind) -> bool {
  matches!(
    kind,
    Kind::Inductive | Kind::Constructor | Kind::Recursor | Kind::Quotient
  )
}
fn primitive_fragment(
  p: &Program,
  m: &Metadata,
  limits: Limits,
  selected: &[bool],
) -> Result<(), Error> {
  let roots = selected
    .iter()
    .enumerate()
    .filter_map(|(i, b)| {
      (*b && m.kinds.get(i).is_some_and(primitive)).then_some(i)
    })
    .collect::<Vec<_>>();
  let dependencies = forward_closure(p, limits, &roots)?;
  let (_, marked) = dependency_graph(p, limits)?;
  if m.unsafe_primitives.iter().any(|i| dependencies.get(*i) == Some(&true)) {
    return Err(Error::Unsupported(
      "transport: unsafe primitive family is outside the validated fragment",
    ));
  }
  if dependencies.iter().zip(&marked).any(|(a, b)| *a && *b) {
    return Err(Error::Unsupported(
      "transport: annotated primitive family requires contract-sensitive primitive rules",
    ));
  }
  for i in roots {
    match m.kinds[i] {
      Kind::Inductive => {
        let ind = m.inductive(i as u64).ok_or(Error::Unsupported(
          "transport: incomplete inductive metadata",
        ))?;
        for c in &ind.constructors {
          let ctor = m.constructor(*c).ok_or(Error::Unsupported(
            "transport: incomplete constructor family",
          ))?;
          if ctor.family != i as u64 || ctor.params != ind.params {
            return Err(Error::Unsupported(
              "transport: mismatched constructor family",
            ));
          }
        }
      },
      Kind::Constructor => {
        let ctor = m.constructor(i as u64).ok_or(Error::Unsupported(
          "transport: incomplete constructor metadata",
        ))?;
        let ind = m
          .inductive(ctor.family)
          .ok_or(Error::Unsupported("transport: constructor owner missing"))?;
        if ind.constructors.get(ctor.position) != Some(&ctor.index) {
          return Err(Error::Unsupported(
            "transport: constructor ordinal mismatch",
          ));
        }
      },
      Kind::Recursor => {
        let rec = m.recursor(i as u64).ok_or(Error::Unsupported(
          "transport: incomplete recursor metadata",
        ))?;
        let ind = m
          .inductive(rec.family)
          .ok_or(Error::Unsupported("transport: recursor family missing"))?;
        if rec.rules.len() != ind.constructors.len() {
          return Err(Error::Unsupported(
            "transport: incomplete recursor rules",
          ));
        }
        for (j, rule) in rec.rules.iter().enumerate() {
          let ctor = m.constructor(ind.constructors[j]).ok_or(
            Error::Unsupported("transport: recursor constructor missing"),
          )?;
          if rule.fields != ctor.fields {
            return Err(Error::Unsupported(
              "transport: recursor rule field mismatch",
            ));
          }
        }
      },
      _ => {},
    }
  }
  Ok(())
}
impl TransportChecker<'_> {
  fn validate_equation(
    &mut self,
    fuel: usize,
    definition: usize,
    equation: usize,
  ) -> Result<usize, Error> {
    let eq = self.metadata.eq_type.ok_or(Error::Unsupported(
      "transport: canonical equality identity absent",
    ))?;
    let levels = *self
      .metadata
      .level_arities
      .get(definition)
      .ok_or(Error::BadReference(definition as u64))?;
    if self.metadata.level_arities.get(equation) != Some(&levels) {
      return Err(Error::Unsupported(
        "transport: equation universe arity differs from definition",
      ));
    }
    let mut statement = self.declaration(equation as u64)?.typ.clone();
    let mut expected = self.declaration(definition as u64)?.typ.clone();
    let mut ctx = vec![];
    let mut count = 0;
    for _ in 0..fuel {
      let reduced = self.whnf(fuel, &statement)?;
      let Expr::All(_, _, domain, body) = reduced.as_ref() else {
        statement = reduced;
        break;
      };
      let (input, _, source_domain, source_body) =
        self.arrow(fuel, &expected)?;
      if !self.compatible(fuel, &ctx, domain, &source_domain)? {
        return Err(Error::TypeMismatch);
      }
      ctx.push((input, source_domain));
      expected = source_body;
      statement = body.clone();
      count += 1;
    }
    let (head, args) = self.split_app(fuel, &statement)?;
    if !matches!(head.as_ref(),Expr::Ref(i,_)if *i==eq) || args.len() != 3 {
      return Err(Error::Unsupported(
        "transport: equation has no canonical equality statement",
      ));
    }
    let (function, arguments) = self.split_app(fuel, &args[1])?;
    let Expr::Ref(index, us) = function.as_ref() else {
      return Err(Error::Unsupported(
        "transport: equation lhs is not a declaration",
      ));
    };
    if *index as usize != definition
      || us.len() != levels
      || arguments.len() != count
    {
      return Err(Error::Unsupported(
        "transport: equation lhs does not apply its original declaration",
      ));
    }
    for (i, u) in us.iter().enumerate() {
      if self.read_universe(*u)?.as_ref() != &Univ::Var(i as u64) {
        return Err(Error::Unsupported(
          "transport: equation specializes a declaration universe",
        ));
      }
    }
    for (i, a) in arguments.iter().enumerate() {
      let mut a = a.clone();
      let mut depth = fuel;
      while let Expr::Share(j) = a.as_ref() {
        depth = self.tick(depth)?;
        a = self.expansion(*j)?;
      }
      if a.as_ref() != &Expr::Var((count - 1 - i) as u64) {
        return Err(Error::Unsupported(
          "transport: equation lhs argument telescope differs",
        ));
      }
    }
    Ok(count)
  }
}
pub(super) fn validate(
  logical: &Program,
  runtime: &Program,
  metadata: &Metadata,
  request: &Request,
  limits: Limits,
) -> Result<(), Failure> {
  let p = source_program(metadata, logical);
  let mut metadata = metadata.clone();
  let global = |error| Failure { declaration: None, error };
  metadata.resource_sensitive =
    resource_sensitivity(&p, runtime, limits).map_err(global)?;
  if metadata.kinds.len() != p.declarations.len()
    || metadata.level_arities.len() != p.declarations.len()
  {
    return Err(global(Error::Unsupported(
      "transport: incomplete declaration metadata",
    )));
  }
  let mut roots = request.roots.clone();
  for (d, t) in &request.equations {
    roots.extend([*d, *t]);
  }
  let selected = forward_closure(&p, limits, &roots).map_err(global)?;
  primitive_fragment(&p, &metadata, limits, &selected).map_err(global)?;
  let marked = relevance(runtime, limits).map_err(global)?;
  let mut replacements = vec![];
  for (d, t) in &request.equations {
    let mut c = TransportChecker::new(&p, runtime, &metadata, limits);
    let count = c
      .validate_equation(limits.depth, *d, *t)
      .map_err(|error| Failure { declaration: Some(*t), error })?;
    if marked.get(*d) == Some(&true)
      && !request.assumptions.contains(d)
      && runtime
        .declarations
        .get(*d)
        .is_some_and(|decl| decl.kind == DeclKind::Definition)
      && runtime.equations.contains(&(*d as u64, *t as u64))
    {
      replacements.push((*d, count));
    }
  }
  for (i, d) in p.declarations.iter().enumerate() {
    if !selected[i] {
      continue;
    }
    let mut c = TransportChecker::new(&p, runtime, &metadata, limits);
    let result = (|| {
      let sort = c.infer(limits.depth, &vec![], &d.typ, Coverage::Uncovered)?;
      c.require_sort(limits.depth, &sort)?;
      if let Some(body) = &d.body {
        let coverage =
          if let Some((_, n)) = replacements.iter().find(|(j, _)| *j == i) {
            Coverage::Replacement(*n)
          } else if request.runtime_covered.contains(&i) {
            Coverage::Runtime
          } else {
            Coverage::Uncovered
          };
        c.check(limits.depth, &vec![], body, &d.typ, coverage)
      } else {
        match metadata.kinds[i] {
          Kind::Inductive
          | Kind::Constructor
          | Kind::Recursor
          | Kind::Quotient => Ok(()),
          Kind::Axiom { standard }
            if standard || request.assumptions.contains(&i) =>
          {
            Ok(())
          },
          Kind::Axiom { .. } => {
            Err(Error::Unsupported("transport: untrusted source axiom"))
          },
          _ => Err(Error::Unsupported(
            "transport: source declaration has no checked body",
          )),
        }
      }
    })();
    #[cfg(test)]
    if result == Err(Error::Budget)
      && std::env::var_os("IX_TRANSPORT_TRACE").is_some()
    {
      eprintln!(
        "transport budget declaration={i} remaining={} depth={}",
        c.remaining, limits.depth
      );
    }
    result.map_err(|error| Failure { declaration: Some(i), error })?;
  }
  Ok(())
}

#[cfg(test)]
mod safety_tests {
  use super::*;
  #[test]
  fn equation_binding_rejects_universe_specialization() {
    for (level, expected) in [(0, true), (1, false)] {
      let lhs = Expr::reference(0, vec![level]);
      let statement = Expr::app(
        Expr::app(
          Expr::app(Expr::reference(2, vec![]), Expr::sort(0)),
          lhs.clone(),
        ),
        lhs,
      );
      let p = Program {
        declarations: vec![
          Declaration {
            typ: Expr::sort(0),
            body: None,
            kind: DeclKind::Assumption,
          },
          Declaration {
            typ: statement,
            body: None,
            kind: DeclKind::Assumption,
          },
          Declaration {
            typ: Expr::sort(0),
            body: None,
            kind: DeclKind::Assumption,
          },
        ],
        ..Program::default()
      };
      let m = Metadata {
        universes: vec![Arc::new(Univ::Var(0)), Univ::zero()],
        level_arities: vec![1, 1, 0],
        eq_type: Some(2),
        ..Metadata::default()
      };
      let result = TransportChecker::new(&p, &p, &m, Limits::default())
        .validate_equation(256, 0, 1);
      assert_eq!(result.is_ok(), expected, "universe {level}: {result:?}");
    }
  }
  #[test]
  fn selected_unsafe_primitive_is_rejected() {
    let p = Program {
      declarations: vec![Declaration {
        typ: Expr::sort(0),
        body: None,
        kind: DeclKind::Assumption,
      }],
      ..Program::default()
    };
    let mut m = Metadata {
      kinds: vec![Kind::Inductive],
      inductives: vec![Inductive {
        index: 0,
        params: 0,
        indices: 0,
        constructors: vec![],
      }],
      ..Metadata::default()
    };
    assert!(primitive_fragment(&p, &m, Limits::default(), &[true]).is_ok());
    m.unsafe_primitives.push(0);
    assert_eq!(
      primitive_fragment(&p, &m, Limits::default(), &[true]),
      Err(Error::Unsupported(
        "transport: unsafe primitive family is outside the validated fragment"
      ))
    );
    assert!(primitive_fragment(&p, &m, Limits::default(), &[false]).is_ok());
  }
}
