//! Narrow ownership operations used by the strengthened typing gate.
//! These are resource diagnostics, not a certificate of erased/source typing.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coverage {
  Uncovered,
  Runtime,
  Alternative(usize),
}

fn metered<T>(
  p: &Program,
  depth: usize,
  steps: &mut usize,
  action: impl FnOnce(&mut Checker<'_>) -> Result<T, Error>,
) -> Result<T, Error> {
  let mut checker = Checker::new(p, Limits { depth, steps: *steps });
  let result = action(&mut checker);
  *steps = checker.state.remaining;
  result
}

pub fn shift(
  p: &Program,
  fuel: usize,
  steps: &mut usize,
  term: &Term,
  amount: u64,
  cutoff: u64,
) -> Result<Term, Error> {
  metered(p, fuel, steps, |c| c.shift(fuel, term, amount, cutoff))
}
pub fn substitute(
  p: &Program,
  fuel: usize,
  steps: &mut usize,
  term: &Term,
  value: &Term,
  depth: u64,
) -> Result<Term, Error> {
  metered(p, fuel, steps, |c| c.substitute(fuel, term, value, depth))
}

/// Mirrors the runtime interpreter's argument eligibility. All types and
/// arguments must use runtime sort IDs; lexical entries retain binder order.
pub fn argument_coverage(
  p: &Program,
  fuel: usize,
  steps: &mut usize,
  lexical: &[(BinderContract, Term)],
  head: &Term,
  args: &[Term],
  position: usize,
) -> Result<Coverage, Error> {
  metered(p, fuel, steps, |c| {
    if position >= args.len() {
      return Err(Error::Unsupported("transport: argument index"));
    }
    let mut ctx = Context::default();
    for (contract, typ) in lexical {
      ctx.vars.push(c.push(*contract, Value::shared(typ.clone())));
    }
    let mut typ = c.type_of(fuel, &ctx, head)?;
    if let Expr::Ref(index, _) = head.as_ref() {
      let special = p.choices.contains(index)
        || (p.cases
          && c.recursor_info(*index).is_some_and(|r| args.len() >= r.arity()));
      if special {
        typ = c.declaration(*index)?.typ.clone();
      }
    }
    for arg in &args[..position] {
      let (_, _, _, body) = c.arrow(fuel, &typ)?;
      typ = c.substitute(fuel, &body, arg, 0)?;
    }
    let (input, _, domain, _) = c.arrow(fuel, &typ)?;
    if let Expr::Ref(index, _) = head.as_ref() {
      if p.choices.contains(index) {
        let declared = c.declaration(*index)?.typ.clone();
        let n = c.arity(fuel, &declared)?;
        if args.len() >= n && n >= 2 && position >= n - 2 && position < n {
          let mut inner = ctx.clone();
          let mut ty = domain.clone();
          let mut count = 0;
          loop {
            let reduced = c.whnf(fuel, &ty)?;
            let Expr::All(contract, _, a, b) = reduced.as_ref() else {
              break;
            };
            if !c.is_proposition(fuel, &inner, a)? {
              break;
            }
            inner.vars.push(c.push(*contract, Value::shared(a.clone())));
            ty = b.clone();
            count += 1;
          }
          return Ok(Coverage::Alternative(count));
        }
      }
      if p.cases {
        if let Some(r) = c.recursor_info(*index) {
          if args.len() >= r.arity() {
            if position >= r.params + r.motives
              && position < r.params + r.motives + r.minors
            {
              return Ok(Coverage::Alternative(
                r.binders[position - r.params - r.motives],
              ));
            }
            if position < r.arity() - 1 {
              return Ok(Coverage::Uncovered);
            }
          }
        }
      }
      if let Some(shape) = c.case_definition(fuel, 4, *index)? {
        if args.len() >= shape.arity {
          if let Some(Some(supplied)) = shape.by_need.get(position) {
            if c.alternative_argument(
              fuel,
              &ctx,
              *supplied,
              &args[position],
              &domain,
            )? {
              return Ok(Coverage::Alternative(*supplied));
            }
          }
        }
      }
    }
    if input.uses == Uses::Erased
      || c.is_proposition(fuel, &ctx, &typ)?
      || c.is_proposition(fuel, &ctx, &domain)?
      || matches!(c.whnf(fuel, &domain)?.as_ref(), Expr::Sort(_))
    {
      Ok(Coverage::Uncovered)
    } else {
      Ok(Coverage::Runtime)
    }
  })
}

pub fn runtime_sort(
  p: &Program,
  fuel: usize,
  steps: &mut usize,
  typ: &Term,
) -> Result<bool, Error> {
  metered(p, fuel, steps, |c| {
    Ok(matches!(c.whnf(fuel, typ)?.as_ref(), Expr::Sort(_)))
  })
}
pub fn default_closed(
  p: &Program,
  fuel: usize,
  steps: &mut usize,
  lexical: &[(BinderContract, Term)],
  term: &Term,
  expected: &Term,
  sensitive: &[bool],
) -> Result<bool, Error> {
  if sensitive.len() != p.declarations.len() {
    return Ok(false);
  }
  metered(p, fuel, steps, |c| {
    if lexical.iter().any(|(b, _)| *b != BinderContract::default()) {
      return Ok(false);
    }
    for e in std::iter::once(term)
      .chain(std::iter::once(expected))
      .chain(lexical.iter().map(|(_, t)| t))
    {
      let scan = c.scan(fuel, e)?;
      if scan.annotated
        || scan
          .dependencies
          .iter()
          .any(|i| sensitive.get(*i).copied().unwrap_or(true))
      {
        return Ok(false);
      }
    }
    Ok(true)
  })
}
pub fn contextual_witness(
  p: &Program,
  fuel: usize,
  steps: &mut usize,
  lexical: &[(BinderContract, Term)],
  term: &Term,
  expected: &Term,
) -> Result<(), Error> {
  metered(p, fuel, steps, |c| {
    if matches!(c.whnf(fuel, expected)?.as_ref(), Expr::Sort(_)) {
      return Err(Error::Unsupported(
        "transport: runtime type erasure would skip a computational witness",
      ));
    }
    let caller = c.scope(0)?;
    let scope = c.scope(caller)?;
    let mut ctx = Context { vars: vec![], scope, ..Context::default() };
    for (contract, domain) in lexical {
      let contract = BinderContract {
        uses: if contract.uses == Uses::Linear {
          Uses::Affine
        } else {
          contract.uses
        },
        ..*contract
      };
      let duplicable = contract.value.owned == Owned::Shared
        || c.is_shareable(fuel, domain)?
        || c.is_scalar(fuel, domain)?;
      let freezable = contract.value.owned == Owned::Unique
        && !duplicable
        && c.plain_data(fuel, domain)?;
      let value = Value {
        typ: domain.clone(),
        owned: contract.value.owned,
        duplicable,
        freezable,
        origins: if contract.value.locality == Locality::Local {
          vec![caller]
        } else {
          vec![]
        },
        ..Value::shared(domain.clone())
      };
      ctx.vars.push(c.push(contract, value));
    }
    c.analyze(
      fuel,
      &ctx,
      term,
      Some((expected.clone(), ValueContract::shared())),
      caller,
      Uses::Linear,
    )?;
    for id in ctx.vars {
      c.validate_binder(fuel, id)?;
    }
    Ok(())
  })
}
