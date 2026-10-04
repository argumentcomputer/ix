//! Contract-preserving reduction; no erased conversion fallback.
use super::*;
fn apply_args(head: Term, args: impl IntoIterator<Item = Term>) -> Term {
  args.into_iter().fold(head, Expr::app)
}
impl TransportChecker<'_> {
  fn natural_constructor(
    &mut self,
    fuel: usize,
    value: &BigUint,
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    let Some(typ) = &self.source.nat_type else {
      return Err(Error::Unsupported(
        "transport: numeric reduction has no natural type",
      ));
    };
    let Expr::Ref(family, _) = typ.as_ref() else {
      return Err(Error::TypeMismatch);
    };
    let ind = self.metadata.inductive(*family).cloned().ok_or(
      Error::Unsupported("transport: natural constructor metadata missing"),
    )?;
    if ind.params != 0 || ind.indices != 0 || ind.constructors.len() != 2 {
      return Err(Error::Unsupported(
        "transport: invalid natural constructor metadata",
      ));
    }
    if value == &BigUint::from(0u8) {
      Ok(Expr::reference(ind.constructors[0], vec![]))
    } else {
      Ok(Expr::app(
        Expr::reference(ind.constructors[1], vec![]),
        self.natural_constructor(fuel, &(value - BigUint::from(1u8)))?,
      ))
    }
  }
  pub(super) fn whnf(&mut self, fuel: usize, e: &Term) -> Result<Term, Error> {
    self.tick(fuel)?;
    if let Some(result) = self.whnf_cache.get(e) {
      return Ok(result.clone());
    }
    let result = self.whnf_core(fuel, e)?;
    self.whnf_cache.insert(e.clone(), result.clone());
    Ok(result)
  }
  fn whnf_core(&mut self, fuel: usize, e: &Term) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    match e.as_ref() {
      Expr::Share(i) => self.whnf(fuel, &self.expansion(*i)?),
      Expr::Let(_, _, value, body) => {
        let body = self.substitute(fuel, body, value, 0)?;
        self.whnf(fuel, &body)
      },
      Expr::Ref(i, levels) => {
        if self.metadata.kinds.get(*i as usize) == Some(&Kind::Opaque) {
          return Ok(e.clone());
        }
        if let Some(body) = self.declaration(*i)?.body.clone() {
          let body = self.instantiate_declaration(fuel, *i, levels, &body)?;
          self.whnf(fuel, &body)
        } else {
          Ok(e.clone())
        }
      },
      Expr::Prj(owner, field, value) => {
        let value = self.whnf(fuel, value)?;
        let (head, args) = self.split_app(fuel, &value)?;
        if let Expr::Ref(c, _) = head.as_ref() {
          if let Some(ctor) = self.metadata.constructor(*c).cloned() {
            if ctor.family != *owner {
              return Err(Error::Unsupported(
                "transport: projection constructor owner mismatch",
              ));
            }
            if (*field as usize) < ctor.fields
              && args.len() == ctor.params + ctor.fields
            {
              return self.whnf(fuel, &args[ctor.params + *field as usize]);
            }
          }
        }
        Ok(Expr::prj(*owner, *field, value))
      },
      Expr::App(fun, arg) => {
        let fun = self.whnf(fuel, fun)?;
        if let Expr::Lam(_, _, body) = fun.as_ref() {
          let body = self.substitute(fuel, body, arg, 0)?;
          return self.whnf(fuel, &body);
        }
        let rebuilt = Expr::app(fun, arg.clone());
        let (head, args) = self.split_app(fuel, &rebuilt)?;
        let Expr::Ref(i, levels) = head.as_ref() else {
          return Ok(rebuilt);
        };
        let Some(rec) = self.metadata.recursor(*i).cloned() else {
          return Ok(rebuilt);
        };
        let position = rec.major()?;
        if args.len() <= position {
          return Ok(rebuilt);
        }
        let mut major = self.whnf(fuel, &args[position])?;
        if let Expr::Nat(payload) = major.as_ref() {
          let n = self
            .metadata
            .naturals
            .iter()
            .find(|(i, _)| i == payload)
            .map(|(_, n)| n.clone())
            .ok_or(Error::Unsupported(
              "transport: numeric payload metadata missing",
            ))?;
          major = self.natural_constructor(fuel, &n)?;
        }
        let (ctor_head, ctor_args) = self.split_app(fuel, &major)?;
        let Expr::Ref(c, _) = ctor_head.as_ref() else {
          return Ok(rebuilt);
        };
        let Some(ctor) = self.metadata.constructor(*c).cloned() else {
          return Ok(rebuilt);
        };
        if ctor.family != rec.family {
          return Err(Error::Unsupported(
            "transport: recursor constructor family mismatch",
          ));
        }
        let rule = rec
          .rules
          .get(ctor.position)
          .ok_or(Error::Unsupported("transport: recursor rule missing"))?;
        if rule.fields != ctor.fields
          || ctor_args.len() != ctor.params + ctor.fields
        {
          return Err(Error::Unsupported(
            "transport: recursor constructor arity mismatch",
          ));
        }
        let leading = rec.params + rec.motives + rec.minors;
        let rhs = self.instantiate_declaration(fuel, *i, levels, &rule.rhs)?;
        let args = args[..leading]
          .iter()
          .chain(&ctor_args[ctor.params..])
          .chain(&args[position + 1..])
          .cloned();
        self.whnf(fuel, &apply_args(rhs, args))
      },
      Expr::Rec(..) => {
        Err(Error::Unsupported("transport: unresolved recursive reference"))
      },
      _ => Ok(e.clone()),
    }
  }
  pub(super) fn arrow(
    &mut self,
    fuel: usize,
    typ: &Term,
  ) -> Result<Arrow, Error> {
    match self.whnf(fuel, typ)?.as_ref() {
      Expr::All(c, r, a, b) => Ok((*c, *r, a.clone(), b.clone())),
      _ => Err(Error::Unsupported("transport: expected a dependent arrow")),
    }
  }
}
