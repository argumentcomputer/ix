//! Bidirectional full-contract source typing and typed conversion.
use super::*;
impl TransportChecker<'_> {
  pub(super) fn get_sort(
    &mut self,
    fuel: usize,
    typ: &Term,
  ) -> Result<u64, Error> {
    match self.whnf(fuel, typ)?.as_ref() {
      Expr::Sort(u) => Ok(*u),
      _ => Err(Error::Unsupported("transport: expected a sort")),
    }
  }
  pub(super) fn require_sort(
    &mut self,
    fuel: usize,
    typ: &Term,
  ) -> Result<(), Error> {
    self.get_sort(fuel, typ).map(|_| ())
  }
  fn atom_type(
    &mut self,
    fuel: usize,
    ctx: &Context,
    e: &Term,
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    match e.as_ref() {
      Expr::Var(i) => {
        let n = *i as usize;
        let pos = ctx
          .len()
          .checked_sub(n)
          .and_then(|v| v.checked_sub(1))
          .ok_or(Error::Unbound(n))?;
        self.shift(fuel, &ctx[pos].1, i.checked_add(1).ok_or(Error::Budget)?, 0)
      },
      Expr::Nat(_) => self
        .source
        .nat_type
        .clone()
        .ok_or(Error::Unsupported("transport: natural type missing")),
      Expr::Str(_) => self
        .source
        .string_type
        .clone()
        .ok_or(Error::Unsupported("transport: string type missing")),
      _ => Err(Error::TypeMismatch),
    }
  }
  fn projection_type(
    &mut self,
    fuel: usize,
    owner: u64,
    field: u64,
    value: &Term,
    value_type: &Term,
  ) -> Result<Term, Error> {
    let ind = self.metadata.inductive(owner).cloned().ok_or(
      Error::Unsupported("transport: projection family metadata missing"),
    )?;
    if ind.constructors.len() != 1 {
      return Err(Error::Unsupported(
        "transport: projection family is not a structure",
      ));
    }
    let ctor = self.metadata.constructor(ind.constructors[0]).cloned().ok_or(
      Error::Unsupported("transport: projection constructor metadata missing"),
    )?;
    if field as usize >= ctor.fields {
      return Err(Error::Unsupported(
        "transport: projection field is out of bounds",
      ));
    }
    let typ = self.whnf(fuel, value_type)?;
    let (head, args) = self.split_app(fuel, &typ)?;
    if !matches!(head.as_ref(),Expr::Ref(i,_)if *i==owner)
      || args.len() != ind.params + ind.indices
    {
      return Err(Error::Unsupported(
        "transport: projected value has no exposed structure type",
      ));
    }
    let Expr::Ref(_, levels) = head.as_ref() else {
      return Err(Error::TypeMismatch);
    };
    let mut telescope = self.instantiate_declaration(
      fuel,
      ctor.index,
      levels,
      &self.declaration(ctor.index)?.typ.clone(),
    )?;
    for arg in args.iter().take(ctor.params) {
      let (_, _, _, body) = self.arrow(fuel, &telescope)?;
      telescope = self.substitute(fuel, &body, arg, 0)?;
    }
    for k in 0..field {
      let (_, _, _, body) = self.arrow(fuel, &telescope)?;
      telescope =
        self.substitute(fuel, &body, &Expr::prj(owner, k, value.clone()), 0)?;
    }
    Ok(self.arrow(fuel, &telescope)?.2)
  }
  fn erased_context(
    &mut self,
    fuel: usize,
    ctx: &Context,
    prop: u64,
    typ: u64,
  ) -> Result<Context, Error> {
    ctx
      .iter()
      .map(|(c, t)| Ok((*c, self.erase_levels(fuel, t, prop, typ)?)))
      .collect()
  }
  fn check_witness(
    &mut self,
    fuel: usize,
    ctx: &Context,
    term: &Term,
    expected: &Term,
  ) -> Result<bool, Error> {
    if support::default_closed(
      self.source,
      fuel,
      &mut self.remaining,
      ctx,
      term,
      expected,
      &self.metadata.resource_sensitive,
    )? {
      return Ok(false);
    }
    let prop = self
      .runtime
      .prop_sort
      .ok_or(Error::Unsupported("transport: ownership Prop metadata absent"))?;
    let typ = if prop == 0 { 1 } else { 0 };
    let term = self.erase_levels(fuel, term, prop, typ)?;
    let expected = self.erase_levels(fuel, expected, prop, typ)?;
    let lexical = self.erased_context(fuel, ctx, prop, typ)?;
    support::contextual_witness(
      self.runtime,
      fuel,
      &mut self.remaining,
      &lexical,
      &term,
      &expected,
    )?;
    Ok(true)
  }
  fn argument_coverage(
    &mut self,
    fuel: usize,
    ctx: &Context,
    head: &Term,
    args: &[Term],
    position: usize,
  ) -> Result<Coverage, Error> {
    let prop = self
      .runtime
      .prop_sort
      .ok_or(Error::Unsupported("transport: ownership Prop metadata absent"))?;
    let typ = if prop == 0 { 1 } else { 0 };
    let lexical = self.erased_context(fuel, ctx, prop, typ)?;
    let head = self.erase_levels(fuel, head, prop, typ)?;
    let args = args
      .iter()
      .map(|a| self.erase_levels(fuel, a, prop, typ))
      .collect::<Result<Vec<_>, _>>()?;
    Ok(
      match support::argument_coverage(
        self.runtime,
        fuel,
        &mut self.remaining,
        &lexical,
        &head,
        &args,
        position,
      )? {
        support::Coverage::Uncovered => Coverage::Uncovered,
        support::Coverage::Runtime => Coverage::Runtime,
        support::Coverage::Alternative(n) => Coverage::Alternative(n),
      },
    )
  }
  fn conversion_type(
    &mut self,
    fuel: usize,
    ctx: &Context,
    e: &Term,
  ) -> Result<Term, Error> {
    self.tick(fuel)?;
    let key = (e.clone(), ctx.clone());
    if let Some(result) = self.types_cache.get(&key) {
      return Ok(result.clone());
    }
    let result = self.conversion_type_core(fuel, ctx, e)?;
    self.types_cache.insert(key, result.clone());
    Ok(result)
  }
  fn conversion_type_core(
    &mut self,
    fuel: usize,
    ctx: &Context,
    e: &Term,
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    match e.as_ref() {
      Expr::Var(_) | Expr::Nat(_) | Expr::Str(_) => {
        self.atom_type(fuel + 1, ctx, e)
      },
      Expr::Ref(i, ls) => self.instantiate_declaration(
        fuel,
        *i,
        ls,
        &self.declaration(*i)?.typ.clone(),
      ),
      Expr::Share(i) => self.conversion_type(fuel, ctx, &self.expansion(*i)?),
      Expr::Sort(u) => {
        let u = self.read_universe(*u)?;
        Ok(Expr::sort(self.intern_universe(Univ::succ(u))?))
      },
      Expr::All(c, _, a, b) => {
        let ty = self.conversion_type(fuel, ctx, a)?;
        let u = self.get_sort(fuel, &ty)?;
        let v = self.under_binder(ctx, *c, a.clone(), |s, inner| {
          let ty = s.conversion_type(fuel, inner, b)?;
          s.get_sort(fuel, &ty)
        })?;
        let (u, v) = (self.read_universe(u)?, self.read_universe(v)?);
        Ok(Expr::sort(self.intern_universe(Univ::imax(u, v))?))
      },
      Expr::Lam(c, a, b) => {
        let ty = self.under_binder(ctx, *c, a.clone(), |s, inner| {
          s.conversion_type(fuel, inner, b)
        })?;
        Ok(Expr::all_contract(*c, ValueContract::shared(), a.clone(), ty))
      },
      Expr::App(f, a) => {
        let ty = self.conversion_type(fuel, ctx, f)?;
        let (_, _, _, body) = self.arrow(fuel, &ty)?;
        self.substitute(fuel, &body, a, 0)
      },
      Expr::Let(_, _, value, body) => {
        let body = self.substitute(fuel, body, value, 0)?;
        self.conversion_type(fuel, ctx, &body)
      },
      Expr::Prj(i, field, value) => {
        let ty = self.conversion_type(fuel, ctx, value)?;
        self.projection_type(fuel, *i, *field, value, &ty)
      },
      Expr::Rec(..) => {
        Err(Error::Unsupported("transport: unresolved recursive reference"))
      },
    }
  }
  fn canonical_equality(
    &mut self,
    fuel: usize,
    expected: &Term,
  ) -> Result<bool, Error> {
    let Some(eq) = self.metadata.eq_type else {
      return Ok(false);
    };
    let expected = self.whnf(fuel, expected)?;
    let (head, args) = self.split_app(fuel, &expected)?;
    Ok(args.len() == 3 && matches!(head.as_ref(), Expr::Ref(i, _) if *i == eq))
  }
  fn equality_argument(&self, head: &Term, position: usize) -> bool {
    let Some(eq) = self.metadata.eq_type else {
      return false;
    };
    let Expr::Ref(i, _) = head.as_ref() else {
      return false;
    };
    if *i == eq {
      return position == 1 || position == 2;
    }
    if self.metadata.constructor(*i).is_some_and(|c| c.family == eq) {
      return position == 1;
    }
    if let Some(rec) = self.metadata.recursor(*i) {
      if rec.family == eq {
        return position == 1
          || position == rec.params
          || (rec.params + rec.motives + rec.minors <= position
            && rec.major().is_ok_and(|major| position < major));
      }
    }
    false
  }
  fn natural_value(
    &mut self,
    fuel: usize,
    value: &Term,
  ) -> Result<Option<BigUint>, Error> {
    let fuel = self.tick(fuel)?;
    let Some(typ) = &self.metadata.nat_type else {
      return Ok(None);
    };
    let Expr::Ref(family, _) = typ.as_ref() else {
      return Ok(None);
    };
    let Some(ind) = self.metadata.inductive(*family).cloned() else {
      return Ok(None);
    };
    if ind.constructors.len() != 2 || ind.params != 0 || ind.indices != 0 {
      return Ok(None);
    }
    let value = self.whnf(fuel, value)?;
    if let Expr::Nat(payload) = value.as_ref() {
      return Ok(
        self
          .metadata
          .naturals
          .iter()
          .find(|(i, _)| i == payload)
          .map(|(_, n)| n.clone()),
      );
    }
    let (head, args) = self.split_app(fuel, &value)?;
    let Expr::Ref(ctor, _) = head.as_ref() else {
      return Ok(None);
    };
    if *ctor == ind.constructors[0] && args.is_empty() {
      return Ok(Some(BigUint::from(0u8)));
    }
    if *ctor == ind.constructors[1] && args.len() == 1 {
      return Ok(
        self.natural_value(fuel, &args[0])?.map(|n| n + BigUint::from(1u8)),
      );
    }
    Ok(None)
  }
  pub(super) fn infer(
    &mut self,
    fuel: usize,
    ctx: &Context,
    term: &Term,
    coverage: Coverage,
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    let mut coverage = coverage;
    if matches!(coverage, Coverage::EqualityEndpoint | Coverage::Replacement(0))
    {
      let typ = self.conversion_type(fuel, ctx, term)?;
      if self.proof_type(fuel, ctx, &typ)?
        || matches!(self.whnf(fuel, &typ)?.as_ref(), Expr::Sort(_))
      {
        coverage = Coverage::Uncovered;
      }
    }
    match term.as_ref() {
      Expr::Ref(i, ls) => self.instantiate_declaration(
        fuel,
        *i,
        ls,
        &self.declaration(*i)?.typ.clone(),
      ),
      Expr::Var(_) | Expr::Nat(_) | Expr::Str(_) => {
        self.atom_type(fuel + 1, ctx, term)
      },
      Expr::Sort(u) => {
        let u = self.read_universe(*u)?;
        Ok(Expr::sort(self.intern_universe(Univ::succ(u))?))
      },
      Expr::Share(i) => self.infer(fuel, ctx, &self.expansion(*i)?, coverage),
      Expr::Rec(..) => {
        Err(Error::Unsupported("transport: unresolved recursive reference"))
      },
      Expr::All(c, _, domain, body) => {
        let ty = self.infer(fuel, ctx, domain, Coverage::Uncovered)?;
        let u = self.get_sort(fuel, &ty)?;
        let v = self.under_binder(ctx, *c, domain.clone(), |s, inner| {
          let ty = s.infer(fuel, inner, body, Coverage::Uncovered)?;
          s.get_sort(fuel, &ty)
        })?;
        let (u, v) = (self.read_universe(u)?, self.read_universe(v)?);
        Ok(Expr::sort(self.intern_universe(Univ::imax(u, v))?))
      },
      Expr::Lam(c, domain, body) => {
        let ty = self.infer(fuel, ctx, domain, Coverage::Uncovered)?;
        self.require_sort(fuel, &ty)?;
        let result =
          self.under_binder(ctx, *c, domain.clone(), |s, inner| {
            s.infer(fuel, inner, body, coverage.under_lambda())
          })?;
        let expected = Expr::all_contract(
          *c,
          ValueContract::shared(),
          domain.clone(),
          result,
        );
        if !self.proof_type(fuel, ctx, &expected)?
          && matches!(coverage, Coverage::Uncovered | Coverage::Replacement(0))
        {
          self.check_witness(fuel, ctx, term, &expected)?;
        }
        Ok(expected)
      },
      Expr::Let(_, domain, value, body) => {
        let ty = self.infer(fuel, ctx, domain, Coverage::Uncovered)?;
        self.require_sort(fuel, &ty)?;
        let typ = self.conversion_type(fuel, ctx, term)?;
        let ghost = self.canonical_equality(fuel, &typ)?;
        let value_coverage = if ghost {
          Coverage::EqualityEndpoint
        } else if coverage == Coverage::Replacement(0) {
          coverage
        } else {
          Coverage::Uncovered
        };
        self.check(fuel, ctx, value, domain, value_coverage)?;
        let body = self.substitute(fuel, body, value, 0)?;
        self.infer(fuel, ctx, &body, coverage)
      },
      Expr::Prj(owner, field, value) => {
        let ty = self.infer(fuel, ctx, value, coverage)?;
        self.projection_type(fuel, *owner, *field, value, &ty)
      },
      Expr::App(..) => {
        let (head, args) = self.split_app(fuel, term)?;
        // A direct beta-redex constructing a canonical Eq type does not
        // produce an escaping function value. Check the actual domain and
        // argument, then the entire substituted body with witness guards.
        if let Expr::Lam(_, domain, body) = head.as_ref() {
          if !args.is_empty() && self.canonical_equality(fuel, term)? {
            let domain_type =
              self.infer(fuel, ctx, domain, Coverage::Uncovered)?;
            self.require_sort(fuel, &domain_type)?;
            self.check(
              fuel,
              ctx,
              &args[0],
              domain,
              Coverage::EqualityEndpoint,
            )?;
            let body = self.substitute(fuel, body, &args[0], 0)?;
            let body = args.iter().skip(1).cloned().fold(body, Expr::app);
            return self.infer(fuel, ctx, &body, Coverage::Uncovered);
          }
        }
        let covered =
          matches!(coverage, Coverage::Runtime | Coverage::Alternative(_));
        let mut expanded = None;
        let application_type = self.conversion_type(fuel, ctx, term)?;
        if !covered
          && self.canonical_equality(fuel, &application_type)?
          && !support::default_closed(
            self.source,
            fuel,
            &mut self.remaining,
            ctx,
            term,
            &application_type,
            &self.metadata.resource_sensitive,
          )?
        {
          if let Expr::Ref(i, levels) = head.as_ref() {
            if matches!(
              self.metadata.kinds.get(*i as usize),
              Some(Kind::Definition | Kind::Theorem)
            ) {
              if let Some(body) = self.declaration(*i)?.body.clone() {
                let body =
                  self.instantiate_declaration(fuel, *i, levels, &body)?;
                expanded =
                  Some(args.iter().fold(body, |f, a| Expr::app(f, a.clone())));
              }
            }
          }
        }
        let head_coverage = if covered
          || matches!(
            coverage,
            Coverage::EqualityEndpoint | Coverage::Replacement(0)
          ) {
          coverage
        } else {
          Coverage::Uncovered
        };
        let mut typ = self.infer(fuel, ctx, &head, head_coverage)?;
        for (position, arg) in args.iter().enumerate() {
          let (input, _, domain, body) = self.arrow(fuel, &typ)?;
          let mut argument_coverage = if expanded.is_some()
            || coverage == Coverage::EqualityEndpoint
            || self.equality_argument(&head, position)
          {
            Coverage::EqualityEndpoint
          } else if coverage == Coverage::Replacement(0)
            && input.uses != ixon::expr::Uses::Erased
          {
            coverage
          } else {
            Coverage::Uncovered
          };
          if covered {
            argument_coverage =
              self.argument_coverage(fuel, ctx, &head, &args, position)?;
          }
          self.check(fuel, ctx, arg, &domain, argument_coverage)?;
          typ = self.substitute(fuel, &body, arg, 0)?;
        }
        if let Some(body) = expanded {
          let body = self.whnf(fuel, &body)?;
          self.check(fuel, ctx, &body, &typ, Coverage::Uncovered)?;
        }
        Ok(typ)
      },
    }
  }
  pub(super) fn check(
    &mut self,
    fuel: usize,
    ctx: &Context,
    term: &Term,
    expected: &Term,
    requested: Coverage,
  ) -> Result<(), Error> {
    self.tick(fuel)?;
    let key = (term.clone(), expected.clone(), ctx.clone(), requested);
    if self.checked_cache.contains(&key) {
      return Ok(());
    }
    self.check_core(fuel, ctx, term, expected, requested)?;
    self.checked_cache.insert(key);
    Ok(())
  }
  fn check_core(
    &mut self,
    fuel: usize,
    ctx: &Context,
    term: &Term,
    expected: &Term,
    requested: Coverage,
  ) -> Result<(), Error> {
    let fuel = self.tick(fuel)?;
    let requested = if matches!(term.as_ref(), Expr::Lam(..))
      && requested == Coverage::Replacement(0)
    {
      Coverage::Uncovered
    } else {
      requested
    };
    let proof = self.proof_type(fuel, ctx, expected)?;
    let mut coverage = if proof
      || matches!(self.whnf(fuel, expected)?.as_ref(), Expr::Sort(_))
    {
      Coverage::Uncovered
    } else {
      requested
    };
    if !proof && coverage != Coverage::Uncovered {
      let prop = self.runtime.prop_sort.ok_or(Error::Unsupported(
        "transport: ownership Prop metadata absent",
      ))?;
      let erased = self.erase_levels(
        fuel,
        expected,
        prop,
        if prop == 0 { 1 } else { 0 },
      )?;
      if support::runtime_sort(
        self.runtime,
        fuel,
        &mut self.remaining,
        &erased,
      )? {
        return Err(Error::Unsupported(
          "transport: inherited runtime coverage skipped a computational type",
        ));
      }
    }
    if !proof
      && coverage == Coverage::Uncovered
      && !matches!(self.whnf(fuel, expected)?.as_ref(), Expr::Sort(_))
      && self.check_witness(fuel, ctx, term, expected)?
    {
      coverage = Coverage::Runtime;
    }
    match term.as_ref() {
      Expr::Share(i) => {
        self.check(fuel, ctx, &self.expansion(*i)?, expected, coverage)
      },
      Expr::Lam(input, domain, body) => {
        let (declared, _, expected_domain, codomain) =
          self.arrow(fuel, expected)?;
        if *input != declared {
          return Err(Error::BinderMismatch);
        }
        let ty = self.infer(fuel, ctx, domain, Coverage::Uncovered)?;
        self.require_sort(fuel, &ty)?;
        if !self.compatible(fuel, ctx, domain, &expected_domain)? {
          return Err(Error::TypeMismatch);
        }
        self.under_binder(ctx, *input, domain.clone(), |s, inner| {
          s.check(fuel, inner, body, &codomain, coverage.under_lambda())
        })
      },
      Expr::Let(_, domain, value, body) => {
        let ty = self.infer(fuel, ctx, domain, Coverage::Uncovered)?;
        self.require_sort(fuel, &ty)?;
        let ghost = self.canonical_equality(fuel, expected)?;
        let value_coverage = if ghost {
          Coverage::EqualityEndpoint
        } else if coverage == Coverage::Replacement(0) {
          coverage
        } else {
          Coverage::Uncovered
        };
        self.check(fuel, ctx, value, domain, value_coverage)?;
        let body = self.substitute(fuel, body, value, 0)?;
        self.check(fuel, ctx, &body, expected, coverage)
      },
      _ => {
        let actual = self.infer(fuel, ctx, term, coverage)?;
        if self.compatible(fuel, ctx, &actual, expected)? {
          Ok(())
        } else {
          Err(Error::TypeMismatch)
        }
      },
    }
  }
  fn proof_type(
    &mut self,
    fuel: usize,
    ctx: &Context,
    typ: &Term,
  ) -> Result<bool, Error> {
    let fuel = self.tick(fuel)?;
    let reduced = self.whnf(fuel, typ)?;
    match reduced.as_ref() {
      Expr::Sort(_) => Ok(false),
      Expr::All(c, _, a, b) => {
        self.under_binder(ctx, *c, a.clone(), |s, inner| {
          s.proof_type(fuel, inner, b)
        })
      },
      _ => {
        let ty = self.conversion_type(fuel, ctx, &reduced)?;
        match self.whnf(fuel, &ty)?.as_ref() {
          Expr::Sort(u) => self.universe_zero(fuel, *u),
          _ => Err(Error::Unsupported("transport: type has no exposed sort")),
        }
      },
    }
  }
  pub(super) fn compatible(
    &mut self,
    fuel: usize,
    ctx: &Context,
    left: &Term,
    right: &Term,
  ) -> Result<bool, Error> {
    self.tick(fuel)?;
    let key = (left.clone(), right.clone(), ctx.clone());
    if let Some(result) = self.compatible_cache.get(&key) {
      return Ok(*result);
    }
    let result = self.compatible_core(fuel, ctx, left, right)?;
    self.compatible_cache.insert(key, result);
    Ok(result)
  }
  fn compatible_core(
    &mut self,
    fuel: usize,
    ctx: &Context,
    left: &Term,
    right: &Term,
  ) -> Result<bool, Error> {
    let fuel = self.tick(fuel)?;
    if left == right {
      return Ok(true);
    }
    let left = self.whnf(fuel, left)?;
    let right = self.whnf(fuel, right)?;
    if left == right {
      return Ok(true);
    }
    if matches!(left.as_ref(), Expr::Nat(_))
      || matches!(right.as_ref(), Expr::Nat(_))
    {
      if let Some(a) = self.natural_value(fuel, &left)? {
        if let Some(b) = self.natural_value(fuel, &right)? {
          return Ok(a == b);
        }
      }
    }
    match (left.as_ref(), right.as_ref()) {
      (Expr::Sort(i), Expr::Sort(j)) => {
        return self.universe_equal(fuel, *i, *j);
      },
      (Expr::Ref(i, us), Expr::Ref(j, vs))
        if i == j && us.len() == vs.len() =>
      {
        let mut same = true;
        for (u, v) in us.iter().zip(vs) {
          same = same && self.universe_equal(fuel, *u, *v)?;
        }
        if same {
          return Ok(true);
        }
      },
      (Expr::All(c, r, a, b), Expr::All(d, s, x, y)) => {
        if c != d || r != s || !self.compatible(fuel, ctx, a, x)? {
          return Ok(false);
        }
        return self.under_binder(ctx, *c, a.clone(), |this, inner| {
          this.compatible(fuel, inner, b, y)
        });
      },
      (Expr::Lam(c, a, b), Expr::Lam(d, x, y)) => {
        if c != d || !self.compatible(fuel, ctx, a, x)? {
          return Ok(false);
        }
        return self.under_binder(ctx, *c, a.clone(), |this, inner| {
          this.compatible(fuel, inner, b, y)
        });
      },
      (Expr::App(f, a), Expr::App(g, b)) => {
        if self.compatible(fuel, ctx, f, g)?
          && self.compatible(fuel, ctx, a, b)?
        {
          return Ok(true);
        }
      },
      (Expr::Prj(t, i, v), Expr::Prj(u, j, w)) if t == u && i == j => {
        if self.compatible(fuel, ctx, v, w)? {
          return Ok(true);
        }
      },
      _ => {},
    }
    let left_type = self.conversion_type(fuel, ctx, &left)?;
    let right_type = self.conversion_type(fuel, ctx, &right)?;
    if self.proof_type(fuel, ctx, &left_type)?
      && self.proof_type(fuel, ctx, &right_type)?
    {
      return self.compatible(fuel, ctx, &left_type, &right_type);
    }
    match (left.as_ref(), right.as_ref()) {
      (Expr::Lam(c, a, body), _) => {
        let ty = self.whnf(fuel, &right_type)?;
        let Expr::All(d, _, domain, _) = ty.as_ref() else {
          return Ok(false);
        };
        if c != d || !self.compatible(fuel, ctx, a, domain)? {
          return Ok(false);
        }
        self.check(fuel, ctx, &left, &right_type, Coverage::Uncovered)?;
        let shifted = self.shift(fuel, &right, 1, 0)?;
        self.under_binder(ctx, *c, a.clone(), |s, inner| {
          s.compatible(fuel, inner, body, &Expr::app(shifted, Expr::var(0)))
        })
      },
      (_, Expr::Lam(..)) => self.compatible(fuel, ctx, &right, &left),
      _ => Ok(false),
    }
  }
}
