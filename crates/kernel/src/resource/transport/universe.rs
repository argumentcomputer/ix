//! Bounded universe conversion, exactly the source transport fragment.
use super::*;
fn step(fuel: usize, remaining: &mut usize) -> Result<usize, Error> {
  if fuel == 0 || *remaining == 0 {
    return Err(Error::Budget);
  }
  *remaining -= 1;
  Ok(fuel - 1)
}
fn never_zero(
  u: &Univ,
  fuel: usize,
  remaining: &mut usize,
) -> Result<bool, Error> {
  let fuel = step(fuel, remaining)?;
  Ok(match u {
    Univ::Zero | Univ::Var(_) => false,
    Univ::Succ(_) => true,
    Univ::Max(a, b) => {
      never_zero(a, fuel, remaining)? || never_zero(b, fuel, remaining)?
    },
    Univ::IMax(_, b) => never_zero(b, fuel, remaining)?,
  })
}
fn zero(u: &Univ, fuel: usize, remaining: &mut usize) -> Result<bool, Error> {
  let fuel = step(fuel, remaining)?;
  Ok(match u {
    Univ::Zero => true,
    Univ::Succ(_) | Univ::Var(_) => false,
    Univ::Max(a, b) => zero(a, fuel, remaining)? && zero(b, fuel, remaining)?,
    Univ::IMax(_, b) => zero(b, fuel, remaining)?,
  })
}
fn offset(
  u: &Arc<Univ>,
  fuel: usize,
  remaining: &mut usize,
) -> Result<(Arc<Univ>, usize), Error> {
  if fuel == 0 {
    return Err(Error::Budget);
  }
  if let Univ::Succ(a) = u.as_ref() {
    step(fuel, remaining)?;
    let (base, n) = offset(a, fuel - 1, remaining)?;
    Ok((base, n.checked_add(1).ok_or(Error::Budget)?))
  } else {
    Ok((u.clone(), 0))
  }
}
fn maximum(
  a: Arc<Univ>,
  b: Arc<Univ>,
  fuel: usize,
  remaining: &mut usize,
) -> Result<Arc<Univ>, Error> {
  step(1, remaining)?;
  if a == b || matches!(b.as_ref(), Univ::Zero) {
    return Ok(a);
  }
  if matches!(a.as_ref(), Univ::Zero) {
    return Ok(b);
  }
  if matches!(b.as_ref(),Univ::Max(x,y) if a==*x || a==*y) {
    return Ok(b);
  }
  if matches!(a.as_ref(),Univ::Max(x,y) if b==*x || b==*y) {
    return Ok(a);
  }
  let (aa, n) = offset(&a, fuel, remaining)?;
  let (bb, k) = offset(&b, fuel, remaining)?;
  if aa == bb {
    return Ok(if n >= k { a } else { b });
  }
  Ok(Univ::max(a, b))
}
fn normalize(
  u: &Arc<Univ>,
  fuel: usize,
  remaining: &mut usize,
) -> Result<Arc<Univ>, Error> {
  let fuel = step(fuel, remaining)?;
  match u.as_ref() {
    Univ::Zero | Univ::Var(_) => Ok(u.clone()),
    Univ::Succ(a) => Ok(Univ::succ(normalize(a, fuel, remaining)?)),
    Univ::Max(a, b) => {
      let a = normalize(a, fuel, remaining)?;
      let b = normalize(b, fuel, remaining)?;
      maximum(a, b, fuel, remaining)
    },
    Univ::IMax(a, b) => {
      let a = normalize(a, fuel, remaining)?;
      let b = normalize(b, fuel, remaining)?;
      if never_zero(&b, fuel, remaining)? {
        return maximum(a, b, fuel, remaining);
      }
      if matches!(b.as_ref(), Univ::Zero)
        || matches!(a.as_ref(), Univ::Zero)
        || a == Univ::succ(Univ::zero())
        || a == b
      {
        Ok(b)
      } else {
        Ok(Univ::imax(a, b))
      }
    },
  }
}
type Atoms = Vec<(Arc<Univ>, usize)>;
fn atoms(
  u: &Arc<Univ>,
  off: usize,
  out: &mut Atoms,
  fuel: usize,
  remaining: &mut usize,
) -> Result<(), Error> {
  let fuel = step(fuel, remaining)?;
  match u.as_ref() {
    Univ::Succ(a) => {
      atoms(a, off.checked_add(1).ok_or(Error::Budget)?, out, fuel, remaining)
    },
    Univ::Max(a, b) => {
      atoms(a, off, out, fuel, remaining)?;
      atoms(b, off, out, fuel, remaining)
    },
    _ => {
      let mut found = false;
      for (other, n) in out.iter_mut() {
        step(1, remaining)?;
        if other == u {
          found = true;
          *n = (*n).max(off);
        }
      }
      if !found {
        out.push((u.clone(), off));
      }
      Ok(())
    },
  }
}
fn simplified_atoms(
  u: &Arc<Univ>,
  fuel: usize,
  remaining: &mut usize,
) -> Result<Atoms, Error> {
  let mut all = vec![];
  atoms(u, 0, &mut all, fuel, remaining)?;
  let mut out = vec![];
  for (base, n) in &all {
    let mut subsumed = false;
    if matches!(base.as_ref(), Univ::Zero) {
      for (other, k) in &all {
        step(1, remaining)?;
        if !matches!(other.as_ref(), Univ::Zero) && n <= k {
          subsumed = true;
        }
      }
    }
    if !subsumed {
      out.push((base.clone(), *n));
    }
  }
  Ok(out)
}
impl TransportChecker<'_> {
  pub(super) fn read_universe(&self, i: u64) -> Result<Arc<Univ>, Error> {
    self
      .universes
      .get(usize::try_from(i).map_err(|_| Error::Budget)?)
      .cloned()
      .ok_or(Error::Unsupported("transport: universe index out of bounds"))
  }
  pub(super) fn intern_universe(&mut self, u: Arc<Univ>) -> Result<u64, Error> {
    self.tick(1)?;
    if let Some(i) = self.universes.iter().position(|v| *v == u) {
      return u64::try_from(i).map_err(|_| Error::Budget);
    }
    let i = u64::try_from(self.universes.len()).map_err(|_| Error::Budget)?;
    self.universes.push(u);
    Ok(i)
  }
  pub(super) fn universe_equal(
    &mut self,
    fuel: usize,
    i: u64,
    j: u64,
  ) -> Result<bool, Error> {
    if i == j {
      return Ok(true);
    }
    let a = self.read_universe(i)?;
    let b = self.read_universe(j)?;
    let a = normalize(&a, fuel, &mut self.remaining)?;
    let b = normalize(&b, fuel, &mut self.remaining)?;
    if a == b {
      return Ok(true);
    }
    let a = simplified_atoms(&a, fuel, &mut self.remaining)?;
    let b = simplified_atoms(&b, fuel, &mut self.remaining)?;
    if a.len() != b.len() {
      return Ok(false);
    }
    for x in &a {
      let mut found = false;
      for y in &b {
        self.tick(1)?;
        if x == y {
          found = true;
        }
      }
      if !found {
        return Ok(false);
      }
    }
    Ok(true)
  }
  pub(super) fn universe_zero(
    &mut self,
    fuel: usize,
    i: u64,
  ) -> Result<bool, Error> {
    let u = self.read_universe(i)?;
    zero(&u, fuel, &mut self.remaining)
  }
  fn instantiate_universe(
    &mut self,
    fuel: usize,
    u: &Univ,
    values: &[Arc<Univ>],
  ) -> Result<Arc<Univ>, Error> {
    let fuel = self.tick(fuel)?;
    Ok(match u {
      Univ::Zero => Univ::zero(),
      Univ::Var(i) => values
        .get(*i as usize)
        .cloned()
        .ok_or(Error::Unsupported("transport: unbound universe parameter"))?,
      Univ::Succ(a) => Univ::succ(self.instantiate_universe(fuel, a, values)?),
      Univ::Max(a, b) => Univ::max(
        self.instantiate_universe(fuel, a, values)?,
        self.instantiate_universe(fuel, b, values)?,
      ),
      Univ::IMax(a, b) => Univ::imax(
        self.instantiate_universe(fuel, a, values)?,
        self.instantiate_universe(fuel, b, values)?,
      ),
    })
  }
  fn instantiated_level(
    &mut self,
    fuel: usize,
    i: u64,
    values: &[Arc<Univ>],
  ) -> Result<u64, Error> {
    let u = self.read_universe(i)?;
    let u = self.instantiate_universe(fuel, &u, values)?;
    self.intern_universe(u)
  }
  pub(super) fn instantiate_levels(
    &mut self,
    fuel: usize,
    e: &Term,
    values: &[Arc<Univ>],
  ) -> Result<Term, Error> {
    self.tick(fuel)?;
    let key = (e.clone(), values.to_vec());
    if let Some(result) = self.instances_cache.get(&key) {
      return Ok(result.clone());
    }
    let result = self.instantiate_levels_core(fuel, e, values)?;
    self.instances_cache.insert(key, result.clone());
    Ok(result)
  }
  fn instantiate_levels_core(
    &mut self,
    fuel: usize,
    e: &Term,
    values: &[Arc<Univ>],
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    Ok(match e.as_ref() {
      Expr::Sort(i) => Expr::sort(self.instantiated_level(fuel, *i, values)?),
      Expr::Ref(i, ls) => Expr::reference(
        *i,
        ls.iter()
          .map(|l| self.instantiated_level(fuel, *l, values))
          .collect::<Result<_, _>>()?,
      ),
      Expr::Share(i) => {
        let v = self.expansion(*i)?;
        self.instantiate_levels(fuel, &v, values)?
      },
      Expr::All(c, r, a, b) => Expr::all_contract(
        *c,
        *r,
        self.instantiate_levels(fuel, a, values)?,
        self.instantiate_levels(fuel, b, values)?,
      ),
      Expr::Lam(c, a, b) => Expr::lam_contract(
        *c,
        self.instantiate_levels(fuel, a, values)?,
        self.instantiate_levels(fuel, b, values)?,
      ),
      Expr::App(f, a) => Expr::app(
        self.instantiate_levels(fuel, f, values)?,
        self.instantiate_levels(fuel, a, values)?,
      ),
      Expr::Let(c, a, v, b) => Expr::let_contract(
        *c,
        self.instantiate_levels(fuel, a, values)?,
        self.instantiate_levels(fuel, v, values)?,
        self.instantiate_levels(fuel, b, values)?,
      ),
      Expr::Prj(i, f, v) => {
        Expr::prj(*i, *f, self.instantiate_levels(fuel, v, values)?)
      },
      Expr::Rec(..) => {
        return Err(Error::Unsupported(
          "transport: unresolved recursive reference",
        ));
      },
      _ => e.clone(),
    })
  }
  pub(super) fn instantiate_declaration(
    &mut self,
    fuel: usize,
    i: u64,
    levels: &[u64],
    term: &Term,
  ) -> Result<Term, Error> {
    if self.metadata.level_arities.get(i as usize) != Some(&levels.len()) {
      return Err(Error::Unsupported(
        "transport: universe argument arity mismatch",
      ));
    }
    let values = levels
      .iter()
      .map(|i| self.read_universe(*i))
      .collect::<Result<Vec<_>, _>>()?;
    self.instantiate_levels(fuel, term, &values)
  }
  pub(super) fn erase_levels(
    &mut self,
    fuel: usize,
    e: &Term,
    prop: u64,
    typ: u64,
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    Ok(match e.as_ref() {
      Expr::Sort(i) => {
        Expr::sort(if self.universe_zero(fuel, *i)? { prop } else { typ })
      },
      Expr::Share(i) => {
        let v = self.expansion(*i)?;
        self.erase_levels(fuel, &v, prop, typ)?
      },
      Expr::All(c, r, a, b) => Expr::all_contract(
        *c,
        *r,
        self.erase_levels(fuel, a, prop, typ)?,
        self.erase_levels(fuel, b, prop, typ)?,
      ),
      Expr::Lam(c, a, b) => Expr::lam_contract(
        *c,
        self.erase_levels(fuel, a, prop, typ)?,
        self.erase_levels(fuel, b, prop, typ)?,
      ),
      Expr::App(f, a) => Expr::app(
        self.erase_levels(fuel, f, prop, typ)?,
        self.erase_levels(fuel, a, prop, typ)?,
      ),
      Expr::Let(c, a, v, b) => Expr::let_contract(
        *c,
        self.erase_levels(fuel, a, prop, typ)?,
        self.erase_levels(fuel, v, prop, typ)?,
        self.erase_levels(fuel, b, prop, typ)?,
      ),
      Expr::Prj(i, f, v) => {
        Expr::prj(*i, *f, self.erase_levels(fuel, v, prop, typ)?)
      },
      _ => e.clone(),
    })
  }
}
