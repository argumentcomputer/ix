//! Resource checking for Ixon v3. Mirrors `Ix/Resource/{Basic,Check}.lean`.
//!
//! The address adapter supplies a globally indexed program whose erased types
//! have been checked. External interfaces and special primitives are explicit
//! profile assumptions. No result here certifies unverified typechecking or
//! an unbound primitive profile.

pub mod addressed;

use crate::contract::{BinderContract, LetKind, Locality, ValueContract};
use crate::expr::{Expr, Owned, Uses};
use std::sync::Arc;

pub type Term = Arc<Expr>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
  Budget,
  Unbound(usize),
  BadReference(u64),
  UnresolvedSharing(u64),
  Unsupported(&'static str),
  TypeMismatch,
  BinderMismatch,
  Usage(usize, Uses, Uses),
  Moved(usize),
  SharedToUnique,
  ActiveLoan(usize),
  Escape(usize, usize),
  UnrestrictedEscape(usize),
  Nonduplicable,
  InvalidBorrow,
  InvalidPlace,
  InvalidScope,
}

impl Error {
  pub const fn code(&self) -> &'static str {
    match self {
      Self::Budget => "budget",
      Self::Unbound(_) => "unbound",
      Self::BadReference(_) => "reference",
      Self::UnresolvedSharing(_) => "sharing",
      Self::Unsupported(_) => "unsupported",
      Self::TypeMismatch => "type",
      Self::BinderMismatch => "binder",
      Self::Usage(..) => "usage",
      Self::Moved(_) => "moved",
      Self::SharedToUnique => "ownership",
      Self::ActiveLoan(_) => "loan",
      Self::Escape(..) => "escape",
      Self::UnrestrictedEscape(_) => "unrestricted",
      Self::Nonduplicable => "capture",
      Self::InvalidBorrow => "borrow",
      Self::InvalidPlace => "place",
      Self::InvalidScope => "scope",
    }
  }
}

impl std::fmt::Display for Error {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "resource {}: {self:?}", self.code())
  }
}
impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
  pub depth: usize,
  pub steps: usize,
}
impl Default for Limits {
  fn default() -> Self {
    Self { depth: 256, steps: 100_000 }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclKind {
  Definition,
  Assumption,
  Constructor,
  TypeConstructor,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Declaration {
  pub typ: Term,
  pub body: Option<Term>,
  pub kind: DeclKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
  pub type_ref: u64,
  pub index: u64,
  pub typ: Term,
  pub contract: ValueContract,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Program {
  pub declarations: Vec<Declaration>,
  pub groups: Vec<Vec<usize>>,
  /// Additional executable syntax, including addressed recursor rules.
  pub auxiliary: Vec<(usize, Term)>,
  pub sharing: Vec<Term>,
  pub fields: Vec<Field>,
  pub nat_type: Option<Term>,
  pub string_type: Option<Term>,
  pub shareable_types: Vec<u64>,
  /// Profile-bound non-strict selection, with exactly three arguments.
  pub choices: Vec<u64>,
}

#[derive(Clone, Debug)]
struct Value {
  typ: Term,
  owned: Owned,
  origins: Vec<usize>,
  duplicable: bool,
  place: Option<usize>,
  loan_root: Option<usize>,
}
impl Value {
  fn shared(typ: Term) -> Self {
    Self {
      typ,
      owned: Owned::Shared,
      origins: vec![],
      duplicable: true,
      place: None,
      loan_root: None,
    }
  }
  fn fresh(typ: Term) -> Self {
    Self { owned: Owned::Unique, ..Self::shared(typ) }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Owner {
  live: bool,
  unique: bool,
  loans: Vec<usize>,
}
impl Owner {
  fn move_out(&self, id: usize) -> Result<Self, Error> {
    if !self.live {
      return Err(Error::Moved(id));
    }
    if !self.unique {
      return Err(Error::SharedToUnique);
    }
    if !self.loans.is_empty() {
      return Err(Error::ActiveLoan(id));
    }
    Ok(Self { live: false, ..self.clone() })
  }
  fn share(&self, id: usize) -> Result<Self, Error> {
    if !self.live {
      return Err(Error::Moved(id));
    }
    Ok(Self { unique: false, ..self.clone() })
  }
  fn begin_loan(&mut self, id: usize, scope: usize) -> Result<(), Error> {
    if !self.live {
      return Err(Error::Moved(id));
    }
    self.loans.insert(0, scope);
    Ok(())
  }
  fn end_loan(&mut self, scope: usize) {
    self.loans.retain(|x| *x != scope);
  }
  fn join(&self, other: &Self) -> Self {
    Self {
      live: self.live && other.live,
      unique: self.unique && other.unique,
      loans: union(&self.loans, &other.loans),
    }
  }
}

#[derive(Clone, Debug)]
struct Binding {
  contract: BinderContract,
  value: Value,
  owner: Owner,
  demand: Uses,
  touched: bool,
}

#[derive(Clone, Debug)]
struct State {
  bindings: Vec<Binding>,
  parents: Vec<Option<usize>>,
  remaining: usize,
}

#[derive(Clone, Debug, Default)]
struct Context {
  vars: Vec<usize>,
  scope: usize,
}

fn add(a: Uses, b: Uses) -> Uses {
  match (a, b) {
    (Uses::Erased, x) | (x, Uses::Erased) => x,
    _ => Uses::Many,
  }
}
fn scale(a: Uses, b: Uses) -> Uses {
  match (a, b) {
    (Uses::Erased, _) | (_, Uses::Erased) => Uses::Erased,
    (Uses::Linear, x) | (x, Uses::Linear) => x,
    (Uses::Affine, Uses::Affine) => Uses::Affine,
    _ => Uses::Many,
  }
}
fn join(a: Uses, b: Uses) -> Uses {
  match (a, b) {
    (Uses::Erased, Uses::Erased) => Uses::Erased,
    (Uses::Linear, Uses::Linear) => Uses::Linear,
    (Uses::Many, _) | (_, Uses::Many) => Uses::Many,
    _ => Uses::Affine,
  }
}
fn covers(declared: Uses, actual: Uses) -> bool {
  match declared {
    Uses::Many => true,
    Uses::Affine => actual != Uses::Many,
    Uses::Linear => actual == Uses::Linear,
    Uses::Erased => actual == Uses::Erased,
  }
}
fn union(a: &[usize], b: &[usize]) -> Vec<usize> {
  let mut result = a.to_vec();
  for x in b {
    if !result.contains(x) {
      result.push(*x);
    }
  }
  result
}

struct Checker<'a> {
  program: &'a Program,
  state: State,
}
type Arrow = (BinderContract, ValueContract, Term, Term);
type Expected = Option<(Term, ValueContract)>;

impl<'a> Checker<'a> {
  fn new(program: &'a Program, limits: Limits) -> Self {
    Self {
      program,
      state: State {
        bindings: vec![],
        parents: vec![None],
        remaining: limits.steps,
      },
    }
  }
  fn tick(&mut self, fuel: usize) -> Result<usize, Error> {
    if fuel == 0 || self.state.remaining == 0 {
      return Err(Error::Budget);
    }
    self.state.remaining -= 1;
    Ok(fuel - 1)
  }
  fn declaration(&self, index: u64) -> Result<&Declaration, Error> {
    let i =
      usize::try_from(index).map_err(|_error| Error::BadReference(index))?;
    self.program.declarations.get(i).ok_or(Error::BadReference(index))
  }
  fn expansion(&self, index: u64) -> Result<Term, Error> {
    let i = usize::try_from(index)
      .map_err(|_error| Error::UnresolvedSharing(index))?;
    self.program.sharing.get(i).cloned().ok_or(Error::UnresolvedSharing(index))
  }
  fn binding(&self, id: usize) -> Result<&Binding, Error> {
    self.state.bindings.get(id).ok_or(Error::Unbound(id))
  }
  fn binding_mut(&mut self, id: usize) -> Result<&mut Binding, Error> {
    self.state.bindings.get_mut(id).ok_or(Error::Unbound(id))
  }
  fn push(&mut self, contract: BinderContract, value: Value) -> usize {
    let id = self.state.bindings.len();
    let owner =
      Owner { live: true, unique: value.owned == Owned::Unique, loans: vec![] };
    self.state.bindings.push(Binding {
      contract,
      value,
      owner,
      demand: Uses::Erased,
      touched: false,
    });
    id
  }
  fn scope(&mut self, parent: usize) -> Result<usize, Error> {
    if parent >= self.state.parents.len() {
      return Err(Error::InvalidScope);
    }
    let id = self.state.parents.len();
    self.state.parents.push(Some(parent));
    Ok(id)
  }
  fn outlives(&self, origin: usize, mut destination: usize) -> bool {
    for _ in 0..=self.state.parents.len() {
      if origin >= self.state.parents.len()
        || destination >= self.state.parents.len()
      {
        return false;
      }
      if origin == destination {
        return true;
      }
      match self.state.parents[destination] {
        Some(parent) => destination = parent,
        None => return false,
      }
    }
    false
  }
  fn check_origins(
    &self,
    origins: &[usize],
    destination: usize,
  ) -> Result<(), Error> {
    for origin in origins {
      if !self.outlives(*origin, destination) {
        return Err(Error::Escape(*origin, destination));
      }
    }
    Ok(())
  }
  fn charge(&mut self, id: usize, uses: Uses) -> Result<(), Error> {
    let b = self.binding_mut(id)?;
    if !b.owner.live {
      return Err(Error::Moved(id));
    }
    b.demand = add(b.demand, uses);
    b.touched = true;
    Ok(())
  }
  fn validate_usage(&self, id: usize) -> Result<(), Error> {
    let b = self.binding(id)?;
    if !covers(b.contract.uses, b.demand) {
      return Err(Error::Usage(id, b.contract.uses, b.demand));
    }
    Ok(())
  }
  /// Perform a place's ownership action once. Scope exit materializes its
  /// result before ending loans, even when the result is being inferred.
  fn materialize(&mut self, mut v: Value) -> Result<Value, Error> {
    if let Some(id) = v.place {
      let b = self.binding_mut(id)?;
      b.owner = match v.owned {
        Owned::Unique => b.owner.move_out(id)?,
        Owned::Shared => b.owner.share(id)?,
      };
    }
    v.place = None;
    Ok(v)
  }
  fn consume_as(
    &mut self,
    required: ValueContract,
    destination: usize,
    mut v: Value,
  ) -> Result<Value, Error> {
    match required.locality {
      Locality::Unrestricted => {
        if let Some(origin) = v.origins.first() {
          return Err(Error::UnrestrictedEscape(*origin));
        }
      },
      Locality::Local => self.check_origins(&v.origins, destination)?,
    }
    if required.owned == Owned::Unique && v.owned != Owned::Unique {
      return Err(Error::SharedToUnique);
    }
    if required.owned == Owned::Shared && !v.duplicable {
      return Err(Error::Nonduplicable);
    }
    v.owned = required.owned;
    v = self.materialize(v)?;
    if required.locality == Locality::Local {
      v.origins = union(&v.origins, &[destination]);
    }
    Ok(v)
  }
  fn invoke(&mut self, v: &Value) -> Result<(), Error> {
    if v.owned == Owned::Shared && !v.duplicable {
      return Err(Error::Nonduplicable);
    }
    if let Some(id) = v.place {
      let b = self.binding_mut(id)?;
      if v.owned == Owned::Unique {
        b.owner = b.owner.move_out(id)?;
      } else if !b.owner.live {
        return Err(Error::Moved(id));
      }
    }
    Ok(())
  }
  fn close_scope(&mut self, scope: usize, result: &Value) -> Result<(), Error> {
    let parent = self
      .state
      .parents
      .get(scope)
      .copied()
      .flatten()
      .ok_or(Error::InvalidScope)?;
    self.check_origins(&result.origins, parent)?;
    for b in &mut self.state.bindings {
      b.owner.end_loan(scope);
    }
    Ok(())
  }
  fn shift(
    &mut self,
    fuel: usize,
    e: &Term,
    amount: u64,
    cutoff: u64,
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    Ok(match e.as_ref() {
      Expr::Var(i) if *i >= cutoff => Expr::var(
        i.checked_add(amount)
          .ok_or(Error::Unsupported("variable index overflow"))?,
      ),
      Expr::App(f, a) => Expr::app(
        self.shift(fuel, f, amount, cutoff)?,
        self.shift(fuel, a, amount, cutoff)?,
      ),
      Expr::Lam(c, t, b) => Expr::lam_contract(
        *c,
        self.shift(fuel, t, amount, cutoff)?,
        self.shift(
          fuel,
          b,
          amount,
          cutoff.checked_add(1).ok_or(Error::Budget)?,
        )?,
      ),
      Expr::All(c, r, t, b) => Expr::all_contract(
        *c,
        *r,
        self.shift(fuel, t, amount, cutoff)?,
        self.shift(
          fuel,
          b,
          amount,
          cutoff.checked_add(1).ok_or(Error::Budget)?,
        )?,
      ),
      Expr::Let(c, t, v, b) => Expr::let_contract(
        *c,
        self.shift(fuel, t, amount, cutoff)?,
        self.shift(fuel, v, amount, cutoff)?,
        self.shift(
          fuel,
          b,
          amount,
          cutoff.checked_add(1).ok_or(Error::Budget)?,
        )?,
      ),
      Expr::Prj(t, i, v) => {
        Expr::prj(*t, *i, self.shift(fuel, v, amount, cutoff)?)
      },
      Expr::Share(i) => {
        self.shift(fuel, &self.expansion(*i)?, amount, cutoff)?
      },
      Expr::Rec(..) => {
        return Err(Error::Unsupported("unresolved recursive reference"));
      },
      _ => e.clone(),
    })
  }
  fn substitute(
    &mut self,
    fuel: usize,
    e: &Term,
    value: &Term,
    depth: u64,
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    Ok(match e.as_ref() {
      Expr::Var(i) if *i == depth => self.shift(fuel, value, depth, 0)?,
      Expr::Var(i) if *i > depth => Expr::var(i - 1),
      Expr::App(f, a) => Expr::app(
        self.substitute(fuel, f, value, depth)?,
        self.substitute(fuel, a, value, depth)?,
      ),
      Expr::Lam(c, t, b) => Expr::lam_contract(
        *c,
        self.substitute(fuel, t, value, depth)?,
        self.substitute(
          fuel,
          b,
          value,
          depth.checked_add(1).ok_or(Error::Budget)?,
        )?,
      ),
      Expr::All(c, r, t, b) => Expr::all_contract(
        *c,
        *r,
        self.substitute(fuel, t, value, depth)?,
        self.substitute(
          fuel,
          b,
          value,
          depth.checked_add(1).ok_or(Error::Budget)?,
        )?,
      ),
      Expr::Let(c, t, v, b) => Expr::let_contract(
        *c,
        self.substitute(fuel, t, value, depth)?,
        self.substitute(fuel, v, value, depth)?,
        self.substitute(
          fuel,
          b,
          value,
          depth.checked_add(1).ok_or(Error::Budget)?,
        )?,
      ),
      Expr::Prj(t, i, v) => {
        Expr::prj(*t, *i, self.substitute(fuel, v, value, depth)?)
      },
      Expr::Share(i) => {
        self.substitute(fuel, &self.expansion(*i)?, value, depth)?
      },
      Expr::Rec(..) => {
        return Err(Error::Unsupported("unresolved recursive reference"));
      },
      _ => e.clone(),
    })
  }
  fn whnf(&mut self, fuel: usize, e: &Term) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    match e.as_ref() {
      Expr::Share(i) => self.whnf(fuel, &self.expansion(*i)?),
      Expr::Let(_, _, v, b) => {
        let body = self.substitute(fuel, b, v, 0)?;
        self.whnf(fuel, &body)
      },
      Expr::App(f, a) => {
        let f = self.whnf(fuel, f)?;
        if let Expr::Lam(_, _, b) = f.as_ref() {
          let b = self.substitute(fuel, b, a, 0)?;
          self.whnf(fuel, &b)
        } else {
          Ok(Expr::app(f, a.clone()))
        }
      },
      Expr::Ref(i, _) => match self.declaration(*i)?.body.clone() {
        Some(body) => self.whnf(fuel, &body),
        None => Ok(e.clone()),
      },
      Expr::Rec(..) => {
        Err(Error::Unsupported("unresolved recursive reference"))
      },
      _ => Ok(e.clone()),
    }
  }
  fn compatible(
    &mut self,
    fuel: usize,
    a: &Term,
    b: &Term,
  ) -> Result<bool, Error> {
    let fuel = self.tick(fuel)?;
    if a == b {
      return Ok(true);
    }
    let a = self.whnf(fuel, a)?;
    let b = self.whnf(fuel, b)?;
    Ok(match (a.as_ref(), b.as_ref()) {
      (Expr::All(c, r, t, b), Expr::All(d, s, u, e)) => {
        c == d
          && r == s
          && self.compatible(fuel, t, u)?
          && self.compatible(fuel, b, e)?
      },
      (Expr::Lam(c, t, b), Expr::Lam(d, u, e)) => {
        c == d && self.compatible(fuel, t, u)? && self.compatible(fuel, b, e)?
      },
      (Expr::App(f, a), Expr::App(g, b)) => {
        self.compatible(fuel, f, g)? && self.compatible(fuel, a, b)?
      },
      (Expr::Prj(t, i, v), Expr::Prj(u, j, w)) => {
        t == u && i == j && self.compatible(fuel, v, w)?
      },
      (Expr::Sort(_), Expr::Sort(_)) => true,
      (Expr::Ref(i, _), Expr::Ref(j, _)) => i == j,
      _ => a == b,
    })
  }
  fn require_type(
    &mut self,
    fuel: usize,
    actual: &Term,
    expected: &Term,
  ) -> Result<(), Error> {
    if self.compatible(fuel, actual, expected)? {
      Ok(())
    } else {
      Err(Error::TypeMismatch)
    }
  }
  fn arrow(&mut self, fuel: usize, typ: &Term) -> Result<Arrow, Error> {
    let t = self.whnf(fuel, typ)?;
    match t.as_ref() {
      Expr::All(c, r, t, b) => Ok((*c, *r, t.clone(), b.clone())),
      _ => Err(Error::Unsupported(
        "a callable interface must expose its arrow contracts",
      )),
    }
  }
  fn is_shareable(&mut self, fuel: usize, typ: &Term) -> Result<bool, Error> {
    let typ = self.whnf(fuel, typ)?;
    Ok(match typ.as_ref() {
      Expr::Ref(i, _) => self.program.shareable_types.contains(i),
      Expr::Sort(_) => true,
      _ => false,
    })
  }
  fn literal_type(typ: &Option<Term>) -> Result<Term, Error> {
    typ.clone().ok_or(Error::Unsupported(
      "literal type is absent from the addressed profile",
    ))
  }
  fn read_variable(
    &mut self,
    fuel: usize,
    ctx: &Context,
    index: u64,
    uses: Uses,
  ) -> Result<Value, Error> {
    let n = usize::try_from(index).map_err(|_error| Error::Budget)?;
    let pos = ctx
      .vars
      .len()
      .checked_sub(n)
      .and_then(|v| v.checked_sub(1))
      .ok_or(Error::Unbound(n))?;
    let id = ctx.vars[pos];
    let b = self.binding(id)?.clone();
    self.charge(id, uses)?;
    if let Some(root) = b.value.loan_root
      && !self.binding(root)?.owner.live
    {
      return Err(Error::Moved(root));
    }
    let typ = self.shift(
      fuel,
      &b.value.typ,
      index.checked_add(1).ok_or(Error::Budget)?,
      0,
    )?;
    Ok(Value {
      typ,
      place: Some(id),
      owned: if b.owner.unique { Owned::Unique } else { Owned::Shared },
      ..b.value
    })
  }
  fn field(&self, type_ref: u64, index: u64) -> Result<Field, Error> {
    self
      .program
      .fields
      .iter()
      .find(|f| f.type_ref == type_ref && f.index == index)
      .cloned()
      .ok_or(Error::Unsupported("projection has no checked field rule"))
  }
  fn place(
    &mut self,
    fuel: usize,
    ctx: &Context,
    e: &Term,
  ) -> Result<Value, Error> {
    let fuel = self.tick(fuel)?;
    match e.as_ref() {
      Expr::Var(i) => {
        let value = self.read_variable(fuel, ctx, *i, Uses::Erased)?;
        let id = value.place.ok_or(Error::InvalidPlace)?;
        if self.binding(id)?.contract.uses == Uses::Erased {
          return Err(Error::Unsupported(
            "an erased binding cannot be borrowed",
          ));
        }
        Ok(value)
      },
      Expr::Share(i) => self.place(fuel, ctx, &self.expansion(*i)?),
      Expr::Prj(t, i, v) => {
        let mut v = self.place(fuel, ctx, v)?;
        let f = self.field(*t, *i)?;
        v.duplicable = f.contract.owned == Owned::Shared
          || self.is_shareable(fuel, &f.typ)?;
        v.typ = f.typ;
        if v.owned != Owned::Unique || f.contract.owned != Owned::Unique {
          v.owned = Owned::Shared;
        }
        Ok(v)
      },
      _ => Err(Error::InvalidPlace),
    }
  }
  fn type_of(
    &mut self,
    fuel: usize,
    ctx: &Context,
    e: &Term,
  ) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    match e.as_ref() {
      Expr::Var(i) => {
        let n = usize::try_from(*i).map_err(|_error| Error::Budget)?;
        let pos = ctx
          .vars
          .len()
          .checked_sub(n)
          .and_then(|v| v.checked_sub(1))
          .ok_or(Error::Unbound(n))?;
        let typ = self.binding(ctx.vars[pos])?.value.typ.clone();
        self.shift(fuel, &typ, i.checked_add(1).ok_or(Error::Budget)?, 0)
      },
      Expr::Ref(i, _) => Ok(self.declaration(*i)?.typ.clone()),
      Expr::Share(i) => self.type_of(fuel, ctx, &self.expansion(*i)?),
      Expr::Rec(..) => {
        Err(Error::Unsupported("unresolved recursive reference"))
      },
      Expr::Sort(_) | Expr::All(..) => Ok(Expr::sort(0)),
      Expr::Nat(_) => Self::literal_type(&self.program.nat_type),
      Expr::Str(_) => Self::literal_type(&self.program.string_type),
      Expr::Prj(t, i, _) => Ok(self.field(*t, *i)?.typ),
      Expr::App(f, a) => {
        let t = self.type_of(fuel, ctx, f)?;
        let (_, _, _, b) = self.arrow(fuel, &t)?;
        self.substitute(fuel, &b, a, 0)
      },
      Expr::Lam(c, t, b) => {
        let before = self.state.bindings.clone();
        let id = self.push(*c, Value::shared(t.clone()));
        let mut inner = ctx.clone();
        inner.vars.push(id);
        let codomain = self.type_of(fuel, &inner, b)?;
        self.state.bindings = before;
        Ok(Expr::all_contract(*c, ValueContract::shared(), t.clone(), codomain))
      },
      Expr::Let(c, t, v, b) => {
        let before = self.state.bindings.clone();
        let id = self.push(c.binder, Value::shared(t.clone()));
        let mut inner = ctx.clone();
        inner.vars.push(id);
        let typ = self.type_of(fuel, &inner, b)?;
        self.state.bindings = before;
        self.substitute(fuel, &typ, v, 0)
      },
    }
  }
  fn finish(
    &mut self,
    fuel: usize,
    destination: usize,
    expected: Expected,
    value: Value,
  ) -> Result<Value, Error> {
    match expected {
      None => Ok(value),
      Some((typ, contract)) => {
        self.require_type(fuel, &value.typ, &typ)?;
        self.consume_as(contract, destination, value)
      },
    }
  }
  fn ordinary_call(
    &mut self,
    fuel: usize,
    ctx: &Context,
    f: &Term,
    a: &Term,
    destination: usize,
    grade: Uses,
  ) -> Result<Value, Error> {
    let fn_type = self.type_of(fuel, ctx, f)?;
    let (input, result, domain, codomain) = self.arrow(fuel, &fn_type)?;
    let scope =
      if result.locality == Locality::Local { destination } else { ctx.scope };
    let f = self.analyze(fuel, ctx, f, None, scope, grade)?;
    self.require_type(fuel, &f.typ, &fn_type)?;
    self.invoke(&f)?;
    let arg = self.analyze(
      fuel,
      ctx,
      a,
      Some((domain, input.value)),
      scope,
      scale(grade, input.uses),
    )?;
    let typ = self.substitute(fuel, &codomain, a, 0)?;
    let origins = if result.locality == Locality::Local {
      union(&union(&f.origins, &arg.origins), &[scope])
    } else {
      vec![]
    };
    let duplicable =
      result.owned == Owned::Shared || self.is_shareable(fuel, &typ)?;
    Ok(Value { owned: result.owned, origins, duplicable, ..Value::shared(typ) })
  }
  fn selection(
    &mut self,
    fuel: usize,
    ctx: &Context,
    index: u64,
    args: &[Term],
    destination: usize,
    grade: Uses,
  ) -> Result<Value, Error> {
    let typ = self.declaration(index)?.typ.clone();
    let (c, _, selector_type, tail) = self.arrow(fuel, &typ)?;
    self.analyze(
      fuel,
      ctx,
      &args[0],
      Some((selector_type, c.value)),
      ctx.scope,
      scale(grade, c.uses),
    )?;
    let tail = self.substitute(fuel, &tail, &args[0], 0)?;
    let (_, _, left_type, tail) = self.arrow(fuel, &tail)?;
    let tail = self.substitute(fuel, &tail, &args[1], 0)?;
    let (_, result, right_type, output_type) = self.arrow(fuel, &tail)?;
    let output_type = self.substitute(fuel, &output_type, &args[2], 0)?;
    self.require_type(fuel, &left_type, &right_type)?;
    self.require_type(fuel, &left_type, &output_type)?;
    let before = self.state.bindings.clone();
    let left = self.analyze(
      fuel,
      ctx,
      &args[1],
      Some((left_type, result)),
      destination,
      grade,
    )?;
    let left_bindings = self.state.bindings.clone();
    self.state.bindings = before.clone();
    let right = self.analyze(
      fuel,
      ctx,
      &args[2],
      Some((right_type, result)),
      destination,
      grade,
    )?;
    let mut bindings = vec![];
    for (i, mut b) in left_bindings.into_iter().take(before.len()).enumerate() {
      let r = self.binding(i)?;
      b.owner = b.owner.join(&r.owner);
      b.demand = join(b.demand, r.demand);
      b.touched |= r.touched;
      bindings.push(b);
    }
    self.state.bindings = bindings;
    Ok(Value {
      typ: output_type,
      owned: if left.owned == Owned::Unique && right.owned == Owned::Unique {
        Owned::Unique
      } else {
        Owned::Shared
      },
      origins: union(&left.origins, &right.origins),
      duplicable: left.duplicable && right.duplicable,
      place: if left.place == right.place { left.place } else { None },
      loan_root: if left.loan_root == right.loan_root {
        left.loan_root
      } else {
        None
      },
    })
  }
  fn analyze(
    &mut self,
    fuel: usize,
    ctx: &Context,
    e: &Term,
    expected: Expected,
    destination: usize,
    grade: Uses,
  ) -> Result<Value, Error> {
    let fuel = self.tick(fuel)?;
    if grade == Uses::Erased {
      let typ = self.type_of(fuel, ctx, e)?;
      if let Some((expected_type, _)) = expected {
        self.require_type(fuel, &typ, &expected_type)?;
      }
      return Ok(Value::fresh(typ));
    }
    if let Some((t, _)) = &expected
      && matches!(self.whnf(fuel, t)?.as_ref(), Expr::Sort(_))
    {
      return Ok(Value::fresh(t.clone()));
    }
    if grade != Uses::Linear {
      let before = self.state.bindings.clone();
      for b in &mut self.state.bindings {
        b.demand = Uses::Erased;
        b.touched = false;
      }
      let output =
        self.analyze(fuel, ctx, e, expected, destination, Uses::Linear)?;
      for (id, old) in before.into_iter().enumerate() {
        let used = self.binding_mut(id)?;
        used.demand = add(old.demand, scale(grade, used.demand));
        used.touched |= old.touched;
      }
      return Ok(output);
    }
    let value = match e.as_ref() {
      Expr::Share(i) => self.analyze(
        fuel,
        ctx,
        &self.expansion(*i)?,
        expected.clone(),
        destination,
        grade,
      )?,
      Expr::Var(i) => self.read_variable(fuel, ctx, *i, grade)?,
      Expr::Ref(i, _) => {
        if self.program.choices.contains(i) {
          return Err(Error::Unsupported(
            "selection primitives cannot escape as function values",
          ));
        }
        Value::shared(self.declaration(*i)?.typ.clone())
      },
      Expr::Rec(..) => {
        return Err(Error::Unsupported("unresolved recursive reference"));
      },
      Expr::Sort(_) | Expr::All(..) => Value::fresh(Expr::sort(0)),
      Expr::Nat(_) => Value::fresh(Self::literal_type(&self.program.nat_type)?),
      Expr::Str(_) => {
        Value::fresh(Self::literal_type(&self.program.string_type)?)
      },
      Expr::Lam(input, domain, body) => {
        let (result, codomain) = match &expected {
          Some((t, _)) => {
            let (declared, r, t, b) = self.arrow(fuel, t)?;
            if *input != declared {
              return Err(Error::BinderMismatch);
            }
            self.require_type(fuel, domain, &t)?;
            (r, Some(b))
          },
          None => (ValueContract::shared(), None),
        };
        let before = self.state.bindings.clone();
        for b in &mut self.state.bindings {
          b.demand = Uses::Erased;
          b.touched = false;
        }
        let caller_scope = self.scope(ctx.scope)?;
        let body_scope = self.scope(caller_scope)?;
        let duplicable = input.value.owned == Owned::Shared
          || self.is_shareable(fuel, domain)?;
        let parameter = self.push(
          *input,
          Value {
            owned: input.value.owned,
            duplicable,
            origins: if input.value.locality == Locality::Local {
              vec![caller_scope]
            } else {
              vec![]
            },
            ..Value::shared(domain.clone())
          },
        );
        let mut inner = ctx.clone();
        inner.vars.push(parameter);
        inner.scope = body_scope;
        let body_expected = codomain.as_ref().map(|t| (t.clone(), result));
        let output = self.analyze(
          fuel,
          &inner,
          body,
          body_expected.clone(),
          caller_scope,
          Uses::Linear,
        )?;
        let output = if body_expected.is_some() {
          output
        } else {
          self.consume_as(result, caller_scope, output)?
        };
        self.validate_usage(parameter)?;
        let mut origins = vec![];
        let mut duplicable = true;
        let mut bindings = vec![];
        for (id, old) in before.into_iter().enumerate() {
          let used = self.binding(id)?;
          let mut owner = used.owner.clone();
          let mut demand = used.demand;
          if used.touched {
            origins = union(&origins, &old.value.origins);
            if old.contract.uses != Uses::Many || !old.value.duplicable {
              duplicable = false;
            }
            if old.owner.unique {
              old.owner.move_out(id)?;
              owner.live = false;
              if demand == Uses::Erased {
                demand = Uses::Linear;
              }
              duplicable = false;
            }
          }
          let demand = add(old.demand, scale(grade, demand));
          let touched = old.touched || used.touched;
          bindings.push(Binding { owner, demand, touched, ..old });
        }
        self.state.bindings = bindings;
        Value {
          origins,
          duplicable,
          ..Value::fresh(Expr::all_contract(
            *input,
            result,
            domain.clone(),
            codomain.unwrap_or(output.typ),
          ))
        }
      },
      Expr::Let(contract, typ, initializer, body) => {
        let scope = self.scope(ctx.scope)?;
        let initialized = match contract.kind {
          LetKind::Value => self.analyze(
            fuel,
            ctx,
            initializer,
            Some((typ.clone(), contract.binder.value)),
            if contract.binder.value.locality == Locality::Local {
              scope
            } else {
              destination
            },
            scale(grade, contract.binder.uses),
          )?,
          LetKind::BorrowShared => {
            if contract.binder.value != ValueContract::local_shared() {
              return Err(Error::InvalidBorrow);
            }
            let mut v = self.place(fuel, ctx, initializer)?;
            self.require_type(fuel, &v.typ, typ)?;
            if !self.is_shareable(fuel, typ)? && !v.duplicable {
              return Err(Error::Nonduplicable);
            }
            let owner_place = v.place.ok_or(Error::InvalidPlace)?;
            let root = v.loan_root.unwrap_or(owner_place);
            let b = self.binding_mut(root)?;
            b.owner.begin_loan(root, scope)?;
            v.owned = Owned::Shared;
            v.duplicable = true;
            v.origins = union(&v.origins, &[scope]);
            v.place = None;
            v.loan_root = Some(root);
            v
          },
        };
        let id =
          self.push(contract.binder, Value { typ: typ.clone(), ..initialized });
        let mut inner = ctx.clone();
        inner.vars.push(id);
        inner.scope = scope;
        let body_expected = match &expected {
          None => None,
          Some((t, c)) => Some((self.shift(fuel, t, 1, 0)?, *c)),
        };
        let output = self.analyze(
          fuel,
          &inner,
          body,
          body_expected,
          destination,
          grade,
        )?;
        self.validate_usage(id)?;
        let mut output = self.materialize(output)?;
        self.close_scope(scope, &output)?;
        output.typ = self.substitute(fuel, &output.typ, initializer, 0)?;
        output
      },
      Expr::Prj(t, i, value) => {
        let mut v = self.analyze(fuel, ctx, value, None, destination, grade)?;
        let field = self.field(*t, *i)?;
        v.duplicable = field.contract.owned == Owned::Shared
          || self.is_shareable(fuel, &field.typ)?;
        v.typ = field.typ;
        if v.owned != Owned::Unique || field.contract.owned != Owned::Unique {
          v.owned = Owned::Shared;
        }
        v
      },
      Expr::App(f, a) => {
        let mut head = e.clone();
        let mut args = vec![];
        let mut split_fuel = fuel;
        loop {
          split_fuel = self.tick(split_fuel)?;
          match head.as_ref() {
            Expr::App(f, a) => {
              args.push(a.clone());
              head = f.clone();
            },
            Expr::Share(index) => head = self.expansion(*index)?,
            _ => break,
          }
        }
        args.reverse();
        if let Expr::Ref(i, _) = head.as_ref() {
          if self.program.choices.contains(i) {
            if args.len() != 3 {
              return Err(Error::Unsupported(
                "selection primitives require a complete application",
              ));
            }
            self.selection(fuel, ctx, *i, &args, destination, grade)?
          } else {
            self.ordinary_call(fuel, ctx, f, a, destination, grade)?
          }
        } else {
          self.ordinary_call(fuel, ctx, f, a, destination, grade)?
        }
      },
    };
    self.finish(fuel, destination, expected, value)
  }
}

pub fn check_definition(
  program: &Program,
  index: usize,
  limits: Limits,
) -> Result<(), Error> {
  let declaration =
    program.declarations.get(index).ok_or(Error::BadReference(index as u64))?;
  let body = declaration
    .body
    .as_ref()
    .ok_or(Error::Unsupported("definition has no body"))?;
  let mut checker = Checker::new(program, limits);
  let scope = checker.scope(0)?;
  checker.analyze(
    limits.depth,
    &Context { scope, vars: vec![] },
    body,
    Some((declaration.typ.clone(), ValueContract::shared())),
    scope,
    Uses::Linear,
  )?;
  Ok(())
}

#[derive(Clone, Debug, Default)]
struct Scan {
  annotated: bool,
  dependencies: Vec<usize>,
}
impl Scan {
  fn merge(mut self, other: Self) -> Self {
    self.annotated |= other.annotated;
    self.dependencies.extend(other.dependencies);
    self
  }
}

impl Checker<'_> {
  fn scan(&mut self, fuel: usize, e: &Term) -> Result<Scan, Error> {
    if fuel == 0 {
      return Err(Error::Budget);
    }
    let mut finished = std::collections::HashSet::new();
    let mut active = std::collections::HashSet::new();
    let mut stack = vec![(e.clone(), false)];
    let mut scan = Scan::default();
    while let Some((e, closing)) = stack.pop() {
      let key = e.clone();
      if closing {
        active.remove(&key);
        finished.insert(key);
        continue;
      }
      if active.contains(&key) {
        return Err(Error::Unsupported("cyclic sharing"));
      }
      if finished.contains(&key) {
        continue;
      }
      self.tick(1)?;
      active.insert(key);
      stack.push((e.clone(), true));
      match e.as_ref() {
        Expr::Ref(i, _) => {
          self.declaration(*i)?;
          scan.dependencies.push(
            usize::try_from(*i).map_err(|_error| Error::BadReference(*i))?,
          );
        },
        Expr::Rec(..) => {
          return Err(Error::Unsupported("unresolved recursive reference"));
        },
        Expr::Share(i) => stack.push((self.expansion(*i)?, false)),
        Expr::Prj(i, _, v) => {
          self.declaration(*i)?;
          scan.dependencies.push(
            usize::try_from(*i).map_err(|_error| Error::BadReference(*i))?,
          );
          stack.push((v.clone(), false));
        },
        Expr::App(f, a) => {
          stack.push((a.clone(), false));
          stack.push((f.clone(), false));
        },
        Expr::Lam(c, t, b) => {
          scan.annotated |= *c != BinderContract::default();
          stack.push((b.clone(), false));
          stack.push((t.clone(), false));
        },
        Expr::All(c, r, t, b) => {
          scan.annotated |=
            *c != BinderContract::default() || *r != ValueContract::shared();
          stack.push((b.clone(), false));
          stack.push((t.clone(), false));
        },
        Expr::Let(c, t, v, b) => {
          scan.annotated |=
            c.binder != BinderContract::default() || c.kind != LetKind::Value;
          stack.push((b.clone(), false));
          stack.push((v.clone(), false));
          stack.push((t.clone(), false));
        },
        _ => {},
      }
    }
    Ok(scan)
  }
  fn check_constructor_type(
    &mut self,
    fuel: usize,
    typ: &Term,
    has_finite: bool,
    has_local: bool,
  ) -> Result<(), Error> {
    let fuel = self.tick(fuel)?;
    let typ = self.whnf(fuel, typ)?;
    if let Expr::All(input, result, domain, codomain) = typ.as_ref() {
      let domain = self.whnf(fuel, domain)?;
      let erased =
        input.uses == Uses::Erased || matches!(domain.as_ref(), Expr::Sort(_));
      if !covers(input.uses, if erased { Uses::Erased } else { Uses::Linear }) {
        return Err(Error::Unsupported(
          "constructor input quantity does not cover its stored occurrence",
        ));
      }
      let finite = has_finite
        || (!erased
          && (input.uses != Uses::Many || input.value.owned == Owned::Unique));
      let local_capture =
        has_local || (!erased && input.value.locality == Locality::Local);
      if finite && result.owned != Owned::Unique {
        return Err(Error::Unsupported(
          "constructor result drops a finite or unique capture",
        ));
      }
      if local_capture && result.locality != Locality::Local {
        return Err(Error::Unsupported(
          "constructor result drops a local capture",
        ));
      }
      self.check_constructor_type(fuel, codomain, finite, local_capture)?;
    }
    Ok(())
  }
}

/// Dependencies propagate resource relevance to callers and to every member
/// of a mutually addressed block. Only wholly ordinary components bypass the
/// resource analysis; erased typechecking is still required for them.
pub fn relevance(
  program: &Program,
  limits: Limits,
) -> Result<Vec<bool>, Error> {
  let size = program.declarations.len();
  let mut reverse = vec![vec![]; size];
  let mut marked = vec![false; size];
  let mut queue = vec![];
  for (i, d) in program.declarations.iter().enumerate() {
    let mut checker = Checker::new(program, limits);
    let scan = checker.scan(limits.depth, &d.typ)?;
    let scan = match &d.body {
      None => scan,
      Some(body) => scan.merge(checker.scan(limits.depth, body)?),
    };
    if scan.annotated {
      marked[i] = true;
      queue.push(i);
    }
    for dependency in scan.dependencies {
      reverse
        .get_mut(dependency)
        .ok_or(Error::BadReference(dependency as u64))?
        .push(i);
    }
  }
  for (i, expression) in &program.auxiliary {
    if *i >= size {
      return Err(Error::BadReference(*i as u64));
    }
    let mut checker = Checker::new(program, limits);
    let scan = checker.scan(limits.depth, expression)?;
    if scan.annotated && !marked[*i] {
      marked[*i] = true;
      queue.push(*i);
    }
    for dependency in scan.dependencies {
      reverse
        .get_mut(dependency)
        .ok_or(Error::BadReference(dependency as u64))?
        .push(*i);
    }
  }
  for f in &program.fields {
    let i = usize::try_from(f.type_ref)
      .map_err(|_error| Error::BadReference(f.type_ref))?;
    let m = marked.get_mut(i).ok_or(Error::BadReference(f.type_ref))?;
    if f.contract != ValueContract::shared() && !*m {
      *m = true;
      queue.push(i);
    }
  }
  for group in &program.groups {
    if let Some(first) = group.first().copied() {
      if first >= size {
        return Err(Error::BadReference(first as u64));
      }
      for member in group {
        if *member >= size {
          return Err(Error::BadReference(*member as u64));
        }
        reverse[first].push(*member);
        reverse[*member].push(first);
      }
    }
  }
  let mut cursor = 0;
  while cursor < queue.len() {
    let i = queue[cursor];
    cursor += 1;
    for dependent in &reverse[i] {
      if !marked[*dependent] {
        marked[*dependent] = true;
        queue.push(*dependent);
      }
    }
  }
  Ok(marked)
}

#[derive(Clone, Debug, Default)]
pub struct Policy {
  pub assumptions: Vec<usize>,
  pub shareable_types: Vec<usize>,
  pub choices: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmissionError {
  pub declaration: Option<usize>,
  pub error: Error,
}

pub fn admit_program(
  program: &Program,
  policy: &Policy,
  limits: Limits,
) -> Result<(), AdmissionError> {
  for index in &program.choices {
    let index = usize::try_from(*index).map_err(|_error| AdmissionError {
      declaration: None,
      error: Error::BadReference(*index),
    })?;
    if !policy.choices.contains(&index) || !policy.assumptions.contains(&index)
    {
      return Err(AdmissionError {
        declaration: Some(index),
        error: Error::Unsupported(
          "selection behavior is absent from the bound profile",
        ),
      });
    }
    let d = program.declarations.get(index).ok_or(AdmissionError {
      declaration: None,
      error: Error::BadReference(index as u64),
    })?;
    if d.kind != DeclKind::Assumption {
      return Err(AdmissionError {
        declaration: Some(index),
        error: Error::Unsupported(
          "selection behavior requires an external primitive interface",
        ),
      });
    }
  }
  for index in &program.shareable_types {
    let index = usize::try_from(*index).map_err(|_error| AdmissionError {
      declaration: None,
      error: Error::BadReference(*index),
    })?;
    if !policy.shareable_types.contains(&index) {
      return Err(AdmissionError {
        declaration: Some(index),
        error: Error::Unsupported(
          "shareable representation is absent from the bound profile",
        ),
      });
    }
  }
  let marked = relevance(program, limits)
    .map_err(|error| AdmissionError { declaration: None, error })?;
  for (i, d) in program.declarations.iter().enumerate() {
    if marked[i] {
      let result = match d.kind {
        DeclKind::Definition => check_definition(program, i, limits),
        DeclKind::Assumption => {
          if policy.assumptions.contains(&i) {
            Ok(())
          } else {
            Err(Error::Unsupported(
              "external resource interface is absent from the bound profile",
            ))
          }
        },
        DeclKind::Constructor => Checker::new(program, limits)
          .check_constructor_type(limits.depth, &d.typ, false, false),
        DeclKind::TypeConstructor => Ok(()),
      };
      result.map_err(|error| AdmissionError { declaration: Some(i), error })?;
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn b(uses: Uses, value: ValueContract) -> BinderContract {
    BinderContract { uses, value }
  }
  fn nat() -> Term {
    Expr::reference(0, vec![])
  }
  fn arr(
    input: BinderContract,
    result: ValueContract,
    domain: Term,
    codomain: Term,
  ) -> Term {
    Expr::all_contract(input, result, domain, codomain)
  }
  fn unary(input: BinderContract, result: ValueContract) -> Term {
    arr(input, result, nat(), nat())
  }
  fn choice(result: ValueContract) -> Term {
    arr(
      b(Uses::Linear, ValueContract::shared()),
      ValueContract::shared(),
      nat(),
      arr(
        b(Uses::Affine, result),
        ValueContract::shared(),
        nat(),
        unary(b(Uses::Affine, result), result),
      ),
    )
  }
  fn assumption(typ: Term) -> Declaration {
    Declaration { typ, body: None, kind: DeclKind::Assumption }
  }
  fn identity(input: BinderContract, result: ValueContract) -> Declaration {
    Declaration {
      typ: unary(input, result),
      body: Some(Expr::lam_contract(input, nat(), Expr::var(0))),
      kind: DeclKind::Definition,
    }
  }
  fn program() -> Program {
    let mut p = Program {
      declarations: vec![
        Declaration {
          typ: Expr::sort(0),
          body: None,
          kind: DeclKind::TypeConstructor,
        },
        assumption(unary(
          b(Uses::Many, ValueContract::local_shared()),
          ValueContract::shared(),
        )),
        identity(
          b(Uses::Linear, ValueContract::local_shared()),
          ValueContract::local_shared(),
        ),
        identity(
          b(Uses::Linear, ValueContract::unique()),
          ValueContract::unique(),
        ),
        assumption(unary(
          b(Uses::Erased, ValueContract::shared()),
          ValueContract::shared(),
        )),
        assumption(unary(
          b(Uses::Many, ValueContract::shared()),
          ValueContract::shared(),
        )),
        assumption(choice(ValueContract::shared())),
        Declaration {
          typ: Expr::sort(0),
          body: None,
          kind: DeclKind::TypeConstructor,
        },
        assumption(arr(
          b(Uses::Linear, ValueContract::local_shared()),
          ValueContract::local_shared(),
          nat(),
          Expr::reference(7, vec![]),
        )),
        assumption(choice(ValueContract::local_shared())),
        assumption(choice(ValueContract::unique())),
      ],
      ..Default::default()
    };
    p.fields.push(Field {
      type_ref: 7,
      index: 0,
      typ: nat(),
      contract: ValueContract::unique(),
    });
    p.fields.push(Field {
      type_ref: 7,
      index: 1,
      typ: unary(
        b(Uses::Many, ValueContract::shared()),
        ValueContract::shared(),
      ),
      contract: ValueContract::unique(),
    });
    p.fields.push(Field {
      type_ref: 7,
      index: 2,
      typ: unary(
        b(Uses::Many, ValueContract::shared()),
        ValueContract::shared(),
      ),
      contract: ValueContract::shared(),
    });
    p.nat_type = Some(nat());
    p.string_type = Some(nat());
    p.sharing.push(Expr::var(0));
    p.sharing.push(Expr::reference(6, vec![]));
    p.shareable_types = vec![0, 7];
    p.choices = vec![6, 9, 10];
    p
  }
  fn parse(hex: &str) -> Term {
    let bytes: Vec<_> = hex
      .as_bytes()
      .as_chunks::<2>()
      .0
      .iter()
      .map(|pair| {
        u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap()
      })
      .collect();
    assert_eq!(bytes.len() * 2, hex.len());
    let mut input = bytes.as_slice();
    let expr = crate::serialize::get_expr(&mut input).unwrap();
    assert!(input.is_empty());
    expr
  }

  #[test]
  fn shared_resource_acceptance_and_rejection_fixtures() {
    let mut count = 0;
    for line in include_str!("../../../Tests/Fixtures/ixon-v3/resource.tsv")
      .lines()
      .filter(|l| !l.starts_with('#') && !l.is_empty())
    {
      let cols: Vec<_> = line.split('\t').collect();
      assert_eq!(cols.len(), 4);
      let mut p = program();
      let index = p.declarations.len();
      p.declarations.push(Declaration {
        typ: parse(cols[2]),
        body: Some(parse(cols[3])),
        kind: DeclKind::Definition,
      });
      let actual = check_definition(&p, index, Limits::default());
      let code = actual.as_ref().map_or_else(|e| e.code(), |()| "ok");
      assert_eq!(code, cols[1], "{}: {actual:?}", cols[0]);
      count += 1;
    }
    assert!(count >= 55);
  }

  #[test]
  fn every_input_result_contract_is_checked() {
    for input in 0..16 {
      let input = BinderContract::from_bits(input).unwrap();
      for result in 0..4 {
        let result = ValueContract::from_bits(result).unwrap();
        let mut p = program();
        let index = p.declarations.len();
        let body =
          if input.uses == Uses::Erased { Expr::nat(0) } else { Expr::var(0) };
        p.declarations.push(Declaration {
          typ: unary(input, result),
          body: Some(Expr::lam_contract(input, nat(), body)),
          kind: DeclKind::Definition,
        });
        let allowed = input.uses == Uses::Erased
          || ((input.value.owned == Owned::Unique
            || result.owned == Owned::Shared)
            && (input.value.locality == Locality::Unrestricted
              || result.locality == Locality::Local));
        assert_eq!(
          check_definition(&p, index, Limits::default()).is_ok(),
          allowed,
          "{input:?} -> {result:?}"
        );
      }
    }
  }

  #[test]
  fn scope_exit_never_restores_moved_or_shared_owners() {
    for live in [false, true] {
      for unique in [false, true] {
        for loans in [vec![], vec![1], vec![1, 2]] {
          let owner = Owner { live, unique, loans };
          let mut ended = owner.clone();
          ended.end_loan(1);
          assert_eq!((ended.live, ended.unique), (live, unique));
          assert_eq!(
            owner.move_out(0).is_ok(),
            live && unique && owner.loans.is_empty()
          );
          if let Ok(shared) = owner.share(0) {
            assert!(!shared.unique);
          }
          for other_live in [false, true] {
            for other_unique in [false, true] {
              let other =
                Owner { live: other_live, unique: other_unique, loans: vec![] };
              let joined = owner.join(&other);
              assert_eq!(joined.live, live && other_live);
              assert_eq!(joined.unique, unique && other_unique);
            }
          }
        }
      }
    }
  }

  #[test]
  fn cyclic_sharing_exhausts_the_bound() {
    let mut p = program();
    p.sharing = vec![Arc::new(Expr::Share(0))];
    let mut c = Checker::new(&p, Limits::default());
    assert_eq!(
      c.analyze(
        20,
        &Context::default(),
        &Arc::new(Expr::Share(0)),
        None,
        0,
        Uses::Linear
      )
      .unwrap_err(),
      Error::Budget
    );
  }

  #[test]
  fn literals_require_an_addressed_type() {
    let mut p = program();
    p.nat_type = None;
    let mut c = Checker::new(&p, Limits::default());
    assert!(matches!(
      c.analyze(20, &Context::default(), &Expr::nat(0), None, 0, Uses::Linear),
      Err(Error::Unsupported(_))
    ));
  }

  fn policy() -> Policy {
    Policy {
      assumptions: vec![1, 4, 6, 8, 9, 10],
      shareable_types: vec![0, 7],
      choices: vec![6, 9, 10],
    }
  }

  #[test]
  fn admission_binds_external_contracts_behavior_and_representations() {
    let p = program();
    assert!(admit_program(&p, &policy(), Limits::default()).is_ok());
    let mut missing = policy();
    missing.assumptions = vec![6, 9, 10];
    assert!(admit_program(&p, &missing, Limits::default()).is_err());
    let mut missing = policy();
    missing.choices.clear();
    assert!(admit_program(&p, &missing, Limits::default()).is_err());
    let mut missing = policy();
    missing.shareable_types.clear();
    assert!(admit_program(&p, &missing, Limits::default()).is_err());
  }

  #[test]
  fn relevance_scans_shared_dags_and_rejects_cycles() {
    let mut sharing = vec![Expr::sort(0)];
    for i in 0..40 {
      sharing.push(Expr::app(Expr::share(i), Expr::share(i)));
    }
    let mut p = Program {
      declarations: vec![Declaration {
        typ: Expr::sort(0),
        body: Some(Expr::share(40)),
        kind: DeclKind::Definition,
      }],
      sharing,
      ..Default::default()
    };
    assert_eq!(
      relevance(&p, Limits { depth: 1, steps: 200 }).unwrap(),
      vec![false]
    );
    p.sharing = vec![Expr::share(0)];
    p.declarations[0].body = Some(Expr::share(0));
    assert!(relevance(&p, Limits::default()).is_err());
  }

  #[test]
  fn relevance_reaches_aliases_and_mutual_siblings() {
    let mut p = program();
    let typ =
      unary(b(Uses::Many, ValueContract::shared()), ValueContract::shared());
    p.declarations.push(Declaration {
      typ: typ.clone(),
      body: Some(Expr::reference(2, vec![])),
      kind: DeclKind::Definition,
    });
    p.declarations.push(Declaration {
      typ,
      body: Some(Expr::reference(11, vec![])),
      kind: DeclKind::Definition,
    });
    let marked = relevance(&p, Limits::default()).unwrap();
    assert!(marked[11] && marked[12]);
    let rejected = admit_program(&p, &policy(), Limits::default()).unwrap_err();
    assert_eq!(rejected.declaration, Some(11));
    assert_eq!(rejected.error, Error::TypeMismatch);
    let mut p = program();
    p.declarations.push(Declaration {
      typ: nat(),
      body: Some(Expr::nat(0)),
      kind: DeclKind::Definition,
    });
    p.groups.push(vec![2, 11]);
    assert!(relevance(&p, Limits::default()).unwrap()[11]);
    assert!(admit_program(&p, &policy(), Limits::default()).is_ok());
  }

  #[test]
  fn constructors_keep_captures_in_all_results() {
    let linear = b(Uses::Linear, ValueContract::shared());
    let many = b(Uses::Many, ValueContract::shared());
    let local = b(Uses::Many, ValueContract::local_shared());
    for (typ, allowed) in [
      (unary(linear, ValueContract::shared()), false),
      (unary(linear, ValueContract::unique()), true),
      (unary(local, ValueContract::shared()), false),
      (unary(local, ValueContract::local_shared()), true),
      (
        arr(
          linear,
          ValueContract::unique(),
          nat(),
          unary(many, ValueContract::shared()),
        ),
        false,
      ),
      (
        arr(
          linear,
          ValueContract::unique(),
          nat(),
          unary(many, ValueContract::unique()),
        ),
        true,
      ),
      (
        arr(
          b(Uses::Erased, ValueContract::shared()),
          ValueContract::shared(),
          Expr::sort(0),
          nat(),
        ),
        true,
      ),
      (arr(linear, ValueContract::unique(), Expr::sort(0), nat()), false),
    ] {
      let mut p = program();
      p.declarations.push(Declaration {
        typ,
        body: None,
        kind: DeclKind::Constructor,
      });
      assert_eq!(
        admit_program(&p, &policy(), Limits::default()).is_ok(),
        allowed
      );
    }
  }
}
