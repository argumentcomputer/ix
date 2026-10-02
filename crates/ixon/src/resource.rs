//! Resource checking for Ixon. Mirrors `Ix/Resource/{Basic,Check}.lean`.
//!
//! The address adapter supplies a globally indexed program whose erased types
//! have been checked. External interfaces and special primitives are explicit
//! profile assumptions. No result here certifies unverified typechecking or
//! an unbound primitive profile.

pub mod addressed;

use crate::contract::{
  BinderContract, LetContract, LetKind, Locality, ValueContract,
};
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
  /// A safe theorem. Its proof is erased computation that no backend runs, so
  /// admission checks no resource obligation in it. Its statement still
  /// takes part in relevance, and callers still use it as an interface.
  Theorem,
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
  /// `0` when `typ` is closed. Otherwise `typ` is open over the constructor
  /// telescope: the structure's parameters, then the fields before this one
  /// (innermost last), `binders` variables in all.
  pub binders: u64,
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
  /// Profile-bound non-strict selection primitives. A choice is applied to
  /// exactly as many arguments as its type has leading arrows (more are
  /// passed on to both alternatives). Its last two arguments are the
  /// alternatives, evaluated by need; the others are strict. An alternative
  /// expecting a proof (`dite`) is entered with a fresh proof binder.
  pub choices: Vec<u64>,
  /// The sort index that denotes `Prop`. The address adapter rewrites every
  /// sort to `0` (some type universe) or this index (literally `Sort 0`).
  /// Values of a proposition are erased computation with zero demand; without
  /// this index no type is recognized as a proposition.
  pub prop_sort: Option<u64>,
  /// Recursors the case-split rule can read.
  pub recursors: Vec<RecursorInfo>,
  /// Profile behavior: a recursor application whose minor premises ignore
  /// their induction hypotheses is a case split; an unannotated definition
  /// that only wraps a case split or a choice (`casesOn`, matchers) is
  /// inlined, and a beta-redex binds its argument. The consumer must compile
  /// these without closures.
  pub cases: bool,
  /// Admitted resource interfaces: callers see this type in place of the
  /// declaration's own. The profile must also list the declaration as an
  /// assumption.
  pub interfaces: Vec<(u64, Term)>,
}

/// The shape of an addressed recursor of a single, non-mutual inductive type,
/// as the case-split rule needs it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RecursorInfo {
  pub index: u64,
  pub params: usize,
  pub motives: usize,
  pub minors: usize,
  pub indices: usize,
  /// Constructor fields of each minor premise, in minor order.
  pub fields: Vec<usize>,
  /// Leading binders of each minor's declared domain: its fields, then its
  /// induction hypotheses.
  pub binders: Vec<usize>,
}

impl RecursorInfo {
  pub fn arity(&self) -> usize {
    self.params + self.motives + self.minors + self.indices + 1
  }
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

/// What a selection primitive supplies to the binders of its alternatives.
enum Supply {
  /// Proofs (`dite`): erased computation with no origins.
  Proofs,
  /// Constructor fields of an inspected major premise, followed by induction
  /// hypotheses.
  Fields { fields: Vec<usize>, major: Value },
}
impl Supply {
  fn value(
    &self,
    j: usize,
    k: usize,
    domain: Term,
    field: BinderContract,
  ) -> Value {
    match self {
      Self::Fields { fields, major } if k < fields[j] => Value {
        owned: if major.owned == Owned::Unique
          && field.value.owned == Owned::Unique
        {
          Owned::Unique
        } else {
          Owned::Shared
        },
        origins: major.origins.clone(),
        loan_root: major.loan_root,
        ..Value::shared(domain)
      },
      _ => Value::shared(domain),
    }
  }
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
  /// Whether the bounded inference types `typ` as the sort `prop`. An
  /// expression it cannot type is not.
  fn has_sort(
    &mut self,
    fuel: usize,
    ctx: &Context,
    typ: &Term,
    prop: u64,
  ) -> Result<bool, Error> {
    let before = self.state.bindings.clone();
    let sort =
      self.type_of(fuel, ctx, typ).and_then(|sort| self.whnf(fuel, &sort));
    self.state.bindings = before;
    match sort {
      Ok(sort) => Ok(matches!(sort.as_ref(), Expr::Sort(s) if *s == prop)),
      Err(Error::Budget) => Err(Error::Budget),
      Err(_) => Ok(false),
    }
  }
  /// Whether `typ` is a proposition, so that its values are erased proofs.
  /// A `∀` is a proposition when its body is (impredicativity); otherwise the
  /// type's own type must reduce to the program's `Prop` sort. The unreduced
  /// type is tried first: reduction can unfold a proposition such as `a ≤ b`
  /// to a class projection that has no field rule. Anything this bounded
  /// inference cannot type is conservatively not a proposition.
  fn is_proposition(
    &mut self,
    fuel: usize,
    ctx: &Context,
    typ: &Term,
  ) -> Result<bool, Error> {
    let Some(prop) = self.program.prop_sort else { return Ok(false) };
    let fuel = self.tick(fuel)?;
    let reduced = self.whnf(fuel, typ)?;
    match reduced.as_ref() {
      Expr::All(c, _, domain, body) => {
        let before = self.state.bindings.clone();
        let id = self.push(*c, Value::shared(domain.clone()));
        let mut inner = ctx.clone();
        inner.vars.push(id);
        let result = self.is_proposition(fuel, &inner, body);
        self.state.bindings = before;
        result
      },
      Expr::Sort(_) | Expr::Lam(..) => Ok(false),
      _ => Ok(
        self.has_sort(fuel, ctx, typ, prop)?
          || self.has_sort(fuel, ctx, &reduced, prop)?,
      ),
    }
  }
  /// Argument demand at a call. A callee's multiplicity does not scale the
  /// demand on a value of a profile-shareable (immediate) type: the callee
  /// receives a copy that holds no resource, so passing it is one
  /// consumption. The caller's own reads still count, and a zero-use input
  /// still has zero demand.
  fn argument_grade(
    &mut self,
    fuel: usize,
    grade: Uses,
    input: Uses,
    domain: &Term,
  ) -> Result<Uses, Error> {
    if input != Uses::Erased && self.is_shareable(fuel, domain)? {
      Ok(grade)
    } else {
      Ok(scale(grade, input))
    }
  }
  /// Analyze one argument against a callee binder. A proof (an argument whose
  /// domain is a proposition) is erased computation: it has no demand, owner
  /// transfer, or origin, and its typing is the erased typechecker's job.
  #[allow(clippy::too_many_arguments)]
  fn analyze_argument(
    &mut self,
    fuel: usize,
    ctx: &Context,
    a: &Term,
    domain: Term,
    input: BinderContract,
    scope: usize,
    grade: Uses,
  ) -> Result<Value, Error> {
    if self.is_proposition(fuel, ctx, &domain)? {
      return Ok(Value::fresh(domain));
    }
    let grade = self.argument_grade(fuel, grade, input.uses, &domain)?;
    self.analyze(fuel, ctx, a, Some((domain, input.value)), scope, grade)
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
  fn split_app(
    &mut self,
    fuel: usize,
    e: &Term,
  ) -> Result<(Term, Vec<Term>), Error> {
    let mut head = e.clone();
    let mut args = vec![];
    let mut fuel = fuel;
    loop {
      fuel = self.tick(fuel)?;
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
    Ok((head, args))
  }
  /// The type of `field` projected from `value`, whose type is `value_type`.
  /// An open field rule is instantiated with the structure's type arguments,
  /// taken from `value_type`, and with the earlier fields as projections of
  /// `value`.
  fn field_type(
    &mut self,
    fuel: usize,
    field: &Field,
    value_type: &Term,
    value: &Term,
  ) -> Result<Term, Error> {
    if field.binders == 0 {
      return Ok(field.typ.clone());
    }
    let mismatch = Error::Unsupported(
      "projected value does not have the field's structure type",
    );
    let params =
      field.binders.checked_sub(field.index).ok_or(mismatch.clone())?;
    let reduced = self.whnf(fuel, value_type)?;
    let (head, args) = self.split_app(fuel, &reduced)?;
    if !matches!(head.as_ref(), Expr::Ref(i, _) if *i == field.type_ref)
      || args.len() as u64 != params
    {
      return Err(mismatch);
    }
    let mut values = args;
    for j in 0..field.index {
      values.push(Expr::prj(field.type_ref, j, value.clone()));
    }
    let mut typ = field.typ.clone();
    let mut depth = values.len() as u64;
    for x in &values {
      depth -= 1;
      typ = self.substitute(fuel, &typ, x, depth)?;
    }
    Ok(typ)
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
      Expr::Prj(t, i, projected) => {
        let mut v = self.place(fuel, ctx, projected)?;
        let f = self.field(*t, *i)?;
        let typ = self.field_type(fuel, &f, &v.typ, projected)?;
        v.duplicable =
          f.contract.owned == Owned::Shared || self.is_shareable(fuel, &typ)?;
        v.typ = typ;
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
      Expr::Ref(i, _) => self.interface_type(*i),
      Expr::Share(i) => self.type_of(fuel, ctx, &self.expansion(*i)?),
      Expr::Rec(..) => {
        Err(Error::Unsupported("unresolved recursive reference"))
      },
      Expr::Sort(_) | Expr::All(..) => Ok(Expr::sort(0)),
      Expr::Nat(_) => Self::literal_type(&self.program.nat_type),
      Expr::Str(_) => Self::literal_type(&self.program.string_type),
      Expr::Prj(t, i, v) => {
        let field = self.field(*t, *i)?;
        if field.binders == 0 {
          return Ok(field.typ);
        }
        let value_type = self.type_of(fuel, ctx, v)?;
        self.field_type(fuel, &field, &value_type, v)
      },
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
    // Applying a proof (a function whose type is a proposition) yields a
    // proof: erased computation, as a proof argument is.
    if self.is_proposition(fuel, ctx, &fn_type)? {
      return Ok(Value::fresh(self.substitute(fuel, &codomain, a, 0)?));
    }
    let scope =
      if result.locality == Locality::Local { destination } else { ctx.scope };
    let f = self.analyze(fuel, ctx, f, None, scope, grade)?;
    self.require_type(fuel, &f.typ, &fn_type)?;
    self.invoke(&f)?;
    let arg =
      self.analyze_argument(fuel, ctx, a, domain, input, scope, grade)?;
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
  /// The interface callers see: an admitted interface, or the declared type.
  fn interface_type(&self, index: u64) -> Result<Term, Error> {
    match self.program.interfaces.iter().find(|(i, _)| *i == index) {
      Some((_, typ)) => Ok(typ.clone()),
      None => Ok(self.declaration(index)?.typ.clone()),
    }
  }
  /// Expand sharing at the head of an expression.
  fn unshare(&mut self, fuel: usize, e: &Term) -> Result<Term, Error> {
    let fuel = self.tick(fuel)?;
    match e.as_ref() {
      Expr::Share(i) => {
        let expanded = self.expansion(*i)?;
        self.unshare(fuel, &expanded)
      },
      _ => Ok(e.clone()),
    }
  }
  /// Whether an expression carries no resource contract (every binder, arrow
  /// and let has the default contract).
  fn plain(&mut self, fuel: usize, e: &Term) -> Result<bool, Error> {
    let fuel = self.tick(fuel)?;
    Ok(match e.as_ref() {
      Expr::Share(i) => {
        let expanded = self.expansion(*i)?;
        self.plain(fuel, &expanded)?
      },
      Expr::App(f, a) => {
        let f = self.plain(fuel, f)?;
        let a = self.plain(fuel, a)?;
        f && a
      },
      Expr::Lam(c, t, b) => {
        let t = self.plain(fuel, t)?;
        let b = self.plain(fuel, b)?;
        *c == BinderContract::default() && t && b
      },
      Expr::All(c, r, t, b) => {
        let t = self.plain(fuel, t)?;
        let b = self.plain(fuel, b)?;
        *c == BinderContract::default()
          && *r == ValueContract::shared()
          && t
          && b
      },
      Expr::Let(c, t, v, b) => {
        let t = self.plain(fuel, t)?;
        let v = self.plain(fuel, v)?;
        let b = self.plain(fuel, b)?;
        c.binder == BinderContract::default()
          && c.kind == LetKind::Value
          && t
          && v
          && b
      },
      Expr::Prj(_, _, v) => self.plain(fuel, v)?,
      _ => true,
    })
  }
  /// Whether variable `index` occurs in `e`.
  fn occurs(
    &mut self,
    fuel: usize,
    e: &Term,
    index: u64,
  ) -> Result<bool, Error> {
    let fuel = self.tick(fuel)?;
    Ok(match e.as_ref() {
      Expr::Var(i) => *i == index,
      Expr::Share(i) => {
        let expanded = self.expansion(*i)?;
        self.occurs(fuel, &expanded, index)?
      },
      Expr::App(f, a) => {
        let f = self.occurs(fuel, f, index)?;
        let a = self.occurs(fuel, a, index)?;
        f || a
      },
      Expr::Lam(_, t, b) | Expr::All(_, _, t, b) => {
        let t = self.occurs(fuel, t, index)?;
        let b = self.occurs(fuel, b, index + 1)?;
        t || b
      },
      Expr::Let(_, t, v, b) => {
        let t = self.occurs(fuel, t, index)?;
        let v = self.occurs(fuel, v, index)?;
        let b = self.occurs(fuel, b, index + 1)?;
        t || v || b
      },
      Expr::Prj(_, _, v) => self.occurs(fuel, v, index)?,
      _ => false,
    })
  }
  /// Number of leading arrows of a type.
  fn arity(&mut self, fuel: usize, typ: &Term) -> Result<usize, Error> {
    let fuel = fuel.checked_sub(1).ok_or(Error::Budget)?;
    let typ = self.whnf(fuel, typ)?;
    match typ.as_ref() {
      Expr::All(_, _, _, body) => Ok(self.arity(fuel, body)? + 1),
      _ => Ok(0),
    }
  }
  fn recursor_info(&self, index: u64) -> Option<RecursorInfo> {
    self.program.recursors.iter().find(|r| r.index == index).cloned()
  }
  /// Whether a minor premise ignores its induction hypotheses: it binds all
  /// of the minor's binders and its body mentions none of the hypotheses.
  fn ignores_hypotheses(
    &mut self,
    fuel: usize,
    minor: &Term,
    fields: usize,
    binders: usize,
  ) -> Result<bool, Error> {
    if binders == fields {
      return Ok(true);
    }
    let mut body = minor.clone();
    for _ in 0..binders {
      match self.unshare(fuel, &body)?.as_ref() {
        Expr::Lam(_, _, b) => body = b.clone(),
        _ => return Ok(false),
      }
    }
    for k in 0..binders.saturating_sub(fields) {
      if self.occurs(fuel, &body, k as u64)? {
        return Ok(false);
      }
    }
    Ok(true)
  }
  /// The arity of an unannotated, non-recursive definition that only wraps a
  /// case split: its body is a lambda telescope around a full application of
  /// a case recursor whose minors ignore their induction hypotheses, or of
  /// another such wrapper (`casesOn`, matchers). A definition that wraps a
  /// choice is an ordinary function.
  fn case_wrapper(
    &mut self,
    fuel: usize,
    depth: usize,
    index: u64,
  ) -> Result<Option<usize>, Error> {
    let Some(depth) = depth.checked_sub(1) else { return Ok(None) };
    if !self.program.cases || self.program.choices.contains(&index) {
      return Ok(None);
    }
    let Some(d) = usize::try_from(index)
      .ok()
      .and_then(|i| self.program.declarations.get(i))
      .cloned()
    else {
      return Ok(None);
    };
    let Some(body) = d.body.clone() else { return Ok(None) };
    let plain_type = self.plain(fuel, &d.typ)?;
    let plain_body = self.plain(fuel, &body)?;
    if !(d.kind == DeclKind::Definition && plain_type && plain_body) {
      return Ok(None);
    }
    let mut inner = body;
    let mut params = 0;
    loop {
      let unshared = self.unshare(fuel, &inner)?;
      match unshared.as_ref() {
        Expr::Lam(_, _, b) => {
          inner = b.clone();
          params += 1;
        },
        _ => {
          inner = unshared;
          break;
        },
      }
    }
    let (head, args) = self.split_app(fuel, &inner)?;
    let Expr::Ref(target, _) = head.as_ref() else { return Ok(None) };
    if let Some(info) = self.recursor_info(*target) {
      if args.len() < info.arity() {
        return Ok(None);
      }
      for j in 0..info.minors {
        let minor = args[info.params + info.motives + j].clone();
        if !self.ignores_hypotheses(
          fuel,
          &minor,
          info.fields[j],
          info.binders[j],
        )? {
          return Ok(None);
        }
      }
      return Ok(Some(params));
    }
    Ok(match self.case_wrapper(fuel, depth, *target)? {
      Some(n) => (args.len() >= n).then_some(params),
      None => None,
    })
  }
  /// Whether a type is a sort or an arrow into a sort.
  fn type_former(
    &mut self,
    fuel: usize,
    depth: usize,
    typ: &Term,
  ) -> Result<bool, Error> {
    let Some(depth) = depth.checked_sub(1) else { return Ok(false) };
    let typ = self.whnf(fuel, typ)?;
    match typ.as_ref() {
      Expr::Sort(_) => Ok(true),
      Expr::All(_, _, _, b) => self.type_former(fuel, depth, b),
      _ => Ok(false),
    }
  }
  /// Whether an argument may be substituted into a lambda telescope: a
  /// variable, a value form, or a type or proof (erased computation).
  fn substitutable(
    &mut self,
    fuel: usize,
    ctx: &Context,
    arg: &Term,
    domain: &Term,
  ) -> Result<bool, Error> {
    match self.unshare(fuel, arg)?.as_ref() {
      Expr::Var(_)
      | Expr::Lam(..)
      | Expr::Sort(_)
      | Expr::All(..)
      | Expr::Nat(_)
      | Expr::Str(_)
      | Expr::Ref(..) => Ok(true),
      _ => {
        if self.type_former(fuel, 16, domain)? {
          return Ok(true);
        }
        self.is_proposition(fuel, ctx, domain)
      },
    }
  }
  /// Apply a lambda telescope to arguments, as `let`s: an argument of a
  /// binder with the default contract that is a variable, a value form, a
  /// type or a proof is substituted; any other argument is bound by a `let`
  /// carrying the binder's own contract, so it is evaluated once, before the
  /// body, exactly as a call would evaluate it. Arguments beyond the
  /// telescope are applied to the body.
  fn bind_arguments(
    &mut self,
    fuel: usize,
    ctx: &Context,
    telescope: &Term,
    args: &[Term],
  ) -> Result<Term, Error> {
    let before = self.state.bindings.clone();
    let mut term = telescope.clone();
    let mut lets: Vec<(LetContract, Term, Term)> = vec![];
    let mut inner = ctx.clone();
    let mut rest = 0;
    while rest < args.len() {
      let unshared = self.unshare(fuel, &term)?;
      let Expr::Lam(c, domain, body) = unshared.as_ref() else { break };
      let arg = self.shift(fuel, &args[rest], lets.len() as u64, 0)?;
      if *c == BinderContract::default()
        && self.substitutable(fuel, &inner, &arg, domain)?
      {
        term = self.substitute(fuel, body, &arg, 0)?;
      } else {
        lets.push((
          LetContract { non_dep: false, kind: LetKind::Value, binder: *c },
          domain.clone(),
          arg,
        ));
        let id = self.push(*c, Value::shared(domain.clone()));
        inner.vars.push(id);
        term = body.clone();
      }
      rest += 1;
    }
    for arg in &args[rest..] {
      term = Expr::app(term, self.shift(fuel, arg, lets.len() as u64, 0)?);
    }
    self.state.bindings = before;
    for (c, domain, value) in lets.into_iter().rev() {
      term = Expr::let_contract(c, domain, value, term);
    }
    Ok(term)
  }
  fn join_value(a: Value, b: Value) -> Value {
    Value {
      typ: a.typ,
      owned: if a.owned == Owned::Unique && b.owned == Owned::Unique {
        Owned::Unique
      } else {
        Owned::Shared
      },
      origins: union(&a.origins, &b.origins),
      duplicable: a.duplicable && b.duplicable,
      place: if a.place == b.place { a.place } else { None },
      loan_root: if a.loan_root == b.loan_root { a.loan_root } else { None },
    }
  }
  /// Analyze alternatives from the same state and join them. Each alternative
  /// first binds the values the primitive supplies to it (one per flag;
  /// `true` marks an induction hypothesis, which must stay unused), then is
  /// analyzed with the given contract.
  #[allow(clippy::too_many_arguments)]
  fn alternatives(
    &mut self,
    fuel: usize,
    ctx: &Context,
    branches: &[(Term, Term, Vec<bool>)],
    supply: &Supply,
    extra: &[Term],
    contract: Option<ValueContract>,
    output_type: Term,
    destination: usize,
    grade: Uses,
  ) -> Result<Value, Error> {
    let before = self.state.bindings.clone();
    let count = before.len();
    let mut joined: Option<Vec<Binding>> = None;
    let mut result: Option<Value> = None;
    for (j, (alternative, alternative_type, hypotheses)) in
      branches.iter().enumerate()
    {
      self.state.bindings = before.clone();
      let mut body = alternative.clone();
      let mut typ = alternative_type.clone();
      let mut inner = ctx.clone();
      let mut entered = vec![];
      for (k, hypothesis) in hypotheses.iter().enumerate() {
        let (field, _, domain, codomain) = self.arrow(fuel, &typ)?;
        let unshared = self.unshare(fuel, &body)?;
        let (c, rest) = match unshared.as_ref() {
          Expr::Lam(c, _, b) => (*c, b.clone()),
          _ => (
            BinderContract::default(),
            Expr::app(self.shift(fuel, &unshared, 1, 0)?, Expr::var(0)),
          ),
        };
        let value = supply.value(j, k, domain, field);
        let id = self.push(c, value);
        entered.push((id, *hypothesis));
        inner.vars.push(id);
        body = rest;
        typ = codomain;
      }
      for x in extra {
        let x = self.shift(fuel, x, entered.len() as u64, 0)?;
        let (_, _, _, codomain) = self.arrow(fuel, &typ)?;
        typ = self.substitute(fuel, &codomain, &x, 0)?;
        body = Expr::app(body, x);
      }
      let output = self.analyze(
        fuel,
        &inner,
        &body,
        contract.map(|c| (typ, c)),
        destination,
        grade,
      )?;
      for (id, hypothesis) in entered {
        if hypothesis {
          if self.binding(id)?.touched {
            return Err(Error::Unsupported(
              "a case split uses an induction hypothesis",
            ));
          }
        } else {
          self.validate_usage(id)?;
        }
      }
      let mut output = output;
      if output.place.is_some_and(|p| p >= count) {
        output.place = None;
      }
      let bindings: Vec<Binding> =
        self.state.bindings.iter().take(count).cloned().collect();
      joined = Some(match joined {
        None => bindings,
        Some(acc) => acc
          .into_iter()
          .zip(bindings)
          .map(|(mut a, b)| {
            a.owner = a.owner.join(&b.owner);
            a.demand = join(a.demand, b.demand);
            a.touched |= b.touched;
            a
          })
          .collect(),
      });
      result = Some(match result {
        None => output,
        Some(v) => Self::join_value(v, output),
      });
    }
    self.state.bindings = joined.unwrap_or(before);
    let mut value = result.unwrap_or_else(|| Value::fresh(output_type.clone()));
    value.typ = output_type;
    Ok(value)
  }
  /// A choice: strict leading arguments, then two alternatives evaluated by
  /// need. Proof binders of an alternative (`dite`) are supplied by the
  /// primitive. The chosen alternative is the result: the caller's contract
  /// applies to it, or else the primitive's own result contract.
  #[allow(clippy::too_many_arguments)]
  fn choice(
    &mut self,
    fuel: usize,
    ctx: &Context,
    index: u64,
    args: &[Term],
    expected: &Expected,
    destination: usize,
    grade: Uses,
  ) -> Result<Value, Error> {
    let declared = self.declaration(index)?.typ.clone();
    let n = self.arity(fuel, &declared)?;
    if args.len() < n {
      return Err(Error::Unsupported(
        "selection primitives require a complete application",
      ));
    }
    if n < 2 {
      return Err(Error::Unsupported(
        "a selection primitive needs two alternatives",
      ));
    }
    let mut tail = declared;
    for arg in &args[..n - 2] {
      let (c, _, domain, codomain) = self.arrow(fuel, &tail)?;
      self.analyze_argument(fuel, ctx, arg, domain, c, ctx.scope, grade)?;
      tail = self.substitute(fuel, &codomain, arg, 0)?;
    }
    let left = args[n - 2].clone();
    let right = args[n - 1].clone();
    let (_, _, left_type, after_left) = self.arrow(fuel, &tail)?;
    let after_left = self.substitute(fuel, &after_left, &left, 0)?;
    let (_, result, right_type, after_right) = self.arrow(fuel, &after_left)?;
    let mut output_type = self.substitute(fuel, &after_right, &right, 0)?;
    let extra = &args[n..];
    for x in extra {
      let (_, _, _, codomain) = self.arrow(fuel, &output_type)?;
      output_type = self.substitute(fuel, &codomain, x, 0)?;
    }
    let before = self.state.bindings.clone();
    let left_proofs = self.proofs(fuel, ctx, &left_type)?;
    let right_proofs = self.proofs(fuel, ctx, &right_type)?;
    self.state.bindings = before;
    if left_proofs.is_empty() && right_proofs.is_empty() && extra.is_empty() {
      self.require_type(fuel, &left_type, &right_type)?;
      self.require_type(fuel, &left_type, &output_type)?;
    }
    let contract = match expected {
      Some((_, c)) => *c,
      None => result,
    };
    self.alternatives(
      fuel,
      ctx,
      &[(left, left_type, left_proofs), (right, right_type, right_proofs)],
      &Supply::Proofs,
      extra,
      Some(contract),
      output_type,
      destination,
      grade,
    )
  }
  /// The proof binders an alternative expects (`dite`).
  fn proofs(
    &mut self,
    fuel: usize,
    ctx: &Context,
    typ: &Term,
  ) -> Result<Vec<bool>, Error> {
    let mut typ = typ.clone();
    let mut found = vec![];
    let mut inner = ctx.clone();
    loop {
      let reduced = self.whnf(fuel, &typ)?;
      let Expr::All(c, _, domain, body) = reduced.as_ref() else { break };
      if !self.is_proposition(fuel, &inner, domain)? {
        break;
      }
      found.push(false);
      let id = self.push(*c, Value::shared(domain.clone()));
      inner.vars.push(id);
      typ = body.clone();
    }
    Ok(found)
  }
  /// A case split. Parameters, motives and indices have no run-time demand;
  /// the major premise is inspected, not consumed; each minor binds the
  /// constructor's fields, which keep the major's origins and are unique only
  /// when both the major and the field binder are.
  #[allow(clippy::too_many_arguments)]
  fn case_split(
    &mut self,
    fuel: usize,
    ctx: &Context,
    index: u64,
    info: &RecursorInfo,
    args: &[Term],
    expected: &Expected,
    destination: usize,
    grade: Uses,
  ) -> Result<Value, Error> {
    let mut tail = self.declaration(index)?.typ.clone();
    let mut minor_types = vec![];
    for (i, arg) in args[..info.arity()].iter().enumerate() {
      let (_, _, domain, codomain) = self.arrow(fuel, &tail)?;
      if info.params + info.motives <= i
        && i < info.params + info.motives + info.minors
      {
        minor_types.push(domain);
      }
      tail = self.substitute(fuel, &codomain, arg, 0)?;
    }
    let mut output_type = tail;
    let extra = &args[info.arity()..];
    for x in extra {
      let (_, _, _, codomain) = self.arrow(fuel, &output_type)?;
      output_type = self.substitute(fuel, &codomain, x, 0)?;
    }
    let major = self.analyze(
      fuel,
      ctx,
      &args[info.arity() - 1],
      None,
      ctx.scope,
      grade,
    )?;
    let branches: Vec<_> = (0..info.minors)
      .map(|j| {
        (
          args[info.params + info.motives + j].clone(),
          minor_types[j].clone(),
          (0..info.binders[j]).map(|k| k >= info.fields[j]).collect(),
        )
      })
      .collect();
    self.alternatives(
      fuel,
      ctx,
      &branches,
      &Supply::Fields { fields: info.fields.clone(), major },
      extra,
      expected.as_ref().map(|(_, c)| *c),
      output_type,
      destination,
      grade,
    )
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
        Value::shared(self.interface_type(*i)?)
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
          let used_touched = used.touched;
          let mut owner = used.owner.clone();
          let mut demand = used.demand;
          if used_touched {
            origins = union(&origins, &old.value.origins);
            // A captured immediate (a value of a profile-shareable type) is
            // copied into the closure, as at a call boundary: neither its
            // finite use nor its uniqueness makes the closure one-shot.
            let immediate = self.is_shareable(fuel, &old.value.typ)?;
            if (old.contract.uses != Uses::Many && !immediate)
              || !old.value.duplicable
            {
              duplicable = false;
            }
            if old.owner.unique {
              old.owner.move_out(id)?;
              owner.live = false;
              if demand == Uses::Erased {
                demand = Uses::Linear;
              }
              if !immediate {
                duplicable = false;
              }
            }
          }
          let demand = add(old.demand, scale(grade, demand));
          let touched = old.touched || used_touched;
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
        let typ = self.field_type(fuel, &field, &v.typ, value)?;
        v.duplicable = field.contract.owned == Owned::Shared
          || self.is_shareable(fuel, &typ)?;
        v.typ = typ;
        if v.owned != Owned::Unique || field.contract.owned != Owned::Unique {
          v.owned = Owned::Shared;
        }
        v
      },
      Expr::App(f, a) => {
        let (head, args) = self.split_app(fuel, e)?;
        match head.as_ref() {
          Expr::Ref(i, _) if self.program.choices.contains(i) => {
            self.choice(fuel, ctx, *i, &args, &expected, destination, grade)?
          },
          Expr::Ref(i, _) => {
            let info =
              if self.program.cases { self.recursor_info(*i) } else { None };
            match info {
              Some(info) if args.len() >= info.arity() => self.case_split(
                fuel,
                ctx,
                *i,
                &info,
                &args,
                &expected,
                destination,
                grade,
              )?,
              Some(_) => {
                self.ordinary_call(fuel, ctx, f, a, destination, grade)?
              },
              None => match self.case_wrapper(fuel, 4, *i)? {
                Some(n) if args.len() >= n => {
                  // A wrapper around a case split or a choice is unfolded.
                  match self.declaration(*i)?.body.clone() {
                    Some(body) => {
                      let term =
                        self.bind_arguments(fuel, ctx, &body, &args)?;
                      self.analyze(
                        fuel,
                        ctx,
                        &term,
                        expected.clone(),
                        destination,
                        grade,
                      )?
                    },
                    None => {
                      self.ordinary_call(fuel, ctx, f, a, destination, grade)?
                    },
                  }
                },
                _ => self.ordinary_call(fuel, ctx, f, a, destination, grade)?,
              },
            }
          },
          Expr::Lam(..) if self.program.cases => {
            let term = self.bind_arguments(fuel, ctx, &head, &args)?;
            self.analyze(
              fuel,
              ctx,
              &term,
              expected.clone(),
              destination,
              grade,
            )?
          },
          _ => self.ordinary_call(fuel, ctx, f, a, destination, grade)?,
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
  /// The profile admits case splits, case wrappers and beta-redexes.
  pub cases: bool,
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
    // A choice is an external primitive or an assumed definition (whose
    // selection behavior the profile admits; its body is not checked).
    if d.kind != DeclKind::Assumption && d.kind != DeclKind::Definition {
      return Err(AdmissionError {
        declaration: Some(index),
        error: Error::Unsupported(
          "selection behavior requires an external primitive interface",
        ),
      });
    }
  }
  for (index, _) in &program.interfaces {
    let index = usize::try_from(*index).map_err(|_error| AdmissionError {
      declaration: None,
      error: Error::BadReference(*index),
    })?;
    if !policy.assumptions.contains(&index) {
      return Err(AdmissionError {
        declaration: Some(index),
        error: Error::Unsupported(
          "admitted interface is absent from the bound profile",
        ),
      });
    }
  }
  if program.cases && !policy.cases {
    return Err(AdmissionError {
      declaration: None,
      error: Error::Unsupported(
        "case behavior is absent from the bound profile",
      ),
    });
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
        // An assumed definition's interface is admitted by the profile.
        DeclKind::Definition if policy.assumptions.contains(&i) => Ok(()),
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
        DeclKind::TypeConstructor | DeclKind::Theorem => Ok(()),
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
      binders: 0,
    });
    p.fields.push(Field {
      type_ref: 7,
      index: 1,
      typ: unary(
        b(Uses::Many, ValueContract::shared()),
        ValueContract::shared(),
      ),
      contract: ValueContract::unique(),
      binders: 0,
    });
    p.fields.push(Field {
      type_ref: 7,
      index: 2,
      typ: unary(
        b(Uses::Many, ValueContract::shared()),
        ValueContract::shared(),
      ),
      contract: ValueContract::shared(),
      binders: 0,
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

  /// Check every `name, expected code, type hex, body hex` line of a shared
  /// fixture file against `base` extended with the case definition.
  fn run_fixture_lines(base: &Program, text: &str) -> usize {
    let mut count = 0;
    for line in text.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
      let cols: Vec<_> = line.split('\t').collect();
      assert_eq!(cols.len(), 4);
      let mut p = base.clone();
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
    count
  }

  #[test]
  fn shared_resource_acceptance_and_rejection_fixtures() {
    let text = include_str!("../../../Tests/Fixtures/ixon-v4/resource.tsv");
    assert!(run_fixture_lines(&program(), text) >= 55);
  }

  /// The base program extended for the usage and ownership modes. Mirrors
  /// `Tests.Resource.modesProgram`; new declarations are only appended.
  fn modes_program() -> Program {
    let mut p = program();
    let res = Expr::reference(11, vec![]);
    let prf = Expr::reference(13, vec![]);
    let many = b(Uses::Many, ValueContract::shared());
    p.declarations.extend([
      // 11 Res: a type with no shareable or plain-data rule.
      Declaration {
        typ: Expr::sort(0),
        body: None,
        kind: DeclKind::TypeConstructor,
      },
      // 12 consumes a Res through a many binder.
      assumption(arr(many, ValueContract::shared(), res.clone(), res)),
      // 13 Prf: a proposition.
      Declaration {
        typ: Expr::sort(1),
        body: None,
        kind: DeclKind::TypeConstructor,
      },
      // 14 consumes a proof through a many binder.
      assumption(arr(many, ValueContract::shared(), prf, nat())),
      // 15 a binary many function on Nat.
      assumption(arr(
        many,
        ValueContract::shared(),
        nat(),
        unary(many, ValueContract::shared()),
      )),
      // 16 a proposition whose unfolding has no field rule.
      Declaration {
        typ: arr(many, ValueContract::shared(), nat(), Expr::sort(1)),
        body: Some(Expr::lam_contract(
          many,
          nat(),
          Expr::prj(0, 0, Expr::var(0)),
        )),
        kind: DeclKind::Definition,
      },
      // 17 consumes a proof of it.
      assumption(arr(
        many,
        ValueContract::shared(),
        Expr::app(Expr::reference(16, vec![]), Expr::nat(0)),
        nat(),
      )),
      // 18 Duo α β.
      Declaration {
        typ: arr(
          many,
          ValueContract::shared(),
          Expr::sort(0),
          arr(many, ValueContract::shared(), Expr::sort(0), Expr::sort(0)),
        ),
        body: None,
        kind: DeclKind::TypeConstructor,
      },
      // 19 Sig α β, with β : α → Type.
      Declaration {
        typ: arr(
          many,
          ValueContract::shared(),
          Expr::sort(0),
          arr(
            many,
            ValueContract::shared(),
            arr(many, ValueContract::shared(), Expr::var(0), Expr::sort(0)),
            Expr::sort(0),
          ),
        ),
        body: None,
        kind: DeclKind::TypeConstructor,
      },
      // 20 F : Nat → Type.
      Declaration {
        typ: arr(many, ValueContract::shared(), nat(), Expr::sort(0)),
        body: None,
        kind: DeclKind::TypeConstructor,
      },
    ]);
    // Open field rules: `Duo α β` has `fst : α`, `snd : β`; `Sig α β` has
    // `fst : α`, `snd : β fst`.
    for (type_ref, index, typ, binders) in [
      (18, 0, Expr::var(1), 2),
      (18, 1, Expr::var(1), 3),
      (19, 0, Expr::var(1), 2),
      (19, 1, Expr::app(Expr::var(1), Expr::var(0)), 3),
    ] {
      p.fields.push(Field {
        type_ref,
        index,
        typ,
        contract: ValueContract::shared(),
        binders,
      });
    }
    p.prop_sort = Some(1);
    p
  }

  #[test]
  fn usage_and_ownership_mode_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-modes.tsv");
    assert!(run_fixture_lines(&modes_program(), text) >= 8);
  }

  /// The mode program extended with case splits. Mirrors
  /// `Tests.Resource.casesProgram`; new declarations are only appended.
  fn cases_program() -> Program {
    let mut p = modes_program();
    let many = b(Uses::Many, ValueContract::shared());
    let shared = ValueContract::shared();
    let res = || Expr::reference(11, vec![]);
    let prf = || Expr::reference(13, vec![]);
    let boxt = || Expr::reference(21, vec![]);
    let chain = || Expr::reference(25, vec![]);
    let all = |d: Term, c: Term| arr(many, shared, d, c);
    let lam = |d: Term, body: Term| Expr::lam_contract(many, d, body);
    let app = Expr::app;
    let motive = |t: Term| all(t, Expr::sort(0));
    let ctor =
      |typ: Term| Declaration { typ, body: None, kind: DeclKind::Constructor };
    let inductive = || Declaration {
      typ: Expr::sort(0),
      body: None,
      kind: DeclKind::TypeConstructor,
    };
    p.declarations.extend([
      // 21 Box, 22 Box.empty, 23 Box.full.
      inductive(),
      ctor(boxt()),
      ctor(all(res(), boxt())),
      // 24 Box.rec.
      assumption(all(
        motive(boxt()),
        all(
          app(Expr::var(0), Expr::reference(22, vec![])),
          all(
            all(
              res(),
              app(Expr::var(2), app(Expr::reference(23, vec![]), Expr::var(0))),
            ),
            all(boxt(), app(Expr::var(3), Expr::var(0))),
          ),
        ),
      )),
      // 25 Chain, 26 Chain.stop, 27 Chain.link.
      inductive(),
      ctor(chain()),
      ctor(all(chain(), chain())),
      // 28 Chain.rec.
      assumption(all(
        motive(chain()),
        all(
          app(Expr::var(0), Expr::reference(26, vec![])),
          all(
            all(
              chain(),
              all(
                app(Expr::var(2), Expr::var(0)),
                app(
                  Expr::var(3),
                  app(Expr::reference(27, vec![]), Expr::var(1)),
                ),
              ),
            ),
            all(chain(), app(Expr::var(3), Expr::var(0))),
          ),
        ),
      )),
      // 29 Box.casesOn.
      Declaration {
        typ: all(
          motive(boxt()),
          all(
            boxt(),
            all(
              app(Expr::var(1), Expr::reference(22, vec![])),
              all(
                all(
                  res(),
                  app(
                    Expr::var(3),
                    app(Expr::reference(23, vec![]), Expr::var(0)),
                  ),
                ),
                app(Expr::var(3), Expr::var(2)),
              ),
            ),
          ),
        ),
        body: Some(lam(
          motive(boxt()),
          lam(
            boxt(),
            lam(
              app(Expr::var(1), Expr::reference(22, vec![])),
              lam(
                all(
                  res(),
                  app(
                    Expr::var(3),
                    app(Expr::reference(23, vec![]), Expr::var(0)),
                  ),
                ),
                app(
                  app(
                    app(
                      app(Expr::reference(24, vec![]), Expr::var(3)),
                      Expr::var(1),
                    ),
                    lam(res(), app(Expr::var(1), Expr::var(0))),
                  ),
                  Expr::var(2),
                ),
              ),
            ),
          ),
        )),
        kind: DeclKind::Definition,
      },
      // 30 a fresh Res.
      assumption(res()),
      // 31 a choice whose alternatives receive a proof.
      assumption(all(
        nat(),
        all(all(prf(), res()), all(all(prf(), res()), res())),
      )),
      // 32 a choice with a leading type argument.
      assumption(all(
        Expr::sort(0),
        all(nat(), all(Expr::var(1), all(Expr::var(2), Expr::var(3)))),
      )),
    ]);
    p.choices.extend([31, 32]);
    p.recursors = vec![
      RecursorInfo {
        index: 24,
        params: 0,
        motives: 1,
        minors: 2,
        indices: 0,
        fields: vec![0, 1],
        binders: vec![0, 1],
      },
      RecursorInfo {
        index: 28,
        params: 0,
        motives: 1,
        minors: 2,
        indices: 0,
        fields: vec![0, 1],
        binders: vec![0, 2],
      },
    ];
    p.cases = true;
    p
  }

  /// Mirrors the R15 part of `Tests.Resource.runAdmission`.
  #[test]
  fn assumed_definitions_interfaces_and_case_behavior() {
    let linear = b(Uses::Linear, ValueContract::shared());
    let unused = Declaration {
      typ: unary(linear, ValueContract::shared()),
      body: Some(Expr::lam_contract(linear, nat(), Expr::nat(0))),
      kind: DeclKind::Definition,
    };
    let mut assumed = program();
    assumed.declarations.push(unused);
    let mut p = policy();
    p.assumptions.push(11);
    assert!(admit_program(&assumed, &p, Limits::default()).is_ok());
    let affine = b(Uses::Affine, ValueContract::shared());
    let mut chooser = assumed.clone();
    chooser.declarations.push(Declaration {
      typ: choice(ValueContract::shared()),
      body: Some(Expr::lam_contract(
        linear,
        nat(),
        Expr::lam_contract(
          affine,
          nat(),
          Expr::lam_contract(affine, nat(), Expr::var(0)),
        ),
      )),
      kind: DeclKind::Definition,
    });
    chooser.choices.push(12);
    let mut q = p.clone();
    q.choices.push(12);
    assert!(admit_program(&chooser, &q, Limits::default()).is_err());
    q.assumptions.push(12);
    assert!(admit_program(&chooser, &q, Limits::default()).is_ok());
    let mut interfaced = program();
    interfaced.interfaces.push((
      5,
      unary(
        b(Uses::Many, ValueContract::local_shared()),
        ValueContract::shared(),
      ),
    ));
    assert!(admit_program(&interfaced, &policy(), Limits::default()).is_err());
    let mut r = policy();
    r.assumptions.push(5);
    assert!(admit_program(&interfaced, &r, Limits::default()).is_ok());
    let mut cases = program();
    cases.cases = true;
    assert!(admit_program(&cases, &policy(), Limits::default()).is_err());
    let mut s = policy();
    s.cases = true;
    assert!(admit_program(&cases, &s, Limits::default()).is_ok());
  }

  #[test]
  fn case_split_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-cases.tsv");
    assert!(run_fixture_lines(&cases_program(), text) >= 19);
  }

  #[test]
  fn theorem_proofs_carry_no_resource_obligation() {
    let mut p = program();
    let typ =
      unary(b(Uses::Linear, ValueContract::shared()), ValueContract::shared());
    // A linear binder that is never consumed would be rejected in a definition.
    let body = Expr::lam_contract(
      b(Uses::Linear, ValueContract::shared()),
      nat(),
      Expr::nat(0),
    );
    p.declarations.push(Declaration {
      typ: typ.clone(),
      body: Some(body.clone()),
      kind: DeclKind::Theorem,
    });
    assert!(admit_program(&p, &policy(), Limits::default()).is_ok());
    let last = p.declarations.len() - 1;
    p.declarations[last].kind = DeclKind::Definition;
    assert_eq!(
      admit_program(&p, &policy(), Limits::default()).unwrap_err().error,
      Error::Usage(0, Uses::Linear, Uses::Erased)
    );
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
      cases: false,
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
