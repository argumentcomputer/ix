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
  /// Explicit resource-free scalar assumptions; ownership only.
  pub scalar_types: Vec<u64>,
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
  /// their induction hypotheses is a case split, a bound case definition
  /// (`case_definitions`) is unfolded, and a beta-redex binds its arguments
  /// strictly. The consumer must compile these without closures.
  pub cases: bool,
  /// Profile-bound case definitions (`casesOn`, matchers): unannotated
  /// definitions that only wrap a case split. Only these are unfolded, and
  /// only the alternatives they take are bound by need; every other
  /// definition is an ordinary call, however match-shaped its body.
  pub case_definitions: Vec<u64>,
  /// Admitted resource interfaces: callers see this type in place of the
  /// declaration's own. The profile must also list the declaration as an
  /// assumption.
  pub interfaces: Vec<(u64, Term)>,
  /// The `Eq` type, when the profile names unfolding equations.
  pub eq_type: Option<u64>,
  /// Profile-bound unfolding equations `(definition, theorem)`: a definition
  /// with one is checked through the right-hand side of the theorem's
  /// statement `∀ xs, f xs = rhs` instead of its own body (for example a
  /// `brecOn` or `WellFounded.fix` encoding). The consumer must run the
  /// definition by that equation.
  pub equations: Vec<(u64, u64)>,
  /// Axioms other than `propext`, `Quot.sound` and `Classical.choice` (the
  /// adapter recognizes those three by address): an unfolding equation whose
  /// proof depends on one (`sorryAx`, any user axiom) is not admitted.
  pub axioms: Vec<u64>,
  /// Parameter counts of constructors `(constructor, params)`: the leading
  /// arguments of a constructor application that are its inductive type's
  /// parameters, not fields. A constructor that is absent has none.
  pub constructors: Vec<(u64, usize)>,
  /// Usage crossing on plain data (the plain profile, `crossing plain`): a
  /// value of a type that crosses (`crosses`: plain data, or a
  /// profile-shareable type, and not opted out) is not bound by a written
  /// `1`/`&` usage contract (both bounds are dropped; the binder is
  /// reported), as OxCaml's data types cross linearity. Ownership,
  /// locality, borrows and the closure rules are unaffected.
  pub crossing: bool,
  /// Types opted out of usage crossing (`linear NAME`): capability tokens
  /// whose single use the consumer relies on.
  pub linear_types: Vec<u64>,
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

/// How an occurrence of a parameter sits in an alternative argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Occurrence {
  /// The parameter does not occur.
  Absent,
  /// The parameter is the head of an application to this many arguments,
  /// none of which mention it, and nothing else in the alternative does.
  Applied(usize),
  /// Any other occurrence (under a closure, as an argument, more than once).
  Other,
}

/// The shape of a bound case definition: its parameter count, and for each
/// parameter `Some(k)` when it is taken by need (it occurs only as the head
/// of alternatives, applied to at least `k` arguments) or `None` when it is
/// strict.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CaseShape {
  arity: usize,
  by_need: Vec<Option<usize>>,
}

#[derive(Clone, Debug)]
struct Value {
  typ: Term,
  owned: Owned,
  origins: Vec<usize>,
  duplicable: bool,
  place: Option<usize>,
  /// Further owners this value may be: a join of alternatives that returned
  /// different places keeps every one of them, and each action on `place`
  /// is performed on these too.
  also: Vec<usize>,
  loan_root: Option<usize>,
  /// A unique value of a plain-data type (an inductive type whose
  /// constructors all have default contracts). It may enter a shared
  /// position as its last use: the freeze moves its owner, so the value is
  /// never used again as unique or otherwise. Never set for functions or
  /// abstract types.
  freezable: bool,
}
impl Value {
  fn shared(typ: Term) -> Self {
    Self {
      typ,
      owned: Owned::Shared,
      origins: vec![],
      duplicable: true,
      place: None,
      also: vec![],
      loan_root: None,
      freezable: false,
    }
  }
  /// Every owner this value may be: its place, then the joined ones.
  fn places(&self) -> Vec<usize> {
    self.place.iter().copied().chain(self.also.iter().copied()).collect()
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
  /// Binders whose written `1`/`&` contract was not enforced because their
  /// type crosses the usage axis (plain-data crossing), for the diagnostic.
  crossed: Vec<usize>,
  /// The plain-data decisions `crosses` has taken, by type head.
  plain_heads: Vec<(u64, bool)>,
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
  /// Each field is a view of the major, as a projection is: it keeps the
  /// major's origins and loan root and names the major's owner as its place,
  /// so consuming a field acts on the major and a field cannot outlive a
  /// move of the major. A field with a contract (unique or finite use) has
  /// no case rule.
  fn value(
    &self,
    j: usize,
    k: usize,
    domain: Term,
    field: BinderContract,
  ) -> Result<Value, Error> {
    match self {
      Self::Fields { fields, major } if k < fields[j] => {
        if field != BinderContract::default() {
          return Err(Error::Unsupported(
            "a case split on a constructor field with a contract",
          ));
        }
        Ok(Value {
          owned: if major.owned == Owned::Unique
            && field.value.owned == Owned::Unique
          {
            Owned::Unique
          } else {
            Owned::Shared
          },
          origins: major.origins.clone(),
          place: major.place,
          also: major.also.clone(),
          loan_root: major.loan_root,
          ..Value::shared(domain)
        })
      },
      _ => Ok(Value::shared(domain)),
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
        crossed: vec![],
        plain_heads: vec![],
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
    for id in v.places() {
      let b = self.binding_mut(id)?;
      b.owner = match v.owned {
        Owned::Unique => b.owner.move_out(id)?,
        Owned::Shared => b.owner.share(id)?,
      };
    }
    v.place = None;
    v.also = vec![];
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
    // A non-duplicable value cannot become shared, except a freezable unique
    // value, whose owner the freeze moves (its last use).
    let freeze = required.owned == Owned::Shared && !v.duplicable;
    if freeze && !(v.owned == Owned::Unique && v.freezable) {
      return Err(Error::Nonduplicable);
    }
    v.owned = if freeze { Owned::Unique } else { required.owned };
    v = self.materialize(v)?;
    v.owned = required.owned;
    v.duplicable |= freeze;
    v.freezable &= !freeze;
    if required.locality == Locality::Local {
      v.origins = union(&v.origins, &[destination]);
    }
    Ok(v)
  }
  fn invoke(&mut self, v: &Value) -> Result<(), Error> {
    if v.owned == Owned::Shared && !v.duplicable {
      return Err(Error::Nonduplicable);
    }
    for id in v.places() {
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
  fn is_scalar(&mut self, fuel: usize, typ: &Term) -> Result<bool, Error> {
    if self.program.scalar_types.is_empty() {
      return Ok(false);
    }
    let typ = self.whnf(fuel, typ)?;
    match typ.as_ref() {
      Expr::Ref(i, _) if self.program.scalar_types.contains(i) => {
        let d = self.declaration(*i)?;
        Ok(
          d.kind == DeclKind::TypeConstructor
            && matches!(d.typ.as_ref(),
          Expr::Sort(u) if self.program.prop_sort != Some(*u)),
        )
      },
      _ => Ok(false),
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
  /// demand on a value of a crossing type (`crosses`): under R19 the callee
  /// receives a copy of an immediate that holds no resource; under
  /// plain-data crossing the usage of data carries no obligation. Passing
  /// it is one consumption. The caller's own reads still count, and a
  /// zero-use input still has zero demand.
  fn argument_grade(
    &mut self,
    fuel: usize,
    grade: Uses,
    input: Uses,
    domain: &Term,
  ) -> Result<Uses, Error> {
    if input != Uses::Erased && self.crosses(fuel, domain)? {
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
    // A field bound by a case split is a view of the matched value, as a
    // projection is: reading it needs that value's owner live, and consuming
    // it acts on that owner.
    for matched in b.value.places() {
      if !self.binding(matched)?.owner.live {
        return Err(Error::Moved(matched));
      }
    }
    let typ = self.shift(
      fuel,
      &b.value.typ,
      index.checked_add(1).ok_or(Error::Budget)?,
      0,
    )?;
    Ok(Value {
      typ,
      place: Some(b.value.place.unwrap_or(id)),
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
        v.freezable = false;
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
    // Copy the payload; scalar ownership never aliases or moves a heap owner.
    let value = if self.is_scalar(fuel, &value.typ)? {
      Value {
        owned: Owned::Unique,
        duplicable: true,
        freezable: false,
        place: None,
        also: vec![],
        ..value
      }
    } else {
      value
    };
    match expected {
      None => Ok(value),
      Some((typ, contract)) => {
        self.require_type(fuel, &value.typ, &typ)?;
        self.consume_as(contract, destination, value)
      },
    }
  }
  #[allow(clippy::too_many_arguments)]
  fn ordinary_call(
    &mut self,
    fuel: usize,
    ctx: &Context,
    f: &Term,
    a: &Term,
    destination: usize,
    grade: Uses,
    fresh: bool,
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
    let owned = if fresh { Owned::Unique } else { result.owned };
    let duplicable = owned == Owned::Shared || self.is_shareable(fuel, &typ)?;
    let freezable = if owned == Owned::Unique && !duplicable {
      self.plain_data(fuel, &typ)?
    } else {
      false
    };
    Ok(Value { owned, origins, duplicable, freezable, ..Value::shared(typ) })
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
  /// The head constant of a type's final codomain.
  fn result_head(
    &mut self,
    fuel: usize,
    typ: &Term,
  ) -> Result<Option<u64>, Error> {
    let fuel = fuel.checked_sub(1).ok_or(Error::Budget)?;
    let reduced = self.whnf(fuel, typ)?;
    if let Expr::All(_, _, _, body) = reduced.as_ref() {
      return self.result_head(fuel, body);
    }
    let (head, _) = self.split_app(fuel, &reduced)?;
    Ok(match head.as_ref() {
      Expr::Ref(i, _) => Some(*i),
      _ => None,
    })
  }
  /// Whether a type is plain data: an inductive type of an addressed block
  /// whose constructors all carry only default contracts, so that a value of
  /// it holds nothing finite-use or unique. Functions, type parameters and
  /// types without a known block are not.
  fn plain_data(&mut self, fuel: usize, typ: &Term) -> Result<bool, Error> {
    let reduced = self.whnf(fuel, typ)?;
    let (head, _) = self.split_app(fuel, &reduced)?;
    let Expr::Ref(t, _) = head.as_ref() else { return Ok(false) };
    let Some(d) =
      usize::try_from(*t).ok().and_then(|i| self.program.declarations.get(i))
    else {
      return Ok(false);
    };
    if d.kind != DeclKind::TypeConstructor {
      return Ok(false);
    }
    let index = usize::try_from(*t).unwrap_or(usize::MAX);
    let Some(group) =
      self.program.groups.iter().find(|g| g.contains(&index)).cloned()
    else {
      return Ok(false);
    };
    for c in group {
      let Some(cd) = self.program.declarations.get(c).cloned() else {
        return Ok(false);
      };
      if cd.kind == DeclKind::Constructor {
        // The effective interface: an admitted interface replaces the
        // constructor's declared contracts.
        let typ = self.interface_type(c as u64)?;
        if self.result_head(fuel, &typ)? == Some(*t)
          && !self.plain(fuel, &typ)?
        {
          return Ok(false);
        }
      }
    }
    Ok(true)
  }
  /// Whether a value of `typ` crosses the usage axis: a written `1`/`&`
  /// contract on it is not enforced, and passing it to a many-use callee or
  /// capturing it in a reusable closure is one consumption. Without
  /// plain-data crossing (`Program::crossing`) and opt-outs this is exactly
  /// a profile-shareable type (R19). With plain-data crossing (the plain
  /// profile), a type crosses when it is plain data (`plain_data`, on
  /// effective interfaces) or profile-shareable, unless the profile opts it
  /// out (`linear NAME`). Arrows, type variables and types without a visible
  /// block do not cross.
  fn crosses(&mut self, fuel: usize, typ: &Term) -> Result<bool, Error> {
    if !self.program.crossing && self.program.linear_types.is_empty() {
      return self.is_shareable(fuel, typ);
    }
    let reduced = self.whnf(fuel, typ)?;
    let (head, _) = self.split_app(fuel, &reduced)?;
    if let Expr::Ref(t, _) = head.as_ref()
      && self.program.linear_types.contains(t)
    {
      return Ok(false);
    }
    if self.is_shareable(fuel, typ)? {
      return Ok(true);
    }
    if !self.program.crossing {
      return Ok(false);
    }
    // Whether a type is plain data depends only on its head constant: decide
    // it once per head (`State::plain_heads`), so that crossing costs no more
    // than a reduction per argument.
    let Expr::Ref(t, _) = head.as_ref() else { return Ok(false) };
    if let Some((_, known)) =
      self.state.plain_heads.iter().find(|(head, _)| head == t)
    {
      return Ok(*known);
    }
    let t = *t;
    let known = self.plain_data(fuel, typ)?;
    self.state.plain_heads.push((t, known));
    Ok(known)
  }
  /// Check a binder's usage contract when its scope finishes. Under
  /// plain-data crossing, a written `1`/`&` contract on a binder whose type
  /// crosses (`crosses`) is not enforced (neither bound, as in OxCaml, which
  /// has no relevance axis), and the binder is recorded in `State::crossed`
  /// for the diagnostic. `0` (erased) is always enforced.
  fn validate_binder(&mut self, fuel: usize, id: usize) -> Result<(), Error> {
    let b = self.binding(id)?.clone();
    if self.program.crossing
      && (b.contract.uses == Uses::Linear || b.contract.uses == Uses::Affine)
      && self.crosses(fuel, &b.value.typ)?
    {
      self.state.crossed.push(id);
      return Ok(());
    }
    self.validate_usage(id)
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
  /// How variable `index` occurs in the alternative argument `e` of a case,
  /// after entering at most `strip` of its leading lambdas (the binders the
  /// case itself supplies: constructor fields, hypotheses, further
  /// arguments).
  fn alternative_occurrence(
    &mut self,
    fuel: usize,
    e: &Term,
    index: u64,
    strip: usize,
  ) -> Result<Occurrence, Error> {
    let mut body = e.clone();
    let mut index = index;
    let mut remaining = strip;
    for _ in 0..strip {
      let unshared = self.unshare(fuel, &body)?;
      match unshared.as_ref() {
        Expr::Lam(_, t, b) => {
          if self.occurs(fuel, t, index)? {
            return Ok(Occurrence::Other);
          }
          body = b.clone();
          index += 1;
          remaining -= 1;
        },
        _ => break,
      }
    }
    if !self.occurs(fuel, &body, index)? {
      return Ok(Occurrence::Absent);
    }
    let (head, args) = self.split_app(fuel, &body)?;
    let head = self.unshare(fuel, &head)?;
    match head.as_ref() {
      Expr::Var(i) if *i == index => {
        for arg in &args {
          if self.occurs(fuel, arg, index)? {
            return Ok(Occurrence::Other);
          }
        }
        // A bare minor still receives the case-supplied fields/hypotheses/extras.
        Ok(Occurrence::Applied(args.len() + remaining))
      },
      _ => Ok(Occurrence::Other),
    }
  }
  /// The shape of a profile-bound case definition (`casesOn`, a matcher): an
  /// unannotated definition whose body is a lambda telescope around a full
  /// application of a case recursor whose minors ignore their induction
  /// hypotheses, or of another bound case definition. A parameter is by need
  /// when every occurrence of it lies in an alternative of that application
  /// (a minor premise, or a by-need position of the inner definition), after
  /// at most the binders the case enters there, as the head of an
  /// application whose arguments do not mention it; occurrences in different
  /// alternatives are allowed (at most one alternative runs). A parameter
  /// occurring anywhere else (a discriminant, under a closure, twice in one
  /// alternative), or nowhere, is strict. A definition that is not bound, or
  /// not of this shape, or wraps a choice, is an ordinary function.
  fn case_definition(
    &mut self,
    fuel: usize,
    depth: usize,
    index: u64,
  ) -> Result<Option<CaseShape>, Error> {
    let Some(depth) = depth.checked_sub(1) else { return Ok(None) };
    if !self.program.cases
      || !self.program.case_definitions.contains(&index)
      || self.program.choices.contains(&index)
    {
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
    // The alternative positions of the application, with the binders
    // entered there.
    let mut alternatives: Vec<Option<usize>> = vec![None; args.len()];
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
        alternatives[info.params + info.motives + j] =
          Some(info.binders[j] + (args.len() - info.arity()));
      }
    } else {
      let Some(shape) = self.case_definition(fuel, depth, *target)? else {
        return Ok(None);
      };
      if args.len() < shape.arity {
        return Ok(None);
      }
      for (i, by_need) in shape.by_need.iter().enumerate() {
        alternatives[i] = by_need.map(|k| k + (args.len() - shape.arity));
      }
    }
    let mut by_need = vec![];
    for p in 0..params {
      let index = (params - 1 - p) as u64;
      let mut applied: Option<usize> = None;
      let mut lazy = true;
      for (j, arg) in args.iter().enumerate() {
        match alternatives[j] {
          None => {
            if self.occurs(fuel, arg, index)? {
              lazy = false;
            }
          },
          Some(strip) => {
            match self.alternative_occurrence(fuel, arg, index, strip)? {
              Occurrence::Absent => {},
              Occurrence::Applied(k) => {
                applied = Some(applied.map_or(k, |a| a.min(k)));
              },
              Occurrence::Other => lazy = false,
            }
          },
        }
      }
      by_need.push(if lazy { applied } else { None });
    }
    Ok(Some(CaseShape { arity: params, by_need }))
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
  /// Whether `e` has no loose variable at or above `depth`.
  fn closed_at(
    &mut self,
    fuel: usize,
    depth: u64,
    e: &Term,
  ) -> Result<bool, Error> {
    let fuel = self.tick(fuel)?;
    Ok(match e.as_ref() {
      Expr::Var(i) => *i < depth,
      Expr::Share(i) => {
        let expanded = self.expansion(*i)?;
        self.closed_at(fuel, depth, &expanded)?
      },
      Expr::Rec(..) => false,
      Expr::App(f, a) => {
        let f = self.closed_at(fuel, depth, f)?;
        let a = self.closed_at(fuel, depth, a)?;
        f && a
      },
      Expr::Lam(_, t, b) | Expr::All(_, _, t, b) => {
        let t = self.closed_at(fuel, depth, t)?;
        let b = self.closed_at(fuel, depth + 1, b)?;
        t && b
      },
      Expr::Let(_, t, v, b) => {
        let t = self.closed_at(fuel, depth, t)?;
        let v = self.closed_at(fuel, depth, v)?;
        let b = self.closed_at(fuel, depth + 1, b)?;
        t && v && b
      },
      Expr::Prj(_, _, v) => self.closed_at(fuel, depth, v)?,
      _ => true,
    })
  }
  /// The parameter count of a constructor (`Program::constructors`; `0` when
  /// the program records none).
  fn constructor_params(&self, index: u64) -> usize {
    self
      .program
      .constructors
      .iter()
      .find(|(i, _)| *i == index)
      .map_or(0, |(_, params)| *params)
  }
  /// The arguments of `head` applied to `args` that are run-time values: not
  /// a constructor's parameters, and not of a type-former or proposition
  /// domain (types and proofs are erased).
  fn runtime_arguments(
    &mut self,
    fuel: usize,
    ctx: &Context,
    head: &Term,
    args: &[Term],
  ) -> Result<Vec<Term>, Error> {
    let params = match head.as_ref() {
      Expr::Ref(i, _) => {
        if self.declaration(*i)?.kind == DeclKind::Constructor {
          self.constructor_params(*i)
        } else {
          0
        }
      },
      _ => 0,
    };
    let mut typ = self.type_of(fuel, ctx, head)?;
    let mut result = vec![];
    for (k, arg) in args.iter().enumerate() {
      let (_, _, domain, codomain) = self.arrow(fuel, &typ)?;
      if k >= params
        && !self.type_former(fuel, 16, &domain)?
        && !self.is_proposition(fuel, ctx, &domain)?
      {
        result.push(arg.clone());
      }
      typ = self.substitute(fuel, &codomain, arg, 0)?;
    }
    Ok(result)
  }
  /// Whether evaluating `e` depends on a run-time local: a variable of the
  /// context whose type is neither a type former nor a proposition, reached
  /// only through run-time positions (a projected value, the head of an
  /// application, or a run-time argument, see `runtime_arguments`). Anything
  /// else (a constant, a literal, a type, a binder form) conservatively does
  /// not.
  fn runtime_local(
    &mut self,
    fuel: usize,
    ctx: &Context,
    e: &Term,
  ) -> Result<bool, Error> {
    let fuel = self.tick(fuel)?;
    let e = self.unshare(fuel, e)?;
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
        let typ =
          self.shift(fuel, &typ, i.checked_add(1).ok_or(Error::Budget)?, 0)?;
        if self.type_former(fuel, 16, &typ)? {
          return Ok(false);
        }
        Ok(!self.is_proposition(fuel, ctx, &typ)?)
      },
      Expr::Prj(_, _, value) => self.runtime_local(fuel, ctx, value),
      Expr::App(..) => {
        let (head, args) = self.split_app(fuel, &e)?;
        if self.runtime_local(fuel, ctx, &head)? {
          return Ok(true);
        }
        for arg in self.runtime_arguments(fuel, ctx, &head, &args)? {
          if self.runtime_local(fuel, ctx, &arg)? {
            return Ok(true);
          }
        }
        Ok(false)
      },
      _ => Ok(false),
    }
  }
  /// Whether a constructor's type may have it as its only constructor, as
  /// far as the program's addressed blocks show (a type without a known
  /// block counts as one).
  fn single_constructor(
    &mut self,
    fuel: usize,
    index: u64,
  ) -> Result<bool, Error> {
    let d = self.declaration(index)?.clone();
    let Some(t) = self.result_head(fuel, &d.typ)? else { return Ok(true) };
    let ti = usize::try_from(t).unwrap_or(usize::MAX);
    let Some(group) =
      self.program.groups.iter().find(|g| g.contains(&ti)).cloned()
    else {
      return Ok(true);
    };
    let mut count = 0usize;
    for c in group {
      let Some(cd) = self.program.declarations.get(c).cloned() else {
        return Ok(true);
      };
      if cd.kind == DeclKind::Constructor
        && self.result_head(fuel, &cd.typ)? == Some(t)
      {
        count += 1;
      }
    }
    Ok(count <= 1)
  }
  /// Whether a full application of constructor `index` is a fresh object,
  /// unique at every evaluation:
  /// - a constructor with no run-time field (only parameters, types and
  ///   proofs) is an immediate: it has no heap cell, so it is unique (Lean
  ///   and Compilatr represent it as a scalar; named assumption);
  /// - a constructor with exactly one run-time field whose type may have
  ///   only this constructor is represented by that field (Lean's trivial
  ///   structures, Compilatr's unboxed single-field structures): it
  ///   allocates nothing, so it is not fresh;
  /// - otherwise it is fresh only when a run-time field depends on a
  ///   run-time local (`runtime_local`). A closed construction (`[1, 2, 3]`,
  ///   `.node .nil .nil`) is static data that a consumer may materialize
  ///   once (closed-term extraction), like a literal: it is not fresh.
  ///
  /// Anything the bounded inference cannot type is not fresh.
  fn fresh_construction(
    &mut self,
    fuel: usize,
    ctx: &Context,
    head: &Term,
    index: u64,
    args: &[Term],
  ) -> Result<bool, Error> {
    let before = self.state.bindings.clone();
    let result: Result<bool, Error> = (|| {
      let fields = self.runtime_arguments(fuel, ctx, head, args)?;
      if fields.is_empty() {
        return Ok(true);
      }
      if fields.len() == 1 && self.single_constructor(fuel, index)? {
        return Ok(false);
      }
      for field in &fields {
        if self.runtime_local(fuel, ctx, field)? {
          return Ok(true);
        }
      }
      Ok(false)
    })();
    self.state.bindings = before;
    match result {
      Ok(fresh) => Ok(fresh),
      Err(Error::Budget) => Err(Error::Budget),
      Err(_) => Ok(false),
    }
  }
  /// Whether a strict argument may be substituted into a lambda telescope
  /// because evaluating it has no effect: a variable (a place; its reads are
  /// charged where it is used), a sort or `∀`, a constant that is not a
  /// nullary constructor (no allocation), a closed lambda (it captures and
  /// moves nothing), or a type or proof (erased computation). Literals,
  /// constructor applications, nullary constructors (values `analyze`
  /// classifies as fresh or static) and every other computation are not.
  fn substitutable(
    &mut self,
    fuel: usize,
    ctx: &Context,
    arg: &Term,
    domain: &Term,
  ) -> Result<bool, Error> {
    let unshared = self.unshare(fuel, arg)?;
    match unshared.as_ref() {
      Expr::Var(_) | Expr::Sort(_) | Expr::All(..) => Ok(true),
      Expr::Ref(i, _) => {
        let d = self.declaration(*i)?.clone();
        if d.kind == DeclKind::Constructor {
          Ok(self.arity(fuel, &d.typ)? != 0)
        } else {
          Ok(true)
        }
      },
      Expr::Lam(..) => {
        if self.closed_at(fuel, 0, &unshared)? {
          return Ok(true);
        }
        if self.type_former(fuel, 16, domain)? {
          return Ok(true);
        }
        self.is_proposition(fuel, ctx, domain)
      },
      _ => {
        if self.type_former(fuel, 16, domain)? {
          return Ok(true);
        }
        self.is_proposition(fuel, ctx, domain)
      },
    }
  }
  /// An alternative proper is a lambda, not a computation returning one.
  /// A lambda application is allowed only at a zero-argument minor: there
  /// it is the executed alternative, such as an inner `h_i ()`. The count
  /// comes from `case_definition`, not from the argument's spelling.
  fn alternative_argument(
    &mut self,
    fuel: usize,
    ctx: &Context,
    applied: usize,
    arg: &Term,
    domain: &Term,
  ) -> Result<bool, Error> {
    let unshared = self.unshare(fuel, arg)?;
    match unshared.as_ref() {
      Expr::Lam(..) => Ok(true),
      Expr::App(..) => {
        let (head, _) = self.split_app(fuel, &unshared)?;
        let head = self.unshare(fuel, &head)?;
        if matches!(head.as_ref(), Expr::Lam(..)) && applied == 0 {
          Ok(true)
        } else {
          self.substitutable(fuel, ctx, arg, domain)
        }
      },
      _ => self.substitutable(fuel, ctx, arg, domain),
    }
  }
  /// Extra arguments of a case or choice must be evaluation-free so their
  /// position before or after inspecting the major cannot change effects.
  fn require_value(
    &mut self,
    fuel: usize,
    ctx: &Context,
    arg: &Term,
    domain: &Term,
  ) -> Result<(), Error> {
    if self.substitutable(fuel, ctx, arg, domain)? {
      Ok(())
    } else {
      Err(Error::Unsupported(
        "an over-applied case or choice takes an argument that is not a value",
      ))
    }
  }
  /// Apply a lambda telescope to arguments, as `let`s. Arguments are strict:
  /// an argument of a binder with the default contract is substituted only
  /// when evaluating it has no effect (`substitutable`); any other argument
  /// is bound by a `let` carrying the binder's own contract, so it is
  /// analysed exactly once, before the body, whether or not the binder
  /// occurs, as a call evaluates it. The only exception are the by-need
  /// positions of a bound case definition (`by_need`, from
  /// `case_definition`): eligible alternatives (`alternative_argument`) are
  /// substituted, so each is evaluated in its branch. Arguments beyond the
  /// telescope are applied to the body.
  fn bind_arguments(
    &mut self,
    fuel: usize,
    ctx: &Context,
    telescope: &Term,
    args: &[Term],
    by_need: &[Option<usize>],
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
      let substitutable = match by_need.get(rest).copied().flatten() {
        Some(applied) => {
          self.alternative_argument(fuel, &inner, applied, &arg, domain)?
        },
        None => self.substitutable(fuel, &inner, &arg, domain)?,
      };
      if *c == BinderContract::default() && substitutable {
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
  /// A join keeps every owner either alternative may be: an action on the
  /// joined value is performed on all of them (conservatively, since only
  /// one is the actual value).
  fn join_value(a: Value, b: Value) -> Value {
    let places = union(&a.places(), &b.places());
    Value {
      place: places.first().copied(),
      also: places.get(1..).map_or(vec![], <[usize]>::to_vec),
      typ: a.typ,
      owned: if a.owned == Owned::Unique && b.owned == Owned::Unique {
        Owned::Unique
      } else {
        Owned::Shared
      },
      origins: union(&a.origins, &b.origins),
      duplicable: a.duplicable && b.duplicable,
      freezable: a.freezable && b.freezable,
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
        let value = supply.value(j, k, domain, field)?;
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
          self.validate_binder(fuel, id)?;
        }
      }
      let mut output = output;
      let places: Vec<usize> =
        output.places().into_iter().filter(|p| *p < count).collect();
      output.place = places.first().copied();
      output.also = places.get(1..).map_or(vec![], <[usize]>::to_vec);
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
      let (_, _, domain, codomain) = self.arrow(fuel, &output_type)?;
      self.require_value(fuel, ctx, x, &domain)?;
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
  /// The body an annotated recursive definition is checked through: the
  /// right-hand side of its unfolding equation `∀ xs, f xs = rhs`,
  /// abstracted over the equation's binders with the definition's own input
  /// contracts. The statement must be an equality whose left side is the
  /// definition applied to exactly those binders, in order.
  fn equation_body(
    &mut self,
    fuel: usize,
    index: u64,
    equation: u64,
  ) -> Result<Term, Error> {
    let eq = self.program.eq_type.ok_or(Error::Unsupported(
      "the equality type is absent from the profile",
    ))?;
    let d = self.declaration(index)?.clone();
    let t = self.declaration(equation)?.clone();
    if t.kind != DeclKind::Theorem {
      return Err(Error::Unsupported(
        "an unfolding equation must be a theorem",
      ));
    }
    let mut statement = t.typ;
    let mut typ = d.typ;
    let mut binders = vec![];
    loop {
      let reduced = self.whnf(fuel, &statement)?;
      match reduced.as_ref() {
        Expr::All(_, _, domain, body) => {
          let (input, _, _, codomain) = self.arrow(fuel, &typ)?;
          binders.push((input, domain.clone()));
          statement = body.clone();
          typ = codomain;
        },
        _ => {
          statement = reduced;
          break;
        },
      }
    }
    let (head, args) = self.split_app(fuel, &statement)?;
    let not_equality =
      Error::Unsupported("an unfolding equation must state an equality");
    let (lhs, rhs) = match (head.as_ref(), args.as_slice()) {
      (Expr::Ref(e, _), [_, lhs, rhs]) if *e == eq => {
        (lhs.clone(), rhs.clone())
      },
      _ => return Err(not_equality),
    };
    let (function, fargs) = self.split_app(fuel, &lhs)?;
    let mut unfolds = matches!(function.as_ref(), Expr::Ref(f, _) if *f == index)
      && fargs.len() == binders.len();
    if unfolds {
      let mut k = binders.len();
      for arg in &fargs {
        k -= 1;
        let arg = self.unshare(fuel, arg)?;
        unfolds &= matches!(arg.as_ref(), Expr::Var(i) if *i == k as u64);
      }
    }
    if !unfolds {
      return Err(Error::Unsupported(
        "an unfolding equation must unfold its definition",
      ));
    }
    let mut body = rhs;
    for (input, domain) in binders.into_iter().rev() {
      body = Expr::lam_contract(input, domain, body);
    }
    Ok(body)
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
    // Every minor must ignore its induction hypotheses syntactically: an
    // occurrence anywhere (a dead binder, an erased argument, a type) is a
    // use for a consumer that computes it.
    for j in 0..info.minors {
      let minor = args[info.params + info.motives + j].clone();
      if !self.ignores_hypotheses(
        fuel,
        &minor,
        info.fields[j],
        info.binders[j],
      )? {
        return Err(Error::Unsupported(
          "a case split uses an induction hypothesis",
        ));
      }
    }
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
      let (_, _, domain, codomain) = self.arrow(fuel, &output_type)?;
      self.require_value(fuel, ctx, x, &domain)?;
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
        let d = self.declaration(*i)?.clone();
        let typ = self.interface_type(*i)?;
        // A nullary constructor is an immediate (no heap cell): unique.
        if d.kind == DeclKind::Constructor && self.arity(fuel, &d.typ)? == 0 {
          let duplicable = self.is_shareable(fuel, &typ)?;
          let freezable =
            if duplicable { false } else { self.plain_data(fuel, &typ)? };
          Value { duplicable, freezable, ..Value::fresh(typ) }
        } else {
          Value::shared(typ)
        }
      },
      Expr::Rec(..) => {
        return Err(Error::Unsupported("unresolved recursive reference"));
      },
      Expr::Sort(_) | Expr::All(..) => Value::fresh(Expr::sort(0)),
      // A literal is static data (a consumer may keep one persistent object
      // for it): shared, never fresh.
      Expr::Nat(_) => {
        Value::shared(Self::literal_type(&self.program.nat_type)?)
      },
      Expr::Str(_) => {
        Value::shared(Self::literal_type(&self.program.string_type)?)
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
          || self.is_shareable(fuel, domain)?
          || self.is_scalar(fuel, domain)?;
        let freezable = if input.value.owned == Owned::Unique && !duplicable {
          self.plain_data(fuel, domain)?
        } else {
          false
        };
        let parameter = self.push(
          *input,
          Value {
            owned: input.value.owned,
            duplicable,
            freezable,
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
        self.validate_binder(fuel, parameter)?;
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
            // copied into the closure, as at a call boundary: its finite use
            // does not make the closure one-shot (the linearity of an
            // immediate has no run-time meaning), nor does its uniqueness
            // when the body only reads it. Under plain-data crossing the usage
            // axis follows `crosses` (any plain data); the ownership axis
            // below stays with the shareable types.
            let immediate = self.is_shareable(fuel, &old.value.typ)?;
            let crossing = if self.program.crossing
              || !self.program.linear_types.is_empty()
            {
              self.crosses(fuel, &old.value.typ)?
            } else {
              immediate
            };
            if (old.contract.uses != Uses::Many && !crossing)
              || !old.value.duplicable
            {
              duplicable = false;
            }
            // A capture the body moves (a unique transfer, a freeze or a
            // unique invocation) would be moved again by a second call: the
            // closure is one-shot, immediate or not.
            if !owner.live {
              duplicable = false;
            }
            if old.owner.unique && !self.is_scalar(fuel, &old.value.typ)? {
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
            if !self.is_shareable(fuel, typ)? && !v.duplicable && !v.freezable {
              return Err(Error::Nonduplicable);
            }
            let owner_place = v.place.ok_or(Error::InvalidPlace)?;
            // A view of a joined value (several possible owners) has no
            // single root to suspend.
            if !v.also.is_empty() {
              return Err(Error::InvalidPlace);
            }
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
        self.validate_binder(fuel, id)?;
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
        v.freezable = false;
        v.typ = typ;
        if v.owned != Owned::Unique || field.contract.owned != Owned::Unique {
          v.owned = Owned::Shared;
        }
        v
      },
      Expr::App(f, a) => {
        let (head, args) = self.split_app(fuel, e)?;
        // A fully applied constructor that allocates (`fresh_construction`)
        // is a fresh value: unique, whatever its declared result contract
        // (named assumption: the consumer allocates it anew at each
        // evaluation).
        let fresh = match head.as_ref() {
          Expr::Ref(i, _) => {
            let d = self.declaration(*i)?.clone();
            d.kind == DeclKind::Constructor
              && args.len() == self.arity(fuel, &d.typ)?
              && self.fresh_construction(fuel, ctx, &head, *i, &args)?
          },
          _ => false,
        };
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
              Some(_) => self.ordinary_call(
                fuel,
                ctx,
                f,
                a,
                destination,
                grade,
                fresh,
              )?,
              None => match self.case_definition(fuel, 4, *i)? {
                Some(shape) if args.len() >= shape.arity => {
                  // A bound case definition is unfolded: its alternatives by
                  // need, every other argument strictly.
                  match self.declaration(*i)?.body.clone() {
                    Some(body) => {
                      let term = self.bind_arguments(
                        fuel,
                        ctx,
                        &body,
                        &args,
                        &shape.by_need,
                      )?;
                      self.analyze(
                        fuel,
                        ctx,
                        &term,
                        expected.clone(),
                        destination,
                        grade,
                      )?
                    },
                    None => self.ordinary_call(
                      fuel,
                      ctx,
                      f,
                      a,
                      destination,
                      grade,
                      fresh,
                    )?,
                  }
                },
                _ => self.ordinary_call(
                  fuel,
                  ctx,
                  f,
                  a,
                  destination,
                  grade,
                  fresh,
                )?,
              },
            }
          },
          Expr::Lam(..) if self.program.cases => {
            // A beta-redex binds its arguments strictly.
            let term = self.bind_arguments(fuel, ctx, &head, &args, &[])?;
            self.analyze(
              fuel,
              ctx,
              &term,
              expected.clone(),
              destination,
              grade,
            )?
          },
          _ => {
            self.ordinary_call(fuel, ctx, f, a, destination, grade, fresh)?
          },
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
  check_definition_crossed(program, index, limits).map(|_crossed| ())
}

/// Check a definition; on success, the binders (in the order their scopes
/// finished; a header binder's id is its position) whose written `1`/`&`
/// contract plain-data crossing did not enforce (`validate_binder`).
pub fn check_definition_crossed(
  program: &Program,
  index: usize,
  limits: Limits,
) -> Result<Vec<usize>, Error> {
  let declaration =
    program.declarations.get(index).ok_or(Error::BadReference(index as u64))?;
  let mut checker = Checker::new(program, limits);
  let body = match program.equations.iter().find(|(d, _)| *d == index as u64) {
    Some((_, equation)) => {
      checker.equation_body(limits.depth, index as u64, *equation)?
    },
    None => declaration
      .body
      .clone()
      .ok_or(Error::Unsupported("definition has no body"))?,
  };
  let scope = checker.scope(0)?;
  checker.analyze(
    limits.depth,
    &Context { scope, vars: vec![] },
    &body,
    Some((declaration.typ.clone(), ValueContract::shared())),
    scope,
    Uses::Linear,
  )?;
  Ok(checker.state.crossed)
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

/// The reverse dependency edges of a program (a declaration to the
/// declarations that refer to it, and every member of a mutual block to every
/// other), with the declarations that carry a resource contract themselves.
#[allow(clippy::type_complexity)]
pub fn dependency_graph(
  program: &Program,
  limits: Limits,
) -> Result<(Vec<Vec<usize>>, Vec<bool>), Error> {
  let size = program.declarations.len();
  let mut reverse = vec![vec![]; size];
  let mut marked = vec![false; size];
  for (i, d) in program.declarations.iter().enumerate() {
    let mut checker = Checker::new(program, limits);
    let scan = checker.scan(limits.depth, &d.typ)?;
    let scan = match &d.body {
      None => scan,
      Some(body) => scan.merge(checker.scan(limits.depth, body)?),
    };
    if scan.annotated {
      marked[i] = true;
    }
    for dependency in scan.dependencies {
      reverse
        .get_mut(dependency)
        .ok_or(Error::BadReference(dependency as u64))?
        .push(i);
    }
  }
  // Effective interfaces must seed relevance even for plain declarations.
  let overlays = program
    .interfaces
    .iter()
    .map(|(i, e)| (*i as usize, e.clone()))
    .collect::<Vec<_>>();
  for (i, expression) in program.auxiliary.iter().chain(overlays.iter()) {
    if *i >= size {
      return Err(Error::BadReference(*i as u64));
    }
    let mut checker = Checker::new(program, limits);
    let scan = checker.scan(limits.depth, expression)?;
    if scan.annotated {
      marked[*i] = true;
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
    if f.contract != ValueContract::shared() {
      *m = true;
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
  Ok((reverse, marked))
}

/// Every declaration that depends, through `reverse`, on a marked one.
pub fn propagate(reverse: &[Vec<usize>], mut marked: Vec<bool>) -> Vec<bool> {
  let mut queue: Vec<usize> =
    (0..marked.len()).filter(|i| marked[*i]).collect();
  let mut cursor = 0;
  while cursor < queue.len() {
    let i = queue[cursor];
    cursor += 1;
    for dependent in reverse.get(i).map_or(&[][..], Vec::as_slice) {
      if marked.get(*dependent) == Some(&false) {
        marked[*dependent] = true;
        queue.push(*dependent);
      }
    }
  }
  marked
}

/// Dependencies propagate resource relevance to callers and to every member
/// of a mutually addressed block. Only wholly ordinary components bypass the
/// resource analysis; erased typechecking is still required for them.
pub fn relevance(
  program: &Program,
  limits: Limits,
) -> Result<Vec<bool>, Error> {
  let (reverse, marked) = dependency_graph(program, limits)?;
  Ok(propagate(&reverse, marked))
}

/// The declarations that depend on an axiom outside the standard three
/// (`Program::axioms`).
pub fn tainted(
  program: &Program,
  reverse: &[Vec<usize>],
) -> Result<Vec<bool>, Error> {
  let mut seeds = vec![false; program.declarations.len()];
  for index in &program.axioms {
    let i = usize::try_from(*index).unwrap_or(usize::MAX);
    *seeds.get_mut(i).ok_or(Error::BadReference(*index))? = true;
  }
  Ok(propagate(reverse, seeds))
}

#[derive(Clone, Debug, Default)]
pub struct Policy {
  pub assumptions: Vec<usize>,
  pub shareable_types: Vec<usize>,
  pub scalar_types: Vec<usize>,
  pub choices: Vec<usize>,
  /// The profile admits case splits, bound case definitions and
  /// beta-redexes.
  pub cases: bool,
  /// Case definitions (`casesOn`, matchers) bound by the profile.
  pub case_definitions: Vec<usize>,
  /// Unfolding equations `(definition, theorem)` bound by the profile.
  pub equations: Vec<(usize, usize)>,
  /// The profile admits usage crossing on plain data.
  pub crossing: bool,
  /// Types the profile opts out of usage crossing.
  pub linear_types: Vec<usize>,
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
  admit_program_crossed(program, policy, limits).map(|_crossed| ())
}

/// Admit a program; on success, the `(declaration, binder)` pairs whose
/// written `1`/`&` contract plain-data crossing did not enforce
/// (`check_definition_crossed`), for the compiler's diagnostic.
pub fn admit_program_crossed(
  program: &Program,
  policy: &Policy,
  limits: Limits,
) -> Result<Vec<(usize, usize)>, AdmissionError> {
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
  for index in &program.case_definitions {
    let index = usize::try_from(*index).unwrap_or(usize::MAX);
    if !policy.case_definitions.contains(&index) {
      return Err(AdmissionError {
        declaration: Some(index),
        error: Error::Unsupported(
          "case definition is absent from the bound profile",
        ),
      });
    }
  }
  for (definition, equation) in &program.equations {
    let pair = (
      usize::try_from(*definition).unwrap_or(usize::MAX),
      usize::try_from(*equation).unwrap_or(usize::MAX),
    );
    if !policy.equations.contains(&pair) {
      return Err(AdmissionError {
        declaration: Some(pair.0),
        error: Error::Unsupported(
          "unfolding equation is absent from the bound profile",
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
  for index in &program.scalar_types {
    let index = usize::try_from(*index).map_err(|_| AdmissionError {
      declaration: None,
      error: Error::Budget,
    })?;
    if !policy.scalar_types.contains(&index) {
      return Err(AdmissionError {
        declaration: Some(index),
        error: Error::Unsupported(
          "scalar representation is absent from the bound profile",
        ),
      });
    }
  }
  if program.crossing && !policy.crossing {
    return Err(AdmissionError {
      declaration: None,
      error: Error::Unsupported(
        "plain-data crossing is absent from the bound profile",
      ),
    });
  }
  // Opting a type out of crossing only adds checking; every opt-out the
  // profile binds must be in effect.
  for index in &policy.linear_types {
    if !program.linear_types.contains(&(*index as u64)) {
      return Err(AdmissionError {
        declaration: Some(*index),
        error: Error::Unsupported(
          "a linear type of the bound profile is not in effect",
        ),
      });
    }
  }
  let (reverse, seeds) = dependency_graph(program, limits)
    .map_err(|error| AdmissionError { declaration: None, error })?;
  let marked = propagate(&reverse, seeds);
  let tainted = tainted(program, &reverse)
    .map_err(|error| AdmissionError { declaration: None, error })?;
  let mut crossed = vec![];
  for (i, d) in program.declarations.iter().enumerate() {
    if marked[i] {
      let result = match d.kind {
        // An assumed definition's interface is admitted by the profile.
        DeclKind::Definition if policy.assumptions.contains(&i) => Ok(vec![]),
        // A definition checked through an unfolding equation relies on the
        // equation being true: its proof may use only the standard axioms.
        DeclKind::Definition => match program
          .equations
          .iter()
          .find(|(d, _)| usize::try_from(*d).ok() == Some(i))
        {
          Some((_, equation))
            if usize::try_from(*equation)
              .ok()
              .and_then(|t| tainted.get(t))
              .copied()
              .unwrap_or(true) =>
          {
            Err(Error::Unsupported(
              "an unfolding equation depends on an axiom other than propext, Quot.sound and Classical.choice",
            ))
          },
          _ => check_definition_crossed(program, i, limits),
        },
        DeclKind::Assumption => {
          if policy.assumptions.contains(&i) {
            Ok(vec![])
          } else {
            Err(Error::Unsupported(
              "external resource interface is absent from the bound profile",
            ))
          }
        },
        DeclKind::Constructor => {
          let mut checker = Checker::new(program, limits);
          checker
            .interface_type(i as u64)
            .and_then(|typ| {
              checker.check_constructor_type(limits.depth, &typ, false, false)
            })
            .map(|()| vec![])
        },
        DeclKind::TypeConstructor | DeclKind::Theorem => Ok(vec![]),
      };
      let binders = result
        .map_err(|error| AdmissionError { declaration: Some(i), error })?;
      crossed.extend(binders.into_iter().map(|binder| (i, binder)));
    }
  }
  Ok(crossed)
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
    p.case_definitions = vec![29];
    p
  }

  #[test]
  fn effective_interfaces_seed_relevance_and_constructor_checks() {
    let mut p = Program {
      declarations: vec![
        Declaration {
          typ: Expr::sort(0),
          body: None,
          kind: DeclKind::TypeConstructor,
        },
        Declaration {
          typ: unary(BinderContract::default(), ValueContract::shared()),
          body: None,
          kind: DeclKind::Assumption,
        },
        Declaration {
          typ: unary(BinderContract::default(), ValueContract::shared()),
          body: Some(Expr::lam_contract(
            BinderContract::default(),
            nat(),
            Expr::app(Expr::reference(1, vec![]), Expr::var(0)),
          )),
          kind: DeclKind::Definition,
        },
      ],
      interfaces: vec![(
        1,
        unary(b(Uses::Many, ValueContract::unique()), ValueContract::shared()),
      )],
      ..Program::default()
    };
    let policy = Policy { assumptions: vec![1], ..Policy::default() };
    assert_eq!(
      relevance(&p, Limits::default()).unwrap(),
      vec![false, true, true]
    );
    assert!(admit_program(&p, &policy, Limits::default()).is_err());
    p.declarations[2].typ =
      unary(b(Uses::Many, ValueContract::unique()), ValueContract::shared());
    p.declarations[2].body = Some(Expr::lam_contract(
      b(Uses::Many, ValueContract::unique()),
      nat(),
      Expr::app(Expr::reference(1, vec![]), Expr::var(0)),
    ));
    assert!(admit_program(&p, &policy, Limits::default()).is_ok());
    p.declarations.truncate(2);
    p.declarations[1].kind = DeclKind::Constructor;
    assert!(admit_program(&p, &policy, Limits::default()).is_err());
    p.interfaces[0].1 =
      unary(b(Uses::Many, ValueContract::unique()), ValueContract::unique());
    assert!(admit_program(&p, &policy, Limits::default()).is_ok());
    p.interfaces[0].1 =
      unary(BinderContract::default(), ValueContract::shared());
    assert!(admit_program(&p, &policy, Limits::default()).is_ok());
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
    // Review F1: case definitions must be bound by the profile.
    cases.case_definitions = vec![5];
    assert!(admit_program(&cases, &s, Limits::default()).is_err());
    s.case_definitions = vec![5];
    assert!(admit_program(&cases, &s, Limits::default()).is_ok());
  }

  #[test]
  fn case_split_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-cases.tsv");
    assert!(run_fixture_lines(&cases_program(), text) >= 21);
  }

  /// The case program extended with `Eq` and an unfolding equation for the
  /// definition under test (index 35): `∀ r, f r = r`. Mirrors
  /// `Tests.Resource.equationsProgram`.
  fn equations_program() -> Program {
    let mut p = cases_program();
    let many = b(Uses::Many, ValueContract::shared());
    let shared = ValueContract::shared();
    let all = |d: Term, c: Term| arr(many, shared, d, c);
    let res = || Expr::reference(11, vec![]);
    p.declarations.extend([
      // 33 Eq.
      Declaration {
        typ: all(
          Expr::sort(0),
          all(Expr::var(0), all(Expr::var(1), Expr::sort(1))),
        ),
        body: None,
        kind: DeclKind::TypeConstructor,
      },
      // 34 ∀ r, f r = r.
      Declaration {
        typ: all(
          res(),
          Expr::app(
            Expr::app(
              Expr::app(Expr::reference(33, vec![]), res()),
              Expr::app(Expr::reference(35, vec![]), Expr::var(0)),
            ),
            Expr::var(0),
          ),
        ),
        body: Some(Expr::lam_contract(
          many,
          res(),
          Expr::reference(30, vec![]),
        )),
        kind: DeclKind::Theorem,
      },
    ]);
    p.eq_type = Some(33);
    p.equations = vec![(35, 34)];
    p
  }

  /// The case program with `Box` as an addressed block, so that it is plain
  /// data. Mirrors `Tests.Resource.freezeProgram`.
  fn freeze_program() -> Program {
    let mut p = cases_program();
    p.groups = vec![vec![21, 22, 23]];
    p
  }

  #[test]
  fn freeze_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-freeze.tsv");
    assert!(run_fixture_lines(&freeze_program(), text) >= 15);
  }

  /// The mode program without shareable types, as under the strict profile
  /// (strict setting S2). Mirrors `Tests.Resource.noshareProgram`.
  fn noshare_program() -> Program {
    let mut p = modes_program();
    p.shareable_types.clear();
    p
  }

  #[test]
  fn noshare_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-noshare.tsv");
    assert!(run_fixture_lines(&noshare_program(), text) >= 5);
  }

  /// The case program with plain-data crossing, as under the plain profile
  /// (setting S6): `Box` and `Chain` are addressed blocks (plain data),
  /// `Chain` is opted out (`linear`), with a many and a unique `Box`
  /// consumer. Mirrors `Tests.Resource.plainProgram`.
  fn plain_program() -> Program {
    let mut p = cases_program();
    let boxt = || Expr::reference(21, vec![]);
    p.declarations.extend([
      // 33 useBox: Box → Nat.
      assumption(arr(
        b(Uses::Many, ValueContract::shared()),
        ValueContract::shared(),
        boxt(),
        nat(),
      )),
      // 34 keepBox: (! b : Box) → ! Box.
      assumption(arr(
        b(Uses::Many, ValueContract::unique()),
        ValueContract::unique(),
        boxt(),
        boxt(),
      )),
    ]);
    p.groups = vec![vec![21, 22, 23], vec![25, 26, 27]];
    p.crossing = true;
    p.linear_types = vec![25];
    p
  }

  #[test]
  fn plain_crossing_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-plain.tsv");
    assert!(run_fixture_lines(&plain_program(), text) >= 10);
  }

  /// The diagnostic: plain-data crossing reports the binders whose `1`/`&`
  /// contract it did not enforce (a header binder by its position).
  #[test]
  fn plain_crossing_reports_binders() {
    let linear = b(Uses::Linear, ValueContract::shared());
    let many = b(Uses::Many, ValueContract::shared());
    let boxt = || Expr::reference(21, vec![]);
    let run = |mut p: Program, input: BinderContract, body: Term| {
      let index = p.declarations.len();
      p.declarations.push(Declaration {
        typ: arr(input, ValueContract::shared(), boxt(), nat()),
        body: Some(Expr::lam_contract(input, boxt(), body)),
        kind: DeclKind::Definition,
      });
      check_definition_crossed(&p, index, Limits::default())
    };
    assert_eq!(run(plain_program(), linear, Expr::nat(0)), Ok(vec![0]));
    assert_eq!(run(plain_program(), many, Expr::nat(0)), Ok(vec![]));
    let use_box = Expr::app(Expr::reference(33, vec![]), Expr::var(0));
    let mut without = plain_program();
    without.crossing = false;
    assert!(run(without, linear, use_box).is_err());
  }

  /// The case program extended for strict binding (review F1): a unique
  /// consumer, a match-shaped definition that is not bound, and a
  /// matcher-shaped definition that is bound (35) next to an unbound copy
  /// (36). Mirrors `Tests.Resource.strictProgram`.
  fn strict_program() -> Program {
    let mut p = cases_program();
    let many = b(Uses::Many, ValueContract::shared());
    let shared = ValueContract::shared();
    let all = |d: Term, c: Term| arr(many, shared, d, c);
    let lam = |d: Term, body: Term| Expr::lam_contract(many, d, body);
    let res = || Expr::reference(11, vec![]);
    let boxt = || Expr::reference(21, vec![]);
    let app = Expr::app;
    let motive = || lam(boxt(), res());
    let matcher_type =
      all(boxt(), all(all(nat(), res()), all(all(res(), res()), res())));
    // fun t e f => Box.casesOn motive t (e 0) (fun r => f r)
    let matcher_body = lam(
      boxt(),
      lam(
        all(nat(), res()),
        lam(
          all(res(), res()),
          app(
            app(
              app(app(Expr::reference(29, vec![]), motive()), Expr::var(2)),
              app(Expr::var(1), Expr::nat(0)),
            ),
            lam(res(), app(Expr::var(1), Expr::var(0))),
          ),
        ),
      ),
    );
    p.declarations.extend([
      // 33 take: (1 ! r : Res) → Res.
      assumption(arr(
        b(Uses::Linear, ValueContract::unique()),
        shared,
        res(),
        res(),
      )),
      // 34 sel t e f := Box.rec motive e (fun _ => f) t, not bound.
      Declaration {
        typ: all(boxt(), all(res(), all(res(), res()))),
        body: Some(lam(
          boxt(),
          lam(
            res(),
            lam(
              res(),
              app(
                app(
                  app(app(Expr::reference(24, vec![]), motive()), Expr::var(1)),
                  lam(res(), Expr::var(1)),
                ),
                Expr::var(2),
              ),
            ),
          ),
        )),
        kind: DeclKind::Definition,
      },
      // 35 a bound matcher.
      Declaration {
        typ: matcher_type.clone(),
        body: Some(matcher_body.clone()),
        kind: DeclKind::Definition,
      },
      // 36 an unbound copy.
      Declaration {
        typ: matcher_type,
        body: Some(matcher_body),
        kind: DeclKind::Definition,
      },
    ]);
    p.case_definitions = vec![29, 35];
    p
  }

  #[test]
  fn strict_binding_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-strict.tsv");
    assert!(run_fixture_lines(&strict_program(), text) >= 7);
  }

  #[test]
  fn evaluation_order_fixtures() {
    let mut p = strict_program();
    p.declarations.push(assumption(arr(
      b(Uses::Linear, ValueContract::unique()),
      ValueContract::unique(),
      Expr::reference(11, vec![]),
      arr(
        b(Uses::Many, ValueContract::shared()),
        ValueContract::shared(),
        nat(),
        Expr::reference(11, vec![]),
      ),
    )));
    p.declarations.push(assumption(arr(
      b(Uses::Linear, ValueContract::unique()),
      ValueContract::unique(),
      Expr::reference(11, vec![]),
      arr(
        b(Uses::Many, ValueContract::shared()),
        ValueContract::shared(),
        Expr::reference(11, vec![]),
        Expr::reference(11, vec![]),
      ),
    )));
    fn replace_body(telescope: &Term, depth: usize, body: Term) -> Term {
      if depth == 0 {
        return body;
      }
      let Expr::Lam(c, domain, rest) = telescope.as_ref() else {
        panic!("expected a case-wrapper lambda telescope")
      };
      Expr::lam_contract(
        *c,
        domain.clone(),
        replace_body(rest, depth - 1, body),
      )
    }
    let base = p.declarations[29].clone();
    for (head, args) in [(24, [3, 1, 0, 2]), (39, [3, 2, 1, 0])] {
      let body =
        args.into_iter().fold(Expr::reference(head, vec![]), |body, i| {
          Expr::app(body, Expr::var(i))
        });
      p.declarations.push(Declaration {
        body: Some(replace_body(base.body.as_ref().unwrap(), 4, body)),
        ..base.clone()
      });
    }
    p.case_definitions.extend([39, 40]);
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-order.tsv");
    assert!(run_fixture_lines(&p, text) >= 13);
    let mut checker = Checker::new(&p, Limits::default());
    assert_eq!(
      checker.case_definition(256, 4, 29).unwrap().unwrap().by_need,
      vec![None, None, Some(0), Some(1)],
    );
    assert_eq!(
      checker.case_definition(256, 4, 35).unwrap().unwrap().by_need,
      vec![None, Some(1), Some(1)],
    );
    for index in [39, 40] {
      assert_eq!(
        checker.case_definition(256, 4, index).unwrap().unwrap().by_need,
        vec![None, None, Some(0), Some(1)],
      );
    }
  }

  /// The strict program extended for case-split fields (review F5) and joins
  /// (F6): a unique consumer of `Box`, a binary consumer of `Res`, and
  /// `UBox`, whose only constructor has a unique field. Mirrors
  /// `Tests.Resource.fieldProgram`.
  fn field_program() -> Program {
    let mut p = strict_program();
    let many = b(Uses::Many, ValueContract::shared());
    let shared = ValueContract::shared();
    let all = |d: Term, c: Term| arr(many, shared, d, c);
    let res = || Expr::reference(11, vec![]);
    let boxt = || Expr::reference(21, vec![]);
    let ubox = || Expr::reference(39, vec![]);
    let unique_many = b(Uses::Many, ValueContract::unique());
    p.declarations.extend([
      // 37 takeBox: (1 ! b : Box) → Res.
      assumption(arr(
        b(Uses::Linear, ValueContract::unique()),
        shared,
        boxt(),
        res(),
      )),
      // 38 pairR: Res → Res → Res.
      assumption(all(res(), all(res(), res()))),
      // 39 UBox, 40 UBox.mk (! r : Res), 41 UBox.rec.
      Declaration {
        typ: Expr::sort(0),
        body: None,
        kind: DeclKind::TypeConstructor,
      },
      Declaration {
        typ: arr(unique_many, shared, res(), ubox()),
        body: None,
        kind: DeclKind::Constructor,
      },
      assumption(all(
        all(ubox(), Expr::sort(0)),
        all(
          arr(
            unique_many,
            shared,
            res(),
            Expr::app(
              Expr::var(1),
              Expr::app(Expr::reference(40, vec![]), Expr::var(0)),
            ),
          ),
          all(ubox(), Expr::app(Expr::var(2), Expr::var(0))),
        ),
      )),
    ]);
    p.recursors.push(RecursorInfo {
      index: 41,
      params: 0,
      motives: 1,
      minors: 1,
      indices: 0,
      fields: vec![1],
      binders: vec![1],
    });
    p
  }

  #[test]
  fn case_field_and_join_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-fields.tsv");
    assert!(run_fixture_lines(&field_program(), text) >= 5);
  }

  #[test]
  fn unfolding_equation_fixtures() {
    let text =
      include_str!("../../../Tests/Fixtures/ixon-v4/resource-equations.tsv");
    assert!(run_fixture_lines(&equations_program(), text) >= 2);
  }

  /// Mirrors the R17 part of `Tests.Resource.runAdmission`.
  #[test]
  fn definitions_are_checked_through_bound_equations() {
    let many = b(Uses::Many, ValueContract::shared());
    let linear = b(Uses::Linear, ValueContract::shared());
    let statement = |lhs: Term, rhs: Term| {
      arr(
        many,
        ValueContract::shared(),
        nat(),
        Expr::app(
          Expr::app(Expr::app(Expr::reference(11, vec![]), nat()), lhs),
          rhs,
        ),
      )
    };
    let base = |typ: Term, kind: DeclKind, eq_type: Option<u64>| {
      let mut p = program();
      p.declarations.extend([
        Declaration {
          typ: arr(
            many,
            ValueContract::shared(),
            Expr::sort(0),
            arr(
              many,
              ValueContract::shared(),
              Expr::var(0),
              arr(many, ValueContract::shared(), Expr::var(1), Expr::sort(1)),
            ),
          ),
          body: None,
          kind: DeclKind::TypeConstructor,
        },
        Declaration {
          typ,
          body: Some(Expr::lam_contract(many, nat(), Expr::nat(0))),
          kind,
        },
        Declaration {
          typ: unary(linear, ValueContract::shared()),
          body: Some(Expr::lam_contract(linear, nat(), Expr::nat(0))),
          kind: DeclKind::Definition,
        },
      ]);
      p.eq_type = eq_type;
      p.equations = vec![(13, 12)];
      p
    };
    let good = || {
      statement(
        Expr::app(Expr::reference(13, vec![]), Expr::var(0)),
        Expr::var(0),
      )
    };
    let mut bound = policy();
    bound.equations = vec![(13, 12)];
    let p = base(good(), DeclKind::Theorem, Some(11));
    assert!(admit_program(&p, &bound, Limits::default()).is_ok());
    assert!(admit_program(&p, &policy(), Limits::default()).is_err());
    for p in [
      base(good(), DeclKind::Definition, Some(11)),
      base(
        arr(many, ValueContract::shared(), nat(), nat()),
        DeclKind::Theorem,
        Some(11),
      ),
      base(
        statement(
          Expr::app(Expr::reference(5, vec![]), Expr::var(0)),
          Expr::var(0),
        ),
        DeclKind::Theorem,
        Some(11),
      ),
      base(good(), DeclKind::Theorem, None),
    ] {
      assert!(check_definition(&p, 13, Limits::default()).is_err());
    }
    // Review F3: an equation whose proof depends on an axiom other than the
    // standard three (here 14, as `sorryAx`) is not admitted.
    let with_axiom = |proof: Term| {
      let mut p = base(good(), DeclKind::Theorem, Some(11));
      p.declarations[12].body = Some(proof);
      p.declarations.push(assumption(nat()));
      p.axioms = vec![14];
      p
    };
    let uses =
      with_axiom(Expr::lam_contract(many, nat(), Expr::reference(14, vec![])));
    assert!(admit_program(&uses, &bound, Limits::default()).is_err());
    let unused = with_axiom(Expr::lam_contract(many, nat(), Expr::nat(0)));
    assert!(admit_program(&unused, &bound, Limits::default()).is_ok());
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
        // An erased input leaves the literal `0`, which is shared: it
        // satisfies every shared result and no unique one.
        let allowed = if input.uses == Uses::Erased {
          result.owned == Owned::Shared
        } else {
          (input.value.owned == Owned::Unique || result.owned == Owned::Shared)
            && (input.value.locality == Locality::Unrestricted
              || result.locality == Locality::Local)
        };
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

  #[test]
  fn scalar_ownership_is_explicit_and_does_not_cross_other_axes() {
    let mut p = program();
    p.shareable_types.clear();
    p.declarations.push(Declaration {
      typ: Expr::all_contract(
        b(Uses::Erased, ValueContract::shared()),
        ValueContract::shared(),
        Expr::sort(0),
        Expr::sort(0),
      ),
      body: None,
      kind: DeclKind::TypeConstructor,
    });
    assert_eq!(
      run_fixture_lines(
        &p,
        include_str!(
          "../../../Tests/Fixtures/ixon-v4/resource-scalar-disabled.tsv"
        )
      ),
      11
    );
    p.scalar_types = vec![0, 11];
    assert_eq!(
      run_fixture_lines(
        &p,
        include_str!("../../../Tests/Fixtures/ixon-v4/resource-scalar.tsv")
      ),
      11
    );
    assert!(admit_program(&p, &policy(), Limits::default()).is_err());
    let mut bound = policy();
    bound.scalar_types = vec![0, 11];
    assert!(admit_program(&p, &bound, Limits::default()).is_ok());
  }

  fn policy() -> Policy {
    Policy {
      assumptions: vec![1, 4, 6, 8, 9, 10],
      shareable_types: vec![0, 7],
      scalar_types: vec![],
      choices: vec![6, 9, 10],
      cases: false,
      case_definitions: vec![],
      equations: vec![],
      crossing: false,
      linear_types: vec![],
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
