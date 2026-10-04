//! Additional source-contract typing over authenticated nominal metadata.
//! Erased canonical typing and runtime resource checking remain separate gates.
mod check;
mod convert;
mod prepare;
mod universe;
mod validate;
use validate::resource_sensitivity;

use ixon::contract::BinderContract;
use ixon::contract::ValueContract;
use ixon::expr::Expr;
use ixon::resource::transport_support as support;
use ixon::resource::{Declaration, Error, Limits, Program, Term};
use ixon::univ::Univ;
use num_bigint::BigUint;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Kind {
  Definition,
  Theorem,
  Opaque,
  Inductive,
  Constructor,
  Recursor,
  Quotient,
  Axiom { standard: bool },
}
#[derive(Clone, Debug)]
struct Constructor {
  pub index: u64,
  pub family: u64,
  pub position: usize,
  pub params: usize,
  pub fields: usize,
}
#[derive(Clone, Debug)]
struct Inductive {
  pub index: u64,
  pub params: usize,
  pub indices: usize,
  pub constructors: Vec<u64>,
}
#[derive(Clone, Debug)]
struct Rule {
  pub fields: usize,
  pub rhs: Term,
}
#[derive(Clone, Debug)]
struct Recursor {
  pub index: u64,
  pub family: u64,
  /// Retained authenticated header; neutral-major K reduction is unsupported.
  #[allow(dead_code)]
  pub k: bool,
  pub params: usize,
  pub motives: usize,
  pub minors: usize,
  pub indices: usize,
  pub rules: Vec<Rule>,
}
impl Recursor {
  fn major(&self) -> Result<usize, Error> {
    self
      .params
      .checked_add(self.motives)
      .and_then(|n| n.checked_add(self.minors))
      .and_then(|n| n.checked_add(self.indices))
      .ok_or(Error::Budget)
  }
}
#[derive(Clone, Debug, Default)]
struct Metadata {
  pub universes: Vec<Arc<Univ>>,
  pub level_arities: Vec<usize>,
  pub resource_sensitive: Vec<bool>,
  pub eq_type: Option<u64>,
  pub nat_type: Option<Term>,
  pub string_type: Option<Term>,
  pub kinds: Vec<Kind>,
  pub unsafe_primitives: Vec<usize>,
  pub inductives: Vec<Inductive>,
  pub constructors: Vec<Constructor>,
  pub recursors: Vec<Recursor>,
  pub naturals: Vec<(u64, BigUint)>,
}
impl Metadata {
  fn constructor(&self, i: u64) -> Option<&Constructor> {
    self.constructors.iter().find(|c| c.index == i)
  }
  fn inductive(&self, i: u64) -> Option<&Inductive> {
    self.inductives.iter().find(|c| c.index == i)
  }
  fn recursor(&self, i: u64) -> Option<&Recursor> {
    self.recursors.iter().find(|c| c.index == i)
  }
}
#[derive(Clone, Debug)]
struct Failure {
  pub declaration: Option<usize>,
  pub error: Error,
}

fn source_program(m: &Metadata, p: &Program) -> Program {
  Program {
    interfaces: vec![],
    nat_type: m.nat_type.clone(),
    string_type: m.string_type.clone(),
    ..p.clone()
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Coverage {
  Uncovered,
  Runtime,
  Alternative(usize),
  Replacement(usize),
  EqualityEndpoint,
}
impl Coverage {
  fn under_lambda(self) -> Self {
    match self {
      Self::Alternative(n) if n > 0 => Self::Alternative(n - 1),
      Self::Replacement(n) if n > 0 => Self::Replacement(n - 1),
      other => other,
    }
  }
}
type Arrow = (BinderContract, ValueContract, Term, Term);
type Context = Vec<(BinderContract, Term)>;
struct TransportChecker<'a> {
  source: &'a Program,
  runtime: &'a Program,
  metadata: &'a Metadata,
  universes: Vec<Arc<Univ>>,
  remaining: usize,
  // Each cache belongs to this fresh fixed source/runtime/metadata action.
  // Universe IDs are append-only. Only completed results are inserted.
  whnf_cache: HashMap<Term, Term>,
  instances_cache: HashMap<(Term, Vec<Arc<Univ>>), Term>,
  types_cache: HashMap<(Term, Context), Term>,
  compatible_cache: HashMap<(Term, Term, Context), bool>,
  checked_cache: HashSet<(Term, Term, Context, Coverage)>,
}
impl<'a> TransportChecker<'a> {
  fn new(
    source: &'a Program,
    runtime: &'a Program,
    metadata: &'a Metadata,
    limits: Limits,
  ) -> Self {
    Self {
      source,
      runtime,
      metadata,
      universes: metadata.universes.clone(),
      remaining: limits.steps,
      whnf_cache: HashMap::new(),
      instances_cache: HashMap::new(),
      types_cache: HashMap::new(),
      compatible_cache: HashMap::new(),
      checked_cache: HashSet::new(),
    }
  }
  fn tick(&mut self, fuel: usize) -> Result<usize, Error> {
    if fuel == 0 || self.remaining == 0 {
      return Err(Error::Budget);
    }
    self.remaining -= 1;
    Ok(fuel - 1)
  }
  fn declaration(&self, index: u64) -> Result<&Declaration, Error> {
    self
      .source
      .declarations
      .get(index as usize)
      .ok_or(Error::BadReference(index))
  }
  fn expansion(&self, index: u64) -> Result<Term, Error> {
    self
      .source
      .sharing
      .get(index as usize)
      .cloned()
      .ok_or(Error::UnresolvedSharing(index))
  }
  fn shift(
    &mut self,
    fuel: usize,
    term: &Term,
    amount: u64,
    cutoff: u64,
  ) -> Result<Term, Error> {
    support::shift(self.source, fuel, &mut self.remaining, term, amount, cutoff)
  }
  fn substitute(
    &mut self,
    fuel: usize,
    term: &Term,
    value: &Term,
    depth: u64,
  ) -> Result<Term, Error> {
    support::substitute(
      self.source,
      fuel,
      &mut self.remaining,
      term,
      value,
      depth,
    )
  }
  fn split_app(
    &mut self,
    fuel: usize,
    term: &Term,
  ) -> Result<(Term, Vec<Term>), Error> {
    let fuel = self.tick(fuel)?;
    match term.as_ref() {
      Expr::Share(i) => self.split_app(fuel, &self.expansion(*i)?),
      Expr::App(f, a) => {
        let (head, mut args) = self.split_app(fuel, f)?;
        args.push(a.clone());
        Ok((head, args))
      },
      _ => Ok((term.clone(), vec![])),
    }
  }
  fn under_binder<T>(
    &mut self,
    ctx: &Context,
    c: BinderContract,
    typ: Term,
    action: impl FnOnce(&mut Self, &Context) -> Result<T, Error>,
  ) -> Result<T, Error> {
    let mut inner = ctx.clone();
    inner.push((c, typ));
    action(self, &inner)
  }
}
/// Internal combined-validator continuation. Caller must first authenticate
/// and erased-check the same bytes; no profile can supply this judgment.
pub(super) fn gate(
  env: &ixon::env::Env,
  resolved: &ixon::resource::addressed::AddressedProgram,
  limits: Limits,
) -> Result<(), String> {
  let (logical, metadata) = prepare::prepare(env, resolved, limits)?;
  let marked = ixon::resource::relevance(&resolved.program, limits)
    .map_err(|e| format!("resource admission None: {e:?}"))?;
  let roots = metadata
    .resource_sensitive
    .iter()
    .enumerate()
    .filter_map(|(i, b)| b.then_some(i))
    .collect();
  let runtime_covered = marked
    .iter()
    .enumerate()
    .filter_map(|(i, b)| {
      (*b
        && resolved.program.declarations[i].kind
          == ixon::resource::DeclKind::Definition
        && !resolved.policy.assumptions.contains(&i)
        && !resolved.program.equations.iter().any(|(d, _)| *d as usize == i))
      .then_some(i)
    })
    .collect();
  let request = validate::Request {
    roots,
    runtime_covered,
    assumptions: resolved.policy.assumptions.clone(),
    equations: resolved.policy.equations.clone(),
  };
  validate::validate(&logical, &resolved.program, &metadata, &request, limits)
    .map_err(|error| {
      format!(
        "resource admission {:?}: {:?}",
        error.declaration.and_then(|i| resolved.addresses.get(i)),
        error.error
      )
    })
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod beta_tests;
