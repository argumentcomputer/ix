//! Normalization by evaluation for Lean kernel expressions.
//!
//! This module implements an eval-apply style reducer for dependently-typed
//! lambda calculus. Expressions reduce to values, which are either:
//! - Closures (lambda abstractions with captured environments)
//! - Neutral values (stuck applications with free variables at the head)
//! - Canonical forms (sorts, literals, fully-applied constructors)

use crate::kernel::expr::*;

// ============================================================================
// Environment
// ============================================================================

/// A de Bruijn environment mapping indices to values.
///
/// Environments are vectors of values where de Bruijn index `i` looks up
/// the `i`-th value from the end of the vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Env {
  values: Vec<Value>,
}

impl Env {
  /// Creates an empty environment.
  pub fn new() -> Self {
    Env { values: Vec::new() }
  }

  /// Pushes a value onto the environment.
  pub fn push(&mut self, v: Value) {
    self.values.push(v);
  }

  /// Extends the environment with a new value, returning a new environment.
  pub fn extend(&self, v: Value) -> Self {
    let mut new_env = self.clone();
    new_env.push(v);
    new_env
  }

  /// Looks up a de Bruijn index in the environment.
  ///
  /// De Bruijn index 0 refers to the most recently bound variable,
  /// so we index from the end of the vector.
  pub fn lookup(&self, idx: usize) -> Option<&Value> {
    // de Bruijn index i counts from the end: len - 1 - i
    self.values.get(self.values.len().checked_sub(idx + 1)?)
  }

  /// Returns the length of the environment.
  pub fn len(&self) -> usize {
    self.values.len()
  }

  /// Returns true if the environment is empty.
  pub fn is_empty(&self) -> bool {
    self.values.is_empty()
  }
}

impl Default for Env {
  fn default() -> Self {
    Self::new()
  }
}

// ============================================================================
// Values
// ============================================================================

/// A value is what an expression reduces to.
///
/// Values are in weak head normal form (WHNF) - reduced enough to inspect
/// the head constructor, but arguments may not be fully normalized.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
  /// A neutral value (stuck computation).
  VNeutral(Neutral),
  /// A lambda abstraction (closure).
  /// Contains: name, body expression, captured environment, binder info
  VLam(Name, Box<Expr>, Env, BinderInfo),
  /// A universe sort.
  VSort(Level),
  /// A dependent function type (Pi/forall).
  /// Contains: name, domain value, body expression, captured environment, binder info
  VForall(Name, Box<Value>, Box<Expr>, Env, BinderInfo),
  /// A literal value.
  VLit(Literal),
  /// A constant reference (might be reducible depending on global environment).
  VConst(Name, Vec<Level>),
}

/// A neutral value represents a stuck computation.
///
/// Neutral (or "stuck") values arise when we try to reduce an expression
/// that depends on a free variable or metavariable. These are values that
/// cannot reduce further because they're waiting on an unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Neutral {
  /// A free variable (stuck).
  NFvar(Name),
  /// A metavariable (stuck).
  NMvar(Name),
  /// A stuck bound variable (should not appear in well-formed terms under sufficient environment).
  NBvar(usize),
  /// A neutral value applied to a value.
  /// This is the "stuck application" - the head is neutral (contains a free variable).
  NApp(Box<Neutral>, Box<Value>),
  /// Projection from a neutral value.
  NProj(Name, usize, Box<Neutral>),
  /// Metadata-annotated neutral.
  NMdata(Vec<(Name, DataValue)>, Box<Neutral>),
}

// ============================================================================
// Evaluation
// ============================================================================

/// Evaluates an expression in an environment to a value.
///
/// This performs weak head normalization - it reduces the expression
/// until the head constructor is visible, but doesn't normalize under
/// binders or reduce arguments.
pub fn eval(expr: &Expr, env: &Env) -> Value {
  match expr {
    Expr::Bvar(idx) => {
      // Look up the de Bruijn index in the environment
      match env.lookup(*idx) {
        Some(v) => v.clone(),
        // If not in environment, it's a stuck bound variable (shouldn't happen in well-formed terms)
        None => Value::VNeutral(Neutral::NBvar(*idx)),
      }
    },

    Expr::Fvar(name) => {
      // Free variables are always stuck
      Value::VNeutral(Neutral::NFvar(name.clone()))
    },

    Expr::Mvar(name) => {
      // Metavariables are always stuck
      Value::VNeutral(Neutral::NMvar(name.clone()))
    },

    Expr::Sort(level) => {
      // Sorts are already values
      Value::VSort(level.clone())
    },

    Expr::Const(name, levels) => {
      // Constants might be reducible in a global environment
      // For now, treat as values (would need global env to unfold definitions)
      Value::VConst(name.clone(), levels.clone())
    },

    Expr::App(fun, arg) => {
      // Application: evaluate function and argument, then apply
      let vfun = eval(fun, env);
      let varg = eval(arg, env);
      apply(vfun, varg)
    },

    Expr::Lam(name, _ty, body, binder_info) => {
      // Lambda evaluates to a closure capturing the current environment
      // The type is not needed at runtime, so we ignore it
      Value::VLam(name.clone(), body.clone(), env.clone(), binder_info.clone())
    },

    Expr::ForallE(name, ty, body, binder_info) => {
      // Forall evaluates to a dependent function type value
      let vty = eval(ty, env);
      Value::VForall(
        name.clone(),
        Box::new(vty),
        body.clone(),
        env.clone(),
        binder_info.clone(),
      )
    },

    Expr::LetE(_name, _ty, val, body, _non_dep) => {
      // Let-binding: evaluate the bound value and extend the environment
      let vval = eval(val, env);
      let new_env = env.extend(vval);
      eval(body, &new_env)
    },

    Expr::Lit(lit) => {
      // Literals are already values
      Value::VLit(lit.clone())
    },

    Expr::Mdata(kvs, e) => {
      // Metadata: evaluate the inner expression
      let v = eval(e, env);
      // If the result is neutral, preserve metadata in the neutral
      match v {
        Value::VNeutral(n) => {
          Value::VNeutral(Neutral::NMdata(kvs.clone(), Box::new(n)))
        },
        // Otherwise, metadata is erased during reduction
        _ => v,
      }
    },

    Expr::Proj(name, idx, e) => {
      let v = eval(e, env);
      match v {
        Value::VNeutral(n) => {
          // Projection from a neutral value is stuck
          Value::VNeutral(Neutral::NProj(name.clone(), *idx, Box::new(n)))
        },
        // In a full implementation with inductive types, we'd handle
        // projections from fully-applied constructors here
        _ => {
          // For now, we don't have enough information to reduce projections
          // In practice, you'd need to know the structure definition
          // to extract the field. Treating as neutral is conservative.
          Value::VNeutral(Neutral::NProj(
            name.clone(),
            *idx,
            Box::new(Neutral::NFvar(Name::Anonymous)), // placeholder neutral head
          ))
        },
      }
    },
  }
}

/// Applies a value (function) to another value (argument).
///
/// This is the "apply" part of eval-apply style reduction.
/// If the function is a closure (VLam), we extend its environment with
/// the argument and evaluate the body. If it's neutral, we create a
/// stuck application (NApp).
pub fn apply(fun: Value, arg: Value) -> Value {
  match fun {
    Value::VLam(_name, body, env, _binder_info) => {
      // Beta reduction: extend the closure's environment with the argument
      // and evaluate the body in the extended environment
      let new_env = env.extend(arg);
      eval(&body, &new_env)
    },

    Value::VNeutral(n) => {
      // Application to a neutral value creates a stuck application
      // This is the key case: neutral values at the head mean we can't reduce
      Value::VNeutral(Neutral::NApp(Box::new(n), Box::new(arg)))
    },

    // Other values cannot be applied (would be a type error in well-typed terms)
    // In a well-typed program, we should never apply a non-function value
    _ => {
      // Conservative fallback: treat as a stuck application
      // In practice, this indicates a type error
      Value::VNeutral(Neutral::NApp(
        Box::new(Neutral::NFvar(Name::Anonymous)),
        Box::new(arg),
      ))
    },
  }
}

// ============================================================================
// Quotation (Values back to Expressions)
// ============================================================================

/// Quotes a value back to an expression at a given de Bruijn level.
///
/// The level parameter tracks how many binders we've gone under during quotation.
/// This is needed to convert values (which use environments) back to expressions
/// (which use de Bruijn indices).
pub fn quote(val: &Value, level: usize) -> Expr {
  match val {
    Value::VNeutral(n) => quote_neutral(n, level),

    Value::VLam(name, body, env, binder_info) => {
      // Quote a lambda: create a fresh variable and quote the body
      let fresh_var = Value::VNeutral(Neutral::NBvar(level));
      let new_env = env.extend(fresh_var);
      let body_val = eval(body, &new_env);
      let quoted_body = quote(&body_val, level + 1);
      Expr::Lam(
        name.clone(),
        Box::new(Expr::Sort(Level::Zero)), // type is not preserved (would need type quotation)
        Box::new(quoted_body),
        binder_info.clone(),
      )
    },

    Value::VSort(l) => Expr::Sort(l.clone()),

    Value::VForall(name, ty, body, env, binder_info) => {
      let quoted_ty = quote(ty, level);
      // Evaluate body under a fresh variable
      let fresh_var = Value::VNeutral(Neutral::NBvar(level));
      let new_env = env.extend(fresh_var);
      let body_val = eval(body, &new_env);
      let quoted_body = quote(&body_val, level + 1);
      Expr::ForallE(
        name.clone(),
        Box::new(quoted_ty),
        Box::new(quoted_body),
        binder_info.clone(),
      )
    },

    Value::VLit(lit) => Expr::Lit(lit.clone()),

    Value::VConst(name, levels) => Expr::Const(name.clone(), levels.clone()),
  }
}

/// Quotes a neutral value back to an expression.
fn quote_neutral(neutral: &Neutral, level: usize) -> Expr {
  match neutral {
    Neutral::NFvar(name) => Expr::Fvar(name.clone()),

    Neutral::NMvar(name) => Expr::Mvar(name.clone()),

    Neutral::NBvar(idx) => Expr::Bvar(*idx),

    Neutral::NApp(fun, arg) => {
      let quoted_fun = quote_neutral(fun, level);
      let quoted_arg = quote(arg, level);
      Expr::App(Box::new(quoted_fun), Box::new(quoted_arg))
    },

    Neutral::NProj(name, idx, e) => {
      let quoted_e = quote_neutral(e, level);
      Expr::Proj(name.clone(), *idx, Box::new(quoted_e))
    },

    Neutral::NMdata(kvs, n) => {
      let quoted_n = quote_neutral(n, level);
      Expr::Mdata(kvs.clone(), Box::new(quoted_n))
    },
  }
}

// ============================================================================
// Normalization
// ============================================================================

/// Normalizes an expression by evaluating it in an empty environment
/// and quoting the result back to an expression.
///
/// This computes the full normal form (all redexes reduced).
pub fn normalize(expr: &Expr) -> Expr {
  let val = eval(expr, &Env::new());
  quote(&val, 0)
}

/// Reduces an expression to weak head normal form (WHNF).
///
/// This only reduces until the head constructor is visible,
/// without normalizing under binders or in arguments.
pub fn whnf(expr: &Expr) -> Value {
  eval(expr, &Env::new())
}
