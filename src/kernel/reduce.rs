//! Normalization by evaluation for Lean kernel expressions.
//!
//! This module implements an eval-apply style reducer for dependently-typed
//! lambda calculus. Expressions reduce to values, which are either:
//! - Closures (lambda abstractions with captured environments)
//! - Neutral values (stuck applications with free variables at the head)
//! - Canonical forms (sorts, literals, fully-applied constructors)

use crate::kernel::expr::*;
use std::rc::Rc;

// ============================================================================
// Environment
// ============================================================================

/// Internal node structure for the environment linked list.
#[derive(Debug, PartialEq, Eq)]
enum EnvNode {
  /// Empty environment.
  Empty,
  /// Extended environment: most recent value + tail.
  Cons(Value, Env),
}

/// A de Bruijn environment as a linked list.
///
/// Wraps `Rc<EnvNode>` so that cloning is cheap (just incrementing a reference count).
/// Environments are immutable linked lists where de Bruijn index `i` refers
/// to the `i`-th element from the head.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Env(Rc<EnvNode>);

impl Env {
  /// Creates an empty environment.
  pub fn new() -> Self {
    Env(Rc::new(EnvNode::Empty))
  }

  /// Extends the environment with a new value, returning a new environment.
  ///
  /// This is O(1) and shares the tail via Rc.
  pub fn extend(&self, v: Value) -> Self {
    Env(Rc::new(EnvNode::Cons(v, self.clone())))
  }

  /// Looks up a de Bruijn index in the environment.
  ///
  /// De Bruijn index 0 refers to the most recently bound variable (head),
  /// index 1 refers to the next, etc.
  pub fn lookup(&self, idx: usize) -> Option<&Value> {
    let mut current = &*self.0;
    let mut i = idx;

    loop {
      match current {
        EnvNode::Empty => return None,
        EnvNode::Cons(v, rest) => {
          if i == 0 {
            return Some(v);
          }
          i -= 1;
          current = &*rest.0;
        },
      }
    }
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
  Neutral(Neutral),
  /// A lambda abstraction (closure).
  /// Contains: name, body expression, captured environment, binder info
  Fun(Name, Rc<Expr>, Env, BinderInfo),
  /// A universe sort.
  Sort(Level),
  /// A dependent function type (Pi/forall).
  /// Contains: name, domain value, body expression, captured environment, binder info
  Forall(Name, Rc<Value>, Rc<Expr>, Env, BinderInfo),
  /// A literal value.
  Lit(Literal),
  /// A constant reference (might be reducible depending on global environment).
  Const(Name, Vec<Level>),
}

/// A neutral value represents a stuck computation.
///
/// Neutral (or "stuck") values arise when we try to reduce an expression
/// that depends on a free variable or metavariable. These are values that
/// cannot reduce further because they're waiting on an unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Neutral {
  /// A free variable (stuck).
  Fvar(Name),
  /// A metavariable (stuck).
  Mvar(Name),
  /// A stuck bound variable (should not appear in well-formed terms under sufficient environment).
  Bvar(usize),
  /// A neutral value applied to a value.
  /// This is the "stuck application" - the head is neutral (contains a free variable).
  App(Rc<Neutral>, Rc<Value>),
  /// Projection from a neutral value.
  Proj(Name, usize, Rc<Neutral>),
  /// Metadata-annotated neutral.
  Mdata(Vec<(Name, DataValue)>, Rc<Neutral>),
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
        None => Value::Neutral(Neutral::Bvar(*idx)),
      }
    },

    Expr::Fvar(name) => {
      // Free variables are always stuck
      Value::Neutral(Neutral::Fvar(name.clone()))
    },

    Expr::Mvar(name) => {
      // Metavariables are always stuck
      Value::Neutral(Neutral::Mvar(name.clone()))
    },

    Expr::Sort(level) => {
      // Sorts are already values
      Value::Sort(level.clone())
    },

    Expr::Const(name, levels) => {
      // Constants might be reducible in a global environment
      // For now, treat as values (would need global env to unfold definitions)
      Value::Const(name.clone(), levels.clone())
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
      Value::Fun(name.clone(), body.clone(), env.clone(), binder_info.clone())
    },

    Expr::ForallE(name, ty, body, binder_info) => {
      // Forall evaluates to a dependent function type value
      let vty = eval(ty, env);
      Value::Forall(
        name.clone(),
        Rc::new(vty),
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
      Value::Lit(lit.clone())
    },

    Expr::Mdata(kvs, e) => {
      // Metadata: evaluate the inner expression
      let v = eval(e, env);
      // If the result is neutral, preserve metadata in the neutral
      match v {
        Value::Neutral(n) => {
          Value::Neutral(Neutral::Mdata(kvs.clone(), Rc::new(n)))
        },
        // Otherwise, metadata is erased during reduction
        _ => v,
      }
    },

    Expr::Proj(name, idx, e) => {
      let v = eval(e, env);
      match v {
        Value::Neutral(n) => {
          // Projection from a neutral value is stuck
          Value::Neutral(Neutral::Proj(name.clone(), *idx, Rc::new(n)))
        },
        // In a full implementation with inductive types, we'd handle
        // projections from fully-applied constructors here
        _ => {
          // For now, we don't have enough information to reduce projections
          // In practice, you'd need to know the structure definition
          // to extract the field. Treating as neutral is conservative.
          Value::Neutral(Neutral::Proj(
            name.clone(),
            *idx,
            Rc::new(Neutral::Fvar(Name::Anonymous)), // placeholder neutral head
          ))
        },
      }
    },
  }
}

/// Applies a value (function) to another value (argument).
///
/// This is the "apply" part of eval-apply style reduction.
/// If the function is a closure (Fun), we extend its environment with
/// the argument and evaluate the body. If it's neutral, we create a
/// stuck application (App).
pub fn apply(fun: Value, arg: Value) -> Value {
  match fun {
    Value::Fun(_name, body, env, _binder_info) => {
      // Beta reduction: extend the closure's environment with the argument
      // and evaluate the body in the extended environment
      let new_env = env.extend(arg);
      eval(&body, &new_env)
    },

    Value::Neutral(n) => {
      // Application to a neutral value creates a stuck application
      // This is the key case: neutral values at the head mean we can't reduce
      Value::Neutral(Neutral::App(Rc::new(n), Rc::new(arg)))
    },

    // Other values cannot be applied (would be a type error in well-typed terms)
    // In a well-typed program, we should never apply a non-function value
    _ => {
      // Conservative fallback: treat as a stuck application
      // In practice, this indicates a type error
      Value::Neutral(Neutral::App(
        Rc::new(Neutral::Fvar(Name::Anonymous)),
        Rc::new(arg),
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
    Value::Neutral(n) => quote_neutral(n, level),

    Value::Fun(name, body, env, binder_info) => {
      // Quote a lambda: create a fresh variable and quote the body
      let fresh_var = Value::Neutral(Neutral::Bvar(level));
      let new_env = env.extend(fresh_var);
      let body_val = eval(body, &new_env);
      let quoted_body = quote(&body_val, level + 1);
      Expr::Lam(
        name.clone(),
        Rc::new(Expr::Sort(Level::Zero)), // type is not preserved (would need type quotation)
        Rc::new(quoted_body),
        binder_info.clone(),
      )
    },

    Value::Sort(l) => Expr::Sort(l.clone()),

    Value::Forall(name, ty, body, env, binder_info) => {
      let quoted_ty = quote(ty, level);
      // Evaluate body under a fresh variable
      let fresh_var = Value::Neutral(Neutral::Bvar(level));
      let new_env = env.extend(fresh_var);
      let body_val = eval(body, &new_env);
      let quoted_body = quote(&body_val, level + 1);
      Expr::ForallE(
        name.clone(),
        Rc::new(quoted_ty),
        Rc::new(quoted_body),
        binder_info.clone(),
      )
    },

    Value::Lit(lit) => Expr::Lit(lit.clone()),

    Value::Const(name, levels) => Expr::Const(name.clone(), levels.clone()),
  }
}

/// Quotes a neutral value back to an expression.
fn quote_neutral(neutral: &Neutral, level: usize) -> Expr {
  match neutral {
    Neutral::Fvar(name) => Expr::Fvar(name.clone()),

    Neutral::Mvar(name) => Expr::Mvar(name.clone()),

    Neutral::Bvar(idx) => Expr::Bvar(*idx),

    Neutral::App(fun, arg) => {
      let quoted_fun = quote_neutral(fun, level);
      let quoted_arg = quote(arg, level);
      Expr::App(Rc::new(quoted_fun), Rc::new(quoted_arg))
    },

    Neutral::Proj(name, idx, e) => {
      let quoted_e = quote_neutral(e, level);
      Expr::Proj(name.clone(), *idx, Rc::new(quoted_e))
    },

    Neutral::Mdata(kvs, n) => {
      let quoted_n = quote_neutral(n, level);
      Expr::Mdata(kvs.clone(), Rc::new(quoted_n))
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
