//! Normalization by evaluation for Lean kernel expressions.
//!
//! This module implements an eval-apply style reducer for dependently-typed
//! lambda calculus. Expressions reduce to values, which are either:
//! - Closures (lambda abstractions with captured environments)
//! - Neutral values (stuck applications with free variables at the head)
//! - Canonical forms (sorts, literals, fully-applied constructors)

use crate::kernel::expr::*;
use std::cell::RefCell;
use std::rc::Rc;

// ============================================================================
// Thunks
// ============================================================================

/// Internal node structure for a thunk.
#[derive(Debug)]
enum ThunkNode {
  /// A suspended computation: expression + environment pair.
  Suspended(Expr, Env),
  /// An already evaluated value (memoized).
  Forced(Value),
}

/// A thunk represents a delayed computation with memoization.
///
/// Wraps `RefCell<ThunkNode>` so that we can mutate it for memoization.
/// When forced, the thunk evaluates the expression and caches the result.
#[derive(Debug, Clone)]
pub struct Thunk(Rc<RefCell<ThunkNode>>);

impl Thunk {
  /// Creates a new already-forced thunk.
  fn forced(value: Value) -> Self {
    Thunk(Rc::new(RefCell::new(ThunkNode::Forced(value))))
  }
}

// ============================================================================
// Environment
// ============================================================================

/// Internal node structure for the environment linked list.
#[derive(Debug)]
enum EnvNode {
  /// Empty environment.
  Empty,
  /// Extended environment: most recent thunk + tail.
  Cons(Thunk, Env),
}

/// A de Bruijn environment as a linked list.
///
/// Wraps `Rc<EnvNode>` so that cloning is cheap (just incrementing a reference count).
/// Environments are immutable linked lists where de Bruijn index `i` refers
/// to the `i`-th element from the head.
#[derive(Debug, Clone)]
pub struct Env(Rc<EnvNode>);

impl Env {
  /// Creates an empty environment.
  pub fn new() -> Self {
    Env(Rc::new(EnvNode::Empty))
  }

  /// Extends the environment with a new thunk, returning a new environment.
  ///
  /// This is O(1) and shares the tail via Rc.
  pub fn extend(&self, thunk: Thunk) -> Self {
    Env(Rc::new(EnvNode::Cons(thunk, self.clone())))
  }

  /// Looks up a de Bruijn index in the environment.
  ///
  /// De Bruijn index 0 refers to the most recently bound variable (head),
  /// index 1 refers to the next, etc.
  pub fn lookup(&self, idx: usize) -> Option<&Thunk> {
    let mut current = &*self.0;
    let mut i = idx;

    loop {
      match current {
        EnvNode::Empty => return None,
        EnvNode::Cons(thunk, rest) => {
          if i == 0 {
            return Some(thunk);
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

/// A neutral value represents a stuck computation.
///
/// Neutral (or "stuck") values arise when we try to reduce an expression
/// that depends on a free variable. These are values that cannot reduce
/// further because they're waiting on an unknown.
#[derive(Debug, Clone)]
pub enum Neutral {
  /// A free variable (stuck).
  Fvar(Name),
  /// A neutral value applied to a thunk (lazy argument).
  /// This is the "stuck application" - the head is neutral (contains a free variable).
  App(Rc<Neutral>, Thunk),
  /// Projection from a neutral value.
  Proj(Name, usize, Rc<Neutral>),
}

/// Internal node structure for a value.
#[derive(Debug)]
pub enum ValueNode {
  /// A neutral value (stuck computation).
  Neutral(Neutral),
  /// A lambda abstraction (closure).
  /// Contains: name, type thunk, body expression, captured environment, binder info
  Fun(Name, Thunk, Expr, Env, BinderInfo),
  /// A universe sort.
  Sort(Level),
  /// A dependent function type (Pi/forall).
  /// Contains: name, domain thunk, body expression, captured environment, binder info
  Forall(Name, Thunk, Expr, Env, BinderInfo),
  /// A literal value.
  Lit(Literal),
  /// A constant reference (might be reducible depending on global environment).
  Const(Name, Vec<Level>),
}

/// A value is what an expression reduces to.
///
/// Values are in weak head normal form (WHNF) - reduced enough to inspect
/// the head constructor, but arguments may not be fully normalized.
/// Wraps `Rc<ValueNode>` so that cloning is cheap (just incrementing a reference count).
#[derive(Debug, Clone)]
pub struct Value(pub Rc<ValueNode>);

// ============================================================================
// Thunk Operations
// ============================================================================

/// Suspends an expression with its environment, creating a thunk.
///
/// This delays the evaluation of the expression until it's needed.
pub fn suspend(expr: Expr, env: Env) -> Thunk {
  Thunk(Rc::new(RefCell::new(ThunkNode::Suspended(expr, env))))
}

/// Forces a thunk, evaluating it to a value if necessary with memoization.
///
/// If the thunk is already forced, returns the cached value.
/// If suspended, evaluates the expression in its captured environment,
/// updates the thunk to cache the result (memoization), and returns the value.
pub fn force(thunk: &Thunk) -> Value {
  // Need to evaluate - extract expr and env
  let node = thunk.0.borrow();
  let (expr, env) = {
    match &*node {
      ThunkNode::Suspended(expr, env) => (expr, env),
      ThunkNode::Forced(value) => return value.clone(),
    }
  };

  // Evaluate the expression
  let value = eval(expr, env);
  drop(node);

  // Memoize: update the thunk to store the computed value
  *thunk.0.borrow_mut() = ThunkNode::Forced(value.clone());

  value
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
  match expr.0.as_ref() {
    ExprNode::Bvar(idx) => {
      // Look up the de Bruijn index in the environment and force the thunk
      match env.lookup(*idx) {
        Some(thunk) => force(thunk),
        // Unbound de Bruijn index - should never happen in well-formed terms
        None => panic!("Unbound de Bruijn index: {}", idx),
      }
    },

    ExprNode::Fvar(name) => {
      // Free variables are always stuck
      Value(Rc::new(ValueNode::Neutral(Neutral::Fvar(name.clone()))))
    },

    ExprNode::Sort(level) => {
      // Sorts are already values
      Value(Rc::new(ValueNode::Sort(level.clone())))
    },

    ExprNode::Const(name, levels) => {
      // Constants might be reducible in a global environment
      // For now, treat as values (would need global env to unfold definitions)
      Value(Rc::new(ValueNode::Const(name.clone(), levels.clone())))
    },

    ExprNode::App(fun, arg) => {
      // Application: evaluate function, suspend argument (lazy evaluation)
      let vfun = eval(fun, env);
      let arg_thunk = suspend(arg.clone(), env.clone());
      apply(&vfun, arg_thunk)
    },

    ExprNode::Lam(name, ty, body, binder_info) => {
      // Lambda evaluates to a closure capturing the current environment
      // Type is suspended as a thunk
      let ty_thunk = suspend(ty.clone(), env.clone());
      Value(Rc::new(ValueNode::Fun(
        name.clone(),
        ty_thunk,
        body.clone(),
        env.clone(),
        binder_info.clone(),
      )))
    },

    ExprNode::ForallE(name, ty, body, binder_info) => {
      // Forall evaluates to a dependent function type value (type is suspended)
      let ty_thunk = suspend(ty.clone(), env.clone());
      Value(Rc::new(ValueNode::Forall(
        name.clone(),
        ty_thunk,
        body.clone(),
        env.clone(),
        binder_info.clone(),
      )))
    },

    ExprNode::LetE(_name, _ty, val, body, _non_dep) => {
      // Let-binding: suspend the bound value (lazy evaluation)
      let thunk = suspend(val.clone(), env.clone());
      let new_env = env.extend(thunk);
      eval(body, &new_env)
    },

    ExprNode::Lit(lit) => {
      // Literals are already values
      Value(Rc::new(ValueNode::Lit(lit.clone())))
    },

    ExprNode::Proj(name, idx, e) => {
      let v = eval(e, env);
      match v.0.as_ref() {
        ValueNode::Neutral(n) => {
          // Projection from a neutral value is stuck
          Value(Rc::new(ValueNode::Neutral(Neutral::Proj(
            name.clone(),
            *idx,
            Rc::new(n.clone()),
          ))))
        },
        // In a full implementation with inductive types, we'd handle
        // projections from fully-applied constructors here
        _ => {
          // For now, we don't have enough information to reduce projections
          // In practice, you'd need to know the structure definition
          // to extract the field. Treating as neutral is conservative.
          Value(Rc::new(ValueNode::Neutral(Neutral::Proj(
            name.clone(),
            *idx,
            Rc::new(Neutral::Fvar(Name::Anonymous)), // placeholder neutral head
          ))))
        },
      }
    },
  }
}

/// Applies a value (function) to a thunk (argument).
///
/// This is the "apply" part of eval-apply style reduction with lazy evaluation.
/// If the function is a closure (Fun), we extend its environment with the
/// suspended argument thunk and evaluate the body. The argument is only
/// evaluated when actually needed (via Bvar lookup and force).
/// If it's neutral, we create a stuck application (App).
pub fn apply(fun: &Value, arg_thunk: Thunk) -> Value {
  match fun.0.as_ref() {
    ValueNode::Fun(_name, _ty, body, env, _binder_info) => {
      // Beta reduction: extend the closure's environment with the suspended thunk
      // The argument will only be evaluated when/if it's actually used
      let new_env = env.extend(arg_thunk);
      eval(body, &new_env)
    },

    ValueNode::Neutral(n) => {
      // Application to a neutral value creates a stuck application
      // Keep the argument as a thunk (lazy evaluation)
      Value(Rc::new(ValueNode::Neutral(Neutral::App(
        Rc::new(n.clone()),
        arg_thunk,
      ))))
    },

    // Other values cannot be applied (would be a type error in well-typed terms)
    // In a well-typed program, we should never apply a non-function value
    _ => {
      // Conservative fallback: treat as a stuck application
      // Keep the argument as a thunk
      Value(Rc::new(ValueNode::Neutral(Neutral::App(
        Rc::new(Neutral::Fvar(Name::Anonymous)),
        arg_thunk,
      ))))
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
  match val.0.as_ref() {
    ValueNode::Neutral(n) => quote_neutral(n, level),

    ValueNode::Fun(name, ty_thunk, body, env, binder_info) => {
      // Quote a lambda: force and quote the type, then quote the body
      let ty_val = force(ty_thunk);
      let quoted_ty = quote(&ty_val, level);
      // Create a fresh variable thunk and quote the body
      let fresh_thunk = Thunk::forced(Value(Rc::new(ValueNode::Neutral(
        Neutral::Fvar(Name::Anonymous),
      ))));
      let new_env = env.extend(fresh_thunk);
      let body_val = eval(body, &new_env);
      let quoted_body = quote(&body_val, level + 1);
      Expr(Rc::new(ExprNode::Lam(
        name.clone(),
        quoted_ty,
        quoted_body,
        binder_info.clone(),
      )))
    },

    ValueNode::Sort(l) => Expr(Rc::new(ExprNode::Sort(l.clone()))),

    ValueNode::Forall(name, ty_thunk, body, env, binder_info) => {
      // Force the type thunk and quote it
      let ty_val = force(ty_thunk);
      let quoted_ty = quote(&ty_val, level);
      // Evaluate body under a fresh variable thunk
      let fresh_thunk = Thunk::forced(Value(Rc::new(ValueNode::Neutral(
        Neutral::Fvar(Name::Anonymous),
      ))));
      let new_env = env.extend(fresh_thunk);
      let body_val = eval(body, &new_env);
      let quoted_body = quote(&body_val, level + 1);
      Expr(Rc::new(ExprNode::ForallE(
        name.clone(),
        quoted_ty,
        quoted_body,
        binder_info.clone(),
      )))
    },

    ValueNode::Lit(lit) => Expr(Rc::new(ExprNode::Lit(lit.clone()))),

    ValueNode::Const(name, levels) => {
      Expr(Rc::new(ExprNode::Const(name.clone(), levels.clone())))
    },
  }
}

/// Quotes a neutral value back to an expression.
fn quote_neutral(neutral: &Neutral, level: usize) -> Expr {
  match neutral {
    Neutral::Fvar(name) => Expr(Rc::new(ExprNode::Fvar(name.clone()))),

    Neutral::App(fun, arg_thunk) => {
      let quoted_fun = quote_neutral(fun, level);
      // Force the thunk to get the value, then quote it
      let arg_val = force(arg_thunk);
      let quoted_arg = quote(&arg_val, level);
      Expr(Rc::new(ExprNode::App(quoted_fun, quoted_arg)))
    },

    Neutral::Proj(name, idx, e) => {
      let quoted_e = quote_neutral(e, level);
      Expr(Rc::new(ExprNode::Proj(name.clone(), *idx, quoted_e)))
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_identity_normalization() {
    // Create identity function: λx. x
    let identity = Expr(Rc::new(ExprNode::Lam(
      Name::Anonymous,
      Expr(Rc::new(ExprNode::Sort(Level::Zero))),
      Expr(Rc::new(ExprNode::Bvar(0))),
      BinderInfo::Default,
    )));

    // Normalize should preserve it
    let normalized = normalize(&identity);

    // Should still be a lambda
    match normalized.0.as_ref() {
      ExprNode::Lam(_, _, _, _) => {},
      _ => panic!("Expected lambda"),
    }
  }
}
