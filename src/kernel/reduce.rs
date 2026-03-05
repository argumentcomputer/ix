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
// Generic List
// ============================================================================

/// Internal node structure for a generic linked list.
#[derive(Debug, Clone)]
enum ListNode<T> {
  /// Empty list.
  Nil,
  /// Cons cell: head element + tail.
  Cons(T, List<T>),
}

/// A generic immutable linked list.
///
/// Wraps `Rc<ListNode<T>>` so that cloning is cheap (just incrementing a reference count).
#[derive(Debug, Clone)]
pub struct List<T>(Rc<ListNode<T>>);

impl<T> List<T> {
  /// Creates an empty list.
  pub fn new() -> Self {
    List(Rc::new(ListNode::Nil))
  }

  /// Extends the list with a new element at the head, returning a new list.
  ///
  /// This is O(1) and shares the tail via Rc.
  pub fn cons(&self, elem: T) -> Self {
    List(Rc::new(ListNode::Cons(elem, List(self.0.clone()))))
  }

  /// Looks up a de Bruijn index in the list.
  ///
  /// De Bruijn index 0 refers to the most recently added element (head),
  /// index 1 refers to the next, etc.
  pub fn lookup(&self, idx: usize) -> Option<&T> {
    let mut current = &*self.0;
    let mut i = idx;

    loop {
      match current {
        ListNode::Nil => return None,
        ListNode::Cons(elem, rest) => {
          if i == 0 {
            return Some(elem);
          }
          i -= 1;
          current = &*rest.0;
        },
      }
    }
  }
}

impl<T> Default for List<T> {
  fn default() -> Self {
    Self::new()
  }
}

// ============================================================================
// Environment
// ============================================================================

/// A de Bruijn environment containing both value thunks and universe levels.
#[derive(Debug, Clone)]
pub struct Env {
  /// Value environment (de Bruijn indexed thunks).
  pub values: List<Thunk>,
  /// Level environment (de Bruijn indexed universe levels).
  pub levels: List<Level>,
}

impl Env {
  /// Creates an empty environment.
  pub fn new() -> Self {
    Env { values: List::new(), levels: List::new() }
  }

  /// Extends the value environment with a new thunk.
  pub fn cons_value(&self, thunk: Thunk) -> Self {
    Env { values: self.values.cons(thunk), levels: self.levels.clone() }
  }

  /// Extends the level environment with a new level.
  pub fn cons_level(&self, level: Level) -> Self {
    Env { values: self.values.clone(), levels: self.levels.cons(level) }
  }

  /// Looks up a value by de Bruijn index.
  pub fn lookup_value(&self, idx: usize) -> Option<&Thunk> {
    self.values.lookup(idx)
  }

  /// Looks up a level by de Bruijn index.
  pub fn lookup_level(&self, idx: usize) -> Option<&Level> {
    self.levels.lookup(idx)
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

/// Internal node structure for a neutral value.
///
/// Neutral (or "stuck") values arise when we try to reduce an expression
/// that depends on a free variable. These are values that cannot reduce
/// further because they're waiting on an unknown.
#[derive(Debug)]
pub enum NeutralNode {
  /// A free variable (stuck).
  Fvar(usize),
  /// A neutral value applied to a thunk (lazy argument).
  /// This is the "stuck application" - the head is neutral (contains a free variable).
  App(Neutral, Thunk),
  /// Projection from a neutral value.
  Proj(usize, usize, Neutral),
}

/// A neutral value represents a stuck computation.
///
/// Wraps `Rc<NeutralNode>` so that cloning is cheap (just incrementing a reference count).
#[derive(Debug, Clone)]
pub struct Neutral(pub Rc<NeutralNode>);

impl From<NeutralNode> for Neutral {
  fn from(node: NeutralNode) -> Self {
    Neutral(Rc::new(node))
  }
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
  Const(usize, Vec<Level>),
}

/// A value is what an expression reduces to.
///
/// Values are in weak head normal form (WHNF) - reduced enough to inspect
/// the head constructor, but arguments may not be fully normalized.
/// Wraps `Rc<ValueNode>` so that cloning is cheap (just incrementing a reference count).
#[derive(Debug, Clone)]
pub struct Value(pub Rc<ValueNode>);

impl From<ValueNode> for Value {
  fn from(node: ValueNode) -> Self {
    Value(Rc::new(node))
  }
}

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
pub fn force(thunk: &Thunk, toplevel: &Toplevel) -> Value {
  // Need to evaluate - extract expr and env
  let node = thunk.0.borrow();
  let (expr, env) = {
    match &*node {
      ThunkNode::Suspended(expr, env) => (expr, env),
      ThunkNode::Forced(value) => return value.clone(),
    }
  };

  // Evaluate the expression with the thunk's captured environment
  let value = eval(expr, env, toplevel);
  drop(node);

  // Memoize: update the thunk to store the computed value
  *thunk.0.borrow_mut() = ThunkNode::Forced(value.clone());

  value
}

// ============================================================================
// Level Reduction
// ============================================================================

/// Reduces a universe level to normal form.
///
/// Level reduction implements:
/// - `Max(a, b)`: Maximum of two levels
/// - `IMax(a, b)`: Impredicative maximum (like Max if b is Succ, but Zero if b is Zero)
/// - `Param(idx)`: Lookup in level environment by de Bruijn index
pub fn level_reduce(level: &Level, env: &Env) -> Level {
  match level.0.as_ref() {
    LevelNode::Zero => LevelNode::Zero.into(),

    LevelNode::Succ(l) => {
      let reduced = level_reduce(l, env);
      LevelNode::Succ(reduced).into()
    },

    LevelNode::Max(l1, l2) => {
      let r1 = level_reduce(l1, env);
      let r2 = level_reduce(l2, env);
      level_max(&r1, &r2)
    },

    LevelNode::Imax(l1, l2) => {
      let r1 = level_reduce(l1, env);
      let r2 = level_reduce(l2, env);
      level_imax(&r1, &r2)
    },

    LevelNode::Param(idx) => {
      // Look up the parameter in the level environment
      match env.lookup_level(*idx) {
        Some(level) => level.clone(),
        // Unbound level parameter - should never happen in well-formed terms
        None => panic!("Unbound level parameter: {}", idx),
      }
    },
  }
}

/// Helper: Check if a level is definitely not zero.
///
/// Returns true if the level is guaranteed to be non-zero.
/// This is used for imax simplification.
fn is_not_zero(l: &Level) -> bool {
  match l.0.as_ref() {
    LevelNode::Zero | LevelNode::Param(_) => false,
    LevelNode::Succ(_) => true,
    LevelNode::Max(lhs, rhs) => is_not_zero(lhs) || is_not_zero(rhs),
    LevelNode::Imax(_, rhs) => is_not_zero(rhs), // Only check rhs for imax
  }
}

/// Helper: Convert (succ^k l) into (l, k). If l is not a succ, return (l, 0).
fn to_offset(mut l: Level) -> (Level, usize) {
  let mut k = 0;
  while let LevelNode::Succ(inner) = l.0.as_ref() {
    l = inner.clone();
    k += 1;
  }
  (l, k)
}

/// Computes the maximum of two reduced levels.
fn level_max(l1: &Level, l2: &Level) -> Level {
  // Check for explicit levels (concrete numbers)
  if is_explicit(l1) && is_explicit(l2) {
    let d1 = to_offset(l1.clone()).1;
    let d2 = to_offset(l2.clone()).1;
    return if d1 >= d2 { l1.clone() } else { l2.clone() };
  }

  // max(u, u) = u
  if l1 == l2 {
    return l1.clone();
  }

  match (l1.0.as_ref(), l2.0.as_ref()) {
    // max(0, l) = l
    (LevelNode::Zero, _) => l2.clone(),
    // max(l, 0) = l
    (_, LevelNode::Zero) => l1.clone(),

    // Subsumption: if l2 == max(l1, l'), then max(l1, l2) = l2
    (_, LevelNode::Max(l2_lhs, l2_rhs)) if l1 == l2_lhs || l1 == l2_rhs => {
      l2.clone()
    },

    // Subsumption: if l1 == max(l2, l'), then max(l1, l2) = l1
    (LevelNode::Max(l1_lhs, l1_rhs), _) if l2 == l1_lhs || l2 == l1_rhs => {
      l1.clone()
    },

    // Otherwise check if they have the same base (after stripping succs)
    _ => {
      let (base1, offset1) = to_offset(l1.clone());
      let (base2, offset2) = to_offset(l2.clone());

      if base1 == base2 {
        // Same base, return the one with larger offset
        if offset1 > offset2 { l1.clone() } else { l2.clone() }
      } else {
        // Different bases, create Max node
        LevelNode::Max(l1.clone(), l2.clone()).into()
      }
    },
  }
}

/// Helper: Check if a level is explicit (concrete number).
fn is_explicit(l: &Level) -> bool {
  match l.0.as_ref() {
    LevelNode::Zero => true,
    LevelNode::Succ(inner) => is_explicit(inner),
    _ => false,
  }
}

/// Computes the impredicative maximum of two reduced levels.
///
/// IMax is like Max when the second argument is definitely non-zero,
/// but reduces to Zero when the second argument is Zero.
/// This is used for universe-polymorphic definitions in Prop.
fn level_imax(l1: &Level, l2: &Level) -> Level {
  // If we can prove l2 is not zero, convert to max
  if is_not_zero(l2) {
    return level_max(l1, l2);
  }

  // imax(u, 0) = 0 for any u
  if matches!(l2.0.as_ref(), LevelNode::Zero) {
    return l2.clone();
  }

  // imax(0, u) = u for any u
  // imax(1, u) = u for any u
  if matches!(l1.0.as_ref(), LevelNode::Zero) {
    return l2.clone();
  }
  if is_one(l1) {
    return l2.clone();
  }

  // imax(u, u) = u
  if l1 == l2 {
    return l1.clone();
  }

  // Can't reduce further
  LevelNode::Imax(l1.clone(), l2.clone()).into()
}

/// Helper: Check if a level is exactly one (succ(zero)).
fn is_one(l: &Level) -> bool {
  match l.0.as_ref() {
    LevelNode::Succ(inner) => matches!(inner.0.as_ref(), LevelNode::Zero),
    _ => false,
  }
}

// ============================================================================
// Evaluation
// ============================================================================

/// Evaluates an expression in an environment to a value.
///
/// This performs weak head normalization - it reduces the expression
/// until the head constructor is visible, but doesn't normalize under
/// binders or reduce arguments.
pub fn eval(expr: &Expr, env: &Env, toplevel: &Toplevel) -> Value {
  match expr.0.as_ref() {
    ExprNode::Bvar(idx) => {
      // Look up the de Bruijn index in the environment and force the thunk
      match env.lookup_value(*idx) {
        Some(thunk) => force(thunk, toplevel),
        // Unbound de Bruijn index - should never happen in well-formed terms
        None => panic!("Unbound de Bruijn index: {}", idx),
      }
    },

    ExprNode::Fvar(idx) => {
      // Free variables are always stuck
      ValueNode::Neutral(NeutralNode::Fvar(*idx).into()).into()
    },

    ExprNode::Sort(level) => {
      // Reduce the universe level
      let reduced_level = level_reduce(level, env);
      ValueNode::Sort(reduced_level).into()
    },

    ExprNode::Const(idx, levels) => {
      // Look up the constant in the toplevel environment
      match toplevel.constants.get(*idx) {
        None => panic!("Unbound constant {}", idx),
        Some(ConstantInfo::DefnInfo(defn))
          if defn.hints != ReducibilityHints::Opaque =>
        {
          // Unfold abbreviations and regular definitions
          // Evaluate the body in an empty environment (definitions are closed terms)
          eval(&defn.value, &Env::new(), toplevel)
        },
        // Axioms, quotients, inductives, constructors, recursors: no body to unfold
        // Opaques are never unfolded. Theorems are proof-irrelevant.
        _ => ValueNode::Const(*idx, levels.clone()).into(),
      }
    },

    ExprNode::App(fun, arg) => {
      // Application: evaluate function, suspend argument (lazy evaluation)
      let vfun = eval(fun, env, toplevel);
      let arg_thunk = suspend(arg.clone(), env.clone());
      apply(&vfun, arg_thunk, toplevel)
    },

    ExprNode::Lam(name, ty, body, binder_info) => {
      // Lambda evaluates to a closure capturing the current environment
      // Type is suspended as a thunk
      let ty_thunk = suspend(ty.clone(), env.clone());
      ValueNode::Fun(
        name.clone(),
        ty_thunk,
        body.clone(),
        env.clone(),
        binder_info.clone(),
      )
      .into()
    },

    ExprNode::ForallE(name, ty, body, binder_info) => {
      // Forall evaluates to a dependent function type value (type is suspended)
      let ty_thunk = suspend(ty.clone(), env.clone());
      ValueNode::Forall(
        name.clone(),
        ty_thunk,
        body.clone(),
        env.clone(),
        binder_info.clone(),
      )
      .into()
    },

    ExprNode::LetE(_name, _ty, val, body, _non_dep) => {
      // Let-binding: suspend the bound value (lazy evaluation)
      let thunk = suspend(val.clone(), env.clone());
      let new_env = env.cons_value(thunk);
      eval(body, &new_env, toplevel)
    },

    ExprNode::Lit(lit) => {
      // Literals are already values
      ValueNode::Lit(lit.clone()).into()
    },

    ExprNode::Proj(type_idx, field_idx, e) => {
      let v = eval(e, env, toplevel);
      match v.0.as_ref() {
        ValueNode::Neutral(n) => {
          // Projection from a neutral value is stuck
          ValueNode::Neutral(
            NeutralNode::Proj(*type_idx, *field_idx, n.clone()).into(),
          )
          .into()
        },
        // In a full implementation with inductive types, we'd handle
        // projections from fully-applied constructors here
        _ => {
          // For now, we don't have enough information to reduce projections
          // In practice, you'd need to know the structure definition
          // to extract the field. Treating as neutral is conservative.
          ValueNode::Neutral(
            NeutralNode::Proj(
              *type_idx,
              *field_idx,
              NeutralNode::Fvar(0).into(), // placeholder neutral head
            )
            .into(),
          )
          .into()
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
pub fn apply(fun: &Value, arg_thunk: Thunk, toplevel: &Toplevel) -> Value {
  match fun.0.as_ref() {
    ValueNode::Fun(_name, _ty, body, env, _binder_info) => {
      // Beta reduction: extend the closure's environment with the suspended thunk
      // The argument will only be evaluated when/if it's actually used
      let new_env = env.cons_value(arg_thunk);
      eval(body, &new_env, toplevel)
    },

    ValueNode::Neutral(n) => {
      // Application to a neutral value creates a stuck application
      // Keep the argument as a thunk (lazy evaluation)
      ValueNode::Neutral(NeutralNode::App(n.clone(), arg_thunk).into()).into()
    },

    // Other values cannot be applied (would be a type error in well-typed terms)
    // In a well-typed program, we should never apply a non-function value
    // TODO: Implement recursor reduction (iota reduction)
    _ => {
      // Conservative fallback: treat as a stuck application
      // Keep the argument as a thunk
      ValueNode::Neutral(
        NeutralNode::App(NeutralNode::Fvar(0).into(), arg_thunk).into(),
      )
      .into()
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
pub fn quote(val: &Value, level: usize, toplevel: &Toplevel) -> Expr {
  match val.0.as_ref() {
    ValueNode::Neutral(n) => quote_neutral(n, level, toplevel),

    ValueNode::Fun(name, ty_thunk, body, env, binder_info) => {
      // Quote a lambda: force and quote the type, then quote the body
      let ty_val = force(ty_thunk, toplevel);
      let quoted_ty = quote(&ty_val, level, toplevel);
      // Create a fresh variable thunk and quote the body
      let fresh_thunk = Thunk::forced(
        ValueNode::Neutral(NeutralNode::Fvar(level).into()).into(),
      );
      let new_env = env.cons_value(fresh_thunk);
      let body_val = eval(body, &new_env, toplevel);
      let quoted_body = quote(&body_val, level + 1, toplevel);
      ExprNode::Lam(name.clone(), quoted_ty, quoted_body, binder_info.clone())
        .into()
    },

    ValueNode::Sort(level) => ExprNode::Sort(level.clone()).into(),

    ValueNode::Forall(name, ty_thunk, body, env, binder_info) => {
      // Force the type thunk and quote it
      let ty_val = force(ty_thunk, toplevel);
      let quoted_ty = quote(&ty_val, level, toplevel);
      // Evaluate body under a fresh variable thunk
      let fresh_thunk = Thunk::forced(
        ValueNode::Neutral(NeutralNode::Fvar(level).into()).into(),
      );
      let new_env = env.cons_value(fresh_thunk);
      let body_val = eval(body, &new_env, toplevel);
      let quoted_body = quote(&body_val, level + 1, toplevel);
      ExprNode::ForallE(
        name.clone(),
        quoted_ty,
        quoted_body,
        binder_info.clone(),
      )
      .into()
    },

    ValueNode::Lit(lit) => ExprNode::Lit(lit.clone()).into(),

    ValueNode::Const(idx, levels) => {
      ExprNode::Const(*idx, levels.clone()).into()
    },
  }
}

/// Quotes a neutral value back to an expression.
fn quote_neutral(neutral: &Neutral, level: usize, toplevel: &Toplevel) -> Expr {
  match neutral.0.as_ref() {
    NeutralNode::Fvar(idx) => ExprNode::Fvar(*idx).into(),

    NeutralNode::App(fun, arg_thunk) => {
      let quoted_fun = quote_neutral(fun, level, toplevel);
      // Force the thunk to get the value, then quote it
      let arg_val = force(arg_thunk, toplevel);
      let quoted_arg = quote(&arg_val, level, toplevel);
      ExprNode::App(quoted_fun, quoted_arg).into()
    },

    NeutralNode::Proj(type_idx, field_idx, e) => {
      let quoted_e = quote_neutral(e, level, toplevel);
      ExprNode::Proj(*type_idx, *field_idx, quoted_e).into()
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
pub fn normalize(expr: &Expr, toplevel: &Toplevel) -> Expr {
  let val = eval(expr, &Env::new(), toplevel);
  quote(&val, 0, toplevel)
}

/// Reduces an expression to weak head normal form (WHNF).
///
/// This only reduces until the head constructor is visible,
/// without normalizing under binders or in arguments.
pub fn whnf(expr: &Expr, toplevel: &Toplevel) -> Value {
  eval(expr, &Env::new(), toplevel)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_identity_normalization() {
    // Create identity function: λx. x
    let identity = ExprNode::Lam(
      Name::Anonymous,
      ExprNode::Sort(LevelNode::Zero.into()).into(),
      ExprNode::Bvar(0).into(),
      BinderInfo::Default,
    )
    .into();

    // Create an empty toplevel (no constants)
    let toplevel = Toplevel { constants: vec![] };

    // Normalize should preserve it
    let normalized = normalize(&identity, &toplevel);

    // Should still be a lambda
    match normalized.0.as_ref() {
      ExprNode::Lam(_, _, _, _) => {},
      _ => panic!("Expected lambda"),
    }
  }

  #[test]
  fn test_definition_unfolding() {
    use crate::lean::nat::Nat;

    // Create a constant that is an abbreviation for a natural number literal
    // def myConst : Nat := 42
    let nat_type = ExprNode::Const(1, vec![]).into(); // Assume Nat is at index 1
    let nat_val = ExprNode::Lit(Literal::NatVal(Nat::from(42u64))).into();

    let defn = ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: Name::Str(Rc::new(Name::Anonymous), "myConst".to_string()),
        level_params: vec![],
        typ: nat_type,
      },
      value: nat_val,
      hints: ReducibilityHints::Abbrev, // Should always unfold
      safety: DefinitionSafety::Safe,
      all: vec![],
    });

    // Create toplevel with our definition at index 0
    let toplevel = Toplevel { constants: vec![defn] };

    // Reference to our constant
    let const_ref = ExprNode::Const(0, vec![]).into();

    // Normalize should unfold the abbreviation
    let normalized = normalize(&const_ref, &toplevel);

    // Should be the literal value
    match normalized.0.as_ref() {
      ExprNode::Lit(Literal::NatVal(n)) => {
        assert_eq!(n.to_u64(), Some(42));
      },
      _ => panic!("Expected literal nat value, got {:?}", normalized),
    }
  }

  #[test]
  fn test_opaque_not_unfolded() {
    use crate::lean::nat::Nat;

    // Create an opaque constant
    // opaque myOpaque : Nat := 42
    let nat_type = ExprNode::Const(1, vec![]).into();
    let nat_val = ExprNode::Lit(Literal::NatVal(Nat::from(42u64))).into();

    let opaque = ConstantInfo::OpaqueInfo(OpaqueVal {
      cnst: ConstantVal {
        name: Name::Str(Rc::new(Name::Anonymous), "myOpaque".to_string()),
        level_params: vec![],
        typ: nat_type,
      },
      value: nat_val,
      is_unsafe: false,
      all: vec![],
    });

    // Create toplevel with our opaque at index 0
    let toplevel = Toplevel { constants: vec![opaque] };

    // Reference to our opaque constant
    let const_ref = ExprNode::Const(0, vec![]).into();

    // Normalize should NOT unfold the opaque
    let normalized = normalize(&const_ref, &toplevel);

    // Should still be a constant reference
    match normalized.0.as_ref() {
      ExprNode::Const(idx, _) => {
        assert_eq!(*idx, 0);
      },
      _ => panic!("Expected constant reference, got {:?}", normalized),
    }
  }

  #[test]
  fn test_theorem_not_unfolded() {
    use crate::lean::nat::Nat;

    // Create a theorem
    // theorem myTheorem : Nat := 42
    let nat_type = ExprNode::Const(1, vec![]).into();
    let nat_val = ExprNode::Lit(Literal::NatVal(Nat::from(42u64))).into();

    let theorem = ConstantInfo::ThmInfo(TheoremVal {
      cnst: ConstantVal {
        name: Name::Str(Rc::new(Name::Anonymous), "myTheorem".to_string()),
        level_params: vec![],
        typ: nat_type,
      },
      value: nat_val,
      all: vec![],
    });

    // Create toplevel with our theorem at index 0
    let toplevel = Toplevel { constants: vec![theorem] };

    // Reference to our theorem
    let const_ref = ExprNode::Const(0, vec![]).into();

    // Normalize should NOT unfold theorems (proof irrelevance)
    let normalized = normalize(&const_ref, &toplevel);

    // Should still be a constant reference
    match normalized.0.as_ref() {
      ExprNode::Const(idx, _) => {
        assert_eq!(*idx, 0);
      },
      _ => panic!("Expected constant reference, got {:?}", normalized),
    }
  }

  #[test]
  fn test_level_max_reduction() {
    // max(0, 1) = 1
    let zero: Level = LevelNode::Zero.into();
    let one: Level = LevelNode::Succ(zero.clone()).into();
    let max_0_1: Level = LevelNode::Max(zero.clone(), one.clone()).into();

    let reduced = level_reduce(&max_0_1, &Env::new());
    assert_eq!(reduced, one);

    // max(1, 0) = 1
    let max_1_0: Level = LevelNode::Max(one.clone(), zero.clone()).into();
    let reduced = level_reduce(&max_1_0, &Env::new());
    assert_eq!(reduced, one);

    // max(succ(a), succ(b)) = succ(max(a, b))
    let two: Level = LevelNode::Succ(one.clone()).into();
    let three: Level = LevelNode::Succ(two.clone()).into();
    let max_2_3: Level = LevelNode::Max(two.clone(), three.clone()).into();
    let reduced = level_reduce(&max_2_3, &Env::new());
    assert_eq!(reduced, three);
  }

  #[test]
  fn test_level_imax_reduction() {
    // imax(a, 0) = 0 (impredicativity)
    let zero: Level = LevelNode::Zero.into();
    let one: Level = LevelNode::Succ(zero.clone()).into();
    let imax_1_0: Level = LevelNode::Imax(one.clone(), zero.clone()).into();

    let reduced = level_reduce(&imax_1_0, &Env::new());
    assert_eq!(reduced, zero);

    // imax(0, succ(b)) = succ(b)
    let imax_0_1: Level = LevelNode::Imax(zero.clone(), one.clone()).into();
    let reduced = level_reduce(&imax_0_1, &Env::new());
    assert_eq!(reduced, one);

    // imax(succ(a), succ(b)) = succ(max(a, b))
    let two: Level = LevelNode::Succ(one.clone()).into();
    let imax_1_2: Level = LevelNode::Imax(one.clone(), two.clone()).into();
    let reduced = level_reduce(&imax_1_2, &Env::new());
    assert_eq!(reduced, two);
  }

  #[test]
  fn test_sort_reduction() {
    // Sort with max(0, 1) should reduce to Sort 1
    let zero: Level = LevelNode::Zero.into();
    let one: Level = LevelNode::Succ(zero.clone()).into();
    let max_0_1: Level = LevelNode::Max(zero, one.clone()).into();

    let sort_expr = ExprNode::Sort(max_0_1).into();
    let toplevel = Toplevel { constants: vec![] };

    let normalized = normalize(&sort_expr, &toplevel);

    match normalized.0.as_ref() {
      ExprNode::Sort(level) => {
        assert_eq!(*level, one);
      },
      _ => panic!("Expected sort, got {:?}", normalized),
    }
  }

  #[test]
  fn test_level_param_lookup() {
    // Create an environment with two level parameters
    // levels[0] = 1, levels[1] = 2
    let zero: Level = LevelNode::Zero.into();
    let one: Level = LevelNode::Succ(zero.clone()).into();
    let two: Level = LevelNode::Succ(one.clone()).into();

    let env = Env::new()
      .cons_level(one.clone())  // levels[0] = 1
      .cons_level(two.clone()); // levels[1] = 2

    // Param(0) should reduce to 2 (most recent)
    let param_0: Level = LevelNode::Param(0).into();
    let reduced = level_reduce(&param_0, &env);
    assert_eq!(reduced, two);

    // Param(1) should reduce to 1
    let param_1: Level = LevelNode::Param(1).into();
    let reduced = level_reduce(&param_1, &env);
    assert_eq!(reduced, one);

    // Max(Param(0), Param(1)) = max(2, 1) = 2
    let max_params: Level =
      LevelNode::Max(param_0.clone(), param_1.clone()).into();
    let reduced = level_reduce(&max_params, &env);
    assert_eq!(reduced, two);
  }

  #[test]
  fn test_level_max_subsumption() {
    let zero: Level = LevelNode::Zero.into();
    let one: Level = LevelNode::Succ(zero.clone()).into();
    let two: Level = LevelNode::Succ(one.clone()).into();
    let param: Level = LevelNode::Param(0).into();

    // If l2 = max(l1, x), then max(l1, l2) = l2
    let max_one_two: Level = LevelNode::Max(one.clone(), two.clone()).into();
    let reduced = level_max(&one, &max_one_two);
    assert_eq!(reduced, max_one_two);

    // If l1 = max(l2, x), then max(l1, l2) = l1
    let max_two_param: Level =
      LevelNode::Max(two.clone(), param.clone()).into();
    let reduced = level_max(&max_two_param, &two);
    assert_eq!(reduced, max_two_param);

    // Same base with different offsets: max(succ^2(u), succ^3(u)) = succ^3(u)
    let succ2_param: Level =
      LevelNode::Succ(LevelNode::Succ(param.clone()).into()).into();
    let succ3_param: Level = LevelNode::Succ(succ2_param.clone()).into();
    let reduced = level_max(&succ2_param, &succ3_param);
    assert_eq!(reduced, succ3_param);
  }

  #[test]
  fn test_imax_with_not_zero() {
    let zero: Level = LevelNode::Zero.into();
    let one: Level = LevelNode::Succ(zero.clone()).into();
    let two: Level = LevelNode::Succ(one.clone()).into();

    // imax(1, succ(v)) = max(1, succ(v)) because succ is definitely not zero
    let imax_one_two: Level = LevelNode::Imax(one.clone(), two.clone()).into();
    let reduced = level_reduce(&imax_one_two, &Env::new());
    // Should convert to max, which should reduce to two (since both are explicit)
    assert_eq!(reduced, two);

    // imax(1, max(v, w)) where one is not zero should convert to max
    let max_one_two: Level = LevelNode::Max(one.clone(), two.clone()).into();
    let imax_one_max: Level =
      LevelNode::Imax(one.clone(), max_one_two.clone()).into();
    let reduced = level_reduce(&imax_one_max, &Env::new());
    // Should convert to max(1, max(1, 2)) which reduces to 2
    // because max(1, 2) = 2 (both explicit), and max(1, 2) = 2
    assert_eq!(reduced, two);
  }

  #[test]
  fn test_imax_special_cases() {
    let zero: Level = LevelNode::Zero.into();
    let one: Level = LevelNode::Succ(zero.clone()).into();
    let two: Level = LevelNode::Succ(one.clone()).into();

    // imax(1, 0) = 0
    let imax_one_zero: Level =
      LevelNode::Imax(one.clone(), zero.clone()).into();
    let reduced = level_reduce(&imax_one_zero, &Env::new());
    assert_eq!(reduced, zero);

    // imax(0, 1) = 1
    let imax_zero_one: Level =
      LevelNode::Imax(zero.clone(), one.clone()).into();
    let reduced = level_reduce(&imax_zero_one, &Env::new());
    assert_eq!(reduced, one);

    // imax(1, 1) = 1
    let imax_one_one: Level = LevelNode::Imax(one.clone(), one.clone()).into();
    let reduced = level_reduce(&imax_one_one, &Env::new());
    assert_eq!(reduced, one);

    // imax(1, 2) = max(1, 2) = 2 (because 2 is not zero)
    let imax_one_two: Level = LevelNode::Imax(one.clone(), two.clone()).into();
    let reduced = level_reduce(&imax_one_two, &Env::new());
    assert_eq!(reduced, two);
  }
}
