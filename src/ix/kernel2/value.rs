//! Semantic value domain for NbE.
//!
//! `Val` is the core semantic type used during type checking. It represents
//! expressions in evaluated form, with closures for lambda/pi, lazy thunks
//! for spine arguments, and de Bruijn levels for free variables.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use crate::ix::address::Address;
use crate::ix::env::{BinderInfo, Literal, Name};
use crate::lean::nat::Nat;

use super::types::{KExpr, KLevel, MetaMode};

// ============================================================================
// Thunk — call-by-need lazy evaluation
// ============================================================================

/// A lazy thunk that is either unevaluated (expr + env closure) or evaluated.
#[derive(Debug)]
pub enum ThunkEntry<M: MetaMode> {
  Unevaluated { expr: KExpr<M>, env: Vec<Val<M>> },
  Evaluated(Val<M>),
}

/// A reference-counted, mutable thunk for call-by-need evaluation.
pub type Thunk<M> = Rc<RefCell<ThunkEntry<M>>>;

/// Create a new unevaluated thunk.
pub fn mk_thunk<M: MetaMode>(expr: KExpr<M>, env: Vec<Val<M>>) -> Thunk<M> {
  Rc::new(RefCell::new(ThunkEntry::Unevaluated { expr, env }))
}

/// Create a thunk that is already evaluated.
pub fn mk_thunk_val<M: MetaMode>(val: Val<M>) -> Thunk<M> {
  Rc::new(RefCell::new(ThunkEntry::Evaluated(val)))
}

/// Check if a thunk has been evaluated.
pub fn is_thunk_evaluated<M: MetaMode>(thunk: &Thunk<M>) -> bool {
  matches!(&*thunk.borrow(), ThunkEntry::Evaluated(_))
}

/// Peek at a thunk's entry without forcing it.
pub fn peek_thunk<M: MetaMode>(thunk: &Thunk<M>) -> ThunkEntry<M> {
  match &*thunk.borrow() {
    ThunkEntry::Unevaluated { expr, env } => ThunkEntry::Unevaluated {
      expr: expr.clone(),
      env: env.clone(),
    },
    ThunkEntry::Evaluated(v) => ThunkEntry::Evaluated(v.clone()),
  }
}

// ============================================================================
// Val — semantic values
// ============================================================================

/// A semantic value in the NbE domain.
///
/// Uses `Rc` for O(1) clone and stable pointer identity (for caching).
#[derive(Clone, Debug)]
pub struct Val<M: MetaMode>(pub Rc<ValInner<M>>);

/// The inner data of a semantic value.
#[derive(Debug)]
pub enum ValInner<M: MetaMode> {
  /// Lambda closure: evaluated domain, unevaluated body with environment.
  Lam {
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
    dom: Val<M>,
    body: KExpr<M>,
    env: Vec<Val<M>>,
  },
  /// Pi/forall closure: evaluated domain, unevaluated body with environment.
  Pi {
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
    dom: Val<M>,
    body: KExpr<M>,
    env: Vec<Val<M>>,
  },
  /// Universe sort.
  Sort(KLevel<M>),
  /// A stuck/neutral term: either a free variable or unresolved constant,
  /// with a spine of lazily-evaluated arguments.
  Neutral { head: Head<M>, spine: Vec<Thunk<M>> },
  /// A constructor application with lazily-evaluated arguments.
  Ctor {
    addr: Address,
    levels: Vec<KLevel<M>>,
    name: M::Field<Name>,
    cidx: usize,
    num_params: usize,
    num_fields: usize,
    induct_addr: Address,
    spine: Vec<Thunk<M>>,
  },
  /// A literal value (nat or string).
  Lit(Literal),
  /// A stuck projection with lazily-evaluated struct and spine.
  Proj {
    type_addr: Address,
    idx: usize,
    strct: Thunk<M>,
    type_name: M::Field<Name>,
    spine: Vec<Thunk<M>>,
  },
}

/// The head of a neutral term.
#[derive(Debug)]
pub enum Head<M: MetaMode> {
  /// A free variable at de Bruijn level, carrying its type.
  FVar { level: usize, ty: Val<M> },
  /// An unresolved constant reference.
  Const {
    addr: Address,
    levels: Vec<KLevel<M>>,
    name: M::Field<Name>,
  },
}

impl<M: MetaMode> Val<M> {
  pub fn inner(&self) -> &ValInner<M> {
    &self.0
  }

  /// Returns the pointer identity for caching.
  pub fn ptr_id(&self) -> usize {
    Rc::as_ptr(&self.0) as usize
  }

  /// Check pointer equality between two Vals.
  pub fn ptr_eq(&self, other: &Val<M>) -> bool {
    Rc::ptr_eq(&self.0, &other.0)
  }

  // -- Smart constructors ---------------------------------------------------

  pub fn mk_sort(level: KLevel<M>) -> Self {
    Val(Rc::new(ValInner::Sort(level)))
  }

  pub fn mk_lit(l: Literal) -> Self {
    Val(Rc::new(ValInner::Lit(l)))
  }

  pub fn mk_const(
    addr: Address,
    levels: Vec<KLevel<M>>,
    name: M::Field<Name>,
  ) -> Self {
    Val(Rc::new(ValInner::Neutral {
      head: Head::Const {
        addr,
        levels,
        name,
      },
      spine: Vec::new(),
    }))
  }

  pub fn mk_fvar(level: usize, ty: Val<M>) -> Self {
    Val(Rc::new(ValInner::Neutral {
      head: Head::FVar { level, ty },
      spine: Vec::new(),
    }))
  }

  pub fn mk_lam(
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
    dom: Val<M>,
    body: KExpr<M>,
    env: Vec<Val<M>>,
  ) -> Self {
    Val(Rc::new(ValInner::Lam {
      name,
      bi,
      dom,
      body,
      env,
    }))
  }

  pub fn mk_pi(
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
    dom: Val<M>,
    body: KExpr<M>,
    env: Vec<Val<M>>,
  ) -> Self {
    Val(Rc::new(ValInner::Pi {
      name,
      bi,
      dom,
      body,
      env,
    }))
  }

  pub fn mk_ctor(
    addr: Address,
    levels: Vec<KLevel<M>>,
    name: M::Field<Name>,
    cidx: usize,
    num_params: usize,
    num_fields: usize,
    induct_addr: Address,
    spine: Vec<Thunk<M>>,
  ) -> Self {
    Val(Rc::new(ValInner::Ctor {
      addr,
      levels,
      name,
      cidx,
      num_params,
      num_fields,
      induct_addr,
      spine,
    }))
  }

  pub fn mk_neutral(head: Head<M>, spine: Vec<Thunk<M>>) -> Self {
    Val(Rc::new(ValInner::Neutral { head, spine }))
  }

  pub fn mk_proj(
    type_addr: Address,
    idx: usize,
    strct: Thunk<M>,
    type_name: M::Field<Name>,
    spine: Vec<Thunk<M>>,
  ) -> Self {
    Val(Rc::new(ValInner::Proj {
      type_addr,
      idx,
      strct,
      type_name,
      spine,
    }))
  }

  // -- Accessors ------------------------------------------------------------

  /// If this is a sort, return its level.
  pub fn sort_level(&self) -> Option<&KLevel<M>> {
    match self.inner() {
      ValInner::Sort(l) => Some(l),
      _ => None,
    }
  }

  pub fn is_sort(&self) -> bool {
    matches!(self.inner(), ValInner::Sort(_))
  }

  pub fn is_pi(&self) -> bool {
    matches!(self.inner(), ValInner::Pi { .. })
  }

  pub fn is_lam(&self) -> bool {
    matches!(self.inner(), ValInner::Lam { .. })
  }

  /// If this is a neutral with a const head, return the address.
  pub fn const_addr(&self) -> Option<&Address> {
    match self.inner() {
      ValInner::Neutral {
        head: Head::Const { addr, .. },
        ..
      } => Some(addr),
      ValInner::Ctor { addr, .. } => Some(addr),
      _ => None,
    }
  }

  /// Get the universe levels from a neutral const head.
  pub fn head_levels(&self) -> Option<&[KLevel<M>]> {
    match self.inner() {
      ValInner::Neutral {
        head: Head::Const { levels, .. },
        ..
      } => Some(levels),
      _ => None,
    }
  }

  /// Get the spine of a neutral, ctor, or proj.
  pub fn spine(&self) -> Option<&[Thunk<M>]> {
    match self.inner() {
      ValInner::Neutral { spine, .. }
      | ValInner::Ctor { spine, .. }
      | ValInner::Proj { spine, .. } => Some(spine),
      _ => None,
    }
  }

  /// Extract a natural number value from a literal or zero ctor.
  pub fn nat_val(&self) -> Option<&Nat> {
    match self.inner() {
      ValInner::Lit(Literal::NatVal(n)) => Some(n),
      _ => None,
    }
  }

  /// Extract a string value from a literal.
  pub fn str_val(&self) -> Option<&str> {
    match self.inner() {
      ValInner::Lit(Literal::StrVal(s)) => Some(s),
      _ => None,
    }
  }

  /// Check if two values have the same head constant address.
  pub fn same_head_const(&self, other: &Val<M>) -> bool {
    match (self.const_addr(), other.const_addr()) {
      (Some(a), Some(b)) => a == b,
      _ => false,
    }
  }
}

impl<M: MetaMode> fmt::Display for Val<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.inner() {
      ValInner::Lam { name, .. } => {
        write!(f, "(fun {:?} => ...)", name)
      }
      ValInner::Pi { name, dom, .. } => {
        write!(f, "(({:?} : {dom}) -> ...)", name)
      }
      ValInner::Sort(l) => write!(f, "Sort {l}"),
      ValInner::Neutral { head, spine } => {
        match head {
          Head::FVar { level, .. } => write!(f, "fvar@{level}")?,
          Head::Const { name, .. } => write!(f, "{:?}", name)?,
        }
        if !spine.is_empty() {
          write!(f, " ({}args)", spine.len())?;
        }
        Ok(())
      }
      ValInner::Ctor {
        name, spine, cidx, ..
      } => {
        write!(f, "ctor#{cidx}«{:?}»", name)?;
        if !spine.is_empty() {
          write!(f, " ({}args)", spine.len())?;
        }
        Ok(())
      }
      ValInner::Lit(Literal::NatVal(n)) => write!(f, "{n}"),
      ValInner::Lit(Literal::StrVal(s)) => write!(f, "\"{s}\""),
      ValInner::Proj {
        idx, type_name, ..
      } => {
        write!(f, "proj#{idx}«{:?}»", type_name)
      }
    }
  }
}
