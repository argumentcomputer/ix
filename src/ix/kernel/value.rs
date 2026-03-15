//! Semantic value domain for NbE.
//!
//! `Val` is the core semantic type used during type checking. It represents
//! expressions in evaluated form, with closures for lambda/pi, lazy thunks
//! for spine arguments, and de Bruijn levels for free variables.
//!
//! All types carry blake3 hashes for compositional structural fingerprinting,
//! enabling content-aware caching that catches structurally-equal values
//! regardless of allocation identity.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use crate::ix::address::Address;
use crate::ix::env::{BinderInfo, Literal, Name};
use crate::lean::nat::Nat;

use super::types::{
  KExpr, KLevel, MetaId, MetaMode,
  combine_hashes, hash_tag1, hash_tag2, hash_tag3,
  hash_levels, hash_literal,
};


// ============================================================================
// Env — COW (copy-on-write) closure environment with rolling blake3 hash
// ============================================================================

/// A copy-on-write closure environment with a rolling blake3 hash.
/// Uses `Rc<Vec<...>>` so that cloning an env for closure capture is O(1),
/// and extending it copies only when shared (matching Lean's Array.push COW).
/// The hash is updated O(1) on each push by combining with the new value's hash.
#[derive(Clone, Debug)]
pub struct Env<M: MetaMode> {
  vals: Rc<Vec<Val<M>>>,
  hash: M::HashVal,
}

impl<M: MetaMode> Env<M> {
  /// Get the hash of this environment.
  pub fn blake3_hash(&self) -> &M::HashVal {
    &self.hash
  }

  /// Get the underlying Rc for COW operations.
  pub fn vals_rc(&self) -> &Rc<Vec<Val<M>>> {
    &self.vals
  }

  /// Get the underlying Rc mutably for COW operations.
  pub fn vals_rc_mut(&mut self) -> &mut Rc<Vec<Val<M>>> {
    &mut self.vals
  }
}

/// Deref to slice for read access (.len(), .get(), .is_empty(), indexing, .iter()).
impl<M: MetaMode> std::ops::Deref for Env<M> {
  type Target = [Val<M>];
  fn deref(&self) -> &[Val<M>] {
    &self.vals
  }
}

/// Create an empty environment.
pub fn empty_env<M: MetaMode>() -> Env<M> {
  Env {
    vals: Rc::new(Vec::new()),
    hash: M::mk_hash(|| blake3::hash(b"empty_env")),
  }
}

/// Extend an environment with a new value (COW push).
/// If the Rc is unique, mutates in place. Otherwise clones first.
/// Hash is updated incrementally in O(1).
pub fn env_push<M: MetaMode>(env: &Env<M>, val: Val<M>) -> Env<M> {
  let env_hash = env.hash.clone();
  let val_hash = val.blake3_hash().clone();
  let new_hash = M::mk_hash(|| {
    combine_hashes(
      M::as_blake3(&env_hash).unwrap(),
      M::as_blake3(&val_hash).unwrap(),
    )
  });
  let mut new_vals = env.vals.clone();
  Rc::make_mut(&mut new_vals).push(val);
  Env { vals: new_vals, hash: new_hash }
}

/// Build an Env directly from a pre-built Vec (O(n), avoids Rc clone+make_mut per element).
pub fn env_from_vec<M: MetaMode>(vals: Vec<Val<M>>) -> Env<M> {
  let hash = M::mk_hash(|| {
    let mut h = blake3::Hasher::new();
    h.update(b"empty_env");
    for v in &vals {
      h.update(M::as_blake3(v.blake3_hash()).unwrap().as_bytes());
    }
    h.finalize()
  });
  Env { vals: Rc::new(vals), hash }
}

// ============================================================================
// Thunk — call-by-need lazy evaluation with blake3 hash
// ============================================================================

/// A lazy thunk that is either unevaluated (expr + env closure) or evaluated.
#[derive(Debug)]
pub enum ThunkEntry<M: MetaMode> {
  Unevaluated { expr: KExpr<M>, env: Env<M> },
  Evaluated(Val<M>),
}

/// Internal thunk node: immutable blake3 hash + mutable evaluation state.
#[derive(Debug)]
pub struct ThunkNode<M: MetaMode> {
  pub hash: M::HashVal,
  pub entry: RefCell<ThunkEntry<M>>,
}

/// A reference-counted, mutable thunk for call-by-need evaluation.
pub type Thunk<M> = Rc<ThunkNode<M>>;

/// Create a new unevaluated thunk.
/// Hash = blake3(expr.hash || env.hash).
pub fn mk_thunk<M: MetaMode>(expr: KExpr<M>, env: Env<M>) -> Thunk<M> {
  let expr_hash = expr.blake3_hash().clone();
  let env_hash = env.blake3_hash().clone();
  let hash = M::mk_hash(|| {
    combine_hashes(
      M::as_blake3(&expr_hash).unwrap(),
      M::as_blake3(&env_hash).unwrap(),
    )
  });
  Rc::new(ThunkNode {
    hash,
    entry: RefCell::new(ThunkEntry::Unevaluated { expr, env }),
  })
}

/// Create a thunk that is already evaluated.
/// Hash = val.hash.
pub fn mk_thunk_val<M: MetaMode>(val: Val<M>) -> Thunk<M> {
  let hash = val.blake3_hash().clone();
  Rc::new(ThunkNode {
    hash,
    entry: RefCell::new(ThunkEntry::Evaluated(val)),
  })
}

/// Check if a thunk has been evaluated.
pub fn is_thunk_evaluated<M: MetaMode>(thunk: &Thunk<M>) -> bool {
  matches!(&*thunk.entry.borrow(), ThunkEntry::Evaluated(_))
}

/// Peek at a thunk's entry without forcing it.
pub fn peek_thunk<M: MetaMode>(thunk: &Thunk<M>) -> ThunkEntry<M> {
  match &*thunk.entry.borrow() {
    ThunkEntry::Unevaluated { expr, env } => ThunkEntry::Unevaluated {
      expr: expr.clone(),
      env: env.clone(),
    },
    ThunkEntry::Evaluated(v) => ThunkEntry::Evaluated(v.clone()),
  }
}

/// Compute the combined blake3 hash of a spine of thunks.
pub fn hash_spine<M: MetaMode>(spine: &[Thunk<M>]) -> M::HashVal {
  M::mk_hash(|| hash_spine_raw::<M>(spine))
}

/// Raw blake3 hash of a spine (called inside mk_hash closures).
fn hash_spine_raw<M: MetaMode>(spine: &[Thunk<M>]) -> blake3::Hash {
  if spine.is_empty() {
    return blake3::hash(b"spine");
  }
  let mut h = blake3::Hasher::new();
  h.update(b"spine");
  for thunk in spine {
    h.update(M::as_blake3(&thunk.hash).unwrap().as_bytes());
  }
  h.finalize()
}

/// Raw blake3 hash of a Head (called inside mk_hash closures).
fn hash_head_raw<M: MetaMode>(head: &Head<M>) -> blake3::Hash {
  match head {
    Head::FVar { level, ty } => {
      let mut buf = [0u8; 41];
      buf[0] = 0;
      buf[1..9].copy_from_slice(&level.to_le_bytes());
      buf[9..41].copy_from_slice(M::as_blake3(ty.blake3_hash()).unwrap().as_bytes());
      blake3::hash(&buf)
    }
    Head::Const { id, levels } => {
      let lh = hash_levels(levels);
      let mut buf = [0u8; 65];
      buf[0] = 1;
      buf[1..33].copy_from_slice(id.addr.as_bytes());
      buf[33..65].copy_from_slice(lh.as_bytes());
      blake3::hash(&buf)
    }
  }
}

/// Combine two M::HashVal values using blake3.
pub fn combine_hash_vals<M: MetaMode>(a: &M::HashVal, b: &M::HashVal) -> M::HashVal {
  M::mk_hash(|| combine_hashes(M::as_blake3(a).unwrap(), M::as_blake3(b).unwrap()))
}

// ============================================================================
// Val — semantic values with blake3 hash
// ============================================================================

/// A semantic value in the NbE domain.
///
/// Uses `Rc` for O(1) clone and stable pointer identity (for caching).
/// Carries a cached blake3 hash for structural fingerprinting.
#[derive(Clone, Debug)]
pub struct Val<M: MetaMode>(Rc<ValNode<M>>);

/// Internal node wrapping hash + data for Val.
#[derive(Debug)]
struct ValNode<M: MetaMode> {
  hash: M::HashVal,
  inner: ValInner<M>,
}

/// The inner data of a semantic value.
#[derive(Debug)]
pub enum ValInner<M: MetaMode> {
  /// Lambda closure: evaluated domain, unevaluated body with environment.
  Lam {
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
    dom: Val<M>,
    body: KExpr<M>,
    env: Env<M>,
  },
  /// Pi/forall closure: evaluated domain, unevaluated body with environment.
  Pi {
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
    dom: Val<M>,
    body: KExpr<M>,
    env: Env<M>,
  },
  /// Universe sort.
  Sort(KLevel<M>),
  /// A stuck/neutral term: either a free variable or unresolved constant,
  /// with a spine of lazily-evaluated arguments.
  /// `spine_hash` tracks the combined hash of spine thunks for incremental updates.
  Neutral { head: Head<M>, spine: Vec<Thunk<M>>, spine_hash: M::HashVal },
  /// A constructor application with lazily-evaluated arguments.
  Ctor {
    id: MetaId<M>,
    levels: Vec<KLevel<M>>,
    cidx: usize,
    num_params: usize,
    num_fields: usize,
    induct_addr: Address,
    spine: Vec<Thunk<M>>,
    spine_hash: M::HashVal,
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
    spine_hash: M::HashVal,
  },
}

/// The head of a neutral term.
#[derive(Debug)]
pub enum Head<M: MetaMode> {
  /// A free variable at de Bruijn level, carrying its type.
  FVar { level: usize, ty: Val<M> },
  /// An unresolved constant reference.
  Const {
    id: MetaId<M>,
    levels: Vec<KLevel<M>>,
  },
}

impl<M: MetaMode> Val<M> {
  pub fn inner(&self) -> &ValInner<M> {
    &self.0.inner
  }

  /// Returns the cached blake3 hash of this value.
  pub fn blake3_hash(&self) -> &M::HashVal {
    &self.0.hash
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
    let level_hash = level.blake3_hash().clone();
    let hash = M::mk_hash(|| hash_tag1(0, M::as_blake3(&level_hash).unwrap()));
    Val(Rc::new(ValNode { hash, inner: ValInner::Sort(level) }))
  }

  pub fn mk_lit(l: Literal) -> Self {
    let hash = M::mk_hash(|| hash_tag1(1, &hash_literal(&l)));
    Val(Rc::new(ValNode { hash, inner: ValInner::Lit(l) }))
  }

  pub fn mk_const(
    id: MetaId<M>,
    levels: Vec<KLevel<M>>,
  ) -> Self {
    let head = Head::Const { id, levels };
    // Single blake3 call: head + empty spine combined
    let (hash, spine_hash) = Self::hash_neutral_inline::<M>(&head, &[]);
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Neutral {
        head,
        spine: Vec::new(),
        spine_hash,
      },
    }))
  }

  pub fn mk_fvar(level: usize, ty: Val<M>) -> Self {
    let head = Head::FVar { level, ty };
    // Single blake3 call: head + empty spine combined
    let (hash, spine_hash) = Self::hash_neutral_inline::<M>(&head, &[]);
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Neutral {
        head,
        spine: Vec::new(),
        spine_hash,
      },
    }))
  }

  pub fn mk_lam(
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
    dom: Val<M>,
    body: KExpr<M>,
    env: Env<M>,
  ) -> Self {
    let dom_hash = dom.blake3_hash().clone();
    let body_hash = body.blake3_hash().clone();
    let env_hash = env.blake3_hash().clone();
    let hash = M::mk_hash(|| hash_tag3(2, M::as_blake3(&dom_hash).unwrap(), M::as_blake3(&body_hash).unwrap(), M::as_blake3(&env_hash).unwrap()));
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Lam { name, bi, dom, body, env },
    }))
  }

  pub fn mk_pi(
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
    dom: Val<M>,
    body: KExpr<M>,
    env: Env<M>,
  ) -> Self {
    let dom_hash = dom.blake3_hash().clone();
    let body_hash = body.blake3_hash().clone();
    let env_hash = env.blake3_hash().clone();
    let hash = M::mk_hash(|| hash_tag3(3, M::as_blake3(&dom_hash).unwrap(), M::as_blake3(&body_hash).unwrap(), M::as_blake3(&env_hash).unwrap()));
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Pi { name, bi, dom, body, env },
    }))
  }

  pub fn mk_ctor(
    id: MetaId<M>,
    levels: Vec<KLevel<M>>,
    cidx: usize,
    num_params: usize,
    num_fields: usize,
    induct_addr: Address,
    spine: Vec<Thunk<M>>,
  ) -> Self {
    let spine_hash = hash_spine(&spine);
    let hash = M::mk_hash(|| Self::hash_ctor(&id.addr, &levels, cidx, M::as_blake3(&spine_hash).unwrap()));
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Ctor {
        id, levels, cidx, num_params, num_fields, induct_addr, spine, spine_hash,
      },
    }))
  }

  pub fn mk_neutral(head: Head<M>, spine: Vec<Thunk<M>>) -> Self {
    let (hash, spine_hash) = Self::hash_neutral_inline::<M>(&head, &spine);
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Neutral { head, spine, spine_hash },
    }))
  }

  /// Create a neutral with a pre-computed spine_hash (for incremental updates).
  pub fn mk_neutral_with_spine_hash(head: Head<M>, spine: Vec<Thunk<M>>, spine_hash: M::HashVal) -> Self {
    // 1 blake3 call: combine head + pre-computed spine_hash
    let hash = M::mk_hash(|| {
      let hh = hash_head_raw::<M>(&head);
      hash_tag2(6, &hh, M::as_blake3(&spine_hash).unwrap())
    });
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Neutral { head, spine, spine_hash },
    }))
  }

  pub fn mk_proj(
    type_addr: Address,
    idx: usize,
    strct: Thunk<M>,
    type_name: M::Field<Name>,
    spine: Vec<Thunk<M>>,
  ) -> Self {
    let spine_hash = hash_spine(&spine);
    let hash = M::mk_hash(|| Self::hash_proj(&type_addr, idx, M::as_blake3(&strct.hash).unwrap(), M::as_blake3(&spine_hash).unwrap()));
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Proj { type_addr, idx, strct, type_name, spine, spine_hash },
    }))
  }

  /// Compute neutral hash with head + spine in a single M::mk_hash call (avoids 3 separate blake3 calls).
  /// Returns (val_hash, spine_hash).
  #[inline]
  fn hash_neutral_inline<M2: MetaMode>(head: &Head<M2>, spine: &[Thunk<M2>]) -> (M2::HashVal, M2::HashVal) {
    // Compute raw hashes inside a single closure context
    let spine_hash_raw = M2::mk_hash(|| hash_spine_raw::<M2>(spine));
    let hash = M2::mk_hash(|| {
      let hh = hash_head_raw::<M2>(head);
      let sh = M2::as_blake3(&spine_hash_raw).unwrap();
      hash_tag2(6, &hh, sh)
    });
    (hash, spine_hash_raw)
  }

  /// Compute ctor hash from components.
  #[inline]
  fn hash_ctor(addr: &Address, levels: &[KLevel<M>], cidx: usize, spine_hash: &blake3::Hash) -> blake3::Hash {
    let lh = hash_levels(levels);
    let mut buf = [0u8; 105]; // 1 + 32 + 32 + 8 + 32
    buf[0] = 7;
    buf[1..33].copy_from_slice(addr.as_bytes());
    buf[33..65].copy_from_slice(lh.as_bytes());
    buf[65..73].copy_from_slice(&cidx.to_le_bytes());
    buf[73..105].copy_from_slice(spine_hash.as_bytes());
    blake3::hash(&buf)
  }

  /// Compute proj hash from components.
  #[inline]
  fn hash_proj(type_addr: &Address, idx: usize, strct_hash: &blake3::Hash, spine_hash: &blake3::Hash) -> blake3::Hash {
    let mut buf = [0u8; 105]; // 1 + 32 + 8 + 32 + 32
    buf[0] = 8;
    buf[1..33].copy_from_slice(type_addr.as_bytes());
    buf[33..41].copy_from_slice(&idx.to_le_bytes());
    buf[41..73].copy_from_slice(strct_hash.as_bytes());
    buf[73..105].copy_from_slice(spine_hash.as_bytes());
    blake3::hash(&buf)
  }

  /// Create a ctor with a pre-computed spine_hash (for incremental updates).
  pub fn mk_ctor_with_spine_hash(
    id: MetaId<M>,
    levels: Vec<KLevel<M>>,
    cidx: usize,
    num_params: usize,
    num_fields: usize,
    induct_addr: Address,
    spine: Vec<Thunk<M>>,
    spine_hash: M::HashVal,
  ) -> Self {
    let hash = M::mk_hash(|| Self::hash_ctor(&id.addr, &levels, cidx, M::as_blake3(&spine_hash).unwrap()));
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Ctor {
        id, levels, cidx, num_params, num_fields, induct_addr, spine, spine_hash,
      },
    }))
  }

  /// Create a proj with a pre-computed spine_hash (for incremental updates).
  pub fn mk_proj_with_spine_hash(
    type_addr: Address,
    idx: usize,
    strct: Thunk<M>,
    type_name: M::Field<Name>,
    spine: Vec<Thunk<M>>,
    spine_hash: M::HashVal,
  ) -> Self {
    let hash = M::mk_hash(|| Self::hash_proj(&type_addr, idx, M::as_blake3(&strct.hash).unwrap(), M::as_blake3(&spine_hash).unwrap()));
    Val(Rc::new(ValNode {
      hash,
      inner: ValInner::Proj { type_addr, idx, strct, type_name, spine, spine_hash },
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
        head: Head::Const { id, .. },
        ..
      } => Some(&id.addr),
      ValInner::Ctor { id, .. } => Some(&id.addr),
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

  /// Get the spine_hash of a neutral, ctor, or proj.
  pub fn spine_hash(&self) -> Option<&M::HashVal> {
    match self.inner() {
      ValInner::Neutral { spine_hash, .. }
      | ValInner::Ctor { spine_hash, .. }
      | ValInner::Proj { spine_hash, .. } => Some(spine_hash),
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
    fmt_val::<M>(self, f, 0)
  }
}

/// Pretty-print a Val with depth-limited recursion to avoid infinite output.
fn fmt_val<M: MetaMode>(
  v: &Val<M>,
  f: &mut fmt::Formatter<'_>,
  depth: usize,
) -> fmt::Result {
  const MAX_DEPTH: usize = 8;
  if depth > MAX_DEPTH {
    return write!(f, "...");
  }
  match v.inner() {
    ValInner::Lam { name, dom, body, .. } => {
      write!(f, "(fun (")?;
      super::types::fmt_field_name::<M>(name, f)?;
      write!(f, " : ")?;
      fmt_val::<M>(dom, f, depth + 1)?;
      write!(f, ") => {body})")
    }
    ValInner::Pi { name, dom, body, .. } => {
      write!(f, "((")?;
      super::types::fmt_field_name::<M>(name, f)?;
      write!(f, " : ")?;
      fmt_val::<M>(dom, f, depth + 1)?;
      write!(f, ") -> {body})")
    }
    ValInner::Sort(l) => write!(f, "Sort {l}"),
    ValInner::Neutral { head, spine, .. } => {
      match head {
        Head::FVar { level, .. } => write!(f, "fvar@{level}")?,
        Head::Const { id, .. } => {
          super::types::fmt_field_name::<M>(&id.name, f)?;
        }
      }
      if !spine.is_empty() {
        write!(f, " ({} args)", spine.len())?;
      }
      Ok(())
    }
    ValInner::Ctor {
      id, spine, cidx, ..
    } => {
      write!(f, "ctor#{cidx} ")?;
      super::types::fmt_field_name::<M>(&id.name, f)?;
      if !spine.is_empty() {
        write!(f, " ({} args)", spine.len())?;
      }
      Ok(())
    }
    ValInner::Lit(Literal::NatVal(n)) => write!(f, "{n}"),
    ValInner::Lit(Literal::StrVal(s)) => write!(f, "\"{s}\""),
    ValInner::Proj {
      idx, type_name, ..
    } => {
      write!(f, "proj[{idx}] ")?;
      super::types::fmt_field_name::<M>(type_name, f)
    }
  }
}
