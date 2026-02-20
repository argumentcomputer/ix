use core::ptr::NonNull;

use crate::ix::env::{BinderInfo, Level, Literal, Name};
use crate::lean::nat::Nat;
use rustc_hash::{FxHashMap, FxHashSet};

use super::level::subst_level;

use super::dll::DLL;

pub type Parents = DLL<ParentPtr>;

// ============================================================================
// Pointer types
// ============================================================================

#[derive(Debug)]
pub enum DAGPtr {
  Var(NonNull<Var>),
  Sort(NonNull<Sort>),
  Cnst(NonNull<Cnst>),
  Lit(NonNull<LitNode>),
  Lam(NonNull<Lam>),
  Fun(NonNull<Fun>),
  Pi(NonNull<Pi>),
  App(NonNull<App>),
  Let(NonNull<LetNode>),
  Proj(NonNull<ProjNode>),
}

impl Copy for DAGPtr {}
impl Clone for DAGPtr {
  fn clone(&self) -> Self {
    *self
  }
}

impl PartialEq for DAGPtr {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (DAGPtr::Var(a), DAGPtr::Var(b)) => a == b,
      (DAGPtr::Sort(a), DAGPtr::Sort(b)) => a == b,
      (DAGPtr::Cnst(a), DAGPtr::Cnst(b)) => a == b,
      (DAGPtr::Lit(a), DAGPtr::Lit(b)) => a == b,
      (DAGPtr::Lam(a), DAGPtr::Lam(b)) => a == b,
      (DAGPtr::Fun(a), DAGPtr::Fun(b)) => a == b,
      (DAGPtr::Pi(a), DAGPtr::Pi(b)) => a == b,
      (DAGPtr::App(a), DAGPtr::App(b)) => a == b,
      (DAGPtr::Let(a), DAGPtr::Let(b)) => a == b,
      (DAGPtr::Proj(a), DAGPtr::Proj(b)) => a == b,
      _ => false,
    }
  }
}
impl Eq for DAGPtr {}

#[derive(Debug)]
pub enum ParentPtr {
  Root,
  LamBod(NonNull<Lam>),
  FunDom(NonNull<Fun>),
  FunImg(NonNull<Fun>),
  PiDom(NonNull<Pi>),
  PiImg(NonNull<Pi>),
  AppFun(NonNull<App>),
  AppArg(NonNull<App>),
  LetTyp(NonNull<LetNode>),
  LetVal(NonNull<LetNode>),
  LetBod(NonNull<LetNode>),
  ProjExpr(NonNull<ProjNode>),
}

impl Copy for ParentPtr {}
impl Clone for ParentPtr {
  fn clone(&self) -> Self {
    *self
  }
}

impl PartialEq for ParentPtr {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (ParentPtr::Root, ParentPtr::Root) => true,
      (ParentPtr::LamBod(a), ParentPtr::LamBod(b)) => a == b,
      (ParentPtr::FunDom(a), ParentPtr::FunDom(b)) => a == b,
      (ParentPtr::FunImg(a), ParentPtr::FunImg(b)) => a == b,
      (ParentPtr::PiDom(a), ParentPtr::PiDom(b)) => a == b,
      (ParentPtr::PiImg(a), ParentPtr::PiImg(b)) => a == b,
      (ParentPtr::AppFun(a), ParentPtr::AppFun(b)) => a == b,
      (ParentPtr::AppArg(a), ParentPtr::AppArg(b)) => a == b,
      (ParentPtr::LetTyp(a), ParentPtr::LetTyp(b)) => a == b,
      (ParentPtr::LetVal(a), ParentPtr::LetVal(b)) => a == b,
      (ParentPtr::LetBod(a), ParentPtr::LetBod(b)) => a == b,
      (ParentPtr::ProjExpr(a), ParentPtr::ProjExpr(b)) => a == b,
      _ => false,
    }
  }
}
impl Eq for ParentPtr {}

/// Binder pointer: from a Var to its binding Lam, or Free.
#[derive(Debug)]
pub enum BinderPtr {
  Free,
  Lam(NonNull<Lam>),
}

impl Copy for BinderPtr {}
impl Clone for BinderPtr {
  fn clone(&self) -> Self {
    *self
  }
}

impl PartialEq for BinderPtr {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (BinderPtr::Free, BinderPtr::Free) => true,
      (BinderPtr::Lam(a), BinderPtr::Lam(b)) => a == b,
      _ => false,
    }
  }
}

// ============================================================================
// Node structs
// ============================================================================

/// Bound or free variable.
#[repr(C)]
pub struct Var {
  /// De Bruijn level (used during from_expr/to_expr conversion).
  pub depth: u64,
  /// Points to the binding Lam, or Free for free variables.
  pub binder: BinderPtr,
  /// If this Var came from an Fvar, preserves the name for roundtrip.
  pub fvar_name: Option<Name>,
  /// Parent pointers.
  pub parents: Option<NonNull<Parents>>,
}

/// Sort node (universe).
#[repr(C)]
pub struct Sort {
  pub level: Level,
  pub parents: Option<NonNull<Parents>>,
}

/// Constant reference.
#[repr(C)]
pub struct Cnst {
  pub name: Name,
  pub levels: Vec<Level>,
  pub parents: Option<NonNull<Parents>>,
}

/// Literal value (Nat or String).
#[repr(C)]
pub struct LitNode {
  pub val: Literal,
  pub parents: Option<NonNull<Parents>>,
}

/// Internal binding node (spine). Carries an embedded Var.
/// Always appears as the img/bod of Fun/Pi/Let.
#[repr(C)]
pub struct Lam {
  pub bod: DAGPtr,
  pub bod_ref: Parents,
  pub var: Var,
  pub parents: Option<NonNull<Parents>>,
}

/// Lean lambda: `fun (name : dom) => bod`.
/// Branch node wrapping a Lam for the body.
#[repr(C)]
pub struct Fun {
  pub binder_name: Name,
  pub binder_info: BinderInfo,
  pub dom: DAGPtr,
  pub img: NonNull<Lam>,
  pub dom_ref: Parents,
  pub img_ref: Parents,
  pub copy: Option<NonNull<Fun>>,
  pub parents: Option<NonNull<Parents>>,
}

/// Lean Pi/ForallE: `(name : dom) → bod`.
/// Branch node wrapping a Lam for the body.
#[repr(C)]
pub struct Pi {
  pub binder_name: Name,
  pub binder_info: BinderInfo,
  pub dom: DAGPtr,
  pub img: NonNull<Lam>,
  pub dom_ref: Parents,
  pub img_ref: Parents,
  pub copy: Option<NonNull<Pi>>,
  pub parents: Option<NonNull<Parents>>,
}

/// Application node.
#[repr(C)]
pub struct App {
  pub fun: DAGPtr,
  pub arg: DAGPtr,
  pub fun_ref: Parents,
  pub arg_ref: Parents,
  pub copy: Option<NonNull<App>>,
  pub parents: Option<NonNull<Parents>>,
}

/// Let binding: `let name : typ := val in bod`.
#[repr(C)]
pub struct LetNode {
  pub binder_name: Name,
  pub non_dep: bool,
  pub typ: DAGPtr,
  pub val: DAGPtr,
  pub bod: NonNull<Lam>,
  pub typ_ref: Parents,
  pub val_ref: Parents,
  pub bod_ref: Parents,
  pub copy: Option<NonNull<LetNode>>,
  pub parents: Option<NonNull<Parents>>,
}

/// Projection from a structure.
#[repr(C)]
pub struct ProjNode {
  pub type_name: Name,
  pub idx: Nat,
  pub expr: DAGPtr,
  pub expr_ref: Parents,
  pub parents: Option<NonNull<Parents>>,
}

/// A DAG with a head node.
pub struct DAG {
  pub head: DAGPtr,
}

// ============================================================================
// Allocation helpers
// ============================================================================

#[inline]
pub fn alloc_val<T>(val: T) -> NonNull<T> {
  NonNull::new(Box::into_raw(Box::new(val))).unwrap()
}

pub fn alloc_lam(
  depth: u64,
  bod: DAGPtr,
  parents: Option<NonNull<Parents>>,
) -> NonNull<Lam> {
  let lam_ptr = alloc_val(Lam {
    bod,
    bod_ref: DLL::singleton(ParentPtr::Root),
    var: Var { depth, binder: BinderPtr::Free, fvar_name: None, parents: None },
    parents,
  });
  unsafe {
    let lam = &mut *lam_ptr.as_ptr();
    lam.bod_ref = DLL::singleton(ParentPtr::LamBod(lam_ptr));
    lam.var.binder = BinderPtr::Lam(lam_ptr);
  }
  lam_ptr
}

pub fn alloc_app(
  fun: DAGPtr,
  arg: DAGPtr,
  parents: Option<NonNull<Parents>>,
) -> NonNull<App> {
  let app_ptr = alloc_val(App {
    fun,
    arg,
    fun_ref: DLL::singleton(ParentPtr::Root),
    arg_ref: DLL::singleton(ParentPtr::Root),
    copy: None,
    parents,
  });
  unsafe {
    let app = &mut *app_ptr.as_ptr();
    app.fun_ref = DLL::singleton(ParentPtr::AppFun(app_ptr));
    app.arg_ref = DLL::singleton(ParentPtr::AppArg(app_ptr));
  }
  app_ptr
}

pub fn alloc_fun(
  binder_name: Name,
  binder_info: BinderInfo,
  dom: DAGPtr,
  img: NonNull<Lam>,
  parents: Option<NonNull<Parents>>,
) -> NonNull<Fun> {
  let fun_ptr = alloc_val(Fun {
    binder_name,
    binder_info,
    dom,
    img,
    dom_ref: DLL::singleton(ParentPtr::Root),
    img_ref: DLL::singleton(ParentPtr::Root),
    copy: None,
    parents,
  });
  unsafe {
    let fun = &mut *fun_ptr.as_ptr();
    fun.dom_ref = DLL::singleton(ParentPtr::FunDom(fun_ptr));
    fun.img_ref = DLL::singleton(ParentPtr::FunImg(fun_ptr));
  }
  fun_ptr
}

pub fn alloc_pi(
  binder_name: Name,
  binder_info: BinderInfo,
  dom: DAGPtr,
  img: NonNull<Lam>,
  parents: Option<NonNull<Parents>>,
) -> NonNull<Pi> {
  let pi_ptr = alloc_val(Pi {
    binder_name,
    binder_info,
    dom,
    img,
    dom_ref: DLL::singleton(ParentPtr::Root),
    img_ref: DLL::singleton(ParentPtr::Root),
    copy: None,
    parents,
  });
  unsafe {
    let pi = &mut *pi_ptr.as_ptr();
    pi.dom_ref = DLL::singleton(ParentPtr::PiDom(pi_ptr));
    pi.img_ref = DLL::singleton(ParentPtr::PiImg(pi_ptr));
  }
  pi_ptr
}

pub fn alloc_let(
  binder_name: Name,
  non_dep: bool,
  typ: DAGPtr,
  val: DAGPtr,
  bod: NonNull<Lam>,
  parents: Option<NonNull<Parents>>,
) -> NonNull<LetNode> {
  let let_ptr = alloc_val(LetNode {
    binder_name,
    non_dep,
    typ,
    val,
    bod,
    typ_ref: DLL::singleton(ParentPtr::Root),
    val_ref: DLL::singleton(ParentPtr::Root),
    bod_ref: DLL::singleton(ParentPtr::Root),
    copy: None,
    parents,
  });
  unsafe {
    let let_node = &mut *let_ptr.as_ptr();
    let_node.typ_ref = DLL::singleton(ParentPtr::LetTyp(let_ptr));
    let_node.val_ref = DLL::singleton(ParentPtr::LetVal(let_ptr));
    let_node.bod_ref = DLL::singleton(ParentPtr::LetBod(let_ptr));
  }
  let_ptr
}

pub fn alloc_proj(
  type_name: Name,
  idx: Nat,
  expr: DAGPtr,
  parents: Option<NonNull<Parents>>,
) -> NonNull<ProjNode> {
  let proj_ptr = alloc_val(ProjNode {
    type_name,
    idx,
    expr,
    expr_ref: DLL::singleton(ParentPtr::Root),
    parents,
  });
  unsafe {
    let proj = &mut *proj_ptr.as_ptr();
    proj.expr_ref = DLL::singleton(ParentPtr::ProjExpr(proj_ptr));
  }
  proj_ptr
}

// ============================================================================
// Parent pointer helpers
// ============================================================================

pub fn get_parents(node: DAGPtr) -> Option<NonNull<Parents>> {
  unsafe {
    match node {
      DAGPtr::Var(p) => (*p.as_ptr()).parents,
      DAGPtr::Sort(p) => (*p.as_ptr()).parents,
      DAGPtr::Cnst(p) => (*p.as_ptr()).parents,
      DAGPtr::Lit(p) => (*p.as_ptr()).parents,
      DAGPtr::Lam(p) => (*p.as_ptr()).parents,
      DAGPtr::Fun(p) => (*p.as_ptr()).parents,
      DAGPtr::Pi(p) => (*p.as_ptr()).parents,
      DAGPtr::App(p) => (*p.as_ptr()).parents,
      DAGPtr::Let(p) => (*p.as_ptr()).parents,
      DAGPtr::Proj(p) => (*p.as_ptr()).parents,
    }
  }
}

pub fn set_parents(node: DAGPtr, parents: Option<NonNull<Parents>>) {
  unsafe {
    match node {
      DAGPtr::Var(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::Sort(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::Cnst(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::Lit(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::Lam(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::Fun(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::Pi(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::App(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::Let(p) => (*p.as_ptr()).parents = parents,
      DAGPtr::Proj(p) => (*p.as_ptr()).parents = parents,
    }
  }
}

pub fn add_to_parents(node: DAGPtr, parent_link: NonNull<Parents>) {
  unsafe {
    match get_parents(node) {
      None => set_parents(node, Some(parent_link)),
      Some(parents) => {
        (*parents.as_ptr()).merge(parent_link);
      },
    }
  }
}

// ============================================================================
// DAG-level helpers
// ============================================================================

/// Get a unique key for a DAG node pointer (for use in hash sets).
pub fn dag_ptr_key(node: DAGPtr) -> usize {
  match node {
    DAGPtr::Var(p) => p.as_ptr() as usize,
    DAGPtr::Sort(p) => p.as_ptr() as usize,
    DAGPtr::Cnst(p) => p.as_ptr() as usize,
    DAGPtr::Lit(p) => p.as_ptr() as usize,
    DAGPtr::Lam(p) => p.as_ptr() as usize,
    DAGPtr::Fun(p) => p.as_ptr() as usize,
    DAGPtr::Pi(p) => p.as_ptr() as usize,
    DAGPtr::App(p) => p.as_ptr() as usize,
    DAGPtr::Let(p) => p.as_ptr() as usize,
    DAGPtr::Proj(p) => p.as_ptr() as usize,
  }
}

/// Free all DAG nodes reachable from the head.
/// Only frees the node structs themselves; DLL parent entries that are
/// inline in parent structs are freed with those structs. The root_parents
/// DLL node (heap-allocated in from_expr) is a small accepted leak.
pub fn free_dag(dag: DAG) {
  let mut visited = FxHashSet::default();
  free_dag_nodes(dag.head, &mut visited);
}

fn free_dag_nodes(root: DAGPtr, visited: &mut FxHashSet<usize>) {
  let mut stack: Vec<DAGPtr> = vec![root];
  while let Some(node) = stack.pop() {
    let key = dag_ptr_key(node);
    if !visited.insert(key) {
      continue;
    }
    unsafe {
      match node {
        DAGPtr::Var(link) => {
          let var = &*link.as_ptr();
          if let BinderPtr::Free = var.binder {
            drop(Box::from_raw(link.as_ptr()));
          }
        },
        DAGPtr::Sort(link) => drop(Box::from_raw(link.as_ptr())),
        DAGPtr::Cnst(link) => drop(Box::from_raw(link.as_ptr())),
        DAGPtr::Lit(link) => drop(Box::from_raw(link.as_ptr())),
        DAGPtr::Lam(link) => {
          let lam = &*link.as_ptr();
          stack.push(lam.bod);
          drop(Box::from_raw(link.as_ptr()));
        },
        DAGPtr::Fun(link) => {
          let fun = &*link.as_ptr();
          stack.push(fun.dom);
          stack.push(DAGPtr::Lam(fun.img));
          drop(Box::from_raw(link.as_ptr()));
        },
        DAGPtr::Pi(link) => {
          let pi = &*link.as_ptr();
          stack.push(pi.dom);
          stack.push(DAGPtr::Lam(pi.img));
          drop(Box::from_raw(link.as_ptr()));
        },
        DAGPtr::App(link) => {
          let app = &*link.as_ptr();
          stack.push(app.fun);
          stack.push(app.arg);
          drop(Box::from_raw(link.as_ptr()));
        },
        DAGPtr::Let(link) => {
          let let_node = &*link.as_ptr();
          stack.push(let_node.typ);
          stack.push(let_node.val);
          stack.push(DAGPtr::Lam(let_node.bod));
          drop(Box::from_raw(link.as_ptr()));
        },
        DAGPtr::Proj(link) => {
          let proj = &*link.as_ptr();
          stack.push(proj.expr);
          drop(Box::from_raw(link.as_ptr()));
        },
      }
    }
  }
}

// ============================================================================
// DAG utilities for typechecker
// ============================================================================

/// Decompose `f a1 a2 ... an` into `(f, [a1, a2, ..., an])` at the DAG level.
pub fn dag_unfold_apps(dag: DAGPtr) -> (DAGPtr, Vec<DAGPtr>) {
  let mut args = Vec::new();
  let mut cursor = dag;
  loop {
    match cursor {
      DAGPtr::App(app) => unsafe {
        let app_ref = &*app.as_ptr();
        args.push(app_ref.arg);
        cursor = app_ref.fun;
      },
      _ => break,
    }
  }
  args.reverse();
  (cursor, args)
}

/// Reconstruct `f a1 a2 ... an` from a head and arguments at the DAG level.
pub fn dag_foldl_apps(fun: DAGPtr, args: &[DAGPtr]) -> DAGPtr {
  let mut result = fun;
  for &arg in args {
    let app = alloc_app(result, arg, None);
    result = DAGPtr::App(app);
  }
  result
}

/// Substitute universe level parameters in-place throughout a DAG.
///
/// Replaces `Level::param(params[i])` with `values[i]` in all Sort and Cnst
/// nodes reachable from `root`. Uses a visited set to handle DAG sharing.
///
/// The DAG must not be shared with other live structures, since this mutates
/// nodes in place (intended for freshly `from_expr`'d DAGs).
pub fn subst_dag_levels(
  root: DAGPtr,
  params: &[Name],
  values: &[Level],
) -> DAGPtr {
  if params.is_empty() {
    return root;
  }
  let mut visited = FxHashSet::default();
  let mut stack: Vec<DAGPtr> = vec![root];
  while let Some(node) = stack.pop() {
    let key = dag_ptr_key(node);
    if !visited.insert(key) {
      continue;
    }
    unsafe {
      match node {
        DAGPtr::Sort(p) => {
          let sort = &mut *p.as_ptr();
          sort.level = subst_level(&sort.level, params, values);
        },
        DAGPtr::Cnst(p) => {
          let cnst = &mut *p.as_ptr();
          cnst.levels =
            cnst.levels.iter().map(|l| subst_level(l, params, values)).collect();
        },
        DAGPtr::App(p) => {
          let app = &*p.as_ptr();
          stack.push(app.fun);
          stack.push(app.arg);
        },
        DAGPtr::Fun(p) => {
          let fun = &*p.as_ptr();
          stack.push(fun.dom);
          stack.push(DAGPtr::Lam(fun.img));
        },
        DAGPtr::Pi(p) => {
          let pi = &*p.as_ptr();
          stack.push(pi.dom);
          stack.push(DAGPtr::Lam(pi.img));
        },
        DAGPtr::Lam(p) => {
          let lam = &*p.as_ptr();
          stack.push(lam.bod);
        },
        DAGPtr::Let(p) => {
          let let_node = &*p.as_ptr();
          stack.push(let_node.typ);
          stack.push(let_node.val);
          stack.push(DAGPtr::Lam(let_node.bod));
        },
        DAGPtr::Proj(p) => {
          let proj = &*p.as_ptr();
          stack.push(proj.expr);
        },
        DAGPtr::Var(_) | DAGPtr::Lit(_) => {},
      }
    }
  }
  root
}

// ============================================================================
// Deep-copy substitution for typechecker
// ============================================================================

/// Deep-copy a Lam body, substituting `replacement` for the Lam's bound variable.
///
/// Unlike `subst_pi_body` (which mutates nodes in place via BUBS), this creates
/// a completely fresh DAG. This prevents the type DAG from sharing mutable nodes
/// with the term DAG, avoiding corruption when WHNF later beta-reduces in the
/// type DAG.
///
/// The `replacement` is also deep-copied to prevent WHNF's `reduce_lam` from
/// modifying the original term DAG when it beta-reduces through substituted
/// Fun/Lam nodes. Vars not bound within the copy scope (outer-binder vars and
/// free vars) are preserved by pointer to maintain identity for `def_eq`.
///
/// Deep-copy the Lam body with substitution. Used when the Lam is from
/// the TERM DAG (e.g., `infer_lambda`, `infer_pi`, `infer_let`) to
/// protect the term from destructive in-place modification.
///
/// The replacement is also deep-copied to isolate the term DAG from
/// WHNF mutations. Vars not bound within the copy scope are preserved
/// by pointer to maintain identity for `def_eq`.
pub fn dag_copy_subst(lam: NonNull<Lam>, replacement: DAGPtr) -> DAGPtr {
  use std::sync::atomic::{AtomicU64, Ordering};
  static COPY_SUBST_CALLS: AtomicU64 = AtomicU64::new(0);
  static COPY_SUBST_NODES: AtomicU64 = AtomicU64::new(0);
  let call_num = COPY_SUBST_CALLS.fetch_add(1, Ordering::Relaxed);

  let mut cache: FxHashMap<usize, DAGPtr> = FxHashMap::default();
  unsafe {
    let lambda = &*lam.as_ptr();
    let var_ptr =
      NonNull::new(&lambda.var as *const Var as *mut Var).unwrap();
    let var_key = dag_ptr_key(DAGPtr::Var(var_ptr));
    // Deep-copy the replacement (isolates from term DAG mutations)
    let copied_replacement = dag_copy_node(replacement, &mut cache);
    let repl_nodes = cache.len();
    // Clear cache: body and replacement are separate DAGs, no shared nodes.
    cache.clear();
    // Map the target var to the copied replacement
    cache.insert(var_key, copied_replacement);
    // Deep copy the body
    let result = dag_copy_node(lambda.bod, &mut cache);
    let body_nodes = cache.len();
    let total = COPY_SUBST_NODES.fetch_add(body_nodes as u64, Ordering::Relaxed) + body_nodes as u64;
    if call_num % 10 == 0 || body_nodes > 1000 {
      eprintln!("[dag_copy_subst] call={call_num} repl={repl_nodes} body={body_nodes} total_nodes={total}");
    }
    result
  }
}

/// Lightweight substitution for TYPE DAG Lams (from `from_expr` or derived).
/// Only the replacement is deep-copied; the body is modified in-place via
/// BUBS `subst_pi_body`, preserving DAG sharing and avoiding exponential
/// blowup.
pub fn dag_type_subst(lam: NonNull<Lam>, replacement: DAGPtr) -> DAGPtr {
  use super::upcopy::subst_pi_body;
  let mut cache: FxHashMap<usize, DAGPtr> = FxHashMap::default();
  let copied_replacement = dag_copy_node(replacement, &mut cache);
  subst_pi_body(lam, copied_replacement)
}

/// Iteratively copy a DAG node, using `cache` for sharing and var substitution.
///
/// Uses an explicit work stack to avoid stack overflow on deeply nested DAGs
/// (e.g., 40000+ left-nested App chains from unfolded definitions).
fn dag_copy_node(
  root: DAGPtr,
  cache: &mut FxHashMap<usize, DAGPtr>,
) -> DAGPtr {
  // Stack frames for the iterative traversal.
  // Compound nodes use a two-phase approach:
  //   Visit → push children + Finish frame → children processed → Finish builds node
  // Binder nodes (Fun/Pi/Let/Lam) use three phases:
  //   Visit → push dom/typ/val + CreateLam → CreateLam inserts var mapping + pushes body + Finish
  enum Frame {
    Visit(DAGPtr),
    FinishApp(usize, NonNull<App>),
    FinishProj(usize, NonNull<ProjNode>),
    CreateFunLam(usize, NonNull<Fun>),
    FinishFun(usize, NonNull<Fun>, NonNull<Lam>),
    CreatePiLam(usize, NonNull<Pi>),
    FinishPi(usize, NonNull<Pi>, NonNull<Lam>),
    CreateLamBody(usize, NonNull<Lam>),
    // FinishLam(key, new_lam, old_lam) — old_lam needed to look up body key
    FinishLam(usize, NonNull<Lam>, NonNull<Lam>),
    CreateLetLam(usize, NonNull<LetNode>),
    FinishLet(usize, NonNull<LetNode>, NonNull<Lam>),
  }

  let mut stack: Vec<Frame> = vec![Frame::Visit(root)];
  // Track nodes that have been visited (started processing) to prevent
  // exponential blowup when copying DAGs with shared compound nodes.
  // Without this, a shared node visited from two parents would be
  // processed twice, leading to 2^depth duplication.
  let mut visited: FxHashSet<usize> = FxHashSet::default();
  // Deferred back-edge patches: (key_of_placeholder, original_node)
  // WHNF iota reduction can create cyclic DAGs (e.g., Nat.rec step
  // function body → recursive Nat.rec result → step function).
  // When we encounter a back-edge during copy, we allocate a placeholder
  // and record it here. After the main traversal completes, we patch
  // each placeholder's children to point to the cached (copied) versions.
  let mut deferred: Vec<(usize, DAGPtr)> = Vec::new();

  while let Some(frame) = stack.pop() {
    unsafe {
      match frame {
        Frame::Visit(node) => {
          let key = dag_ptr_key(node);
          if cache.contains_key(&key) {
            continue;
          }
          if visited.contains(&key) {
            // Cycle back-edge: allocate placeholder, defer patching
            match node {
              DAGPtr::App(p) => {
                let app = &*p.as_ptr();
                let placeholder = alloc_app(app.fun, app.arg, None);
                cache.insert(key, DAGPtr::App(placeholder));
                deferred.push((key, node));
              },
              DAGPtr::Proj(p) => {
                let proj = &*p.as_ptr();
                let placeholder = alloc_proj(
                  proj.type_name.clone(), proj.idx.clone(), proj.expr, None,
                );
                cache.insert(key, DAGPtr::Proj(placeholder));
                deferred.push((key, node));
              },
              // Leaf-like nodes shouldn't cycle; handle just in case
              _ => {
                cache.insert(key, node);
              },
            }
            continue;
          }
          visited.insert(key);
          match node {
            DAGPtr::Var(_) => {
              // Not in cache: outer-binder or free var. Preserve original.
              cache.insert(key, node);
            },
            DAGPtr::Sort(p) => {
              let sort = &*p.as_ptr();
              cache.insert(
                key,
                DAGPtr::Sort(alloc_val(Sort {
                  level: sort.level.clone(),
                  parents: None,
                })),
              );
            },
            DAGPtr::Cnst(p) => {
              let cnst = &*p.as_ptr();
              cache.insert(
                key,
                DAGPtr::Cnst(alloc_val(Cnst {
                  name: cnst.name.clone(),
                  levels: cnst.levels.clone(),
                  parents: None,
                })),
              );
            },
            DAGPtr::Lit(p) => {
              let lit = &*p.as_ptr();
              cache.insert(
                key,
                DAGPtr::Lit(alloc_val(LitNode {
                  val: lit.val.clone(),
                  parents: None,
                })),
              );
            },
            DAGPtr::App(p) => {
              let app = &*p.as_ptr();
              // Finish after children; visit fun then arg
              stack.push(Frame::FinishApp(key, p));
              stack.push(Frame::Visit(app.arg));
              stack.push(Frame::Visit(app.fun));
            },
            DAGPtr::Fun(p) => {
              let fun = &*p.as_ptr();
              // Phase 1: visit dom, then create Lam
              stack.push(Frame::CreateFunLam(key, p));
              stack.push(Frame::Visit(fun.dom));
            },
            DAGPtr::Pi(p) => {
              let pi = &*p.as_ptr();
              stack.push(Frame::CreatePiLam(key, p));
              stack.push(Frame::Visit(pi.dom));
            },
            DAGPtr::Lam(p) => {
              // Standalone Lam: create Lam, then visit body
              stack.push(Frame::CreateLamBody(key, p));
            },
            DAGPtr::Let(p) => {
              let let_node = &*p.as_ptr();
              // Visit typ and val, then create Lam
              stack.push(Frame::CreateLetLam(key, p));
              stack.push(Frame::Visit(let_node.val));
              stack.push(Frame::Visit(let_node.typ));
            },
            DAGPtr::Proj(p) => {
              let proj = &*p.as_ptr();
              stack.push(Frame::FinishProj(key, p));
              stack.push(Frame::Visit(proj.expr));
            },
          }
        },

        Frame::FinishApp(key, app_ptr) => {
          let app = &*app_ptr.as_ptr();
          let new_fun = cache[&dag_ptr_key(app.fun)];
          let new_arg = cache[&dag_ptr_key(app.arg)];
          let new_app = alloc_app(new_fun, new_arg, None);
          let app_ref = &mut *new_app.as_ptr();
          let fun_ref =
            NonNull::new(&mut app_ref.fun_ref as *mut Parents).unwrap();
          add_to_parents(new_fun, fun_ref);
          let arg_ref =
            NonNull::new(&mut app_ref.arg_ref as *mut Parents).unwrap();
          add_to_parents(new_arg, arg_ref);
          cache.insert(key, DAGPtr::App(new_app));
        },

        Frame::FinishProj(key, proj_ptr) => {
          let proj = &*proj_ptr.as_ptr();
          let new_expr = cache[&dag_ptr_key(proj.expr)];
          let new_proj = alloc_proj(
            proj.type_name.clone(),
            proj.idx.clone(),
            new_expr,
            None,
          );
          let proj_ref = &mut *new_proj.as_ptr();
          let expr_ref =
            NonNull::new(&mut proj_ref.expr_ref as *mut Parents).unwrap();
          add_to_parents(new_expr, expr_ref);
          cache.insert(key, DAGPtr::Proj(new_proj));
        },

        // --- Fun binder: dom visited, create Lam, visit body ---
        Frame::CreateFunLam(key, fun_ptr) => {
          let fun = &*fun_ptr.as_ptr();
          let old_lam = &*fun.img.as_ptr();
          let old_var_ptr =
            NonNull::new(&old_lam.var as *const Var as *mut Var).unwrap();
          let old_var_key = dag_ptr_key(DAGPtr::Var(old_var_ptr));
          let new_lam = alloc_lam(
            old_lam.var.depth,
            DAGPtr::Var(NonNull::dangling()),
            None,
          );
          let new_lam_ref = &mut *new_lam.as_ptr();
          let new_var =
            NonNull::new(&mut new_lam_ref.var as *mut Var).unwrap();
          cache.insert(old_var_key, DAGPtr::Var(new_var));
          // Phase 2: visit body, then finish
          stack.push(Frame::FinishFun(key, fun_ptr, new_lam));
          stack.push(Frame::Visit(old_lam.bod));
        },

        Frame::FinishFun(key, fun_ptr, new_lam) => {
          let fun = &*fun_ptr.as_ptr();
          let old_lam = &*fun.img.as_ptr();
          let new_dom = cache[&dag_ptr_key(fun.dom)];
          let new_bod = cache[&dag_ptr_key(old_lam.bod)];
          let new_lam_ref = &mut *new_lam.as_ptr();
          new_lam_ref.bod = new_bod;
          let bod_ref =
            NonNull::new(&mut new_lam_ref.bod_ref as *mut Parents).unwrap();
          add_to_parents(new_bod, bod_ref);
          let new_fun_node = alloc_fun(
            fun.binder_name.clone(),
            fun.binder_info.clone(),
            new_dom,
            new_lam,
            None,
          );
          let fun_ref = &mut *new_fun_node.as_ptr();
          let dom_ref =
            NonNull::new(&mut fun_ref.dom_ref as *mut Parents).unwrap();
          add_to_parents(new_dom, dom_ref);
          let img_ref =
            NonNull::new(&mut fun_ref.img_ref as *mut Parents).unwrap();
          add_to_parents(DAGPtr::Lam(new_lam), img_ref);
          cache.insert(key, DAGPtr::Fun(new_fun_node));
        },

        // --- Pi binder: dom visited, create Lam, visit body ---
        Frame::CreatePiLam(key, pi_ptr) => {
          let pi = &*pi_ptr.as_ptr();
          let old_lam = &*pi.img.as_ptr();
          let old_var_ptr =
            NonNull::new(&old_lam.var as *const Var as *mut Var).unwrap();
          let old_var_key = dag_ptr_key(DAGPtr::Var(old_var_ptr));
          let new_lam = alloc_lam(
            old_lam.var.depth,
            DAGPtr::Var(NonNull::dangling()),
            None,
          );
          let new_lam_ref = &mut *new_lam.as_ptr();
          let new_var =
            NonNull::new(&mut new_lam_ref.var as *mut Var).unwrap();
          cache.insert(old_var_key, DAGPtr::Var(new_var));
          stack.push(Frame::FinishPi(key, pi_ptr, new_lam));
          stack.push(Frame::Visit(old_lam.bod));
        },

        Frame::FinishPi(key, pi_ptr, new_lam) => {
          let pi = &*pi_ptr.as_ptr();
          let old_lam = &*pi.img.as_ptr();
          let new_dom = cache[&dag_ptr_key(pi.dom)];
          let new_bod = cache[&dag_ptr_key(old_lam.bod)];
          let new_lam_ref = &mut *new_lam.as_ptr();
          new_lam_ref.bod = new_bod;
          let bod_ref =
            NonNull::new(&mut new_lam_ref.bod_ref as *mut Parents).unwrap();
          add_to_parents(new_bod, bod_ref);
          let new_pi = alloc_pi(
            pi.binder_name.clone(),
            pi.binder_info.clone(),
            new_dom,
            new_lam,
            None,
          );
          let pi_ref = &mut *new_pi.as_ptr();
          let dom_ref =
            NonNull::new(&mut pi_ref.dom_ref as *mut Parents).unwrap();
          add_to_parents(new_dom, dom_ref);
          let img_ref =
            NonNull::new(&mut pi_ref.img_ref as *mut Parents).unwrap();
          add_to_parents(DAGPtr::Lam(new_lam), img_ref);
          cache.insert(key, DAGPtr::Pi(new_pi));
        },

        // --- Standalone Lam: create Lam, visit body ---
        Frame::CreateLamBody(key, old_lam_ptr) => {
          let old_lam = &*old_lam_ptr.as_ptr();
          let old_var_ptr =
            NonNull::new(&old_lam.var as *const Var as *mut Var).unwrap();
          let old_var_key = dag_ptr_key(DAGPtr::Var(old_var_ptr));
          let new_lam = alloc_lam(
            old_lam.var.depth,
            DAGPtr::Var(NonNull::dangling()),
            None,
          );
          let new_lam_ref = &mut *new_lam.as_ptr();
          let new_var =
            NonNull::new(&mut new_lam_ref.var as *mut Var).unwrap();
          cache.insert(old_var_key, DAGPtr::Var(new_var));
          stack.push(Frame::FinishLam(key, new_lam, old_lam_ptr));
          stack.push(Frame::Visit(old_lam.bod));
        },

        Frame::FinishLam(key, new_lam, old_lam_ptr) => {
          let old_lam = &*old_lam_ptr.as_ptr();
          let new_bod = cache[&dag_ptr_key(old_lam.bod)];
          let new_lam_ref = &mut *new_lam.as_ptr();
          new_lam_ref.bod = new_bod;
          let bod_ref =
            NonNull::new(&mut new_lam_ref.bod_ref as *mut Parents).unwrap();
          add_to_parents(new_bod, bod_ref);
          cache.insert(key, DAGPtr::Lam(new_lam));
        },

        // --- Let binder: typ+val visited, create Lam, visit body ---
        Frame::CreateLetLam(key, let_ptr) => {
          let let_node = &*let_ptr.as_ptr();
          let old_lam = &*let_node.bod.as_ptr();
          let old_var_ptr =
            NonNull::new(&old_lam.var as *const Var as *mut Var).unwrap();
          let old_var_key = dag_ptr_key(DAGPtr::Var(old_var_ptr));
          let new_lam = alloc_lam(
            old_lam.var.depth,
            DAGPtr::Var(NonNull::dangling()),
            None,
          );
          let new_lam_ref = &mut *new_lam.as_ptr();
          let new_var =
            NonNull::new(&mut new_lam_ref.var as *mut Var).unwrap();
          cache.insert(old_var_key, DAGPtr::Var(new_var));
          stack.push(Frame::FinishLet(key, let_ptr, new_lam));
          stack.push(Frame::Visit(old_lam.bod));
        },

        Frame::FinishLet(key, let_ptr, new_lam) => {
          let let_node = &*let_ptr.as_ptr();
          let old_lam = &*let_node.bod.as_ptr();
          let new_typ = cache[&dag_ptr_key(let_node.typ)];
          let new_val = cache[&dag_ptr_key(let_node.val)];
          let new_bod = cache[&dag_ptr_key(old_lam.bod)];
          let new_lam_ref = &mut *new_lam.as_ptr();
          new_lam_ref.bod = new_bod;
          let bod_ref =
            NonNull::new(&mut new_lam_ref.bod_ref as *mut Parents).unwrap();
          add_to_parents(new_bod, bod_ref);
          let new_let = alloc_let(
            let_node.binder_name.clone(),
            let_node.non_dep,
            new_typ,
            new_val,
            new_lam,
            None,
          );
          let let_ref = &mut *new_let.as_ptr();
          let typ_ref =
            NonNull::new(&mut let_ref.typ_ref as *mut Parents).unwrap();
          add_to_parents(new_typ, typ_ref);
          let val_ref =
            NonNull::new(&mut let_ref.val_ref as *mut Parents).unwrap();
          add_to_parents(new_val, val_ref);
          let bod_ref2 =
            NonNull::new(&mut let_ref.bod_ref as *mut Parents).unwrap();
          add_to_parents(DAGPtr::Lam(new_lam), bod_ref2);
          cache.insert(key, DAGPtr::Let(new_let));
        },
      }
    }
  }

  cache[&dag_ptr_key(root)]
}
