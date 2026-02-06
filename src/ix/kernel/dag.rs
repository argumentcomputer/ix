use core::ptr::NonNull;

use crate::ix::env::{BinderInfo, Level, Literal, Name};
use crate::lean::nat::Nat;
use rustc_hash::FxHashSet;

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
  /// Parent pointers.
  pub parents: Option<NonNull<Parents>>,
}

impl Copy for Var {}
impl Clone for Var {
  fn clone(&self) -> Self {
    *self
  }
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
    var: Var { depth, binder: BinderPtr::Free, parents: None },
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

fn free_dag_nodes(node: DAGPtr, visited: &mut FxHashSet<usize>) {
  let key = dag_ptr_key(node);
  if !visited.insert(key) {
    return;
  }
  unsafe {
    match node {
      DAGPtr::Var(link) => {
        let var = &*link.as_ptr();
        // Only free separately-allocated free vars; bound vars are
        // embedded in their Lam struct and freed with it.
        if let BinderPtr::Free = var.binder {
          drop(Box::from_raw(link.as_ptr()));
        }
      },
      DAGPtr::Sort(link) => drop(Box::from_raw(link.as_ptr())),
      DAGPtr::Cnst(link) => drop(Box::from_raw(link.as_ptr())),
      DAGPtr::Lit(link) => drop(Box::from_raw(link.as_ptr())),
      DAGPtr::Lam(link) => {
        let lam = &*link.as_ptr();
        free_dag_nodes(lam.bod, visited);
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Fun(link) => {
        let fun = &*link.as_ptr();
        free_dag_nodes(fun.dom, visited);
        free_dag_nodes(DAGPtr::Lam(fun.img), visited);
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Pi(link) => {
        let pi = &*link.as_ptr();
        free_dag_nodes(pi.dom, visited);
        free_dag_nodes(DAGPtr::Lam(pi.img), visited);
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::App(link) => {
        let app = &*link.as_ptr();
        free_dag_nodes(app.fun, visited);
        free_dag_nodes(app.arg, visited);
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Let(link) => {
        let let_node = &*link.as_ptr();
        free_dag_nodes(let_node.typ, visited);
        free_dag_nodes(let_node.val, visited);
        free_dag_nodes(DAGPtr::Lam(let_node.bod), visited);
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Proj(link) => {
        let proj = &*link.as_ptr();
        free_dag_nodes(proj.expr, visited);
        drop(Box::from_raw(link.as_ptr()));
      },
    }
  }
}
