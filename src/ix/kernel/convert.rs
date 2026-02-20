use core::ptr::NonNull;
use std::collections::BTreeMap;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::ix::env::{BinderInfo, Expr, ExprData, Level, Name};
use crate::lean::nat::Nat;

use super::dag::*;
use super::dll::DLL;

// ============================================================================
// Expr -> DAG
// ============================================================================

pub fn from_expr(expr: &Expr) -> DAG {
  let root_parents = DLL::alloc(ParentPtr::Root);
  let head = from_expr_go(expr, 0, &BTreeMap::new(), Some(root_parents));
  DAG { head }
}

fn from_expr_go(
  expr: &Expr,
  depth: u64,
  ctx: &BTreeMap<u64, NonNull<Var>>,
  parents: Option<NonNull<Parents>>,
) -> DAGPtr {
  // Frame-based iterative Expr → DAG conversion.
  //
  // For compound nodes, we pre-allocate the DAG node with dangling child
  // pointers, then push frames to fill in children after they're converted.
  //
  // The ctx is cloned at binder boundaries (Fun, Pi, Let) to track
  // bound variable bindings.
  enum Frame<'a> {
    Visit {
      expr: &'a Expr,
      depth: u64,
      ctx: BTreeMap<u64, NonNull<Var>>,
      parents: Option<NonNull<Parents>>,
    },
    SetAppFun(NonNull<App>),
    SetAppArg(NonNull<App>),
    SetFunDom(NonNull<Fun>),
    SetPiDom(NonNull<Pi>),
    SetLetTyp(NonNull<LetNode>),
    SetLetVal(NonNull<LetNode>),
    SetProjExpr(NonNull<ProjNode>),
    // After domain is set, wire up binder body with new ctx
    FunBody {
      lam_ptr: NonNull<Lam>,
      body: &'a Expr,
      depth: u64,
      ctx: BTreeMap<u64, NonNull<Var>>,
    },
    PiBody {
      lam_ptr: NonNull<Lam>,
      body: &'a Expr,
      depth: u64,
      ctx: BTreeMap<u64, NonNull<Var>>,
    },
    LetBody {
      lam_ptr: NonNull<Lam>,
      body: &'a Expr,
      depth: u64,
      ctx: BTreeMap<u64, NonNull<Var>>,
    },
    SetLamBod(NonNull<Lam>),
  }

  let mut work: Vec<Frame<'_>> = vec![Frame::Visit {
    expr,
    depth,
    ctx: ctx.clone(),
    parents,
  }];
  // Results stack holds DAGPtr for each completed subtree
  let mut results: Vec<DAGPtr> = Vec::new();
  let mut visit_count: u64 = 0;
  // Cache for context-independent leaf nodes (Cnst, Sort, Lit).
  // Keyed by Arc pointer identity. Enables DAG sharing so the infer cache
  // (keyed by DAGPtr address) can dedup repeated references to the same constant.
  let mut leaf_cache: FxHashMap<*const ExprData, DAGPtr> = FxHashMap::default();

  while let Some(frame) = work.pop() {
    visit_count += 1;
    if visit_count % 100_000 == 0 {
      eprintln!("[from_expr_go] visit_count={visit_count} work_len={}", work.len());
    }
    match frame {
      Frame::Visit { expr, depth, ctx, parents } => {
        match expr.as_data() {
          ExprData::Bvar(idx, _) => {
            let idx_u64 = idx.to_u64().unwrap_or(u64::MAX);
            if idx_u64 < depth {
              let level = depth - 1 - idx_u64;
              match ctx.get(&level) {
                Some(&var_ptr) => {
                  if let Some(parent_link) = parents {
                    add_to_parents(DAGPtr::Var(var_ptr), parent_link);
                  }
                  results.push(DAGPtr::Var(var_ptr));
                },
                None => {
                  let var = alloc_val(Var {
                    depth: level,
                    binder: BinderPtr::Free,
                    fvar_name: None,
                    parents,
                  });
                  results.push(DAGPtr::Var(var));
                },
              }
            } else {
              let var = alloc_val(Var {
                depth: idx_u64,
                binder: BinderPtr::Free,
                fvar_name: None,
                parents,
              });
              results.push(DAGPtr::Var(var));
            }
          },

          ExprData::Fvar(name, _) => {
            let var = alloc_val(Var {
              depth: 0,
              binder: BinderPtr::Free,
              fvar_name: Some(name.clone()),
              parents,
            });
            results.push(DAGPtr::Var(var));
          },

          ExprData::Sort(level, _) => {
            let key = Arc::as_ptr(&expr.0);
            if let Some(&cached) = leaf_cache.get(&key) {
              if let Some(parent_link) = parents {
                add_to_parents(cached, parent_link);
              }
              results.push(cached);
            } else {
              let sort = alloc_val(Sort { level: level.clone(), parents });
              let ptr = DAGPtr::Sort(sort);
              leaf_cache.insert(key, ptr);
              results.push(ptr);
            }
          },

          ExprData::Const(name, levels, _) => {
            let key = Arc::as_ptr(&expr.0);
            if let Some(&cached) = leaf_cache.get(&key) {
              if let Some(parent_link) = parents {
                add_to_parents(cached, parent_link);
              }
              results.push(cached);
            } else {
              let cnst = alloc_val(Cnst {
                name: name.clone(),
                levels: levels.clone(),
                parents,
              });
              let ptr = DAGPtr::Cnst(cnst);
              leaf_cache.insert(key, ptr);
              results.push(ptr);
            }
          },

          ExprData::Lit(lit, _) => {
            let key = Arc::as_ptr(&expr.0);
            if let Some(&cached) = leaf_cache.get(&key) {
              if let Some(parent_link) = parents {
                add_to_parents(cached, parent_link);
              }
              results.push(cached);
            } else {
              let lit_node = alloc_val(LitNode { val: lit.clone(), parents });
              let ptr = DAGPtr::Lit(lit_node);
              leaf_cache.insert(key, ptr);
              results.push(ptr);
            }
          },

          ExprData::App(fun_expr, arg_expr, _) => {
            let app_ptr = alloc_app(
              DAGPtr::Var(NonNull::dangling()),
              DAGPtr::Var(NonNull::dangling()),
              parents,
            );
            unsafe {
              let app = &mut *app_ptr.as_ptr();
              let fun_ref =
                NonNull::new(&mut app.fun_ref as *mut Parents).unwrap();
              let arg_ref =
                NonNull::new(&mut app.arg_ref as *mut Parents).unwrap();
              // Process arg first (pushed last = processed first after fun)
              work.push(Frame::SetAppArg(app_ptr));
              work.push(Frame::Visit {
                expr: arg_expr,
                depth,
                ctx: ctx.clone(),
                parents: Some(arg_ref),
              });
              work.push(Frame::SetAppFun(app_ptr));
              work.push(Frame::Visit {
                expr: fun_expr,
                depth,
                ctx,
                parents: Some(fun_ref),
              });
            }
            results.push(DAGPtr::App(app_ptr));
          },

          ExprData::Lam(name, typ, body, bi, _) => {
            let lam_ptr =
              alloc_lam(depth, DAGPtr::Var(NonNull::dangling()), None);
            let fun_ptr = alloc_fun(
              name.clone(),
              bi.clone(),
              DAGPtr::Var(NonNull::dangling()),
              lam_ptr,
              parents,
            );
            unsafe {
              let fun = &mut *fun_ptr.as_ptr();
              let dom_ref =
                NonNull::new(&mut fun.dom_ref as *mut Parents).unwrap();
              let img_ref =
                NonNull::new(&mut fun.img_ref as *mut Parents).unwrap();
              add_to_parents(DAGPtr::Lam(lam_ptr), img_ref);

              let dom_ctx = ctx.clone();
              work.push(Frame::FunBody {
                lam_ptr,
                body,
                depth,
                ctx,
              });
              work.push(Frame::SetFunDom(fun_ptr));
              work.push(Frame::Visit {
                expr: typ,
                depth,
                ctx: dom_ctx,
                parents: Some(dom_ref),
              });
            }
            results.push(DAGPtr::Fun(fun_ptr));
          },

          ExprData::ForallE(name, typ, body, bi, _) => {
            let lam_ptr =
              alloc_lam(depth, DAGPtr::Var(NonNull::dangling()), None);
            let pi_ptr = alloc_pi(
              name.clone(),
              bi.clone(),
              DAGPtr::Var(NonNull::dangling()),
              lam_ptr,
              parents,
            );
            unsafe {
              let pi = &mut *pi_ptr.as_ptr();
              let dom_ref =
                NonNull::new(&mut pi.dom_ref as *mut Parents).unwrap();
              let img_ref =
                NonNull::new(&mut pi.img_ref as *mut Parents).unwrap();
              add_to_parents(DAGPtr::Lam(lam_ptr), img_ref);

              let dom_ctx = ctx.clone();
              work.push(Frame::PiBody {
                lam_ptr,
                body,
                depth,
                ctx,
              });
              work.push(Frame::SetPiDom(pi_ptr));
              work.push(Frame::Visit {
                expr: typ,
                depth,
                ctx: dom_ctx,
                parents: Some(dom_ref),
              });
            }
            results.push(DAGPtr::Pi(pi_ptr));
          },

          ExprData::LetE(name, typ, val, body, non_dep, _) => {
            let lam_ptr =
              alloc_lam(depth, DAGPtr::Var(NonNull::dangling()), None);
            let let_ptr = alloc_let(
              name.clone(),
              *non_dep,
              DAGPtr::Var(NonNull::dangling()),
              DAGPtr::Var(NonNull::dangling()),
              lam_ptr,
              parents,
            );
            unsafe {
              let let_node = &mut *let_ptr.as_ptr();
              let typ_ref =
                NonNull::new(&mut let_node.typ_ref as *mut Parents).unwrap();
              let val_ref =
                NonNull::new(&mut let_node.val_ref as *mut Parents).unwrap();
              let bod_ref =
                NonNull::new(&mut let_node.bod_ref as *mut Parents).unwrap();
              add_to_parents(DAGPtr::Lam(lam_ptr), bod_ref);

              work.push(Frame::LetBody {
                lam_ptr,
                body,
                depth,
                ctx: ctx.clone(),
              });
              work.push(Frame::SetLetVal(let_ptr));
              work.push(Frame::Visit {
                expr: val,
                depth,
                ctx: ctx.clone(),
                parents: Some(val_ref),
              });
              work.push(Frame::SetLetTyp(let_ptr));
              work.push(Frame::Visit {
                expr: typ,
                depth,
                ctx,
                parents: Some(typ_ref),
              });
            }
            results.push(DAGPtr::Let(let_ptr));
          },

          ExprData::Proj(type_name, idx, structure, _) => {
            let proj_ptr = alloc_proj(
              type_name.clone(),
              idx.clone(),
              DAGPtr::Var(NonNull::dangling()),
              parents,
            );
            unsafe {
              let proj = &mut *proj_ptr.as_ptr();
              let expr_ref =
                NonNull::new(&mut proj.expr_ref as *mut Parents).unwrap();
              work.push(Frame::SetProjExpr(proj_ptr));
              work.push(Frame::Visit {
                expr: structure,
                depth,
                ctx,
                parents: Some(expr_ref),
              });
            }
            results.push(DAGPtr::Proj(proj_ptr));
          },

          ExprData::Mdata(_, inner, _) => {
            // Strip metadata, convert inner
            work.push(Frame::Visit { expr: inner, depth, ctx, parents });
          },

          ExprData::Mvar(_name, _) => {
            let var = alloc_val(Var {
              depth: 0,
              binder: BinderPtr::Free,
              fvar_name: None,
              parents,
            });
            results.push(DAGPtr::Var(var));
          },
        }
      },
      Frame::SetAppFun(app_ptr) => unsafe {
        let result = results.pop().unwrap();
        (*app_ptr.as_ptr()).fun = result;
      },
      Frame::SetAppArg(app_ptr) => unsafe {
        let result = results.pop().unwrap();
        (*app_ptr.as_ptr()).arg = result;
      },
      Frame::SetFunDom(fun_ptr) => unsafe {
        let result = results.pop().unwrap();
        (*fun_ptr.as_ptr()).dom = result;
      },
      Frame::SetPiDom(pi_ptr) => unsafe {
        let result = results.pop().unwrap();
        (*pi_ptr.as_ptr()).dom = result;
      },
      Frame::SetLetTyp(let_ptr) => unsafe {
        let result = results.pop().unwrap();
        (*let_ptr.as_ptr()).typ = result;
      },
      Frame::SetLetVal(let_ptr) => unsafe {
        let result = results.pop().unwrap();
        (*let_ptr.as_ptr()).val = result;
      },
      Frame::SetProjExpr(proj_ptr) => unsafe {
        let result = results.pop().unwrap();
        (*proj_ptr.as_ptr()).expr = result;
      },
      Frame::SetLamBod(lam_ptr) => unsafe {
        let result = results.pop().unwrap();
        (*lam_ptr.as_ptr()).bod = result;
      },
      Frame::FunBody { lam_ptr, body, depth, mut ctx } => unsafe {
        // Domain has been set; now set up body with var binding
        let lam = &mut *lam_ptr.as_ptr();
        let var_ptr = NonNull::new(&mut lam.var as *mut Var).unwrap();
        ctx.insert(depth, var_ptr);
        let bod_ref =
          NonNull::new(&mut lam.bod_ref as *mut Parents).unwrap();
        work.push(Frame::SetLamBod(lam_ptr));
        work.push(Frame::Visit {
          expr: body,
          depth: depth + 1,
          ctx,
          parents: Some(bod_ref),
        });
      },
      Frame::PiBody { lam_ptr, body, depth, mut ctx } => unsafe {
        let lam = &mut *lam_ptr.as_ptr();
        let var_ptr = NonNull::new(&mut lam.var as *mut Var).unwrap();
        ctx.insert(depth, var_ptr);
        let bod_ref =
          NonNull::new(&mut lam.bod_ref as *mut Parents).unwrap();
        work.push(Frame::SetLamBod(lam_ptr));
        work.push(Frame::Visit {
          expr: body,
          depth: depth + 1,
          ctx,
          parents: Some(bod_ref),
        });
      },
      Frame::LetBody { lam_ptr, body, depth, mut ctx } => unsafe {
        let lam = &mut *lam_ptr.as_ptr();
        let var_ptr = NonNull::new(&mut lam.var as *mut Var).unwrap();
        ctx.insert(depth, var_ptr);
        let bod_ref =
          NonNull::new(&mut lam.bod_ref as *mut Parents).unwrap();
        work.push(Frame::SetLamBod(lam_ptr));
        work.push(Frame::Visit {
          expr: body,
          depth: depth + 1,
          ctx,
          parents: Some(bod_ref),
        });
      },
    }
  }

  results.pop().unwrap()
}

// ============================================================================
// Literal clone
// ============================================================================

impl Clone for crate::ix::env::Literal {
  fn clone(&self) -> Self {
    match self {
      crate::ix::env::Literal::NatVal(n) => {
        crate::ix::env::Literal::NatVal(n.clone())
      },
      crate::ix::env::Literal::StrVal(s) => {
        crate::ix::env::Literal::StrVal(s.clone())
      },
    }
  }
}

// ============================================================================
// DAG -> Expr
// ============================================================================

pub fn to_expr(dag: &DAG) -> Expr {
  let mut var_map: BTreeMap<*const Var, u64> = BTreeMap::new();
  let mut cache: rustc_hash::FxHashMap<(usize, u64), Expr> =
    rustc_hash::FxHashMap::default();
  to_expr_go(dag.head, &mut var_map, 0, &mut cache)
}

fn to_expr_go(
  node: DAGPtr,
  var_map: &mut BTreeMap<*const Var, u64>,
  depth: u64,
  cache: &mut rustc_hash::FxHashMap<(usize, u64), Expr>,
) -> Expr {
  // Frame-based iterative conversion from DAG to Expr.
  //
  // Uses a cache keyed on (dag_ptr_key, depth) to avoid exponential
  // blowup when the DAG has sharing (e.g., after beta reduction).
  //
  // For binder nodes (Fun, Pi, Let, Lam), the pattern is:
  //   1. Visit domain/type/value children
  //   2. BinderBody: register var in var_map, push Visit for body
  //   3. *Build: pop results, unregister var, build Expr
  //   4. CacheStore: cache the built result
  enum Frame {
    Visit(DAGPtr, u64),
    App,
    BinderBody(*const Var, DAGPtr, u64),
    FunBuild(Name, BinderInfo, *const Var),
    PiBuild(Name, BinderInfo, *const Var),
    LetBuild(Name, bool, *const Var),
    Proj(Name, Nat),
    LamBuild(*const Var),
    CacheStore(usize, u64),
  }

  let mut work: Vec<Frame> = vec![Frame::Visit(node, depth)];
  let mut results: Vec<Expr> = Vec::new();

  while let Some(frame) = work.pop() {
    match frame {
      Frame::Visit(node, depth) => unsafe {
        // Check cache first for non-Var nodes
        match node {
          DAGPtr::Var(_) => {}, // Vars depend on var_map, skip cache
          _ => {
            let key = (dag_ptr_key(node), depth);
            if let Some(cached) = cache.get(&key) {
              results.push(cached.clone());
              continue;
            }
          },
        }
        match node {
          DAGPtr::Var(link) => {
            let var = link.as_ptr();
            let var_key = var as *const Var;
            if let Some(&bind_depth) = var_map.get(&var_key) {
              results.push(Expr::bvar(Nat::from(depth - bind_depth - 1)));
            } else if let Some(name) = &(*var).fvar_name {
              results.push(Expr::fvar(name.clone()));
            } else {
              results.push(Expr::bvar(Nat::from((*var).depth)));
            }
          },
          DAGPtr::Sort(link) => {
            let sort = &*link.as_ptr();
            results.push(Expr::sort(sort.level.clone()));
          },
          DAGPtr::Cnst(link) => {
            let cnst = &*link.as_ptr();
            results.push(Expr::cnst(cnst.name.clone(), cnst.levels.clone()));
          },
          DAGPtr::Lit(link) => {
            let lit = &*link.as_ptr();
            results.push(Expr::lit(lit.val.clone()));
          },
          DAGPtr::App(link) => {
            let app = &*link.as_ptr();
            work.push(Frame::CacheStore(dag_ptr_key(node), depth));
            work.push(Frame::App);
            work.push(Frame::Visit(app.arg, depth));
            work.push(Frame::Visit(app.fun, depth));
          },
          DAGPtr::Fun(link) => {
            let fun = &*link.as_ptr();
            let lam = &*fun.img.as_ptr();
            let var_ptr = &lam.var as *const Var;
            work.push(Frame::CacheStore(dag_ptr_key(node), depth));
            work.push(Frame::FunBuild(
              fun.binder_name.clone(),
              fun.binder_info.clone(),
              var_ptr,
            ));
            work.push(Frame::BinderBody(var_ptr, lam.bod, depth));
            work.push(Frame::Visit(fun.dom, depth));
          },
          DAGPtr::Pi(link) => {
            let pi = &*link.as_ptr();
            let lam = &*pi.img.as_ptr();
            let var_ptr = &lam.var as *const Var;
            work.push(Frame::CacheStore(dag_ptr_key(node), depth));
            work.push(Frame::PiBuild(
              pi.binder_name.clone(),
              pi.binder_info.clone(),
              var_ptr,
            ));
            work.push(Frame::BinderBody(var_ptr, lam.bod, depth));
            work.push(Frame::Visit(pi.dom, depth));
          },
          DAGPtr::Let(link) => {
            let let_node = &*link.as_ptr();
            let lam = &*let_node.bod.as_ptr();
            let var_ptr = &lam.var as *const Var;
            work.push(Frame::CacheStore(dag_ptr_key(node), depth));
            work.push(Frame::LetBuild(
              let_node.binder_name.clone(),
              let_node.non_dep,
              var_ptr,
            ));
            work.push(Frame::BinderBody(var_ptr, lam.bod, depth));
            work.push(Frame::Visit(let_node.val, depth));
            work.push(Frame::Visit(let_node.typ, depth));
          },
          DAGPtr::Proj(link) => {
            let proj = &*link.as_ptr();
            work.push(Frame::CacheStore(dag_ptr_key(node), depth));
            work.push(Frame::Proj(proj.type_name.clone(), proj.idx.clone()));
            work.push(Frame::Visit(proj.expr, depth));
          },
          DAGPtr::Lam(link) => {
            // Standalone Lam: no domain to visit, just body
            let lam = &*link.as_ptr();
            let var_ptr = &lam.var as *const Var;
            work.push(Frame::CacheStore(dag_ptr_key(node), depth));
            work.push(Frame::LamBuild(var_ptr));
            work.push(Frame::BinderBody(var_ptr, lam.bod, depth));
          },
        }
      },
      Frame::App => {
        let arg = results.pop().unwrap();
        let fun = results.pop().unwrap();
        results.push(Expr::app(fun, arg));
      },
      Frame::BinderBody(var_ptr, body, depth) => {
        var_map.insert(var_ptr, depth);
        work.push(Frame::Visit(body, depth + 1));
      },
      Frame::FunBuild(name, bi, var_ptr) => {
        var_map.remove(&var_ptr);
        let bod = results.pop().unwrap();
        let dom = results.pop().unwrap();
        results.push(Expr::lam(name, dom, bod, bi));
      },
      Frame::PiBuild(name, bi, var_ptr) => {
        var_map.remove(&var_ptr);
        let bod = results.pop().unwrap();
        let dom = results.pop().unwrap();
        results.push(Expr::all(name, dom, bod, bi));
      },
      Frame::LetBuild(name, non_dep, var_ptr) => {
        var_map.remove(&var_ptr);
        let bod = results.pop().unwrap();
        let val = results.pop().unwrap();
        let typ = results.pop().unwrap();
        results.push(Expr::letE(name, typ, val, bod, non_dep));
      },
      Frame::Proj(name, idx) => {
        let structure = results.pop().unwrap();
        results.push(Expr::proj(name, idx, structure));
      },
      Frame::LamBuild(var_ptr) => {
        var_map.remove(&var_ptr);
        let bod = results.pop().unwrap();
        results.push(Expr::lam(
          Name::anon(),
          Expr::sort(Level::zero()),
          bod,
          BinderInfo::Default,
        ));
      },
      Frame::CacheStore(key, depth) => {
        let result = results.last().unwrap().clone();
        cache.insert((key, depth), result);
      },
    }
  }

  results.pop().unwrap()
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::{BinderInfo, Literal};
  use quickcheck::{Arbitrary, Gen};
  use quickcheck_macros::quickcheck;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }

  fn mk_name2(a: &str, b: &str) -> Name {
    Name::str(Name::str(Name::anon(), a.into()), b.into())
  }

  fn nat_type() -> Expr {
    Expr::cnst(mk_name("Nat"), vec![])
  }

  fn nat_zero() -> Expr {
    Expr::cnst(mk_name2("Nat", "zero"), vec![])
  }

  // ==========================================================================
  // Terminal roundtrips
  // ==========================================================================

  #[test]
  fn roundtrip_sort() {
    let e = Expr::sort(Level::succ(Level::zero()));
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_sort_param() {
    let e = Expr::sort(Level::param(mk_name("u")));
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_const() {
    let e = Expr::cnst(
      mk_name("Foo"),
      vec![Level::zero(), Level::succ(Level::zero())],
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_nat_lit() {
    let e = Expr::lit(Literal::NatVal(Nat::from(42u64)));
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_string_lit() {
    let e = Expr::lit(Literal::StrVal("hello world".into()));
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  // ==========================================================================
  // Binder roundtrips
  // ==========================================================================

  #[test]
  fn roundtrip_identity_lambda() {
    // fun (x : Nat) => x
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_const_lambda() {
    // fun (x : Nat) (y : Nat) => x
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::lam(
        mk_name("y"),
        nat_type(),
        Expr::bvar(Nat::from(1u64)),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_pi() {
    // (x : Nat) → Nat
    let e = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_dependent_pi() {
    // (A : Sort 0) → A → A
    let sort0 = Expr::sort(Level::zero());
    let e = Expr::all(
      mk_name("A"),
      sort0,
      Expr::all(
        mk_name("x"),
        Expr::bvar(Nat::from(0u64)), // A
        Expr::bvar(Nat::from(1u64)), // A
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  // ==========================================================================
  // App roundtrips
  // ==========================================================================

  #[test]
  fn roundtrip_app() {
    // f a
    let e = Expr::app(
      Expr::cnst(mk_name("f"), vec![]),
      nat_zero(),
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_nested_app() {
    // f a b
    let f = Expr::cnst(mk_name("f"), vec![]);
    let a = nat_zero();
    let b = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let e = Expr::app(Expr::app(f, a), b);
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  // ==========================================================================
  // Let roundtrips
  // ==========================================================================

  #[test]
  fn roundtrip_let() {
    // let x : Nat := Nat.zero in x
    let e = Expr::letE(
      mk_name("x"),
      nat_type(),
      nat_zero(),
      Expr::bvar(Nat::from(0u64)),
      false,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_let_non_dep() {
    // let x : Nat := Nat.zero in Nat.zero  (non_dep = true)
    let e = Expr::letE(
      mk_name("x"),
      nat_type(),
      nat_zero(),
      nat_zero(),
      true,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  // ==========================================================================
  // Proj roundtrips
  // ==========================================================================

  #[test]
  fn roundtrip_proj() {
    let e = Expr::proj(mk_name("Prod"), Nat::from(0u64), nat_zero());
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  // ==========================================================================
  // Complex roundtrips
  // ==========================================================================

  #[test]
  fn roundtrip_app_of_lambda() {
    // (fun x : Nat => x) Nat.zero
    let id_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let e = Expr::app(id_fn, nat_zero());
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_lambda_in_lambda() {
    // fun (f : Nat → Nat) (x : Nat) => f x
    let nat_to_nat = Expr::all(
      mk_name("_"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let e = Expr::lam(
      mk_name("f"),
      nat_to_nat,
      Expr::lam(
        mk_name("x"),
        nat_type(),
        Expr::app(
          Expr::bvar(Nat::from(1u64)), // f
          Expr::bvar(Nat::from(0u64)), // x
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_bvar_sharing() {
    // fun (x : Nat) => App(x, x)
    // Both bvar(0) should map to the same Var in DAG
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::app(
        Expr::bvar(Nat::from(0u64)),
        Expr::bvar(Nat::from(0u64)),
      ),
      BinderInfo::Default,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_free_bvar() {
    // Bvar(5) with no enclosing binder — should survive roundtrip
    let e = Expr::bvar(Nat::from(5u64));
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  #[test]
  fn roundtrip_implicit_binder() {
    // fun {x : Nat} => x
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Implicit,
    );
    let dag = from_expr(&e);
    let result = to_expr(&dag);
    assert_eq!(result, e);
  }

  // ==========================================================================
  // Property tests (quickcheck)
  // ==========================================================================

  /// Generate a random well-formed Expr with bound variables properly scoped.
  /// `depth` tracks how many binders are in scope (for valid bvar generation).
  fn arb_expr(g: &mut Gen, depth: u64, size: usize) -> Expr {
    if size == 0 {
      // Terminal: pick among Sort, Const, Lit, or Bvar (if depth > 0)
      let choices = if depth > 0 { 5 } else { 4 };
      match usize::arbitrary(g) % choices {
        0 => Expr::sort(arb_level(g, 2)),
        1 => {
          let names = ["Nat", "Bool", "String", "Unit", "Int"];
          let idx = usize::arbitrary(g) % names.len();
          Expr::cnst(mk_name(names[idx]), vec![])
        },
        2 => {
          let n = u64::arbitrary(g) % 100;
          Expr::lit(Literal::NatVal(Nat::from(n)))
        },
        3 => {
          let s: String = String::arbitrary(g);
          // Truncate at a char boundary to avoid panics
          let s: String = s.chars().take(10).collect();
          Expr::lit(Literal::StrVal(s))
        },
        4 => {
          // Bvar within scope
          let idx = u64::arbitrary(g) % depth;
          Expr::bvar(Nat::from(idx))
        },
        _ => unreachable!(),
      }
    } else {
      let next = size / 2;
      match usize::arbitrary(g) % 5 {
        0 => {
          // App
          let f = arb_expr(g, depth, next);
          let a = arb_expr(g, depth, next);
          Expr::app(f, a)
        },
        1 => {
          // Lam
          let dom = arb_expr(g, depth, next);
          let bod = arb_expr(g, depth + 1, next);
          Expr::lam(mk_name("x"), dom, bod, BinderInfo::Default)
        },
        2 => {
          // Pi
          let dom = arb_expr(g, depth, next);
          let bod = arb_expr(g, depth + 1, next);
          Expr::all(mk_name("a"), dom, bod, BinderInfo::Default)
        },
        3 => {
          // Let
          let typ = arb_expr(g, depth, next);
          let val = arb_expr(g, depth, next);
          let bod = arb_expr(g, depth + 1, next / 2);
          Expr::letE(mk_name("v"), typ, val, bod, bool::arbitrary(g))
        },
        4 => {
          // Proj
          let idx = u64::arbitrary(g) % 4;
          let structure = arb_expr(g, depth, next);
          Expr::proj(mk_name("S"), Nat::from(idx), structure)
        },
        _ => unreachable!(),
      }
    }
  }

  fn arb_level(g: &mut Gen, size: usize) -> Level {
    if size == 0 {
      match usize::arbitrary(g) % 3 {
        0 => Level::zero(),
        1 => {
          let params = ["u", "v", "w"];
          let idx = usize::arbitrary(g) % params.len();
          Level::param(mk_name(params[idx]))
        },
        2 => Level::succ(Level::zero()),
        _ => unreachable!(),
      }
    } else {
      match usize::arbitrary(g) % 3 {
        0 => Level::succ(arb_level(g, size - 1)),
        1 => Level::max(arb_level(g, size / 2), arb_level(g, size / 2)),
        2 => Level::imax(arb_level(g, size / 2), arb_level(g, size / 2)),
        _ => unreachable!(),
      }
    }
  }

  /// Newtype wrapper for quickcheck Arbitrary derivation.
  #[derive(Clone, Debug)]
  struct ArbExpr(Expr);

  impl Arbitrary for ArbExpr {
    fn arbitrary(g: &mut Gen) -> Self {
      let size = usize::arbitrary(g) % 5;
      ArbExpr(arb_expr(g, 0, size))
    }
  }

  #[quickcheck]
  fn prop_roundtrip(e: ArbExpr) -> bool {
    let dag = from_expr(&e.0);
    let result = to_expr(&dag);
    result == e.0
  }

  /// Same test but with expressions generated inside binders.
  #[derive(Clone, Debug)]
  struct ArbBinderExpr(Expr);

  impl Arbitrary for ArbBinderExpr {
    fn arbitrary(g: &mut Gen) -> Self {
      let inner_size = usize::arbitrary(g) % 4;
      let body = arb_expr(g, 1, inner_size);
      let dom = arb_expr(g, 0, 0);
      ArbBinderExpr(Expr::lam(
        mk_name("x"),
        dom,
        body,
        BinderInfo::Default,
      ))
    }
  }

  #[quickcheck]
  fn prop_roundtrip_binder(e: ArbBinderExpr) -> bool {
    let dag = from_expr(&e.0);
    let result = to_expr(&dag);
    result == e.0
  }
}
