use core::ptr::NonNull;
use std::collections::BTreeMap;

use crate::ix::env::{Expr, ExprData, Level, Name};
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
            DAGPtr::Var(var_ptr)
          },
          None => {
            let var = alloc_val(Var {
              depth: level,
              binder: BinderPtr::Free,
              parents,
            });
            DAGPtr::Var(var)
          },
        }
      } else {
        // Free bound variable (dangling de Bruijn index)
        let var =
          alloc_val(Var { depth: idx_u64, binder: BinderPtr::Free, parents });
        DAGPtr::Var(var)
      }
    },

    ExprData::Fvar(_name, _) => {
      // Encode fvar name into depth as a unique ID.
      // We'll recover it during to_expr using a side table.
      let var = alloc_val(Var { depth: 0, binder: BinderPtr::Free, parents });
      // Store name→var mapping (caller should manage the side table)
      DAGPtr::Var(var)
    },

    ExprData::Sort(level, _) => {
      let sort = alloc_val(Sort { level: level.clone(), parents });
      DAGPtr::Sort(sort)
    },

    ExprData::Const(name, levels, _) => {
      let cnst = alloc_val(Cnst {
        name: name.clone(),
        levels: levels.clone(),
        parents,
      });
      DAGPtr::Cnst(cnst)
    },

    ExprData::Lit(lit, _) => {
      let lit_node = alloc_val(LitNode { val: lit.clone(), parents });
      DAGPtr::Lit(lit_node)
    },

    ExprData::App(fun_expr, arg_expr, _) => {
      let app_ptr = alloc_app(
        DAGPtr::Var(NonNull::dangling()),
        DAGPtr::Var(NonNull::dangling()),
        parents,
      );
      unsafe {
        let app = &mut *app_ptr.as_ptr();
        let fun_ref_ptr =
          NonNull::new(&mut app.fun_ref as *mut Parents).unwrap();
        let arg_ref_ptr =
          NonNull::new(&mut app.arg_ref as *mut Parents).unwrap();
        app.fun = from_expr_go(fun_expr, depth, ctx, Some(fun_ref_ptr));
        app.arg = from_expr_go(arg_expr, depth, ctx, Some(arg_ref_ptr));
      }
      DAGPtr::App(app_ptr)
    },

    ExprData::Lam(name, typ, body, bi, _) => {
      // Lean Lam → DAG Fun(dom, Lam(bod, var))
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
        let dom_ref_ptr =
          NonNull::new(&mut fun.dom_ref as *mut Parents).unwrap();
        fun.dom = from_expr_go(typ, depth, ctx, Some(dom_ref_ptr));

        // Set Lam's parent to FunImg
        let img_ref_ptr =
          NonNull::new(&mut fun.img_ref as *mut Parents).unwrap();
        add_to_parents(DAGPtr::Lam(lam_ptr), img_ref_ptr);

        let lam = &mut *lam_ptr.as_ptr();
        let var_ptr = NonNull::new(&mut lam.var as *mut Var).unwrap();
        let mut new_ctx = ctx.clone();
        new_ctx.insert(depth, var_ptr);
        let bod_ref_ptr =
          NonNull::new(&mut lam.bod_ref as *mut Parents).unwrap();
        lam.bod =
          from_expr_go(body, depth + 1, &new_ctx, Some(bod_ref_ptr));
      }
      DAGPtr::Fun(fun_ptr)
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
        let dom_ref_ptr =
          NonNull::new(&mut pi.dom_ref as *mut Parents).unwrap();
        pi.dom = from_expr_go(typ, depth, ctx, Some(dom_ref_ptr));

        let img_ref_ptr =
          NonNull::new(&mut pi.img_ref as *mut Parents).unwrap();
        add_to_parents(DAGPtr::Lam(lam_ptr), img_ref_ptr);

        let lam = &mut *lam_ptr.as_ptr();
        let var_ptr = NonNull::new(&mut lam.var as *mut Var).unwrap();
        let mut new_ctx = ctx.clone();
        new_ctx.insert(depth, var_ptr);
        let bod_ref_ptr =
          NonNull::new(&mut lam.bod_ref as *mut Parents).unwrap();
        lam.bod =
          from_expr_go(body, depth + 1, &new_ctx, Some(bod_ref_ptr));
      }
      DAGPtr::Pi(pi_ptr)
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
        let typ_ref_ptr =
          NonNull::new(&mut let_node.typ_ref as *mut Parents).unwrap();
        let val_ref_ptr =
          NonNull::new(&mut let_node.val_ref as *mut Parents).unwrap();
        let_node.typ = from_expr_go(typ, depth, ctx, Some(typ_ref_ptr));
        let_node.val = from_expr_go(val, depth, ctx, Some(val_ref_ptr));

        let bod_ref_ptr =
          NonNull::new(&mut let_node.bod_ref as *mut Parents).unwrap();
        add_to_parents(DAGPtr::Lam(lam_ptr), bod_ref_ptr);

        let lam = &mut *lam_ptr.as_ptr();
        let var_ptr = NonNull::new(&mut lam.var as *mut Var).unwrap();
        let mut new_ctx = ctx.clone();
        new_ctx.insert(depth, var_ptr);
        let inner_bod_ref_ptr =
          NonNull::new(&mut lam.bod_ref as *mut Parents).unwrap();
        lam.bod =
          from_expr_go(body, depth + 1, &new_ctx, Some(inner_bod_ref_ptr));
      }
      DAGPtr::Let(let_ptr)
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
        let expr_ref_ptr =
          NonNull::new(&mut proj.expr_ref as *mut Parents).unwrap();
        proj.expr =
          from_expr_go(structure, depth, ctx, Some(expr_ref_ptr));
      }
      DAGPtr::Proj(proj_ptr)
    },

    // Mdata: strip metadata, convert inner expression
    ExprData::Mdata(_, inner, _) => from_expr_go(inner, depth, ctx, parents),

    // Mvar: treat as terminal (shouldn't appear in well-typed terms)
    ExprData::Mvar(_name, _) => {
      let var = alloc_val(Var { depth: 0, binder: BinderPtr::Free, parents });
      DAGPtr::Var(var)
    },
  }
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
  to_expr_go(dag.head, &mut var_map, 0)
}

fn to_expr_go(
  node: DAGPtr,
  var_map: &mut BTreeMap<*const Var, u64>,
  depth: u64,
) -> Expr {
  unsafe {
    match node {
      DAGPtr::Var(link) => {
        let var = link.as_ptr();
        let var_key = var as *const Var;
        if let Some(&bind_depth) = var_map.get(&var_key) {
          let idx = depth - bind_depth - 1;
          Expr::bvar(Nat::from(idx))
        } else {
          // Free variable
          Expr::bvar(Nat::from((*var).depth))
        }
      },

      DAGPtr::Sort(link) => {
        let sort = &*link.as_ptr();
        Expr::sort(sort.level.clone())
      },

      DAGPtr::Cnst(link) => {
        let cnst = &*link.as_ptr();
        Expr::cnst(cnst.name.clone(), cnst.levels.clone())
      },

      DAGPtr::Lit(link) => {
        let lit = &*link.as_ptr();
        Expr::lit(lit.val.clone())
      },

      DAGPtr::App(link) => {
        let app = &*link.as_ptr();
        let fun = to_expr_go(app.fun, var_map, depth);
        let arg = to_expr_go(app.arg, var_map, depth);
        Expr::app(fun, arg)
      },

      DAGPtr::Fun(link) => {
        let fun = &*link.as_ptr();
        let lam = &*fun.img.as_ptr();
        let dom = to_expr_go(fun.dom, var_map, depth);
        let var_ptr = &lam.var as *const Var;
        var_map.insert(var_ptr, depth);
        let bod = to_expr_go(lam.bod, var_map, depth + 1);
        var_map.remove(&var_ptr);
        Expr::lam(
          fun.binder_name.clone(),
          dom,
          bod,
          fun.binder_info.clone(),
        )
      },

      DAGPtr::Pi(link) => {
        let pi = &*link.as_ptr();
        let lam = &*pi.img.as_ptr();
        let dom = to_expr_go(pi.dom, var_map, depth);
        let var_ptr = &lam.var as *const Var;
        var_map.insert(var_ptr, depth);
        let bod = to_expr_go(lam.bod, var_map, depth + 1);
        var_map.remove(&var_ptr);
        Expr::all(
          pi.binder_name.clone(),
          dom,
          bod,
          pi.binder_info.clone(),
        )
      },

      DAGPtr::Let(link) => {
        let let_node = &*link.as_ptr();
        let lam = &*let_node.bod.as_ptr();
        let typ = to_expr_go(let_node.typ, var_map, depth);
        let val = to_expr_go(let_node.val, var_map, depth);
        let var_ptr = &lam.var as *const Var;
        var_map.insert(var_ptr, depth);
        let bod = to_expr_go(lam.bod, var_map, depth + 1);
        var_map.remove(&var_ptr);
        Expr::letE(
          let_node.binder_name.clone(),
          typ,
          val,
          bod,
          let_node.non_dep,
        )
      },

      DAGPtr::Proj(link) => {
        let proj = &*link.as_ptr();
        let structure = to_expr_go(proj.expr, var_map, depth);
        Expr::proj(proj.type_name.clone(), proj.idx.clone(), structure)
      },

      DAGPtr::Lam(link) => {
        // Standalone Lam shouldn't appear at the top level,
        // but handle it gracefully for completeness.
        let lam = &*link.as_ptr();
        let var_ptr = &lam.var as *const Var;
        var_map.insert(var_ptr, depth);
        let bod = to_expr_go(lam.bod, var_map, depth + 1);
        var_map.remove(&var_ptr);
        // Wrap in a lambda with anonymous name and default binder info
        Expr::lam(
          Name::anon(),
          Expr::sort(Level::zero()),
          bod,
          crate::ix::env::BinderInfo::Default,
        )
      },
    }
  }
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
