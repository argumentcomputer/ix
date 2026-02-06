use core::ptr::NonNull;

use crate::ix::env::{BinderInfo, Name};

use super::dag::*;
use super::dll::DLL;

// ============================================================================
// Upcopy
// ============================================================================

pub fn upcopy(new_child: DAGPtr, cc: ParentPtr) {
  unsafe {
    match cc {
      ParentPtr::Root => {},
      ParentPtr::LamBod(link) => {
        let lam = &*link.as_ptr();
        let var = &lam.var;
        let new_lam = alloc_lam(var.depth, new_child, None);
        let new_lam_ref = &mut *new_lam.as_ptr();
        let bod_ref_ptr =
          NonNull::new(&mut new_lam_ref.bod_ref as *mut Parents).unwrap();
        add_to_parents(new_child, bod_ref_ptr);
        let new_var_ptr =
          NonNull::new(&mut new_lam_ref.var as *mut Var).unwrap();
        for parent in DLL::iter_option(var.parents) {
          upcopy(DAGPtr::Var(new_var_ptr), *parent);
        }
        for parent in DLL::iter_option(lam.parents) {
          upcopy(DAGPtr::Lam(new_lam), *parent);
        }
      },
      ParentPtr::AppFun(link) => {
        let app = &mut *link.as_ptr();
        match app.copy {
          Some(cache) => {
            (*cache.as_ptr()).fun = new_child;
          },
          None => {
            let new_app = alloc_app_no_uplinks(new_child, app.arg);
            app.copy = Some(new_app);
            for parent in DLL::iter_option(app.parents) {
              upcopy(DAGPtr::App(new_app), *parent);
            }
          },
        }
      },
      ParentPtr::AppArg(link) => {
        let app = &mut *link.as_ptr();
        match app.copy {
          Some(cache) => {
            (*cache.as_ptr()).arg = new_child;
          },
          None => {
            let new_app = alloc_app_no_uplinks(app.fun, new_child);
            app.copy = Some(new_app);
            for parent in DLL::iter_option(app.parents) {
              upcopy(DAGPtr::App(new_app), *parent);
            }
          },
        }
      },
      ParentPtr::FunDom(link) => {
        let fun = &mut *link.as_ptr();
        match fun.copy {
          Some(cache) => {
            (*cache.as_ptr()).dom = new_child;
          },
          None => {
            let new_fun = alloc_fun_no_uplinks(
              fun.binder_name.clone(),
              fun.binder_info.clone(),
              new_child,
              fun.img,
            );
            fun.copy = Some(new_fun);
            for parent in DLL::iter_option(fun.parents) {
              upcopy(DAGPtr::Fun(new_fun), *parent);
            }
          },
        }
      },
      ParentPtr::FunImg(link) => {
        let fun = &mut *link.as_ptr();
        // new_child must be a Lam
        let new_lam = match new_child {
          DAGPtr::Lam(p) => p,
          _ => panic!("FunImg parent expects Lam child"),
        };
        match fun.copy {
          Some(cache) => {
            (*cache.as_ptr()).img = new_lam;
          },
          None => {
            let new_fun = alloc_fun_no_uplinks(
              fun.binder_name.clone(),
              fun.binder_info.clone(),
              fun.dom,
              new_lam,
            );
            fun.copy = Some(new_fun);
            for parent in DLL::iter_option(fun.parents) {
              upcopy(DAGPtr::Fun(new_fun), *parent);
            }
          },
        }
      },
      ParentPtr::PiDom(link) => {
        let pi = &mut *link.as_ptr();
        match pi.copy {
          Some(cache) => {
            (*cache.as_ptr()).dom = new_child;
          },
          None => {
            let new_pi = alloc_pi_no_uplinks(
              pi.binder_name.clone(),
              pi.binder_info.clone(),
              new_child,
              pi.img,
            );
            pi.copy = Some(new_pi);
            for parent in DLL::iter_option(pi.parents) {
              upcopy(DAGPtr::Pi(new_pi), *parent);
            }
          },
        }
      },
      ParentPtr::PiImg(link) => {
        let pi = &mut *link.as_ptr();
        let new_lam = match new_child {
          DAGPtr::Lam(p) => p,
          _ => panic!("PiImg parent expects Lam child"),
        };
        match pi.copy {
          Some(cache) => {
            (*cache.as_ptr()).img = new_lam;
          },
          None => {
            let new_pi = alloc_pi_no_uplinks(
              pi.binder_name.clone(),
              pi.binder_info.clone(),
              pi.dom,
              new_lam,
            );
            pi.copy = Some(new_pi);
            for parent in DLL::iter_option(pi.parents) {
              upcopy(DAGPtr::Pi(new_pi), *parent);
            }
          },
        }
      },
      ParentPtr::LetTyp(link) => {
        let let_node = &mut *link.as_ptr();
        match let_node.copy {
          Some(cache) => {
            (*cache.as_ptr()).typ = new_child;
          },
          None => {
            let new_let = alloc_let_no_uplinks(
              let_node.binder_name.clone(),
              let_node.non_dep,
              new_child,
              let_node.val,
              let_node.bod,
            );
            let_node.copy = Some(new_let);
            for parent in DLL::iter_option(let_node.parents) {
              upcopy(DAGPtr::Let(new_let), *parent);
            }
          },
        }
      },
      ParentPtr::LetVal(link) => {
        let let_node = &mut *link.as_ptr();
        match let_node.copy {
          Some(cache) => {
            (*cache.as_ptr()).val = new_child;
          },
          None => {
            let new_let = alloc_let_no_uplinks(
              let_node.binder_name.clone(),
              let_node.non_dep,
              let_node.typ,
              new_child,
              let_node.bod,
            );
            let_node.copy = Some(new_let);
            for parent in DLL::iter_option(let_node.parents) {
              upcopy(DAGPtr::Let(new_let), *parent);
            }
          },
        }
      },
      ParentPtr::LetBod(link) => {
        let let_node = &mut *link.as_ptr();
        let new_lam = match new_child {
          DAGPtr::Lam(p) => p,
          _ => panic!("LetBod parent expects Lam child"),
        };
        match let_node.copy {
          Some(cache) => {
            (*cache.as_ptr()).bod = new_lam;
          },
          None => {
            let new_let = alloc_let_no_uplinks(
              let_node.binder_name.clone(),
              let_node.non_dep,
              let_node.typ,
              let_node.val,
              new_lam,
            );
            let_node.copy = Some(new_let);
            for parent in DLL::iter_option(let_node.parents) {
              upcopy(DAGPtr::Let(new_let), *parent);
            }
          },
        }
      },
      ParentPtr::ProjExpr(link) => {
        let proj = &*link.as_ptr();
        let new_proj = alloc_proj_no_uplinks(
          proj.type_name.clone(),
          proj.idx.clone(),
          new_child,
        );
        for parent in DLL::iter_option(proj.parents) {
          upcopy(DAGPtr::Proj(new_proj), *parent);
        }
      },
    }
  }
}

// ============================================================================
// No-uplink allocators for upcopy
// ============================================================================

fn alloc_app_no_uplinks(fun: DAGPtr, arg: DAGPtr) -> NonNull<App> {
  let app_ptr = alloc_val(App {
    fun,
    arg,
    fun_ref: DLL::singleton(ParentPtr::Root),
    arg_ref: DLL::singleton(ParentPtr::Root),
    copy: None,
    parents: None,
  });
  unsafe {
    let app = &mut *app_ptr.as_ptr();
    app.fun_ref = DLL::singleton(ParentPtr::AppFun(app_ptr));
    app.arg_ref = DLL::singleton(ParentPtr::AppArg(app_ptr));
  }
  app_ptr
}

fn alloc_fun_no_uplinks(
  binder_name: Name,
  binder_info: BinderInfo,
  dom: DAGPtr,
  img: NonNull<Lam>,
) -> NonNull<Fun> {
  let fun_ptr = alloc_val(Fun {
    binder_name,
    binder_info,
    dom,
    img,
    dom_ref: DLL::singleton(ParentPtr::Root),
    img_ref: DLL::singleton(ParentPtr::Root),
    copy: None,
    parents: None,
  });
  unsafe {
    let fun = &mut *fun_ptr.as_ptr();
    fun.dom_ref = DLL::singleton(ParentPtr::FunDom(fun_ptr));
    fun.img_ref = DLL::singleton(ParentPtr::FunImg(fun_ptr));
  }
  fun_ptr
}

fn alloc_pi_no_uplinks(
  binder_name: Name,
  binder_info: BinderInfo,
  dom: DAGPtr,
  img: NonNull<Lam>,
) -> NonNull<Pi> {
  let pi_ptr = alloc_val(Pi {
    binder_name,
    binder_info,
    dom,
    img,
    dom_ref: DLL::singleton(ParentPtr::Root),
    img_ref: DLL::singleton(ParentPtr::Root),
    copy: None,
    parents: None,
  });
  unsafe {
    let pi = &mut *pi_ptr.as_ptr();
    pi.dom_ref = DLL::singleton(ParentPtr::PiDom(pi_ptr));
    pi.img_ref = DLL::singleton(ParentPtr::PiImg(pi_ptr));
  }
  pi_ptr
}

fn alloc_let_no_uplinks(
  binder_name: Name,
  non_dep: bool,
  typ: DAGPtr,
  val: DAGPtr,
  bod: NonNull<Lam>,
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
    parents: None,
  });
  unsafe {
    let let_node = &mut *let_ptr.as_ptr();
    let_node.typ_ref = DLL::singleton(ParentPtr::LetTyp(let_ptr));
    let_node.val_ref = DLL::singleton(ParentPtr::LetVal(let_ptr));
    let_node.bod_ref = DLL::singleton(ParentPtr::LetBod(let_ptr));
  }
  let_ptr
}

fn alloc_proj_no_uplinks(
  type_name: Name,
  idx: crate::lean::nat::Nat,
  expr: DAGPtr,
) -> NonNull<ProjNode> {
  let proj_ptr = alloc_val(ProjNode {
    type_name,
    idx,
    expr,
    expr_ref: DLL::singleton(ParentPtr::Root),
    parents: None,
  });
  unsafe {
    let proj = &mut *proj_ptr.as_ptr();
    proj.expr_ref = DLL::singleton(ParentPtr::ProjExpr(proj_ptr));
  }
  proj_ptr
}

// ============================================================================
// Clean up: Clear copy caches after reduction
// ============================================================================

pub fn clean_up(cc: &ParentPtr) {
  unsafe {
    match cc {
      ParentPtr::Root => {},
      ParentPtr::LamBod(link) => {
        let lam = &*link.as_ptr();
        for parent in DLL::iter_option(lam.var.parents) {
          clean_up(parent);
        }
        for parent in DLL::iter_option(lam.parents) {
          clean_up(parent);
        }
      },
      ParentPtr::AppFun(link) | ParentPtr::AppArg(link) => {
        let app = &mut *link.as_ptr();
        if let Some(app_copy) = app.copy {
          let App { fun, arg, fun_ref, arg_ref, .. } =
            &mut *app_copy.as_ptr();
          app.copy = None;
          add_to_parents(*fun, NonNull::new(fun_ref).unwrap());
          add_to_parents(*arg, NonNull::new(arg_ref).unwrap());
          for parent in DLL::iter_option(app.parents) {
            clean_up(parent);
          }
        }
      },
      ParentPtr::FunDom(link) | ParentPtr::FunImg(link) => {
        let fun = &mut *link.as_ptr();
        if let Some(fun_copy) = fun.copy {
          let Fun { dom, img, dom_ref, img_ref, .. } =
            &mut *fun_copy.as_ptr();
          fun.copy = None;
          add_to_parents(*dom, NonNull::new(dom_ref).unwrap());
          add_to_parents(DAGPtr::Lam(*img), NonNull::new(img_ref).unwrap());
          for parent in DLL::iter_option(fun.parents) {
            clean_up(parent);
          }
        }
      },
      ParentPtr::PiDom(link) | ParentPtr::PiImg(link) => {
        let pi = &mut *link.as_ptr();
        if let Some(pi_copy) = pi.copy {
          let Pi { dom, img, dom_ref, img_ref, .. } =
            &mut *pi_copy.as_ptr();
          pi.copy = None;
          add_to_parents(*dom, NonNull::new(dom_ref).unwrap());
          add_to_parents(DAGPtr::Lam(*img), NonNull::new(img_ref).unwrap());
          for parent in DLL::iter_option(pi.parents) {
            clean_up(parent);
          }
        }
      },
      ParentPtr::LetTyp(link)
      | ParentPtr::LetVal(link)
      | ParentPtr::LetBod(link) => {
        let let_node = &mut *link.as_ptr();
        if let Some(let_copy) = let_node.copy {
          let LetNode { typ, val, bod, typ_ref, val_ref, bod_ref, .. } =
            &mut *let_copy.as_ptr();
          let_node.copy = None;
          add_to_parents(*typ, NonNull::new(typ_ref).unwrap());
          add_to_parents(*val, NonNull::new(val_ref).unwrap());
          add_to_parents(DAGPtr::Lam(*bod), NonNull::new(bod_ref).unwrap());
          for parent in DLL::iter_option(let_node.parents) {
            clean_up(parent);
          }
        }
      },
      ParentPtr::ProjExpr(link) => {
        let proj = &*link.as_ptr();
        for parent in DLL::iter_option(proj.parents) {
          clean_up(parent);
        }
      },
    }
  }
}

// ============================================================================
// Replace child
// ============================================================================

pub fn replace_child(old: DAGPtr, new: DAGPtr) {
  unsafe {
    if let Some(parents) = get_parents(old) {
      for parent in DLL::iter_option(Some(parents)) {
        match parent {
          ParentPtr::Root => {},
          ParentPtr::LamBod(p) => (*p.as_ptr()).bod = new,
          ParentPtr::FunDom(p) => (*p.as_ptr()).dom = new,
          ParentPtr::FunImg(p) => match new {
            DAGPtr::Lam(lam) => (*p.as_ptr()).img = lam,
            _ => panic!("FunImg expects Lam"),
          },
          ParentPtr::PiDom(p) => (*p.as_ptr()).dom = new,
          ParentPtr::PiImg(p) => match new {
            DAGPtr::Lam(lam) => (*p.as_ptr()).img = lam,
            _ => panic!("PiImg expects Lam"),
          },
          ParentPtr::AppFun(p) => (*p.as_ptr()).fun = new,
          ParentPtr::AppArg(p) => (*p.as_ptr()).arg = new,
          ParentPtr::LetTyp(p) => (*p.as_ptr()).typ = new,
          ParentPtr::LetVal(p) => (*p.as_ptr()).val = new,
          ParentPtr::LetBod(p) => match new {
            DAGPtr::Lam(lam) => (*p.as_ptr()).bod = lam,
            _ => panic!("LetBod expects Lam"),
          },
          ParentPtr::ProjExpr(p) => (*p.as_ptr()).expr = new,
        }
      }
      set_parents(old, None);
      match get_parents(new) {
        None => set_parents(new, Some(parents)),
        Some(new_parents) => {
          DLL::concat(new_parents, Some(parents));
        },
      }
    }
  }
}

// ============================================================================
// Free dead nodes
// ============================================================================

pub fn free_dead_node(node: DAGPtr) {
  unsafe {
    match node {
      DAGPtr::Lam(link) => {
        let lam = &*link.as_ptr();
        let bod_ref_ptr = &lam.bod_ref as *const Parents;
        if let Some(remaining) = (*bod_ref_ptr).unlink_node() {
          set_parents(lam.bod, Some(remaining));
        } else {
          set_parents(lam.bod, None);
          free_dead_node(lam.bod);
        }
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::App(link) => {
        let app = &*link.as_ptr();
        let fun_ref_ptr = &app.fun_ref as *const Parents;
        if let Some(remaining) = (*fun_ref_ptr).unlink_node() {
          set_parents(app.fun, Some(remaining));
        } else {
          set_parents(app.fun, None);
          free_dead_node(app.fun);
        }
        let arg_ref_ptr = &app.arg_ref as *const Parents;
        if let Some(remaining) = (*arg_ref_ptr).unlink_node() {
          set_parents(app.arg, Some(remaining));
        } else {
          set_parents(app.arg, None);
          free_dead_node(app.arg);
        }
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Fun(link) => {
        let fun = &*link.as_ptr();
        let dom_ref_ptr = &fun.dom_ref as *const Parents;
        if let Some(remaining) = (*dom_ref_ptr).unlink_node() {
          set_parents(fun.dom, Some(remaining));
        } else {
          set_parents(fun.dom, None);
          free_dead_node(fun.dom);
        }
        let img_ref_ptr = &fun.img_ref as *const Parents;
        if let Some(remaining) = (*img_ref_ptr).unlink_node() {
          set_parents(DAGPtr::Lam(fun.img), Some(remaining));
        } else {
          set_parents(DAGPtr::Lam(fun.img), None);
          free_dead_node(DAGPtr::Lam(fun.img));
        }
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Pi(link) => {
        let pi = &*link.as_ptr();
        let dom_ref_ptr = &pi.dom_ref as *const Parents;
        if let Some(remaining) = (*dom_ref_ptr).unlink_node() {
          set_parents(pi.dom, Some(remaining));
        } else {
          set_parents(pi.dom, None);
          free_dead_node(pi.dom);
        }
        let img_ref_ptr = &pi.img_ref as *const Parents;
        if let Some(remaining) = (*img_ref_ptr).unlink_node() {
          set_parents(DAGPtr::Lam(pi.img), Some(remaining));
        } else {
          set_parents(DAGPtr::Lam(pi.img), None);
          free_dead_node(DAGPtr::Lam(pi.img));
        }
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Let(link) => {
        let let_node = &*link.as_ptr();
        let typ_ref_ptr = &let_node.typ_ref as *const Parents;
        if let Some(remaining) = (*typ_ref_ptr).unlink_node() {
          set_parents(let_node.typ, Some(remaining));
        } else {
          set_parents(let_node.typ, None);
          free_dead_node(let_node.typ);
        }
        let val_ref_ptr = &let_node.val_ref as *const Parents;
        if let Some(remaining) = (*val_ref_ptr).unlink_node() {
          set_parents(let_node.val, Some(remaining));
        } else {
          set_parents(let_node.val, None);
          free_dead_node(let_node.val);
        }
        let bod_ref_ptr = &let_node.bod_ref as *const Parents;
        if let Some(remaining) = (*bod_ref_ptr).unlink_node() {
          set_parents(DAGPtr::Lam(let_node.bod), Some(remaining));
        } else {
          set_parents(DAGPtr::Lam(let_node.bod), None);
          free_dead_node(DAGPtr::Lam(let_node.bod));
        }
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Proj(link) => {
        let proj = &*link.as_ptr();
        let expr_ref_ptr = &proj.expr_ref as *const Parents;
        if let Some(remaining) = (*expr_ref_ptr).unlink_node() {
          set_parents(proj.expr, Some(remaining));
        } else {
          set_parents(proj.expr, None);
          free_dead_node(proj.expr);
        }
        drop(Box::from_raw(link.as_ptr()));
      },
      DAGPtr::Var(link) => {
        let var = &*link.as_ptr();
        if let BinderPtr::Free = var.binder {
          drop(Box::from_raw(link.as_ptr()));
        }
      },
      DAGPtr::Sort(link) => drop(Box::from_raw(link.as_ptr())),
      DAGPtr::Cnst(link) => drop(Box::from_raw(link.as_ptr())),
      DAGPtr::Lit(link) => drop(Box::from_raw(link.as_ptr())),
    }
  }
}

// ============================================================================
// Lambda reduction
// ============================================================================

/// Contract a lambda redex: (Fun dom (Lam bod var)) arg → [arg/var]bod.
pub fn reduce_lam(redex: NonNull<App>, lam: NonNull<Lam>) -> DAGPtr {
  unsafe {
    let app = &*redex.as_ptr();
    let lambda = &*lam.as_ptr();
    let var = &lambda.var;
    let arg = app.arg;

    if DLL::is_singleton(lambda.parents) {
      if DLL::is_empty(var.parents) {
        return lambda.bod;
      }
      replace_child(DAGPtr::Var(NonNull::from(var)), arg);
      return lambda.bod;
    }

    if DLL::is_empty(var.parents) {
      return lambda.bod;
    }

    // General case: upcopy arg through var's parents
    for parent in DLL::iter_option(var.parents) {
      upcopy(arg, *parent);
    }
    for parent in DLL::iter_option(var.parents) {
      clean_up(parent);
    }
    lambda.bod
  }
}

/// Contract a let redex: Let(typ, val, Lam(bod, var)) → [val/var]bod.
pub fn reduce_let(let_node: NonNull<LetNode>) -> DAGPtr {
  unsafe {
    let ln = &*let_node.as_ptr();
    let lam = &*ln.bod.as_ptr();
    let var = &lam.var;
    let val = ln.val;

    if DLL::is_singleton(lam.parents) {
      if DLL::is_empty(var.parents) {
        return lam.bod;
      }
      replace_child(DAGPtr::Var(NonNull::from(var)), val);
      return lam.bod;
    }

    if DLL::is_empty(var.parents) {
      return lam.bod;
    }

    for parent in DLL::iter_option(var.parents) {
      upcopy(val, *parent);
    }
    for parent in DLL::iter_option(var.parents) {
      clean_up(parent);
    }
    lam.bod
  }
}
