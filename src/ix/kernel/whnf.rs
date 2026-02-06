use core::ptr::NonNull;

use crate::ix::env::*;
use crate::lean::nat::Nat;
use num_bigint::BigUint;

use super::convert::{from_expr, to_expr};
use super::dag::*;
use super::level::{simplify, subst_level};
use super::upcopy::{reduce_lam, reduce_let};


// ============================================================================
// Expression helpers (inst, unfold_apps, foldl_apps, subst_expr_levels)
// ============================================================================

/// Instantiate bound variables: `body[0 := substs[0], 1 := substs[1], ...]`.
/// `substs[0]` replaces `Bvar(0)` (innermost).
pub fn inst(body: &Expr, substs: &[Expr]) -> Expr {
  if substs.is_empty() {
    return body.clone();
  }
  inst_aux(body, substs, 0)
}

fn inst_aux(e: &Expr, substs: &[Expr], offset: u64) -> Expr {
  match e.as_data() {
    ExprData::Bvar(idx, _) => {
      let idx_u64 = idx.to_u64().unwrap_or(u64::MAX);
      if idx_u64 >= offset {
        let adjusted = (idx_u64 - offset) as usize;
        if adjusted < substs.len() {
          return substs[adjusted].clone();
        }
      }
      e.clone()
    },
    ExprData::App(f, a, _) => {
      let f2 = inst_aux(f, substs, offset);
      let a2 = inst_aux(a, substs, offset);
      Expr::app(f2, a2)
    },
    ExprData::Lam(n, t, b, bi, _) => {
      let t2 = inst_aux(t, substs, offset);
      let b2 = inst_aux(b, substs, offset + 1);
      Expr::lam(n.clone(), t2, b2, bi.clone())
    },
    ExprData::ForallE(n, t, b, bi, _) => {
      let t2 = inst_aux(t, substs, offset);
      let b2 = inst_aux(b, substs, offset + 1);
      Expr::all(n.clone(), t2, b2, bi.clone())
    },
    ExprData::LetE(n, t, v, b, nd, _) => {
      let t2 = inst_aux(t, substs, offset);
      let v2 = inst_aux(v, substs, offset);
      let b2 = inst_aux(b, substs, offset + 1);
      Expr::letE(n.clone(), t2, v2, b2, *nd)
    },
    ExprData::Proj(n, i, s, _) => {
      let s2 = inst_aux(s, substs, offset);
      Expr::proj(n.clone(), i.clone(), s2)
    },
    ExprData::Mdata(kvs, inner, _) => {
      let inner2 = inst_aux(inner, substs, offset);
      Expr::mdata(kvs.clone(), inner2)
    },
    // Terminals with no bound vars
    ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Fvar(..)
    | ExprData::Mvar(..)
    | ExprData::Lit(..) => e.clone(),
  }
}

/// Abstract: replace free variable `fvar` with `Bvar(offset)` in `e`.
pub fn abstr(e: &Expr, fvars: &[Expr]) -> Expr {
  if fvars.is_empty() {
    return e.clone();
  }
  abstr_aux(e, fvars, 0)
}

fn abstr_aux(e: &Expr, fvars: &[Expr], offset: u64) -> Expr {
  match e.as_data() {
    ExprData::Fvar(..) => {
      for (i, fv) in fvars.iter().enumerate().rev() {
        if e == fv {
          return Expr::bvar(Nat::from(i as u64 + offset));
        }
      }
      e.clone()
    },
    ExprData::App(f, a, _) => {
      let f2 = abstr_aux(f, fvars, offset);
      let a2 = abstr_aux(a, fvars, offset);
      Expr::app(f2, a2)
    },
    ExprData::Lam(n, t, b, bi, _) => {
      let t2 = abstr_aux(t, fvars, offset);
      let b2 = abstr_aux(b, fvars, offset + 1);
      Expr::lam(n.clone(), t2, b2, bi.clone())
    },
    ExprData::ForallE(n, t, b, bi, _) => {
      let t2 = abstr_aux(t, fvars, offset);
      let b2 = abstr_aux(b, fvars, offset + 1);
      Expr::all(n.clone(), t2, b2, bi.clone())
    },
    ExprData::LetE(n, t, v, b, nd, _) => {
      let t2 = abstr_aux(t, fvars, offset);
      let v2 = abstr_aux(v, fvars, offset);
      let b2 = abstr_aux(b, fvars, offset + 1);
      Expr::letE(n.clone(), t2, v2, b2, *nd)
    },
    ExprData::Proj(n, i, s, _) => {
      let s2 = abstr_aux(s, fvars, offset);
      Expr::proj(n.clone(), i.clone(), s2)
    },
    ExprData::Mdata(kvs, inner, _) => {
      let inner2 = abstr_aux(inner, fvars, offset);
      Expr::mdata(kvs.clone(), inner2)
    },
    ExprData::Bvar(..)
    | ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Mvar(..)
    | ExprData::Lit(..) => e.clone(),
  }
}

/// Decompose `f a1 a2 ... an` into `(f, [a1, a2, ..., an])`.
pub fn unfold_apps(e: &Expr) -> (Expr, Vec<Expr>) {
  let mut args = Vec::new();
  let mut cursor = e.clone();
  loop {
    match cursor.as_data() {
      ExprData::App(f, a, _) => {
        args.push(a.clone());
        cursor = f.clone();
      },
      _ => break,
    }
  }
  args.reverse();
  (cursor, args)
}

/// Reconstruct `f a1 a2 ... an`.
pub fn foldl_apps(mut fun: Expr, args: impl Iterator<Item = Expr>) -> Expr {
  for arg in args {
    fun = Expr::app(fun, arg);
  }
  fun
}

/// Substitute universe level parameters in an expression.
pub fn subst_expr_levels(
  e: &Expr,
  params: &[Name],
  values: &[Level],
) -> Expr {
  if params.is_empty() {
    return e.clone();
  }
  subst_expr_levels_aux(e, params, values)
}

fn subst_expr_levels_aux(
  e: &Expr,
  params: &[Name],
  values: &[Level],
) -> Expr {
  match e.as_data() {
    ExprData::Sort(level, _) => {
      Expr::sort(subst_level(level, params, values))
    },
    ExprData::Const(name, levels, _) => {
      let new_levels: Vec<Level> =
        levels.iter().map(|l| subst_level(l, params, values)).collect();
      Expr::cnst(name.clone(), new_levels)
    },
    ExprData::App(f, a, _) => {
      let f2 = subst_expr_levels_aux(f, params, values);
      let a2 = subst_expr_levels_aux(a, params, values);
      Expr::app(f2, a2)
    },
    ExprData::Lam(n, t, b, bi, _) => {
      let t2 = subst_expr_levels_aux(t, params, values);
      let b2 = subst_expr_levels_aux(b, params, values);
      Expr::lam(n.clone(), t2, b2, bi.clone())
    },
    ExprData::ForallE(n, t, b, bi, _) => {
      let t2 = subst_expr_levels_aux(t, params, values);
      let b2 = subst_expr_levels_aux(b, params, values);
      Expr::all(n.clone(), t2, b2, bi.clone())
    },
    ExprData::LetE(n, t, v, b, nd, _) => {
      let t2 = subst_expr_levels_aux(t, params, values);
      let v2 = subst_expr_levels_aux(v, params, values);
      let b2 = subst_expr_levels_aux(b, params, values);
      Expr::letE(n.clone(), t2, v2, b2, *nd)
    },
    ExprData::Proj(n, i, s, _) => {
      let s2 = subst_expr_levels_aux(s, params, values);
      Expr::proj(n.clone(), i.clone(), s2)
    },
    ExprData::Mdata(kvs, inner, _) => {
      let inner2 = subst_expr_levels_aux(inner, params, values);
      Expr::mdata(kvs.clone(), inner2)
    },
    // No levels to substitute
    ExprData::Bvar(..)
    | ExprData::Fvar(..)
    | ExprData::Mvar(..)
    | ExprData::Lit(..) => e.clone(),
  }
}

/// Check if an expression has any loose bound variables above `offset`.
pub fn has_loose_bvars(e: &Expr) -> bool {
  has_loose_bvars_aux(e, 0)
}

fn has_loose_bvars_aux(e: &Expr, depth: u64) -> bool {
  match e.as_data() {
    ExprData::Bvar(idx, _) => idx.to_u64().unwrap_or(u64::MAX) >= depth,
    ExprData::App(f, a, _) => {
      has_loose_bvars_aux(f, depth) || has_loose_bvars_aux(a, depth)
    },
    ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
      has_loose_bvars_aux(t, depth) || has_loose_bvars_aux(b, depth + 1)
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      has_loose_bvars_aux(t, depth)
        || has_loose_bvars_aux(v, depth)
        || has_loose_bvars_aux(b, depth + 1)
    },
    ExprData::Proj(_, _, s, _) => has_loose_bvars_aux(s, depth),
    ExprData::Mdata(_, inner, _) => has_loose_bvars_aux(inner, depth),
    _ => false,
  }
}

/// Check if expression contains any free variables (Fvar).
pub fn has_fvars(e: &Expr) -> bool {
  match e.as_data() {
    ExprData::Fvar(..) => true,
    ExprData::App(f, a, _) => has_fvars(f) || has_fvars(a),
    ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
      has_fvars(t) || has_fvars(b)
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      has_fvars(t) || has_fvars(v) || has_fvars(b)
    },
    ExprData::Proj(_, _, s, _) => has_fvars(s),
    ExprData::Mdata(_, inner, _) => has_fvars(inner),
    _ => false,
  }
}

// ============================================================================
// Name helpers
// ============================================================================

pub(crate) fn mk_name2(a: &str, b: &str) -> Name {
  Name::str(Name::str(Name::anon(), a.into()), b.into())
}

// ============================================================================
// WHNF
// ============================================================================

/// Weak head normal form reduction.
///
/// Uses DAG-based reduction internally: converts Expr to DAG, reduces using
/// BUBS (reduce_lam/reduce_let) for beta/zeta, falls back to Expr level for
/// iota/quot/nat/projection, and uses DAG-level splicing for delta.
pub fn whnf(e: &Expr, env: &Env) -> Expr {
  let mut dag = from_expr(e);
  whnf_dag(&mut dag, env);
  let result = to_expr(&dag);
  free_dag(dag);
  result
}

/// Trail-based WHNF on DAG. Walks down the App spine collecting a trail,
/// then dispatches on the head node.
fn whnf_dag(dag: &mut DAG, env: &Env) {
  loop {
    // Build trail of App nodes by walking down the fun chain
    let mut trail: Vec<NonNull<App>> = Vec::new();
    let mut cursor = dag.head;

    loop {
      match cursor {
        DAGPtr::App(app) => {
          trail.push(app);
          cursor = unsafe { (*app.as_ptr()).fun };
        },
        _ => break,
      }
    }

    match cursor {
      // Beta: Fun at head with args on trail
      DAGPtr::Fun(fun_ptr) if !trail.is_empty() => {
        let app = trail.pop().unwrap();
        let lam = unsafe { (*fun_ptr.as_ptr()).img };
        let result = reduce_lam(app, lam);
        set_dag_head(dag, result, &trail);
        continue;
      },

      // Zeta: Let at head
      DAGPtr::Let(let_ptr) => {
        let result = reduce_let(let_ptr);
        set_dag_head(dag, result, &trail);
        continue;
      },

      // Const: try iota, quot, nat, then delta
      DAGPtr::Cnst(_) => {
        // Try iota, quot, nat at Expr level
        if try_expr_reductions(dag, env) {
          continue;
        }
        // Try delta (definition unfolding) on DAG
        if try_dag_delta(dag, &trail, env) {
          continue;
        }
        return; // stuck
      },

      // Proj: try projection reduction (Expr-level fallback)
      DAGPtr::Proj(_) => {
        if try_expr_reductions(dag, env) {
          continue;
        }
        return; // stuck
      },

      // Sort: simplify level in place
      DAGPtr::Sort(sort_ptr) => {
        unsafe {
          let sort = &mut *sort_ptr.as_ptr();
          sort.level = simplify(&sort.level);
        }
        return;
      },

      // Mdata: strip metadata (Expr-level fallback)
      DAGPtr::Lit(_) => {
        // Check if this is a Nat literal that could be a Nat.succ application
        // by trying Expr-level reductions (which handles nat ops)
        if !trail.is_empty() {
          if try_expr_reductions(dag, env) {
            continue;
          }
        }
        return;
      },

      // Everything else (Var, Pi, Lam without args, etc.): already WHNF
      _ => return,
    }
  }
}

/// Set the DAG head after a reduction step.
/// If trail is empty, the result becomes the new head.
/// If trail is non-empty, splice result into the innermost remaining App.
fn set_dag_head(
  dag: &mut DAG,
  result: DAGPtr,
  trail: &[NonNull<App>],
) {
  if trail.is_empty() {
    dag.head = result;
  } else {
    unsafe {
      (*trail.last().unwrap().as_ptr()).fun = result;
    }
    dag.head = DAGPtr::App(trail[0]);
  }
}

/// Try iota/quot/nat/projection reductions at Expr level.
/// Converts current DAG to Expr, attempts reduction, converts back if
/// successful.
fn try_expr_reductions(dag: &mut DAG, env: &Env) -> bool {
  let current_expr = to_expr(&DAG { head: dag.head });

  let (head, args) = unfold_apps(&current_expr);

  let reduced = match head.as_data() {
    ExprData::Const(name, levels, _) => {
      // Try iota (recursor) reduction
      if let Some(result) = try_reduce_rec(name, levels, &args, env) {
        Some(result)
      }
      // Try quotient reduction
      else if let Some(result) = try_reduce_quot(name, &args, env) {
        Some(result)
      }
      // Try nat reduction
      else if let Some(result) =
        try_reduce_nat(&current_expr, env)
      {
        Some(result)
      } else {
        None
      }
    },
    ExprData::Proj(type_name, idx, structure, _) => {
      reduce_proj(type_name, idx, structure, env)
        .map(|result| foldl_apps(result, args.into_iter()))
    },
    ExprData::Mdata(_, inner, _) => {
      Some(foldl_apps(inner.clone(), args.into_iter()))
    },
    _ => None,
  };

  if let Some(result_expr) = reduced {
    let result_dag = from_expr(&result_expr);
    dag.head = result_dag.head;
    true
  } else {
    false
  }
}

/// Try delta (definition) unfolding on DAG.
/// Looks up the constant, substitutes universe levels in the definition body,
/// converts it to a DAG, and splices it into the current DAG.
fn try_dag_delta(
  dag: &mut DAG,
  trail: &[NonNull<App>],
  env: &Env,
) -> bool {
  // Extract constant info from head
  let cnst_ref = match dag_head_past_trail(dag, trail) {
    DAGPtr::Cnst(cnst) => unsafe { &*cnst.as_ptr() },
    _ => return false,
  };

  let ci = match env.get(&cnst_ref.name) {
    Some(c) => c,
    None => return false,
  };
  let (def_params, def_value) = match ci {
    ConstantInfo::DefnInfo(d)
      if d.hints != ReducibilityHints::Opaque =>
    {
      (&d.cnst.level_params, &d.value)
    },
    _ => return false,
  };

  if cnst_ref.levels.len() != def_params.len() {
    return false;
  }

  // Substitute levels at Expr level, then convert to DAG
  let val = subst_expr_levels(def_value, def_params, &cnst_ref.levels);
  let body_dag = from_expr(&val);

  // Splice body into the working DAG
  set_dag_head(dag, body_dag.head, trail);
  true
}

/// Get the head node past the trail (the non-App node at the bottom).
fn dag_head_past_trail(
  dag: &DAG,
  trail: &[NonNull<App>],
) -> DAGPtr {
  if trail.is_empty() {
    dag.head
  } else {
    unsafe { (*trail.last().unwrap().as_ptr()).fun }
  }
}

/// Try to unfold a definition at the head.
pub fn try_unfold_def(e: &Expr, env: &Env) -> Option<Expr> {
  let (head, args) = unfold_apps(e);
  let (name, levels) = match head.as_data() {
    ExprData::Const(name, levels, _) => (name, levels),
    _ => return None,
  };

  let ci = env.get(name)?;
  let (def_params, def_value) = match ci {
    ConstantInfo::DefnInfo(d) => {
      if d.hints == ReducibilityHints::Opaque {
        return None;
      }
      (&d.cnst.level_params, &d.value)
    },
    _ => return None,
  };

  if levels.len() != def_params.len() {
    return None;
  }

  let val = subst_expr_levels(def_value, def_params, levels);
  Some(foldl_apps(val, args.into_iter()))
}

/// Try to reduce a recursor application (iota reduction).
fn try_reduce_rec(
  name: &Name,
  levels: &[Level],
  args: &[Expr],
  env: &Env,
) -> Option<Expr> {
  let ci = env.get(name)?;
  let rec = match ci {
    ConstantInfo::RecInfo(r) => r,
    _ => return None,
  };

  let major_idx = rec.num_params.to_u64().unwrap() as usize
    + rec.num_motives.to_u64().unwrap() as usize
    + rec.num_minors.to_u64().unwrap() as usize
    + rec.num_indices.to_u64().unwrap() as usize;

  let major = args.get(major_idx)?;

  // WHNF the major premise
  let major_whnf = whnf(major, env);

  // Handle nat literal → constructor
  let major_ctor = match major_whnf.as_data() {
    ExprData::Lit(Literal::NatVal(n), _) => nat_lit_to_constructor(n),
    _ => major_whnf.clone(),
  };

  let (ctor_head, ctor_args) = unfold_apps(&major_ctor);

  // Find the matching rec rule
  let ctor_name = match ctor_head.as_data() {
    ExprData::Const(name, _, _) => name,
    _ => return None,
  };

  let rule = rec.rules.iter().find(|r| &r.ctor == ctor_name)?;

  let n_fields = rule.n_fields.to_u64().unwrap() as usize;
  let num_params = rec.num_params.to_u64().unwrap() as usize;
  let num_motives = rec.num_motives.to_u64().unwrap() as usize;
  let num_minors = rec.num_minors.to_u64().unwrap() as usize;

  // The constructor args may have extra params for nested inductives
  let ctor_args_wo_params =
    if ctor_args.len() >= n_fields {
      &ctor_args[ctor_args.len() - n_fields..]
    } else {
      return None;
    };

  // Substitute universe levels in the rule's RHS
  let rhs = subst_expr_levels(
    &rule.rhs,
    &rec.cnst.level_params,
    levels,
  );

  // Apply: params, motives, minors
  let prefix_count = num_params + num_motives + num_minors;
  let mut result = rhs;
  for arg in args.iter().take(prefix_count) {
    result = Expr::app(result, arg.clone());
  }

  // Apply constructor fields
  for arg in ctor_args_wo_params {
    result = Expr::app(result, arg.clone());
  }

  // Apply remaining args after major
  for arg in args.iter().skip(major_idx + 1) {
    result = Expr::app(result, arg.clone());
  }

  Some(result)
}

/// Convert a Nat literal to its constructor form.
fn nat_lit_to_constructor(n: &Nat) -> Expr {
  if n.0 == BigUint::ZERO {
    Expr::cnst(mk_name2("Nat", "zero"), vec![])
  } else {
    let pred = Nat(n.0.clone() - BigUint::from(1u64));
    let pred_expr = Expr::lit(Literal::NatVal(pred));
    Expr::app(Expr::cnst(mk_name2("Nat", "succ"), vec![]), pred_expr)
  }
}

/// Convert a string literal to its constructor form:
/// `"hello"` → `String.mk (List.cons 'h' (List.cons 'e' ... List.nil))`
/// where chars are represented as `Char.ofNat n`.
fn string_lit_to_constructor(s: &str) -> Expr {
  let list_name = Name::str(Name::anon(), "List".into());
  let char_name = Name::str(Name::anon(), "Char".into());
  let char_type = Expr::cnst(char_name.clone(), vec![]);

  // Build the list from right to left
  // List.nil.{0} : List Char
  let nil = Expr::app(
    Expr::cnst(
      Name::str(list_name.clone(), "nil".into()),
      vec![Level::succ(Level::zero())],
    ),
    char_type.clone(),
  );

  let result = s.chars().rev().fold(nil, |acc, c| {
    let char_val = Expr::app(
      Expr::cnst(Name::str(char_name.clone(), "ofNat".into()), vec![]),
      Expr::lit(Literal::NatVal(Nat::from(c as u64))),
    );
    // List.cons.{0} Char char_val acc
    Expr::app(
      Expr::app(
        Expr::app(
          Expr::cnst(
            Name::str(list_name.clone(), "cons".into()),
            vec![Level::succ(Level::zero())],
          ),
          char_type.clone(),
        ),
        char_val,
      ),
      acc,
    )
  });

  // String.mk list
  Expr::app(
    Expr::cnst(
      Name::str(Name::str(Name::anon(), "String".into()), "mk".into()),
      vec![],
    ),
    result,
  )
}

/// Try to reduce a projection.
fn reduce_proj(
  _type_name: &Name,
  idx: &Nat,
  structure: &Expr,
  env: &Env,
) -> Option<Expr> {
  let structure_whnf = whnf(structure, env);

  // Handle string literal → constructor
  let structure_ctor = match structure_whnf.as_data() {
    ExprData::Lit(Literal::StrVal(s), _) => {
      string_lit_to_constructor(s)
    },
    _ => structure_whnf,
  };

  let (ctor_head, ctor_args) = unfold_apps(&structure_ctor);

  let ctor_name = match ctor_head.as_data() {
    ExprData::Const(name, _, _) => name,
    _ => return None,
  };

  // Look up constructor to get num_params
  let ci = env.get(ctor_name)?;
  let num_params = match ci {
    ConstantInfo::CtorInfo(c) => c.num_params.to_u64().unwrap() as usize,
    _ => return None,
  };

  let field_idx = num_params + idx.to_u64().unwrap() as usize;
  ctor_args.get(field_idx).cloned()
}

/// Try to reduce a quotient operation.
fn try_reduce_quot(
  name: &Name,
  args: &[Expr],
  env: &Env,
) -> Option<Expr> {
  let ci = env.get(name)?;
  let kind = match ci {
    ConstantInfo::QuotInfo(q) => &q.kind,
    _ => return None,
  };

  let (qmk_idx, rest_idx) = match kind {
    QuotKind::Lift => (5, 6),
    QuotKind::Ind => (4, 5),
    _ => return None,
  };

  let qmk = args.get(qmk_idx)?;
  let qmk_whnf = whnf(qmk, env);

  // Check that the head is Quot.mk
  let (qmk_head, _) = unfold_apps(&qmk_whnf);
  match qmk_head.as_data() {
    ExprData::Const(n, _, _) if *n == mk_name2("Quot", "mk") => {},
    _ => return None,
  }

  let f = args.get(3)?;

  // Extract the argument of Quot.mk
  let qmk_arg = match qmk_whnf.as_data() {
    ExprData::App(_, arg, _) => arg,
    _ => return None,
  };

  let mut result = Expr::app(f.clone(), qmk_arg.clone());
  for arg in args.iter().skip(rest_idx) {
    result = Expr::app(result, arg.clone());
  }

  Some(result)
}

/// Try to reduce nat operations.
fn try_reduce_nat(e: &Expr, env: &Env) -> Option<Expr> {
  if has_fvars(e) {
    return None;
  }

  let (head, args) = unfold_apps(e);
  let name = match head.as_data() {
    ExprData::Const(name, _, _) => name,
    _ => return None,
  };

  match args.len() {
    1 => {
      if *name == mk_name2("Nat", "succ") {
        let arg_whnf = whnf(&args[0], env);
        let n = get_nat_value(&arg_whnf)?;
        Some(Expr::lit(Literal::NatVal(Nat(n + BigUint::from(1u64)))))
      } else {
        None
      }
    },
    2 => {
      let a_whnf = whnf(&args[0], env);
      let b_whnf = whnf(&args[1], env);
      let a = get_nat_value(&a_whnf)?;
      let b = get_nat_value(&b_whnf)?;

      let result = if *name == mk_name2("Nat", "add") {
        Some(Expr::lit(Literal::NatVal(Nat(a + b))))
      } else if *name == mk_name2("Nat", "sub") {
        Some(Expr::lit(Literal::NatVal(Nat(if a >= b {
          a - b
        } else {
          BigUint::ZERO
        }))))
      } else if *name == mk_name2("Nat", "mul") {
        Some(Expr::lit(Literal::NatVal(Nat(a * b))))
      } else if *name == mk_name2("Nat", "div") {
        Some(Expr::lit(Literal::NatVal(Nat(if b == BigUint::ZERO {
          BigUint::ZERO
        } else {
          a / b
        }))))
      } else if *name == mk_name2("Nat", "mod") {
        Some(Expr::lit(Literal::NatVal(Nat(if b == BigUint::ZERO {
          a
        } else {
          a % b
        }))))
      } else if *name == mk_name2("Nat", "beq") {
        bool_to_expr(a == b)
      } else if *name == mk_name2("Nat", "ble") {
        bool_to_expr(a <= b)
      } else if *name == mk_name2("Nat", "pow") {
        let exp = u32::try_from(&b).unwrap_or(u32::MAX);
        Some(Expr::lit(Literal::NatVal(Nat(a.pow(exp)))))
      } else if *name == mk_name2("Nat", "land") {
        Some(Expr::lit(Literal::NatVal(Nat(a & b))))
      } else if *name == mk_name2("Nat", "lor") {
        Some(Expr::lit(Literal::NatVal(Nat(a | b))))
      } else if *name == mk_name2("Nat", "xor") {
        Some(Expr::lit(Literal::NatVal(Nat(a ^ b))))
      } else if *name == mk_name2("Nat", "shiftLeft") {
        let shift = u64::try_from(&b).unwrap_or(u64::MAX);
        Some(Expr::lit(Literal::NatVal(Nat(a << shift))))
      } else if *name == mk_name2("Nat", "shiftRight") {
        let shift = u64::try_from(&b).unwrap_or(u64::MAX);
        Some(Expr::lit(Literal::NatVal(Nat(a >> shift))))
      } else if *name == mk_name2("Nat", "blt") {
        bool_to_expr(a < b)
      } else {
        None
      };
      result
    },
    _ => None,
  }
}

fn get_nat_value(e: &Expr) -> Option<BigUint> {
  match e.as_data() {
    ExprData::Lit(Literal::NatVal(n), _) => Some(n.0.clone()),
    ExprData::Const(name, _, _) if *name == mk_name2("Nat", "zero") => {
      Some(BigUint::ZERO)
    },
    _ => None,
  }
}

fn bool_to_expr(b: bool) -> Option<Expr> {
  let name = if b {
    mk_name2("Bool", "true")
  } else {
    mk_name2("Bool", "false")
  };
  Some(Expr::cnst(name, vec![]))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
  use super::*;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }

  fn nat_type() -> Expr {
    Expr::cnst(mk_name("Nat"), vec![])
  }

  fn nat_zero() -> Expr {
    Expr::cnst(mk_name2("Nat", "zero"), vec![])
  }

  #[test]
  fn test_inst_bvar() {
    let body = Expr::bvar(Nat::from(0));
    let arg = nat_zero();
    let result = inst(&body, &[arg.clone()]);
    assert_eq!(result, arg);
  }

  #[test]
  fn test_inst_nested() {
    // body = Lam(_, Nat, Bvar(1)) — references outer binder
    // After inst with [zero], should become Lam(_, Nat, zero)
    let body = Expr::lam(
      Name::anon(),
      nat_type(),
      Expr::bvar(Nat::from(1)),
      BinderInfo::Default,
    );
    let result = inst(&body, &[nat_zero()]);
    let expected = Expr::lam(
      Name::anon(),
      nat_type(),
      nat_zero(),
      BinderInfo::Default,
    );
    assert_eq!(result, expected);
  }

  #[test]
  fn test_unfold_apps() {
    let f = Expr::cnst(mk_name("f"), vec![]);
    let a = nat_zero();
    let b = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let e = Expr::app(Expr::app(f.clone(), a.clone()), b.clone());
    let (head, args) = unfold_apps(&e);
    assert_eq!(head, f);
    assert_eq!(args.len(), 2);
    assert_eq!(args[0], a);
    assert_eq!(args[1], b);
  }

  #[test]
  fn test_beta_reduce_identity() {
    // (fun x : Nat => x) Nat.zero
    let id = Expr::lam(
      Name::str(Name::anon(), "x".into()),
      nat_type(),
      Expr::bvar(Nat::from(0)),
      BinderInfo::Default,
    );
    let e = Expr::app(id, nat_zero());
    let env = Env::default();
    let result = whnf(&e, &env);
    assert_eq!(result, nat_zero());
  }

  #[test]
  fn test_zeta_reduce() {
    // let x : Nat := Nat.zero in x
    let e = Expr::letE(
      Name::str(Name::anon(), "x".into()),
      nat_type(),
      nat_zero(),
      Expr::bvar(Nat::from(0)),
      false,
    );
    let env = Env::default();
    let result = whnf(&e, &env);
    assert_eq!(result, nat_zero());
  }

  // ==========================================================================
  // Delta reduction
  // ==========================================================================

  fn mk_defn_env(name: &str, value: Expr, typ: Expr) -> Env {
    let mut env = Env::default();
    let n = mk_name(name);
    env.insert(
      n.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: n.clone(),
          level_params: vec![],
          typ,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![n],
      }),
    );
    env
  }

  #[test]
  fn test_delta_unfold() {
    // def myZero := Nat.zero
    // whnf(myZero) = Nat.zero
    let env = mk_defn_env("myZero", nat_zero(), nat_type());
    let e = Expr::cnst(mk_name("myZero"), vec![]);
    let result = whnf(&e, &env);
    assert_eq!(result, nat_zero());
  }

  #[test]
  fn test_delta_opaque_no_unfold() {
    // An opaque definition should NOT unfold
    let mut env = Env::default();
    let n = mk_name("opaqueVal");
    env.insert(
      n.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: n.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: nat_zero(),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n.clone()],
      }),
    );
    let e = Expr::cnst(n.clone(), vec![]);
    let result = whnf(&e, &env);
    // Should still be the constant, not unfolded
    assert_eq!(result, e);
  }

  #[test]
  fn test_delta_chained() {
    // def a := Nat.zero, def b := a  =>  whnf(b) = Nat.zero
    let mut env = Env::default();
    let a = mk_name("a");
    let b = mk_name("b");
    env.insert(
      a.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: a.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: nat_zero(),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![a.clone()],
      }),
    );
    env.insert(
      b.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: b.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: Expr::cnst(a, vec![]),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![b.clone()],
      }),
    );
    let e = Expr::cnst(b, vec![]);
    let result = whnf(&e, &env);
    assert_eq!(result, nat_zero());
  }

  // ==========================================================================
  // Nat arithmetic reduction
  // ==========================================================================

  fn nat_lit(n: u64) -> Expr {
    Expr::lit(Literal::NatVal(Nat::from(n)))
  }

  #[test]
  fn test_nat_add() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "add"), vec![]), nat_lit(3)),
      nat_lit(4),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(7));
  }

  #[test]
  fn test_nat_sub() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "sub"), vec![]), nat_lit(10)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(7));
  }

  #[test]
  fn test_nat_sub_underflow() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "sub"), vec![]), nat_lit(3)),
      nat_lit(10),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(0));
  }

  #[test]
  fn test_nat_mul() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "mul"), vec![]), nat_lit(6)),
      nat_lit(7),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(42));
  }

  #[test]
  fn test_nat_div() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "div"), vec![]), nat_lit(10)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(3));
  }

  #[test]
  fn test_nat_div_by_zero() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "div"), vec![]), nat_lit(10)),
      nat_lit(0),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(0));
  }

  #[test]
  fn test_nat_mod() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "mod"), vec![]), nat_lit(10)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, nat_lit(1));
  }

  #[test]
  fn test_nat_beq_true() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "beq"), vec![]), nat_lit(5)),
      nat_lit(5),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::cnst(mk_name2("Bool", "true"), vec![]));
  }

  #[test]
  fn test_nat_beq_false() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "beq"), vec![]), nat_lit(5)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::cnst(mk_name2("Bool", "false"), vec![]));
  }

  #[test]
  fn test_nat_ble_true() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "ble"), vec![]), nat_lit(3)),
      nat_lit(5),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::cnst(mk_name2("Bool", "true"), vec![]));
  }

  #[test]
  fn test_nat_ble_false() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "ble"), vec![]), nat_lit(5)),
      nat_lit(3),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::cnst(mk_name2("Bool", "false"), vec![]));
  }

  #[test]
  fn test_nat_pow() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "pow"), vec![]), nat_lit(2)),
      nat_lit(10),
    );
    assert_eq!(whnf(&e, &env), nat_lit(1024));
  }

  #[test]
  fn test_nat_land() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "land"), vec![]), nat_lit(0b1100)),
      nat_lit(0b1010),
    );
    assert_eq!(whnf(&e, &env), nat_lit(0b1000));
  }

  #[test]
  fn test_nat_lor() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "lor"), vec![]), nat_lit(0b1100)),
      nat_lit(0b1010),
    );
    assert_eq!(whnf(&e, &env), nat_lit(0b1110));
  }

  #[test]
  fn test_nat_xor() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "xor"), vec![]), nat_lit(0b1100)),
      nat_lit(0b1010),
    );
    assert_eq!(whnf(&e, &env), nat_lit(0b0110));
  }

  #[test]
  fn test_nat_shift_left() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "shiftLeft"), vec![]), nat_lit(1)),
      nat_lit(8),
    );
    assert_eq!(whnf(&e, &env), nat_lit(256));
  }

  #[test]
  fn test_nat_shift_right() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "shiftRight"), vec![]), nat_lit(256)),
      nat_lit(4),
    );
    assert_eq!(whnf(&e, &env), nat_lit(16));
  }

  #[test]
  fn test_nat_blt_true() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "blt"), vec![]), nat_lit(3)),
      nat_lit(5),
    );
    assert_eq!(whnf(&e, &env), Expr::cnst(mk_name2("Bool", "true"), vec![]));
  }

  #[test]
  fn test_nat_blt_false() {
    let env = Env::default();
    let e = Expr::app(
      Expr::app(Expr::cnst(mk_name2("Nat", "blt"), vec![]), nat_lit(5)),
      nat_lit(3),
    );
    assert_eq!(whnf(&e, &env), Expr::cnst(mk_name2("Bool", "false"), vec![]));
  }

  // ==========================================================================
  // Sort simplification in WHNF
  // ==========================================================================

  #[test]
  fn test_string_lit_proj_reduces() {
    // Build an env with String, String.mk ctor, List, List.cons, List.nil, Char
    let mut env = Env::default();
    let string_name = mk_name("String");
    let string_mk = mk_name2("String", "mk");
    let list_name = mk_name("List");
    let char_name = mk_name("Char");

    // String : Sort 1
    env.insert(
      string_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: string_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![string_name.clone()],
        ctors: vec![string_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    // String.mk : List Char → String (1 field, 0 params)
    let list_char = Expr::app(
      Expr::cnst(list_name, vec![Level::succ(Level::zero())]),
      Expr::cnst(char_name, vec![]),
    );
    env.insert(
      string_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: string_mk,
          level_params: vec![],
          typ: Expr::all(
            mk_name("data"),
            list_char,
            Expr::cnst(string_name.clone(), vec![]),
            BinderInfo::Default,
          ),
        },
        induct: string_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );

    // Proj String 0 "hi" should reduce (not return None)
    let proj = Expr::proj(
      string_name,
      Nat::from(0u64),
      Expr::lit(Literal::StrVal("hi".into())),
    );
    let result = whnf(&proj, &env);
    // The result should NOT be a Proj anymore (it should have reduced)
    assert!(
      !matches!(result.as_data(), ExprData::Proj(..)),
      "String projection should reduce, got: {:?}",
      result
    );
  }

  #[test]
  fn test_whnf_sort_simplifies() {
    // Sort(max 0 u) should simplify to Sort(u)
    let env = Env::default();
    let u = Level::param(mk_name("u"));
    let e = Expr::sort(Level::max(Level::zero(), u.clone()));
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::sort(u));
  }

  // ==========================================================================
  // Already-WHNF terms
  // ==========================================================================

  #[test]
  fn test_whnf_sort_unchanged() {
    let env = Env::default();
    let e = Expr::sort(Level::zero());
    let result = whnf(&e, &env);
    assert_eq!(result, e);
  }

  #[test]
  fn test_whnf_lambda_unchanged() {
    // A lambda without applied arguments is already WHNF
    let env = Env::default();
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0)),
      BinderInfo::Default,
    );
    let result = whnf(&e, &env);
    assert_eq!(result, e);
  }

  #[test]
  fn test_whnf_pi_unchanged() {
    let env = Env::default();
    let e = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let result = whnf(&e, &env);
    assert_eq!(result, e);
  }

  // ==========================================================================
  // Helper function tests
  // ==========================================================================

  #[test]
  fn test_has_loose_bvars_true() {
    assert!(has_loose_bvars(&Expr::bvar(Nat::from(0))));
  }

  #[test]
  fn test_has_loose_bvars_false_under_binder() {
    // fun x : Nat => x  — bvar(0) is bound, not loose
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0)),
      BinderInfo::Default,
    );
    assert!(!has_loose_bvars(&e));
  }

  #[test]
  fn test_has_loose_bvars_const() {
    assert!(!has_loose_bvars(&nat_zero()));
  }

  #[test]
  fn test_has_fvars_true() {
    assert!(has_fvars(&Expr::fvar(mk_name("x"))));
  }

  #[test]
  fn test_has_fvars_false() {
    assert!(!has_fvars(&nat_zero()));
  }

  #[test]
  fn test_foldl_apps_roundtrip() {
    let f = Expr::cnst(mk_name("f"), vec![]);
    let a = nat_zero();
    let b = nat_type();
    let e = Expr::app(Expr::app(f.clone(), a.clone()), b.clone());
    let (head, args) = unfold_apps(&e);
    let rebuilt = foldl_apps(head, args.into_iter());
    assert_eq!(rebuilt, e);
  }

  #[test]
  fn test_abstr_simple() {
    // abstr(fvar("x"), [fvar("x")]) = bvar(0)
    let x = Expr::fvar(mk_name("x"));
    let result = abstr(&x, &[x.clone()]);
    assert_eq!(result, Expr::bvar(Nat::from(0)));
  }

  #[test]
  fn test_abstr_not_found() {
    // abstr(Nat.zero, [fvar("x")]) = Nat.zero (unchanged)
    let x = Expr::fvar(mk_name("x"));
    let result = abstr(&nat_zero(), &[x]);
    assert_eq!(result, nat_zero());
  }

  #[test]
  fn test_subst_expr_levels_simple() {
    // Sort(u) with u := 0 => Sort(0)
    let u_name = mk_name("u");
    let e = Expr::sort(Level::param(u_name.clone()));
    let result = subst_expr_levels(&e, &[u_name], &[Level::zero()]);
    assert_eq!(result, Expr::sort(Level::zero()));
  }
}
