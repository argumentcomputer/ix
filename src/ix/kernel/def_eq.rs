use crate::ix::env::*;
use crate::lean::nat::Nat;
use num_bigint::BigUint;

use super::level::{eq_antisymm, eq_antisymm_many};
use super::tc::TypeChecker;
use super::whnf::*;

/// Result of lazy delta reduction.
enum DeltaResult {
  Found(bool),
  Exhausted(Expr, Expr),
}

/// Check definitional equality of two expressions.
///
/// Uses a conjunction work stack: processes pairs iteratively, all must be equal.
pub fn def_eq(x: &Expr, y: &Expr, tc: &mut TypeChecker) -> bool {
  const DEF_EQ_STEP_LIMIT: u64 = 1_000_000;
  let mut work: Vec<(Expr, Expr)> = vec![(x.clone(), y.clone())];
  let mut steps: u64 = 0;

  while let Some((x, y)) = work.pop() {
    steps += 1;
    if steps > DEF_EQ_STEP_LIMIT {
      eprintln!("[def_eq] step limit exceeded ({steps} steps)");
      return false;
    }
    if !def_eq_step(&x, &y, &mut work, tc) {
      return false;
    }
  }
  true
}

/// Process one def_eq pair. Returns false if definitely not equal.
/// May push additional pairs onto `work` that must all be equal.
fn def_eq_step(
  x: &Expr,
  y: &Expr,
  work: &mut Vec<(Expr, Expr)>,
  tc: &mut TypeChecker,
) -> bool {
  if let Some(quick) = def_eq_quick_check(x, y) {
    return quick;
  }

  let x_n = tc.whnf_no_delta(x);
  let y_n = tc.whnf_no_delta(y);

  if let Some(quick) = def_eq_quick_check(&x_n, &y_n) {
    return quick;
  }

  if proof_irrel_eq(&x_n, &y_n, tc) {
    return true;
  }

  match lazy_delta_step(&x_n, &y_n, tc) {
    DeltaResult::Found(result) => result,
    DeltaResult::Exhausted(x_e, y_e) => {
      def_eq_const(&x_e, &y_e)
        || def_eq_proj_push(&x_e, &y_e, work)
        || def_eq_app_push(&x_e, &y_e, work)
        || def_eq_binder_full_push(&x_e, &y_e, work)
        || try_eta_expansion(&x_e, &y_e, tc)
        || try_eta_struct(&x_e, &y_e, tc)
        || is_def_eq_unit_like(&x_e, &y_e, tc)
    },
  }
}

/// Quick syntactic checks.
fn def_eq_quick_check(x: &Expr, y: &Expr) -> Option<bool> {
  if x == y {
    return Some(true);
  }
  if let Some(r) = def_eq_sort(x, y) {
    return Some(r);
  }
  if let Some(r) = def_eq_binder(x, y) {
    return Some(r);
  }
  None
}

fn def_eq_sort(x: &Expr, y: &Expr) -> Option<bool> {
  match (x.as_data(), y.as_data()) {
    (ExprData::Sort(l, _), ExprData::Sort(r, _)) => {
      Some(eq_antisymm(l, r))
    },
    _ => None,
  }
}

/// Check if two binder expressions (Pi/Lam) are definitionally equal.
/// Always defers to full checking after WHNF, since binder types could be
/// definitionally equal without being syntactically identical.
fn def_eq_binder(_x: &Expr, _y: &Expr) -> Option<bool> {
  None
}

fn def_eq_const(x: &Expr, y: &Expr) -> bool {
  match (x.as_data(), y.as_data()) {
    (
      ExprData::Const(xn, xl, _),
      ExprData::Const(yn, yl, _),
    ) => xn == yn && eq_antisymm_many(xl, yl),
    _ => false,
  }
}

/// Proj congruence: push structure pair onto work stack.
fn def_eq_proj_push(
  x: &Expr,
  y: &Expr,
  work: &mut Vec<(Expr, Expr)>,
) -> bool {
  match (x.as_data(), y.as_data()) {
    (
      ExprData::Proj(_, idx_l, structure_l, _),
      ExprData::Proj(_, idx_r, structure_r, _),
    ) if idx_l == idx_r => {
      work.push((structure_l.clone(), structure_r.clone()));
      true
    },
    _ => false,
  }
}

/// App congruence: push head + arg pairs onto work stack.
fn def_eq_app_push(
  x: &Expr,
  y: &Expr,
  work: &mut Vec<(Expr, Expr)>,
) -> bool {
  let (f1, args1) = unfold_apps(x);
  if args1.is_empty() {
    return false;
  }
  let (f2, args2) = unfold_apps(y);
  if args2.is_empty() {
    return false;
  }
  if args1.len() != args2.len() {
    return false;
  }

  work.push((f1, f2));
  for (a, b) in args1.into_iter().zip(args2.into_iter()) {
    work.push((a, b));
  }
  true
}

/// Eager app congruence (used by lazy_delta_step where we need a definitive answer).
fn def_eq_app(x: &Expr, y: &Expr, tc: &mut TypeChecker) -> bool {
  let (f1, args1) = unfold_apps(x);
  if args1.is_empty() {
    return false;
  }
  let (f2, args2) = unfold_apps(y);
  if args2.is_empty() {
    return false;
  }
  if args1.len() != args2.len() {
    return false;
  }

  if !def_eq(&f1, &f2, tc) {
    return false;
  }
  args1.iter().zip(args2.iter()).all(|(a, b)| def_eq(a, b, tc))
}

/// Iterative binder comparison: peel matching Pi/Lam layers, pushing
/// domain pairs and the final body pair onto the work stack.
fn def_eq_binder_full_push(
  x: &Expr,
  y: &Expr,
  work: &mut Vec<(Expr, Expr)>,
) -> bool {
  let mut cx = x.clone();
  let mut cy = y.clone();
  let mut matched = false;

  loop {
    match (cx.as_data(), cy.as_data()) {
      (
        ExprData::ForallE(_, t1, b1, _, _),
        ExprData::ForallE(_, t2, b2, _, _),
      ) => {
        work.push((t1.clone(), t2.clone()));
        cx = b1.clone();
        cy = b2.clone();
        matched = true;
      },
      (
        ExprData::Lam(_, t1, b1, _, _),
        ExprData::Lam(_, t2, b2, _, _),
      ) => {
        work.push((t1.clone(), t2.clone()));
        cx = b1.clone();
        cy = b2.clone();
        matched = true;
      },
      _ => break,
    }
  }

  if !matched {
    return false;
  }
  // Push the final body pair
  work.push((cx, cy));
  true
}

/// Proof irrelevance: if both x and y are proofs of the same proposition,
/// they are definitionally equal.
fn proof_irrel_eq(x: &Expr, y: &Expr, tc: &mut TypeChecker) -> bool {
  let x_ty = match tc.infer(x) {
    Ok(ty) => ty,
    Err(_) => return false,
  };
  if !is_proposition(&x_ty, tc) {
    return false;
  }
  let y_ty = match tc.infer(y) {
    Ok(ty) => ty,
    Err(_) => return false,
  };
  if !is_proposition(&y_ty, tc) {
    return false;
  }
  def_eq(&x_ty, &y_ty, tc)
}

/// Check if an expression's type is Prop (Sort 0).
fn is_proposition(ty: &Expr, tc: &mut TypeChecker) -> bool {
  let ty_of_ty = match tc.infer(ty) {
    Ok(t) => t,
    Err(_) => return false,
  };
  let whnfd = tc.whnf(&ty_of_ty);
  matches!(whnfd.as_data(), ExprData::Sort(l, _) if super::level::is_zero(l))
}

/// Eta expansion: `fun x => f x` ≡ `f` when `f : (x : A) → B`.
fn try_eta_expansion(x: &Expr, y: &Expr, tc: &mut TypeChecker) -> bool {
  try_eta_expansion_aux(x, y, tc) || try_eta_expansion_aux(y, x, tc)
}

fn try_eta_expansion_aux(
  x: &Expr,
  y: &Expr,
  tc: &mut TypeChecker,
) -> bool {
  if let ExprData::Lam(_, _, _, _, _) = x.as_data() {
    let y_ty = match tc.infer(y) {
      Ok(t) => t,
      Err(_) => return false,
    };
    let y_ty_whnf = tc.whnf(&y_ty);
    if let ExprData::ForallE(name, binder_type, _, bi, _) =
      y_ty_whnf.as_data()
    {
      // eta-expand y: fun x => y x
      let body = Expr::app(y.clone(), Expr::bvar(crate::lean::nat::Nat::from(0)));
      let expanded = Expr::lam(
        name.clone(),
        binder_type.clone(),
        body,
        bi.clone(),
      );
      return def_eq(x, &expanded, tc);
    }
  }
  false
}

/// Check if a name refers to a structure-like inductive:
/// exactly 1 constructor, not recursive, no indices.
fn is_structure_like(name: &Name, env: &Env) -> bool {
  match env.get(name) {
    Some(ConstantInfo::InductInfo(iv)) => {
      iv.ctors.len() == 1 && !iv.is_rec && iv.num_indices == Nat::ZERO
    },
    _ => false,
  }
}

/// Structure eta: `p =def= S.mk (S.1 p) (S.2 p)` when S is a
/// single-constructor non-recursive inductive with no indices.
fn try_eta_struct(x: &Expr, y: &Expr, tc: &mut TypeChecker) -> bool {
  try_eta_struct_core(x, y, tc) || try_eta_struct_core(y, x, tc)
}

/// Try to decompose `s` as a constructor application for a structure-like
/// type, then check that each field matches the corresponding projection of `t`.
fn try_eta_struct_core(
  t: &Expr,
  s: &Expr,
  tc: &mut TypeChecker,
) -> bool {
  let (head, args) = unfold_apps(s);
  let ctor_name = match head.as_data() {
    ExprData::Const(name, _, _) => name,
    _ => return false,
  };

  let ctor_info = match tc.env.get(ctor_name) {
    Some(ConstantInfo::CtorInfo(c)) => c,
    _ => return false,
  };

  if !is_structure_like(&ctor_info.induct, tc.env) {
    return false;
  }

  let num_params = ctor_info.num_params.to_u64().unwrap() as usize;
  let num_fields = ctor_info.num_fields.to_u64().unwrap() as usize;

  if args.len() != num_params + num_fields {
    return false;
  }

  for i in 0..num_fields {
    let field = &args[num_params + i];
    let proj = Expr::proj(
      ctor_info.induct.clone(),
      Nat::from(i as u64),
      t.clone(),
    );
    if !def_eq(field, &proj, tc) {
      return false;
    }
  }

  true
}

/// Unit-like equality: types with a single zero-field constructor have all
/// inhabitants definitionally equal.
fn is_def_eq_unit_like(x: &Expr, y: &Expr, tc: &mut TypeChecker) -> bool {
  let x_ty = match tc.infer(x) {
    Ok(ty) => ty,
    Err(_) => return false,
  };
  let y_ty = match tc.infer(y) {
    Ok(ty) => ty,
    Err(_) => return false,
  };
  // Types must be def-eq
  if !def_eq(&x_ty, &y_ty, tc) {
    return false;
  }
  // Check if the type is a unit-like inductive
  let whnf_ty = tc.whnf(&x_ty);
  let (head, _) = unfold_apps(&whnf_ty);
  let name = match head.as_data() {
    ExprData::Const(name, _, _) => name,
    _ => return false,
  };
  match tc.env.get(name) {
    Some(ConstantInfo::InductInfo(iv)) => {
      if iv.ctors.len() != 1 {
        return false;
      }
      // Check single constructor has zero fields
      if let Some(ConstantInfo::CtorInfo(c)) = tc.env.get(&iv.ctors[0]) {
        c.num_fields == Nat::ZERO
      } else {
        false
      }
    },
    _ => false,
  }
}

/// Check if expression is Nat zero (either `Nat.zero` or `lit 0`).
/// Matches Lean 4's `is_nat_zero`.
fn is_nat_zero(e: &Expr) -> bool {
  match e.as_data() {
    ExprData::Const(name, _, _) => *name == mk_name2("Nat", "zero"),
    ExprData::Lit(Literal::NatVal(n), _) => n.0 == BigUint::ZERO,
    _ => false,
  }
}

/// If expression is `Nat.succ arg` or `lit (n+1)`, return the predecessor.
/// Matches Lean 4's `is_nat_succ` / lean4lean's `isNatSuccOf?`.
fn is_nat_succ(e: &Expr) -> Option<Expr> {
  match e.as_data() {
    ExprData::App(f, arg, _) => match f.as_data() {
      ExprData::Const(name, _, _) if *name == mk_name2("Nat", "succ") => {
        Some(arg.clone())
      },
      _ => None,
    },
    ExprData::Lit(Literal::NatVal(n), _) if n.0 > BigUint::ZERO => {
      Some(Expr::lit(Literal::NatVal(Nat(
        n.0.clone() - BigUint::from(1u64),
      ))))
    },
    _ => None,
  }
}

/// Nat offset equality: `Nat.zero =?= Nat.zero` → true,
/// `Nat.succ n =?= Nat.succ m` → `n =?= m` (recursively via def_eq).
/// Also handles nat literals: `lit 5 =?= Nat.succ (lit 4)` → true.
/// Matches Lean 4's `is_def_eq_offset`.
fn def_eq_nat_offset(x: &Expr, y: &Expr, tc: &mut TypeChecker) -> Option<bool> {
  if is_nat_zero(x) && is_nat_zero(y) {
    return Some(true);
  }
  match (is_nat_succ(x), is_nat_succ(y)) {
    (Some(x_pred), Some(y_pred)) => Some(def_eq(&x_pred, &y_pred, tc)),
    _ => None,
  }
}

/// Try to reduce via nat operations or native reductions, returning the reduced form if successful.
fn try_lazy_delta_nat_native(e: &Expr, env: &Env) -> Option<Expr> {
  let (head, args) = unfold_apps(e);
  match head.as_data() {
    ExprData::Const(name, _, _) => {
      if let Some(r) = try_reduce_native(name, &args) {
        return Some(r);
      }
      if let Some(r) = try_reduce_nat(e, env) {
        return Some(r);
      }
      None
    },
    _ => None,
  }
}

/// Lazy delta reduction: unfold definitions step by step.
fn lazy_delta_step(
  x: &Expr,
  y: &Expr,
  tc: &mut TypeChecker,
) -> DeltaResult {
  let mut x = x.clone();
  let mut y = y.clone();
  let mut iters: u32 = 0;
  const MAX_DELTA_ITERS: u32 = 10_000;

  loop {
    iters += 1;
    if iters > MAX_DELTA_ITERS {
      return DeltaResult::Exhausted(x, y);
    }

    // Nat offset comparison (Lean 4: isDefEqOffset)
    if let Some(quick) = def_eq_nat_offset(&x, &y, tc) {
      return DeltaResult::Found(quick);
    }

    // Try nat/native reduction on each side before delta
    if let Some(x_r) = try_lazy_delta_nat_native(&x, tc.env) {
      let x_r = tc.whnf_no_delta(&x_r);
      if let Some(quick) = def_eq_quick_check(&x_r, &y) {
        return DeltaResult::Found(quick);
      }
      x = x_r;
      continue;
    }
    if let Some(y_r) = try_lazy_delta_nat_native(&y, tc.env) {
      let y_r = tc.whnf_no_delta(&y_r);
      if let Some(quick) = def_eq_quick_check(&x, &y_r) {
        return DeltaResult::Found(quick);
      }
      y = y_r;
      continue;
    }

    let x_def = get_applied_def(&x, tc.env);
    let y_def = get_applied_def(&y, tc.env);

    match (&x_def, &y_def) {
      (None, None) => return DeltaResult::Exhausted(x, y),
      (Some(_), None) => {
        x = delta(&x, tc);
      },
      (None, Some(_)) => {
        y = delta(&y, tc);
      },
      (Some((x_name, x_hint)), Some((y_name, y_hint))) => {
        // Same name and same height: try congruence first
        if x_name == y_name && x_hint == y_hint {
          if def_eq_app(&x, &y, tc) {
            return DeltaResult::Found(true);
          }
          x = delta(&x, tc);
          y = delta(&y, tc);
        } else if hint_lt(x_hint, y_hint) {
          y = delta(&y, tc);
        } else {
          x = delta(&x, tc);
        }
      },
    }

    if let Some(quick) = def_eq_quick_check(&x, &y) {
      return DeltaResult::Found(quick);
    }
  }
}

/// Get the name and reducibility hint of an applied definition.
fn get_applied_def(
  e: &Expr,
  env: &Env,
) -> Option<(Name, ReducibilityHints)> {
  let (head, _) = unfold_apps(e);
  let name = match head.as_data() {
    ExprData::Const(name, _, _) => name,
    _ => return None,
  };
  let ci = env.get(name)?;
  match ci {
    ConstantInfo::DefnInfo(d) => {
      if d.hints == ReducibilityHints::Opaque {
        None
      } else {
        Some((name.clone(), d.hints))
      }
    },
    // Theorems are never unfolded — proof irrelevance handles them.
    // ConstantInfo::ThmInfo(_) => return None,
    _ => None,
  }
}

/// Unfold a definition and do cheap WHNF (no delta).
/// Matches lean4lean: `let delta e := whnfCore (unfoldDefinition env e).get!`.
fn delta(e: &Expr, tc: &mut TypeChecker) -> Expr {
  match try_unfold_def(e, tc.env) {
    Some(unfolded) => tc.whnf_no_delta(&unfolded),
    None => e.clone(),
  }
}

/// Compare reducibility hints for ordering.
fn hint_lt(a: &ReducibilityHints, b: &ReducibilityHints) -> bool {
  match (a, b) {
    (ReducibilityHints::Opaque, _) => true,
    (_, ReducibilityHints::Opaque) => false,
    (ReducibilityHints::Abbrev, _) => false,
    (_, ReducibilityHints::Abbrev) => true,
    (ReducibilityHints::Regular(ha), ReducibilityHints::Regular(hb)) => {
      ha < hb
    },
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::kernel::tc::TypeChecker;
  use crate::lean::nat::Nat;

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

  /// Minimal env with Nat, Nat.zero, Nat.succ.
  fn mk_nat_env() -> Env {
    let mut env = Env::default();
    let nat_name = mk_name("Nat");
    env.insert(
      nat_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: nat_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![nat_name.clone()],
        ctors: vec![mk_name2("Nat", "zero"), mk_name2("Nat", "succ")],
        num_nested: Nat::from(0u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    let zero_name = mk_name2("Nat", "zero");
    env.insert(
      zero_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: zero_name.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        induct: mk_name("Nat"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let succ_name = mk_name2("Nat", "succ");
    env.insert(
      succ_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: succ_name.clone(),
          level_params: vec![],
          typ: Expr::all(
            mk_name("n"),
            nat_type(),
            nat_type(),
            BinderInfo::Default,
          ),
        },
        induct: mk_name("Nat"),
        cidx: Nat::from(1u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    env
  }

  // ==========================================================================
  // Reflexivity
  // ==========================================================================

  #[test]
  fn def_eq_reflexive_sort() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::sort(Level::zero());
    assert!(tc.def_eq(&e, &e));
  }

  #[test]
  fn def_eq_reflexive_const() {
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = nat_zero();
    assert!(tc.def_eq(&e, &e));
  }

  #[test]
  fn def_eq_reflexive_lambda() {
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    assert!(tc.def_eq(&e, &e));
  }

  // ==========================================================================
  // Sort equality
  // ==========================================================================

  #[test]
  fn def_eq_sort_max_comm() {
    // Sort(max u v) =def= Sort(max v u)
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let u = Level::param(mk_name("u"));
    let v = Level::param(mk_name("v"));
    let s1 = Expr::sort(Level::max(u.clone(), v.clone()));
    let s2 = Expr::sort(Level::max(v, u));
    assert!(tc.def_eq(&s1, &s2));
  }

  #[test]
  fn def_eq_sort_not_equal() {
    // Sort(0) ≠ Sort(1)
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let s0 = Expr::sort(Level::zero());
    let s1 = Expr::sort(Level::succ(Level::zero()));
    assert!(!tc.def_eq(&s0, &s1));
  }

  // ==========================================================================
  // Alpha equivalence (same structure, different binder names)
  // ==========================================================================

  #[test]
  fn def_eq_alpha_lambda() {
    // fun (x : Nat) => x  =def=  fun (y : Nat) => y
    // (de Bruijn indices are the same, so this is syntactic equality)
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e1 = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let e2 = Expr::lam(
      mk_name("y"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    assert!(tc.def_eq(&e1, &e2));
  }

  #[test]
  fn def_eq_alpha_pi() {
    // (x : Nat) → Nat  =def=  (y : Nat) → Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e1 = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let e2 = Expr::all(
      mk_name("y"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert!(tc.def_eq(&e1, &e2));
  }

  // ==========================================================================
  // Beta equivalence
  // ==========================================================================

  #[test]
  fn def_eq_beta() {
    // (fun x : Nat => x) Nat.zero  =def=  Nat.zero
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let id_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let lhs = Expr::app(id_fn, nat_zero());
    let rhs = nat_zero();
    assert!(tc.def_eq(&lhs, &rhs));
  }

  #[test]
  fn def_eq_beta_nested() {
    // (fun x y : Nat => x) Nat.zero Nat.zero  =def=  Nat.zero
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let inner = Expr::lam(
      mk_name("y"),
      nat_type(),
      Expr::bvar(Nat::from(1u64)), // x
      BinderInfo::Default,
    );
    let k_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      inner,
      BinderInfo::Default,
    );
    let lhs = Expr::app(Expr::app(k_fn, nat_zero()), nat_zero());
    assert!(tc.def_eq(&lhs, &nat_zero()));
  }

  // ==========================================================================
  // Delta equivalence (definition unfolding)
  // ==========================================================================

  #[test]
  fn def_eq_delta() {
    // def myZero := Nat.zero
    // myZero =def= Nat.zero
    let mut env = mk_nat_env();
    let my_zero = mk_name("myZero");
    env.insert(
      my_zero.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: my_zero.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: nat_zero(),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![my_zero.clone()],
      }),
    );
    let mut tc = TypeChecker::new(&env);
    let lhs = Expr::cnst(my_zero, vec![]);
    assert!(tc.def_eq(&lhs, &nat_zero()));
  }

  #[test]
  fn def_eq_delta_both_sides() {
    // def a := Nat.zero, def b := Nat.zero
    // a =def= b
    let mut env = mk_nat_env();
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
        value: nat_zero(),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![b.clone()],
      }),
    );
    let mut tc = TypeChecker::new(&env);
    let lhs = Expr::cnst(a, vec![]);
    let rhs = Expr::cnst(b, vec![]);
    assert!(tc.def_eq(&lhs, &rhs));
  }

  // ==========================================================================
  // Zeta equivalence (let unfolding)
  // ==========================================================================

  #[test]
  fn def_eq_zeta() {
    // (let x : Nat := Nat.zero in x) =def= Nat.zero
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let lhs = Expr::letE(
      mk_name("x"),
      nat_type(),
      nat_zero(),
      Expr::bvar(Nat::from(0u64)),
      false,
    );
    assert!(tc.def_eq(&lhs, &nat_zero()));
  }

  // ==========================================================================
  // Negative tests
  // ==========================================================================

  #[test]
  fn def_eq_different_consts() {
    // Nat ≠ String
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let nat = nat_type();
    let string = Expr::cnst(mk_name("String"), vec![]);
    assert!(!tc.def_eq(&nat, &string));
  }

  #[test]
  fn def_eq_different_nat_levels() {
    // Nat.zero ≠ Nat.succ
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let zero = nat_zero();
    let succ = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    assert!(!tc.def_eq(&zero, &succ));
  }

  #[test]
  fn def_eq_app_congruence() {
    // f a =def= f a  (for same f, same a)
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let f = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let a = nat_zero();
    let lhs = Expr::app(f.clone(), a.clone());
    let rhs = Expr::app(f, a);
    assert!(tc.def_eq(&lhs, &rhs));
  }

  #[test]
  fn def_eq_app_different_args() {
    // Nat.succ Nat.zero ≠ Nat.succ (Nat.succ Nat.zero)
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let succ = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let lhs = Expr::app(succ.clone(), nat_zero());
    let rhs =
      Expr::app(succ.clone(), Expr::app(succ, nat_zero()));
    assert!(!tc.def_eq(&lhs, &rhs));
  }

  // ==========================================================================
  // Const-level equality
  // ==========================================================================

  #[test]
  fn def_eq_const_levels() {
    // A.{max u v} =def= A.{max v u}
    let mut env = Env::default();
    let a_name = mk_name("A");
    let u_name = mk_name("u");
    let v_name = mk_name("v");
    env.insert(
      a_name.clone(),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: a_name.clone(),
          level_params: vec![u_name.clone(), v_name.clone()],
          typ: Expr::sort(Level::max(
            Level::param(u_name.clone()),
            Level::param(v_name.clone()),
          )),
        },
        is_unsafe: false,
      }),
    );
    let mut tc = TypeChecker::new(&env);
    let u = Level::param(mk_name("u"));
    let v = Level::param(mk_name("v"));
    let lhs = Expr::cnst(a_name.clone(), vec![Level::max(u.clone(), v.clone()), Level::zero()]);
    let rhs = Expr::cnst(a_name, vec![Level::max(v, u), Level::zero()]);
    assert!(tc.def_eq(&lhs, &rhs));
  }

  // ==========================================================================
  // Hint ordering
  // ==========================================================================

  #[test]
  fn hint_lt_opaque_less_than_all() {
    assert!(hint_lt(&ReducibilityHints::Opaque, &ReducibilityHints::Abbrev));
    assert!(hint_lt(
      &ReducibilityHints::Opaque,
      &ReducibilityHints::Regular(0)
    ));
  }

  #[test]
  fn hint_lt_abbrev_greatest() {
    assert!(!hint_lt(
      &ReducibilityHints::Abbrev,
      &ReducibilityHints::Opaque
    ));
    assert!(!hint_lt(
      &ReducibilityHints::Abbrev,
      &ReducibilityHints::Regular(100)
    ));
  }

  #[test]
  fn hint_lt_regular_ordering() {
    assert!(hint_lt(
      &ReducibilityHints::Regular(1),
      &ReducibilityHints::Regular(2)
    ));
    assert!(!hint_lt(
      &ReducibilityHints::Regular(2),
      &ReducibilityHints::Regular(1)
    ));
  }

  // ==========================================================================
  // Eta expansion
  // ==========================================================================

  #[test]
  fn def_eq_eta_lam_vs_const() {
    // fun x : Nat => Nat.succ x  =def=  Nat.succ
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let succ = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let eta_expanded = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::app(succ.clone(), Expr::bvar(Nat::from(0u64))),
      BinderInfo::Default,
    );
    assert!(tc.def_eq(&eta_expanded, &succ));
  }

  #[test]
  fn def_eq_eta_symmetric() {
    // Nat.succ =def= fun x : Nat => Nat.succ x
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let succ = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let eta_expanded = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::app(succ.clone(), Expr::bvar(Nat::from(0u64))),
      BinderInfo::Default,
    );
    assert!(tc.def_eq(&succ, &eta_expanded));
  }

  // ==========================================================================
  // Lazy delta step with different heights
  // ==========================================================================

  #[test]
  fn def_eq_lazy_delta_higher_unfolds_first() {
    // def a := Nat.zero (height 1)
    // def b := a         (height 2)
    // b =def= Nat.zero should work by unfolding b first (higher height)
    let mut env = mk_nat_env();
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
        hints: ReducibilityHints::Regular(1),
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
        hints: ReducibilityHints::Regular(2),
        safety: DefinitionSafety::Safe,
        all: vec![b.clone()],
      }),
    );
    let mut tc = TypeChecker::new(&env);
    let lhs = Expr::cnst(b, vec![]);
    assert!(tc.def_eq(&lhs, &nat_zero()));
  }

  // ==========================================================================
  // Transitivity through delta
  // ==========================================================================

  #[test]
  fn def_eq_transitive_delta() {
    // def a := Nat.zero, def b := Nat.zero
    // def c := Nat.zero
    // a =def= b, a =def= c, b =def= c
    let mut env = mk_nat_env();
    for name_str in &["a", "b", "c"] {
      let n = mk_name(name_str);
      env.insert(
        n.clone(),
        ConstantInfo::DefnInfo(DefinitionVal {
          cnst: ConstantVal {
            name: n.clone(),
            level_params: vec![],
            typ: nat_type(),
          },
          value: nat_zero(),
          hints: ReducibilityHints::Abbrev,
          safety: DefinitionSafety::Safe,
          all: vec![n],
        }),
      );
    }
    let mut tc = TypeChecker::new(&env);
    let a = Expr::cnst(mk_name("a"), vec![]);
    let b = Expr::cnst(mk_name("b"), vec![]);
    let c = Expr::cnst(mk_name("c"), vec![]);
    assert!(tc.def_eq(&a, &b));
    assert!(tc.def_eq(&a, &c));
    assert!(tc.def_eq(&b, &c));
  }

  // ==========================================================================
  // Nat literal equality through WHNF
  // ==========================================================================

  #[test]
  fn def_eq_nat_lit_same() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let a = Expr::lit(Literal::NatVal(Nat::from(42u64)));
    let b = Expr::lit(Literal::NatVal(Nat::from(42u64)));
    assert!(tc.def_eq(&a, &b));
  }

  #[test]
  fn def_eq_nat_lit_different() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let a = Expr::lit(Literal::NatVal(Nat::from(1u64)));
    let b = Expr::lit(Literal::NatVal(Nat::from(2u64)));
    assert!(!tc.def_eq(&a, &b));
  }

  // ==========================================================================
  // Beta-delta combined
  // ==========================================================================

  #[test]
  fn def_eq_beta_delta_combined() {
    // def myId := fun x : Nat => x
    // myId Nat.zero =def= Nat.zero
    let mut env = mk_nat_env();
    let my_id = mk_name("myId");
    let fun_ty = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    env.insert(
      my_id.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: my_id.clone(),
          level_params: vec![],
          typ: fun_ty,
        },
        value: Expr::lam(
          mk_name("x"),
          nat_type(),
          Expr::bvar(Nat::from(0u64)),
          BinderInfo::Default,
        ),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![my_id.clone()],
      }),
    );
    let mut tc = TypeChecker::new(&env);
    let lhs = Expr::app(Expr::cnst(my_id, vec![]), nat_zero());
    assert!(tc.def_eq(&lhs, &nat_zero()));
  }

  // ==========================================================================
  // Structure eta
  // ==========================================================================

  /// Build an env with Nat + Prod.{u,v} structure type.
  fn mk_prod_env() -> Env {
    let mut env = mk_nat_env();
    let u_name = mk_name("u");
    let v_name = mk_name("v");
    let prod_name = mk_name("Prod");
    let mk_ctor_name = mk_name2("Prod", "mk");

    // Prod.{u,v} (α : Sort u) (β : Sort v) : Sort (max u v)
    let prod_type = Expr::all(
      mk_name("α"),
      Expr::sort(Level::param(u_name.clone())),
      Expr::all(
        mk_name("β"),
        Expr::sort(Level::param(v_name.clone())),
        Expr::sort(Level::max(
          Level::param(u_name.clone()),
          Level::param(v_name.clone()),
        )),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    env.insert(
      prod_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: prod_name.clone(),
          level_params: vec![u_name.clone(), v_name.clone()],
          typ: prod_type,
        },
        num_params: Nat::from(2u64),
        num_indices: Nat::from(0u64),
        all: vec![prod_name.clone()],
        ctors: vec![mk_ctor_name.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );

    // Prod.mk.{u,v} (α : Sort u) (β : Sort v) (fst : α) (snd : β) : Prod α β
    let ctor_type = Expr::all(
      mk_name("α"),
      Expr::sort(Level::param(u_name.clone())),
      Expr::all(
        mk_name("β"),
        Expr::sort(Level::param(v_name.clone())),
        Expr::all(
          mk_name("fst"),
          Expr::bvar(Nat::from(1u64)), // α
          Expr::all(
            mk_name("snd"),
            Expr::bvar(Nat::from(1u64)), // β
            Expr::app(
              Expr::app(
                Expr::cnst(
                  prod_name.clone(),
                  vec![
                    Level::param(u_name.clone()),
                    Level::param(v_name.clone()),
                  ],
                ),
                Expr::bvar(Nat::from(3u64)), // α
              ),
              Expr::bvar(Nat::from(2u64)), // β
            ),
            BinderInfo::Default,
          ),
          BinderInfo::Default,
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    env.insert(
      mk_ctor_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: mk_ctor_name,
          level_params: vec![u_name, v_name],
          typ: ctor_type,
        },
        induct: prod_name,
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(2u64),
        is_unsafe: false,
      }),
    );

    env
  }

  #[test]
  fn eta_struct_ctor_eq_proj() {
    // Prod.mk Nat Nat (Prod.1 p) (Prod.2 p) =def= p
    // where p is a free variable of type Prod Nat Nat
    let env = mk_prod_env();
    let mut tc = TypeChecker::new(&env);

    let one = Level::succ(Level::zero());
    let prod_nat_nat = Expr::app(
      Expr::app(
        Expr::cnst(mk_name("Prod"), vec![one.clone(), one.clone()]),
        nat_type(),
      ),
      nat_type(),
    );
    let p = tc.mk_local(&mk_name("p"), &prod_nat_nat);

    let ctor_app = Expr::app(
      Expr::app(
        Expr::app(
          Expr::app(
            Expr::cnst(
              mk_name2("Prod", "mk"),
              vec![one.clone(), one.clone()],
            ),
            nat_type(),
          ),
          nat_type(),
        ),
        Expr::proj(mk_name("Prod"), Nat::from(0u64), p.clone()),
      ),
      Expr::proj(mk_name("Prod"), Nat::from(1u64), p.clone()),
    );

    assert!(tc.def_eq(&ctor_app, &p));
  }

  #[test]
  fn eta_struct_symmetric() {
    // p =def= Prod.mk Nat Nat (Prod.1 p) (Prod.2 p)
    let env = mk_prod_env();
    let mut tc = TypeChecker::new(&env);

    let one = Level::succ(Level::zero());
    let prod_nat_nat = Expr::app(
      Expr::app(
        Expr::cnst(mk_name("Prod"), vec![one.clone(), one.clone()]),
        nat_type(),
      ),
      nat_type(),
    );
    let p = tc.mk_local(&mk_name("p"), &prod_nat_nat);

    let ctor_app = Expr::app(
      Expr::app(
        Expr::app(
          Expr::app(
            Expr::cnst(
              mk_name2("Prod", "mk"),
              vec![one.clone(), one.clone()],
            ),
            nat_type(),
          ),
          nat_type(),
        ),
        Expr::proj(mk_name("Prod"), Nat::from(0u64), p.clone()),
      ),
      Expr::proj(mk_name("Prod"), Nat::from(1u64), p.clone()),
    );

    assert!(tc.def_eq(&p, &ctor_app));
  }

  #[test]
  fn eta_struct_nat_not_structure_like() {
    // Nat has 2 constructors, so it is NOT structure-like
    let env = mk_nat_env();
    assert!(!super::is_structure_like(&mk_name("Nat"), &env));
  }

  // ==========================================================================
  // Binder full comparison
  // ==========================================================================

  #[test]
  fn def_eq_binder_full_different_domains() {
    // (x : myNat) → Nat =def= (x : Nat) → Nat
    // where myNat unfolds to Nat
    let mut env = mk_nat_env();
    let my_nat = mk_name("myNat");
    env.insert(
      my_nat.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: my_nat.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        value: nat_type(),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![my_nat.clone()],
      }),
    );
    let mut tc = TypeChecker::new(&env);
    let lhs = Expr::all(
      mk_name("x"),
      Expr::cnst(my_nat, vec![]),
      nat_type(),
      BinderInfo::Default,
    );
    let rhs = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert!(tc.def_eq(&lhs, &rhs));
  }

  // ==========================================================================
  // Proj congruence
  // ==========================================================================

  #[test]
  fn def_eq_proj_congruence() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let s = nat_zero();
    let lhs = Expr::proj(mk_name("S"), Nat::from(0u64), s.clone());
    let rhs = Expr::proj(mk_name("S"), Nat::from(0u64), s);
    assert!(tc.def_eq(&lhs, &rhs));
  }

  #[test]
  fn def_eq_proj_different_idx() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let s = nat_zero();
    let lhs = Expr::proj(mk_name("S"), Nat::from(0u64), s.clone());
    let rhs = Expr::proj(mk_name("S"), Nat::from(1u64), s);
    assert!(!tc.def_eq(&lhs, &rhs));
  }

  // ==========================================================================
  // Unit-like equality
  // ==========================================================================

  #[test]
  fn def_eq_unit_like() {
    // Unit-type: single ctor, zero fields
    // Any two inhabitants should be def-eq
    let mut env = mk_nat_env();
    let unit_name = mk_name("Unit");
    let unit_star = mk_name2("Unit", "star");

    env.insert(
      unit_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: unit_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![unit_name.clone()],
        ctors: vec![unit_star.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      unit_star.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: unit_star.clone(),
          level_params: vec![],
          typ: Expr::cnst(unit_name.clone(), vec![]),
        },
        induct: unit_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    let mut tc = TypeChecker::new(&env);

    // Two distinct fvars of type Unit should be def-eq
    let unit_ty = Expr::cnst(unit_name, vec![]);
    let x = tc.mk_local(&mk_name("x"), &unit_ty);
    let y = tc.mk_local(&mk_name("y"), &unit_ty);
    assert!(tc.def_eq(&x, &y));
  }

  // ==========================================================================
  // ThmInfo fix: theorems must not enter lazy_delta_step
  // ==========================================================================

  /// Build an env with Nat + two ThmInfo constants.
  fn mk_thm_env() -> Env {
    let mut env = mk_nat_env();
    let thm_a = mk_name("thmA");
    let thm_b = mk_name("thmB");
    let prop = Expr::sort(Level::zero());
    // Two theorems with the same type (True : Prop)
    let true_name = mk_name("True");
    env.insert(
      true_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: true_name.clone(),
          level_params: vec![],
          typ: prop.clone(),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![true_name.clone()],
        ctors: vec![mk_name2("True", "intro")],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    let intro_name = mk_name2("True", "intro");
    env.insert(
      intro_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: intro_name.clone(),
          level_params: vec![],
          typ: Expr::cnst(true_name.clone(), vec![]),
        },
        induct: true_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let true_ty = Expr::cnst(true_name, vec![]);
    env.insert(
      thm_a.clone(),
      ConstantInfo::ThmInfo(TheoremVal {
        cnst: ConstantVal {
          name: thm_a.clone(),
          level_params: vec![],
          typ: true_ty.clone(),
        },
        value: Expr::cnst(intro_name.clone(), vec![]),
        all: vec![thm_a.clone()],
      }),
    );
    env.insert(
      thm_b.clone(),
      ConstantInfo::ThmInfo(TheoremVal {
        cnst: ConstantVal {
          name: thm_b.clone(),
          level_params: vec![],
          typ: true_ty,
        },
        value: Expr::cnst(intro_name, vec![]),
        all: vec![thm_b.clone()],
      }),
    );
    env
  }

  #[test]
  fn test_def_eq_theorem_vs_theorem_terminates() {
    // Two theorem constants of the same Prop type should be def-eq
    // via proof irrelevance (not via delta). Before the fix, this
    // would infinite loop because get_applied_def returned Some for ThmInfo.
    let env = mk_thm_env();
    let mut tc = TypeChecker::new(&env);
    let a = Expr::cnst(mk_name("thmA"), vec![]);
    let b = Expr::cnst(mk_name("thmB"), vec![]);
    assert!(tc.def_eq(&a, &b));
  }

  #[test]
  fn test_def_eq_theorem_vs_constructor_terminates() {
    // A theorem constant vs a constructor of the same type must terminate.
    let env = mk_thm_env();
    let mut tc = TypeChecker::new(&env);
    let thm = Expr::cnst(mk_name("thmA"), vec![]);
    let ctor = Expr::cnst(mk_name2("True", "intro"), vec![]);
    // Both have type True (a Prop), so proof irrelevance should make them def-eq
    assert!(tc.def_eq(&thm, &ctor));
  }

  #[test]
  fn test_get_applied_def_excludes_theorems() {
    // Theorems should never be unfolded — proof irrelevance handles them.
    let env = mk_thm_env();
    let thm = Expr::cnst(mk_name("thmA"), vec![]);
    let result = get_applied_def(&thm, &env);
    assert!(result.is_none());
  }

  // ==========================================================================
  // Nat offset equality (is_nat_zero, is_nat_succ, def_eq_nat_offset)
  // ==========================================================================

  fn nat_lit(n: u64) -> Expr {
    Expr::lit(Literal::NatVal(Nat::from(n)))
  }

  #[test]
  fn test_is_nat_zero_ctor() {
    assert!(super::is_nat_zero(&nat_zero()));
  }

  #[test]
  fn test_is_nat_zero_lit() {
    assert!(super::is_nat_zero(&nat_lit(0)));
  }

  #[test]
  fn test_is_nat_zero_nonzero_lit() {
    assert!(!super::is_nat_zero(&nat_lit(5)));
  }

  #[test]
  fn test_is_nat_succ_ctor() {
    let succ_zero = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      nat_lit(4),
    );
    let pred = super::is_nat_succ(&succ_zero);
    assert!(pred.is_some());
    assert_eq!(pred.unwrap(), nat_lit(4));
  }

  #[test]
  fn test_is_nat_succ_lit() {
    // lit 5 should decompose to lit 4 (Lean 4: isNatSuccOf?)
    let pred = super::is_nat_succ(&nat_lit(5));
    assert!(pred.is_some());
    assert_eq!(pred.unwrap(), nat_lit(4));
  }

  #[test]
  fn test_is_nat_succ_lit_one() {
    // lit 1 should decompose to lit 0
    let pred = super::is_nat_succ(&nat_lit(1));
    assert!(pred.is_some());
    assert_eq!(pred.unwrap(), nat_lit(0));
  }

  #[test]
  fn test_is_nat_succ_lit_zero() {
    // lit 0 should NOT decompose (it's zero, not succ of anything)
    assert!(super::is_nat_succ(&nat_lit(0)).is_none());
  }

  #[test]
  fn test_is_nat_succ_nat_zero_ctor() {
    assert!(super::is_nat_succ(&nat_zero()).is_none());
  }

  #[test]
  fn def_eq_nat_zero_ctor_vs_lit() {
    // Nat.zero =def= lit 0
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    assert!(tc.def_eq(&nat_zero(), &nat_lit(0)));
  }

  #[test]
  fn def_eq_nat_lit_vs_succ_lit() {
    // lit 5 =def= Nat.succ (lit 4)
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let succ_4 = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      nat_lit(4),
    );
    assert!(tc.def_eq(&nat_lit(5), &succ_4));
  }

  #[test]
  fn def_eq_nat_succ_lit_vs_lit() {
    // Nat.succ (lit 4) =def= lit 5
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let succ_4 = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      nat_lit(4),
    );
    assert!(tc.def_eq(&succ_4, &nat_lit(5)));
  }

  #[test]
  fn def_eq_nat_lit_one_vs_succ_zero() {
    // lit 1 =def= Nat.succ Nat.zero
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let succ_zero = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      nat_zero(),
    );
    assert!(tc.def_eq(&nat_lit(1), &succ_zero));
  }

  #[test]
  fn def_eq_nat_lit_not_equal_succ() {
    // lit 5 ≠ Nat.succ (lit 5)
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let succ_5 = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      nat_lit(5),
    );
    assert!(!tc.def_eq(&nat_lit(5), &succ_5));
  }

  #[test]
  fn def_eq_nat_add_result_vs_lit() {
    // Nat.add (lit 3) (lit 4) =def= lit 7
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let add_3_4 = Expr::app(
      Expr::app(
        Expr::cnst(mk_name2("Nat", "add"), vec![]),
        nat_lit(3),
      ),
      nat_lit(4),
    );
    assert!(tc.def_eq(&add_3_4, &nat_lit(7)));
  }

  #[test]
  fn def_eq_nat_add_vs_succ() {
    // Nat.add (lit 3) (lit 4) =def= Nat.succ (lit 6)
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let add_3_4 = Expr::app(
      Expr::app(
        Expr::cnst(mk_name2("Nat", "add"), vec![]),
        nat_lit(3),
      ),
      nat_lit(4),
    );
    let succ_6 = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      nat_lit(6),
    );
    assert!(tc.def_eq(&add_3_4, &succ_6));
  }
}
