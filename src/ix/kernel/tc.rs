use crate::ix::env::*;
use crate::lean::nat::Nat;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashMap;

use super::def_eq::def_eq;
use super::error::TcError;
use super::level::{all_expr_uparams_defined, no_dupes_all_params};
use super::whnf::*;

type TcResult<T> = Result<T, TcError>;

/// The kernel type checker.
pub struct TypeChecker<'env> {
  pub env: &'env Env,
  pub whnf_cache: FxHashMap<Expr, Expr>,
  pub whnf_no_delta_cache: FxHashMap<Expr, Expr>,
  pub infer_cache: FxHashMap<Expr, Expr>,
  pub local_counter: u64,
  pub local_types: FxHashMap<Name, Expr>,
  pub def_eq_calls: u64,
  pub whnf_calls: u64,
  pub infer_calls: u64,
}

impl<'env> TypeChecker<'env> {
  pub fn new(env: &'env Env) -> Self {
    TypeChecker {
      env,
      whnf_cache: FxHashMap::default(),
      whnf_no_delta_cache: FxHashMap::default(),
      infer_cache: FxHashMap::default(),
      local_counter: 0,
      local_types: FxHashMap::default(),
      def_eq_calls: 0,
      whnf_calls: 0,
      infer_calls: 0,
    }
  }

  // ==========================================================================
  // WHNF with caching
  // ==========================================================================

  pub fn whnf(&mut self, e: &Expr) -> Expr {
    if let Some(cached) = self.whnf_cache.get(e) {
      return cached.clone();
    }
    self.whnf_calls += 1;
    let tag = match e.as_data() {
      ExprData::Sort(..) => "Sort",
      ExprData::Const(_, _, _) => "Const",
      ExprData::App(..) => "App",
      ExprData::Lam(..) => "Lam",
      ExprData::ForallE(..) => "Pi",
      ExprData::LetE(..) => "Let",
      ExprData::Lit(..) => "Lit",
      ExprData::Proj(..) => "Proj",
      ExprData::Fvar(..) => "Fvar",
      ExprData::Bvar(..) => "Bvar",
      ExprData::Mvar(..) => "Mvar",
      ExprData::Mdata(..) => "Mdata",
    };
    eprintln!("[tc.whnf] #{} {tag}", self.whnf_calls);
    let result = whnf(e, self.env);
    eprintln!("[tc.whnf] #{} {tag} done", self.whnf_calls);
    result
  }

  pub fn whnf_no_delta(&mut self, e: &Expr) -> Expr {
    if let Some(cached) = self.whnf_no_delta_cache.get(e) {
      return cached.clone();
    }
    let result = whnf_no_delta(e, self.env);
    self.whnf_no_delta_cache.insert(e.clone(), result.clone());
    result
  }

  // ==========================================================================
  // Local context management
  // ==========================================================================

  /// Create a fresh free variable for entering a binder.
  pub fn mk_local(&mut self, name: &Name, ty: &Expr) -> Expr {
    let id = self.local_counter;
    self.local_counter += 1;
    let local_name = Name::num(name.clone(), Nat::from(id));
    self.local_types.insert(local_name.clone(), ty.clone());
    Expr::fvar(local_name)
  }

  // ==========================================================================
  // Ensure helpers
  // ==========================================================================

  pub fn ensure_sort(&mut self, e: &Expr) -> TcResult<Level> {
    if let ExprData::Sort(level, _) = e.as_data() {
      return Ok(level.clone());
    }
    let whnfd = self.whnf(e);
    match whnfd.as_data() {
      ExprData::Sort(level, _) => Ok(level.clone()),
      _ => Err(TcError::TypeExpected {
        expr: e.clone(),
        inferred: whnfd,
      }),
    }
  }

  pub fn ensure_pi(&mut self, e: &Expr) -> TcResult<Expr> {
    if let ExprData::ForallE(..) = e.as_data() {
      return Ok(e.clone());
    }
    let whnfd = self.whnf(e);
    match whnfd.as_data() {
      ExprData::ForallE(..) => Ok(whnfd),
      _ => Err(TcError::FunctionExpected {
        expr: e.clone(),
        inferred: whnfd,
      }),
    }
  }

  /// Infer the type of `e` and ensure it's a sort; return the universe level.
  pub fn infer_sort_of(&mut self, e: &Expr) -> TcResult<Level> {
    let ty = self.infer(e)?;
    let whnfd = self.whnf(&ty);
    self.ensure_sort(&whnfd)
  }

  // ==========================================================================
  // Type inference
  // ==========================================================================

  pub fn infer(&mut self, e: &Expr) -> TcResult<Expr> {
    if let Some(cached) = self.infer_cache.get(e) {
      return Ok(cached.clone());
    }
    self.infer_calls += 1;
    let tag = match e.as_data() {
      ExprData::Sort(..) => "Sort".to_string(),
      ExprData::Const(n, _, _) => format!("Const({})", n.pretty()),
      ExprData::App(..) => "App".to_string(),
      ExprData::Lam(..) => "Lam".to_string(),
      ExprData::ForallE(..) => "Pi".to_string(),
      ExprData::LetE(..) => "Let".to_string(),
      ExprData::Lit(..) => "Lit".to_string(),
      ExprData::Proj(..) => "Proj".to_string(),
      ExprData::Fvar(n, _) => format!("Fvar({})", n.pretty()),
      ExprData::Bvar(..) => "Bvar".to_string(),
      ExprData::Mvar(..) => "Mvar".to_string(),
      ExprData::Mdata(..) => "Mdata".to_string(),
    };
    eprintln!("[tc.infer] #{} {tag}", self.infer_calls);
    let result = self.infer_core(e)?;
    self.infer_cache.insert(e.clone(), result.clone());
    Ok(result)
  }

  fn infer_core(&mut self, e: &Expr) -> TcResult<Expr> {
    // Peel Mdata and Let layers iteratively to avoid stack depth
    let mut cursor = e.clone();
    loop {
      match cursor.as_data() {
        ExprData::Mdata(_, inner, _) => {
          // Check cache for inner before recursing
          if let Some(cached) = self.infer_cache.get(inner) {
            return Ok(cached.clone());
          }
          cursor = inner.clone();
          continue;
        },
        ExprData::LetE(_, typ, val, body, _, _) => {
          let val_ty = self.infer(val)?;
          self.assert_def_eq(&val_ty, typ)?;
          let body_inst = inst(body, &[val.clone()]);
          // Check cache for body_inst before looping
          if let Some(cached) = self.infer_cache.get(&body_inst) {
            return Ok(cached.clone());
          }
          // Cache the current let expression's result once we compute it
          let orig = cursor.clone();
          cursor = body_inst;
          // We need to compute the result and cache it for `orig`
          let result = self.infer(&cursor)?;
          self.infer_cache.insert(orig, result.clone());
          return Ok(result);
        },
        ExprData::Sort(level, _) => return self.infer_sort(level),
        ExprData::Const(name, levels, _) => {
          return self.infer_const(name, levels)
        },
        ExprData::App(..) => return self.infer_app(&cursor),
        ExprData::Lam(..) => return self.infer_lambda(&cursor),
        ExprData::ForallE(..) => return self.infer_pi(&cursor),
        ExprData::Lit(lit, _) => return self.infer_lit(lit),
        ExprData::Proj(type_name, idx, structure, _) => {
          return self.infer_proj(type_name, idx, structure)
        },
        ExprData::Fvar(name, _) => {
          return match self.local_types.get(name) {
            Some(ty) => Ok(ty.clone()),
            None => Err(TcError::KernelException {
              msg: "cannot infer type of free variable without context"
                .into(),
            }),
          }
        },
        ExprData::Bvar(idx, _) => {
          return Err(TcError::FreeBoundVariable {
            idx: idx.to_u64().unwrap_or(u64::MAX),
          })
        },
        ExprData::Mvar(..) => {
          return Err(TcError::KernelException {
            msg: "cannot infer type of metavariable".into(),
          })
        },
      }
    }
  }

  fn infer_sort(&mut self, level: &Level) -> TcResult<Expr> {
    Ok(Expr::sort(Level::succ(level.clone())))
  }

  fn infer_const(
    &mut self,
    name: &Name,
    levels: &[Level],
  ) -> TcResult<Expr> {
    let ci = self
      .env
      .get(name)
      .ok_or_else(|| TcError::UnknownConst { name: name.clone() })?;

    let decl_params = ci.get_level_params();
    if levels.len() != decl_params.len() {
      return Err(TcError::KernelException {
        msg: format!(
          "universe parameter count mismatch for {}",
          name.pretty()
        ),
      });
    }

    let ty = ci.get_type();
    Ok(subst_expr_levels(ty, decl_params, levels))
  }

  fn infer_app(&mut self, e: &Expr) -> TcResult<Expr> {
    let (fun, args) = unfold_apps(e);
    let mut fun_ty = self.infer(&fun)?;

    for arg in &args {
      let pi = self.ensure_pi(&fun_ty)?;
      match pi.as_data() {
        ExprData::ForallE(_, binder_type, body, _, _) => {
          // Check argument type matches binder
          let arg_ty = self.infer(arg)?;
          self.assert_def_eq(&arg_ty, binder_type)?;
          fun_ty = inst(body, &[arg.clone()]);
        },
        _ => unreachable!(),
      }
    }

    Ok(fun_ty)
  }

  fn infer_lambda(&mut self, e: &Expr) -> TcResult<Expr> {
    let mut cursor = e.clone();
    let mut locals = Vec::new();
    let mut binder_types = Vec::new();
    let mut binder_infos = Vec::new();
    let mut binder_names = Vec::new();

    while let ExprData::Lam(name, binder_type, body, bi, _) =
      cursor.as_data()
    {
      let binder_type_inst = inst(binder_type, &locals);
      self.infer_sort_of(&binder_type_inst)?;

      let local = self.mk_local(name, &binder_type_inst);
      locals.push(local);
      binder_types.push(binder_type_inst);
      binder_infos.push(bi.clone());
      binder_names.push(name.clone());
      cursor = body.clone();
    }

    let body_inst = inst(&cursor, &locals);
    let body_ty = self.infer(&body_inst)?;

    // Abstract back: build Pi telescope
    let mut result = abstr(&body_ty, &locals);
    for i in (0..locals.len()).rev() {
      let binder_type_abstrd = abstr(&binder_types[i], &locals[..i]);
      result = Expr::all(
        binder_names[i].clone(),
        binder_type_abstrd,
        result,
        binder_infos[i].clone(),
      );
    }

    Ok(result)
  }

  fn infer_pi(&mut self, e: &Expr) -> TcResult<Expr> {
    let mut cursor = e.clone();
    let mut locals = Vec::new();
    let mut universes = Vec::new();

    while let ExprData::ForallE(name, binder_type, body, _bi, _) =
      cursor.as_data()
    {
      let binder_type_inst = inst(binder_type, &locals);
      let dom_univ = self.infer_sort_of(&binder_type_inst)?;
      universes.push(dom_univ);

      let local = self.mk_local(name, &binder_type_inst);
      locals.push(local);
      cursor = body.clone();
    }

    let body_inst = inst(&cursor, &locals);
    let mut result_level = self.infer_sort_of(&body_inst)?;

    for univ in universes.into_iter().rev() {
      result_level = Level::imax(univ, result_level);
    }

    Ok(Expr::sort(result_level))
  }

  fn infer_lit(&mut self, lit: &Literal) -> TcResult<Expr> {
    match lit {
      Literal::NatVal(_) => {
        Ok(Expr::cnst(Name::str(Name::anon(), "Nat".into()), vec![]))
      },
      Literal::StrVal(_) => {
        Ok(Expr::cnst(Name::str(Name::anon(), "String".into()), vec![]))
      },
    }
  }

  fn infer_proj(
    &mut self,
    type_name: &Name,
    idx: &Nat,
    structure: &Expr,
  ) -> TcResult<Expr> {
    let structure_ty = self.infer(structure)?;
    let structure_ty_whnf = self.whnf(&structure_ty);

    let (_, struct_ty_args) = unfold_apps(&structure_ty_whnf);
    let struct_ty_head = match unfold_apps(&structure_ty_whnf).0.as_data() {
      ExprData::Const(name, levels, _) => (name.clone(), levels.clone()),
      _ => {
        return Err(TcError::KernelException {
          msg: "projection structure type is not a constant".into(),
        })
      },
    };

    let ind = self.env.get(&struct_ty_head.0).ok_or_else(|| {
      TcError::UnknownConst { name: struct_ty_head.0.clone() }
    })?;

    let (num_params, ctor_name) = match ind {
      ConstantInfo::InductInfo(iv) => {
        let ctor = iv.ctors.first().ok_or_else(|| {
          TcError::KernelException {
            msg: "inductive has no constructors".into(),
          }
        })?;
        (iv.num_params.to_u64().unwrap(), ctor.clone())
      },
      _ => {
        return Err(TcError::KernelException {
          msg: "projection type is not an inductive".into(),
        })
      },
    };

    let ctor_ci = self.env.get(&ctor_name).ok_or_else(|| {
      TcError::UnknownConst { name: ctor_name.clone() }
    })?;

    let mut ctor_ty = subst_expr_levels(
      ctor_ci.get_type(),
      ctor_ci.get_level_params(),
      &struct_ty_head.1,
    );

    // Skip params
    for i in 0..num_params as usize {
      let whnf_ty = self.whnf(&ctor_ty);
      match whnf_ty.as_data() {
        ExprData::ForallE(_, _, body, _, _) => {
          ctor_ty = inst(body, &[struct_ty_args[i].clone()]);
        },
        _ => {
          return Err(TcError::KernelException {
            msg: "ran out of constructor telescope (params)".into(),
          })
        },
      }
    }

    // Walk to the idx-th field
    let idx_usize = idx.to_u64().unwrap() as usize;
    for i in 0..idx_usize {
      let whnf_ty = self.whnf(&ctor_ty);
      match whnf_ty.as_data() {
        ExprData::ForallE(_, _, body, _, _) => {
          let proj =
            Expr::proj(type_name.clone(), Nat::from(i as u64), structure.clone());
          ctor_ty = inst(body, &[proj]);
        },
        _ => {
          return Err(TcError::KernelException {
            msg: "ran out of constructor telescope (fields)".into(),
          })
        },
      }
    }

    let whnf_ty = self.whnf(&ctor_ty);
    match whnf_ty.as_data() {
      ExprData::ForallE(_, binder_type, _, _, _) => {
        Ok(binder_type.clone())
      },
      _ => Err(TcError::KernelException {
        msg: "ran out of constructor telescope (target field)".into(),
      }),
    }
  }

  // ==========================================================================
  // Definitional equality (delegated to def_eq module)
  // ==========================================================================

  pub fn def_eq(&mut self, x: &Expr, y: &Expr) -> bool {
    self.def_eq_calls += 1;
    eprintln!("[tc.def_eq] #{}", self.def_eq_calls);
    let result = def_eq(x, y, self);
    eprintln!("[tc.def_eq] #{} done => {result}", self.def_eq_calls);
    result
  }

  pub fn assert_def_eq(&mut self, x: &Expr, y: &Expr) -> TcResult<()> {
    if self.def_eq(x, y) {
      Ok(())
    } else {
      Err(TcError::DefEqFailure { lhs: x.clone(), rhs: y.clone() })
    }
  }

  // ==========================================================================
  // Declaration checking
  // ==========================================================================

  /// Check that a declaration's type is well-formed.
  pub fn check_declar_info(
    &mut self,
    info: &ConstantVal,
  ) -> TcResult<()> {
    // Check for duplicate universe params
    if !no_dupes_all_params(&info.level_params) {
      return Err(TcError::KernelException {
        msg: format!(
          "duplicate universe parameters in {}",
          info.name.pretty()
        ),
      });
    }

    // Check that the type has no loose bound variables
    if has_loose_bvars(&info.typ) {
      return Err(TcError::KernelException {
        msg: format!(
          "free bound variables in type of {}",
          info.name.pretty()
        ),
      });
    }

    // Check that all universe parameters in the type are declared
    if !all_expr_uparams_defined(&info.typ, &info.level_params) {
      return Err(TcError::KernelException {
        msg: format!(
          "undeclared universe parameters in type of {}",
          info.name.pretty()
        ),
      });
    }

    // Check that the type is a type (infers to a Sort)
    let inferred = self.infer(&info.typ)?;
    self.ensure_sort(&inferred)?;

    Ok(())
  }

  /// Check a declaration that has both a type and a value (DefnInfo, ThmInfo, OpaqueInfo).
  fn check_value_declar(
    &mut self,
    cnst: &ConstantVal,
    value: &Expr,
  ) -> TcResult<()> {
    eprintln!("[check_value_declar] checking type for {}", cnst.name.pretty());
    self.check_declar_info(cnst)?;
    eprintln!("[check_value_declar] type OK, checking value uparams");
    if !all_expr_uparams_defined(value, &cnst.level_params) {
      return Err(TcError::KernelException {
        msg: format!(
          "undeclared universe parameters in value of {}",
          cnst.name.pretty()
        ),
      });
    }
    eprintln!("[check_value_declar] inferring value type");
    let inferred_type = self.infer(value)?;
    eprintln!("[check_value_declar] inferred, checking def_eq");
    self.assert_def_eq(&inferred_type, &cnst.typ)?;
    eprintln!("[check_value_declar] done");
    Ok(())
  }

  /// Check a single declaration.
  pub fn check_declar(
    &mut self,
    ci: &ConstantInfo,
  ) -> TcResult<()> {
    match ci {
      ConstantInfo::AxiomInfo(v) => {
        self.check_declar_info(&v.cnst)?;
      },
      ConstantInfo::DefnInfo(v) => {
        self.check_value_declar(&v.cnst, &v.value)?;
      },
      ConstantInfo::ThmInfo(v) => {
        self.check_value_declar(&v.cnst, &v.value)?;
      },
      ConstantInfo::OpaqueInfo(v) => {
        self.check_value_declar(&v.cnst, &v.value)?;
      },
      ConstantInfo::QuotInfo(v) => {
        self.check_declar_info(&v.cnst)?;
        super::quot::check_quot(self.env)?;
      },
      ConstantInfo::InductInfo(v) => {
        super::inductive::check_inductive(v, self)?;
      },
      ConstantInfo::CtorInfo(v) => {
        self.check_declar_info(&v.cnst)?;
        // Verify the parent inductive exists
        if self.env.get(&v.induct).is_none() {
          return Err(TcError::UnknownConst {
            name: v.induct.clone(),
          });
        }
      },
      ConstantInfo::RecInfo(v) => {
        self.check_declar_info(&v.cnst)?;
        for ind_name in &v.all {
          if self.env.get(ind_name).is_none() {
            return Err(TcError::UnknownConst {
              name: ind_name.clone(),
            });
          }
        }
        super::inductive::validate_k_flag(v, self.env)?;
      },
    }
    Ok(())
  }
}

/// Check all declarations in an environment in parallel.
pub fn check_env(env: &Env) -> Vec<(Name, TcError)> {
  use std::collections::BTreeSet;
  use std::io::Write;
  use std::sync::atomic::{AtomicUsize, Ordering};
  use std::sync::Mutex;

  let total = env.len();
  let checked = AtomicUsize::new(0);

  struct Display {
    active: BTreeSet<String>,
    prev_lines: usize,
  }
  let display = Mutex::new(Display { active: BTreeSet::new(), prev_lines: 0 });

  let refresh = |d: &mut Display, checked: usize| {
    let mut stderr = std::io::stderr().lock();
    if d.prev_lines > 0 {
      write!(stderr, "\x1b[{}A", d.prev_lines).ok();
    }
    write!(
      stderr,
      "\x1b[2K[check_env] {}/{} — {} active\n",
      checked,
      total,
      d.active.len()
    )
    .ok();
    let mut new_lines = 1;
    for name in &d.active {
      write!(stderr, "\x1b[2K  {}\n", name).ok();
      new_lines += 1;
    }
    let extra = d.prev_lines.saturating_sub(new_lines);
    for _ in 0..extra {
      write!(stderr, "\x1b[2K\n").ok();
    }
    if extra > 0 {
      write!(stderr, "\x1b[{}A", extra).ok();
    }
    d.prev_lines = new_lines;
    stderr.flush().ok();
  };

  env
    .par_iter()
    .filter_map(|(name, ci)| {
      let pretty = name.pretty();
      {
        let mut d = display.lock().unwrap();
        d.active.insert(pretty.clone());
        refresh(&mut d, checked.load(Ordering::Relaxed));
      }

      let mut tc = TypeChecker::new(env);
      let result = tc.check_declar(ci);

      let n = checked.fetch_add(1, Ordering::Relaxed) + 1;
      {
        let mut d = display.lock().unwrap();
        d.active.remove(&pretty);
        refresh(&mut d, n);
      }

      match result {
        Ok(()) => None,
        Err(e) => Some((name.clone(), e)),
      }
    })
    .collect()
}

#[cfg(test)]
mod tests {
  use super::*;
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

  fn prop() -> Expr {
    Expr::sort(Level::zero())
  }

  fn type_u() -> Expr {
    Expr::sort(Level::param(mk_name("u")))
  }

  fn bvar(n: u64) -> Expr {
    Expr::bvar(Nat::from(n))
  }

  fn nat_succ_expr() -> Expr {
    Expr::cnst(mk_name2("Nat", "succ"), vec![])
  }

  /// Build a minimal environment with Nat, Nat.zero, Nat.succ, and Nat.rec.
  fn mk_nat_env() -> Env {
    let mut env = Env::default();
    let u = mk_name("u");

    let nat_name = mk_name("Nat");
    // Nat : Sort 1
    let nat = ConstantInfo::InductInfo(InductiveVal {
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
    });
    env.insert(nat_name, nat);

    // Nat.zero : Nat
    let zero_name = mk_name2("Nat", "zero");
    let zero = ConstantInfo::CtorInfo(ConstructorVal {
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
    });
    env.insert(zero_name, zero);

    // Nat.succ : Nat → Nat
    let succ_name = mk_name2("Nat", "succ");
    let succ_ty = Expr::all(
      mk_name("n"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let succ = ConstantInfo::CtorInfo(ConstructorVal {
      cnst: ConstantVal {
        name: succ_name.clone(),
        level_params: vec![],
        typ: succ_ty,
      },
      induct: mk_name("Nat"),
      cidx: Nat::from(1u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(1u64),
      is_unsafe: false,
    });
    env.insert(succ_name, succ);

    // Nat.rec.{u} :
    //   {motive : Nat → Sort u} →
    //   motive Nat.zero →
    //   ((n : Nat) → motive n → motive (Nat.succ n)) →
    //   (t : Nat) → motive t
    let rec_name = mk_name2("Nat", "rec");

    // Build the type with de Bruijn indices.
    // Binder stack (from outermost): motive(3), z(2), s(1), t(0)
    // At the innermost body: motive=bvar(3), z=bvar(2), s=bvar(1), t=bvar(0)
    let motive_type = Expr::all(
      mk_name("_"),
      nat_type(),
      Expr::sort(Level::param(u.clone())),
      BinderInfo::Default,
    ); // Nat → Sort u

    // s type: (n : Nat) → motive n → motive (Nat.succ n)
    // At s's position: motive=bvar(1), z=bvar(0)
    // Inside forallE "n": motive=bvar(2), z=bvar(1), n=bvar(0)
    // Inside forallE "_": motive=bvar(3), z=bvar(2), n=bvar(1), _=bvar(0)
    let s_type = Expr::all(
      mk_name("n"),
      nat_type(),
      Expr::all(
        mk_name("_"),
        Expr::app(bvar(2), bvar(0)),  // motive n
        Expr::app(bvar(3), Expr::app(nat_succ_expr(), bvar(1))), // motive (Nat.succ n)
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    let rec_type = Expr::all(
      mk_name("motive"),
      motive_type.clone(),
      Expr::all(
        mk_name("z"),
        Expr::app(bvar(0), nat_zero()), // motive Nat.zero
        Expr::all(
          mk_name("s"),
          s_type,
          Expr::all(
            mk_name("t"),
            nat_type(),
            Expr::app(bvar(3), bvar(0)), // motive t
            BinderInfo::Default,
          ),
          BinderInfo::Default,
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Implicit,
    );

    // Zero rule RHS: fun (motive) (z) (s) => z
    // Inside: motive=bvar(2), z=bvar(1), s=bvar(0)
    let zero_rhs = Expr::lam(
      mk_name("motive"),
      motive_type.clone(),
      Expr::lam(
        mk_name("z"),
        Expr::app(bvar(0), nat_zero()),
        Expr::lam(
          mk_name("s"),
          nat_type(), // placeholder type for s (not checked)
          bvar(1),    // z
          BinderInfo::Default,
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    // Succ rule RHS: fun (motive) (z) (s) (n) => s n (Nat.rec.{u} motive z s n)
    // Inside: motive=bvar(3), z=bvar(2), s=bvar(1), n=bvar(0)
    let nat_rec_u =
      Expr::cnst(rec_name.clone(), vec![Level::param(u.clone())]);
    let recursive_call = Expr::app(
      Expr::app(
        Expr::app(
          Expr::app(nat_rec_u, bvar(3)), // Nat.rec motive
          bvar(2),                        // z
        ),
        bvar(1), // s
      ),
      bvar(0), // n
    );
    let succ_rhs = Expr::lam(
      mk_name("motive"),
      motive_type,
      Expr::lam(
        mk_name("z"),
        Expr::app(bvar(0), nat_zero()),
        Expr::lam(
          mk_name("s"),
          nat_type(), // placeholder
          Expr::lam(
            mk_name("n"),
            nat_type(),
            Expr::app(
              Expr::app(bvar(1), bvar(0)), // s n
              recursive_call,              // (Nat.rec motive z s n)
            ),
            BinderInfo::Default,
          ),
          BinderInfo::Default,
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    let rec = ConstantInfo::RecInfo(RecursorVal {
      cnst: ConstantVal {
        name: rec_name.clone(),
        level_params: vec![u],
        typ: rec_type,
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![
        RecursorRule {
          ctor: mk_name2("Nat", "zero"),
          n_fields: Nat::from(0u64),
          rhs: zero_rhs,
        },
        RecursorRule {
          ctor: mk_name2("Nat", "succ"),
          n_fields: Nat::from(1u64),
          rhs: succ_rhs,
        },
      ],
      k: false,
      is_unsafe: false,
    });
    env.insert(rec_name, rec);

    env
  }

  // ==========================================================================
  // Infer: Sort
  // ==========================================================================

  #[test]
  fn infer_sort_zero() {
    // Sort(0) : Sort(1)
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = prop();
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, Expr::sort(Level::succ(Level::zero())));
  }

  #[test]
  fn infer_sort_succ() {
    // Sort(1) : Sort(2)
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::sort(Level::succ(Level::zero()));
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, Expr::sort(Level::succ(Level::succ(Level::zero()))));
  }

  #[test]
  fn infer_sort_param() {
    // Sort(u) : Sort(u+1)
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let u = Level::param(mk_name("u"));
    let e = Expr::sort(u.clone());
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, Expr::sort(Level::succ(u)));
  }

  // ==========================================================================
  // Infer: Const
  // ==========================================================================

  #[test]
  fn infer_const_nat() {
    // Nat : Sort 1
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::cnst(mk_name("Nat"), vec![]);
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, Expr::sort(Level::succ(Level::zero())));
  }

  #[test]
  fn infer_const_nat_zero() {
    // Nat.zero : Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = nat_zero();
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, nat_type());
  }

  #[test]
  fn infer_const_nat_succ() {
    // Nat.succ : Nat → Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let ty = tc.infer(&e).unwrap();
    let expected = Expr::all(
      mk_name("n"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert_eq!(ty, expected);
  }

  #[test]
  fn infer_const_unknown() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::cnst(mk_name("NonExistent"), vec![]);
    assert!(tc.infer(&e).is_err());
  }

  #[test]
  fn infer_const_universe_mismatch() {
    // Nat has 0 universe params; passing 1 should fail
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::cnst(mk_name("Nat"), vec![Level::zero()]);
    assert!(tc.infer(&e).is_err());
  }

  // ==========================================================================
  // Infer: Lit
  // ==========================================================================

  #[test]
  fn infer_nat_lit() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::lit(Literal::NatVal(Nat::from(42u64)));
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, nat_type());
  }

  #[test]
  fn infer_string_lit() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::lit(Literal::StrVal("hello".into()));
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, Expr::cnst(mk_name("String"), vec![]));
  }

  // ==========================================================================
  // Infer: Lambda
  // ==========================================================================

  #[test]
  fn infer_identity_lambda() {
    // fun (x : Nat) => x : Nat → Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let id_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let ty = tc.infer(&id_fn).unwrap();
    let expected = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert_eq!(ty, expected);
  }

  #[test]
  fn infer_const_lambda() {
    // fun (x : Nat) (y : Nat) => x : Nat → Nat → Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let body = Expr::lam(
      mk_name("y"),
      nat_type(),
      Expr::bvar(Nat::from(1u64)), // x
      BinderInfo::Default,
    );
    let k_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      body,
      BinderInfo::Default,
    );
    let ty = tc.infer(&k_fn).unwrap();
    // Nat → Nat → Nat
    let expected = Expr::all(
      mk_name("x"),
      nat_type(),
      Expr::all(
        mk_name("y"),
        nat_type(),
        nat_type(),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    assert_eq!(ty, expected);
  }

  // ==========================================================================
  // Infer: App
  // ==========================================================================

  #[test]
  fn infer_app_succ_zero() {
    // Nat.succ Nat.zero : Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      nat_zero(),
    );
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, nat_type());
  }

  #[test]
  fn infer_app_identity() {
    // (fun x : Nat => x) Nat.zero : Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let id_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let e = Expr::app(id_fn, nat_zero());
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, nat_type());
  }

  // ==========================================================================
  // Infer: Pi
  // ==========================================================================

  #[test]
  fn infer_pi_nat_to_nat() {
    // (Nat → Nat) : Sort 1
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let pi = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let ty = tc.infer(&pi).unwrap();
    // Sort(imax(1, 1)) which simplifies to Sort(1)
    if let ExprData::Sort(level, _) = ty.as_data() {
      assert!(
        super::super::level::eq_antisymm(
          level,
          &Level::succ(Level::zero())
        ),
        "Nat → Nat should live in Sort 1, got {:?}",
        level
      );
    } else {
      panic!("Expected Sort, got {:?}", ty);
    }
  }

  #[test]
  fn infer_pi_prop_to_prop() {
    // (Prop → Prop) : Sort 1
    // An axiom P : Prop, then P → P : Sort 1
    let mut env = Env::default();
    let p_name = mk_name("P");
    env.insert(
      p_name.clone(),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: p_name.clone(),
          level_params: vec![],
          typ: prop(),
        },
        is_unsafe: false,
      }),
    );

    let mut tc = TypeChecker::new(&env);
    let p = Expr::cnst(p_name, vec![]);
    let pi = Expr::all(mk_name("x"), p.clone(), p.clone(), BinderInfo::Default);
    let ty = tc.infer(&pi).unwrap();
    // Sort(imax(0, 0)) = Sort(0) = Prop
    if let ExprData::Sort(level, _) = ty.as_data() {
      assert!(
        super::super::level::is_zero(level),
        "Prop → Prop should live in Prop, got {:?}",
        level
      );
    } else {
      panic!("Expected Sort, got {:?}", ty);
    }
  }

  // ==========================================================================
  // Infer: Let
  // ==========================================================================

  #[test]
  fn infer_let_simple() {
    // let x : Nat := Nat.zero in x  :  Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::letE(
      mk_name("x"),
      nat_type(),
      nat_zero(),
      Expr::bvar(Nat::from(0u64)),
      false,
    );
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, nat_type());
  }

  // ==========================================================================
  // Infer: errors
  // ==========================================================================

  #[test]
  fn infer_free_bvar_fails() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::bvar(Nat::from(0u64));
    assert!(tc.infer(&e).is_err());
  }

  #[test]
  fn infer_fvar_fails() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::fvar(mk_name("x"));
    assert!(tc.infer(&e).is_err());
  }

  #[test]
  fn infer_app_wrong_arg_type() {
    // Nat.succ expects Nat, but we pass Sort(0) — should fail with DefEqFailure
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      prop(), // Sort(0), not Nat
    );
    assert!(tc.infer(&e).is_err());
  }

  #[test]
  fn infer_let_type_mismatch() {
    // let x : Nat → Nat := Nat.zero in x
    // Nat.zero : Nat, but annotation says Nat → Nat — should fail
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let nat_to_nat = Expr::all(
      mk_name("n"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let e = Expr::letE(
      mk_name("x"),
      nat_to_nat,
      nat_zero(),
      Expr::bvar(Nat::from(0u64)),
      false,
    );
    assert!(tc.infer(&e).is_err());
  }

  // ==========================================================================
  // check_declar
  // ==========================================================================

  #[test]
  fn check_axiom_declar() {
    // axiom myAxiom : Nat → Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let ax_ty = Expr::all(
      mk_name("n"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let ax = ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal {
        name: mk_name("myAxiom"),
        level_params: vec![],
        typ: ax_ty,
      },
      is_unsafe: false,
    });
    assert!(tc.check_declar(&ax).is_ok());
  }

  #[test]
  fn check_defn_declar() {
    // def myId : Nat → Nat := fun x => x
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let fun_ty = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let body = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let defn = ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: mk_name("myId"),
        level_params: vec![],
        typ: fun_ty,
      },
      value: body,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![mk_name("myId")],
    });
    assert!(tc.check_declar(&defn).is_ok());
  }

  #[test]
  fn check_defn_type_mismatch() {
    // def bad : Nat := Nat.succ (wrong: Nat.succ : Nat → Nat, not Nat)
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let defn = ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: mk_name("bad"),
        level_params: vec![],
        typ: nat_type(),
      },
      value: Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![mk_name("bad")],
    });
    assert!(tc.check_declar(&defn).is_err());
  }

  #[test]
  fn check_declar_loose_bvar() {
    // Type with a dangling bound variable should fail
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let ax = ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal {
        name: mk_name("bad"),
        level_params: vec![],
        typ: Expr::bvar(Nat::from(0u64)),
      },
      is_unsafe: false,
    });
    assert!(tc.check_declar(&ax).is_err());
  }

  #[test]
  fn check_declar_duplicate_uparams() {
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let u = mk_name("u");
    let ax = ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal {
        name: mk_name("bad"),
        level_params: vec![u.clone(), u],
        typ: type_u(),
      },
      is_unsafe: false,
    });
    assert!(tc.check_declar(&ax).is_err());
  }

  // ==========================================================================
  // check_env
  // ==========================================================================

  #[test]
  fn check_nat_env() {
    let env = mk_nat_env();
    let errors = check_env(&env);
    assert!(errors.is_empty(), "Expected no errors, got: {:?}", errors);
  }

  // ==========================================================================
  // Polymorphic constants
  // ==========================================================================

  #[test]
  fn infer_polymorphic_const() {
    // axiom A.{u} : Sort u
    // A.{0} should give Sort(0)
    let mut env = Env::default();
    let a_name = mk_name("A");
    let u_name = mk_name("u");
    env.insert(
      a_name.clone(),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: a_name.clone(),
          level_params: vec![u_name.clone()],
          typ: Expr::sort(Level::param(u_name)),
        },
        is_unsafe: false,
      }),
    );
    let mut tc = TypeChecker::new(&env);
    // A.{0} : Sort(0)
    let e = Expr::cnst(a_name, vec![Level::zero()]);
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, Expr::sort(Level::zero()));
  }

  // ==========================================================================
  // Infer: whnf caching
  // ==========================================================================

  #[test]
  fn whnf_cache_works() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::sort(Level::zero());
    let r1 = tc.whnf(&e);
    let r2 = tc.whnf(&e);
    assert_eq!(r1, r2);
  }

  // ==========================================================================
  // check_declar: Theorem
  // ==========================================================================

  #[test]
  fn check_theorem_declar() {
    // theorem myThm : Nat → Nat := fun x => x
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let fun_ty = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let body = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let thm = ConstantInfo::ThmInfo(TheoremVal {
      cnst: ConstantVal {
        name: mk_name("myThm"),
        level_params: vec![],
        typ: fun_ty,
      },
      value: body,
      all: vec![mk_name("myThm")],
    });
    assert!(tc.check_declar(&thm).is_ok());
  }

  #[test]
  fn check_theorem_type_mismatch() {
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let thm = ConstantInfo::ThmInfo(TheoremVal {
      cnst: ConstantVal {
        name: mk_name("badThm"),
        level_params: vec![],
        typ: nat_type(), // claims : Nat
      },
      value: Expr::cnst(mk_name2("Nat", "succ"), vec![]), // but is : Nat → Nat
      all: vec![mk_name("badThm")],
    });
    assert!(tc.check_declar(&thm).is_err());
  }

  // ==========================================================================
  // check_declar: Opaque
  // ==========================================================================

  #[test]
  fn check_opaque_declar() {
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let opaque = ConstantInfo::OpaqueInfo(OpaqueVal {
      cnst: ConstantVal {
        name: mk_name("myOpaque"),
        level_params: vec![],
        typ: nat_type(),
      },
      value: nat_zero(),
      is_unsafe: false,
      all: vec![mk_name("myOpaque")],
    });
    assert!(tc.check_declar(&opaque).is_ok());
  }

  // ==========================================================================
  // check_declar: Ctor (parent existence check)
  // ==========================================================================

  #[test]
  fn check_ctor_missing_parent() {
    // A constructor whose parent inductive doesn't exist
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let ctor = ConstantInfo::CtorInfo(ConstructorVal {
      cnst: ConstantVal {
        name: mk_name2("Fake", "mk"),
        level_params: vec![],
        typ: Expr::sort(Level::succ(Level::zero())),
      },
      induct: mk_name("Fake"),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    });
    assert!(tc.check_declar(&ctor).is_err());
  }

  #[test]
  fn check_ctor_with_parent() {
    // Nat.zero : Nat, with Nat in env
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let ctor = ConstantInfo::CtorInfo(ConstructorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "zero"),
        level_params: vec![],
        typ: nat_type(),
      },
      induct: mk_name("Nat"),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    });
    assert!(tc.check_declar(&ctor).is_ok());
  }

  // ==========================================================================
  // check_declar: Rec (mutual reference check)
  // ==========================================================================

  #[test]
  fn check_rec_missing_inductive() {
    let env = Env::default();
    let mut tc = TypeChecker::new(&env);
    let rec = ConstantInfo::RecInfo(RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Fake", "rec"),
        level_params: vec![],
        typ: Expr::sort(Level::succ(Level::zero())),
      },
      all: vec![mk_name("Fake")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(0u64),
      rules: vec![],
      k: false,
      is_unsafe: false,
    });
    assert!(tc.check_declar(&rec).is_err());
  }

  #[test]
  fn check_rec_with_inductive() {
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let rec = ConstantInfo::RecInfo(RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![],
      k: false,
      is_unsafe: false,
    });
    assert!(tc.check_declar(&rec).is_ok());
  }

  // ==========================================================================
  // Infer: App with delta (definition in head)
  // ==========================================================================

  #[test]
  fn infer_app_through_delta() {
    // def myId : Nat → Nat := fun x => x
    // myId Nat.zero : Nat
    let mut env = mk_nat_env();
    let fun_ty = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let body = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    env.insert(
      mk_name("myId"),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: mk_name("myId"),
          level_params: vec![],
          typ: fun_ty,
        },
        value: body,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![mk_name("myId")],
      }),
    );
    let mut tc = TypeChecker::new(&env);
    let e = Expr::app(
      Expr::cnst(mk_name("myId"), vec![]),
      nat_zero(),
    );
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, nat_type());
  }

  // ==========================================================================
  // Infer: Proj
  // ==========================================================================

  /// Build an env with a simple Prod.{u,v} structure type.
  fn mk_prod_env() -> Env {
    let mut env = mk_nat_env();
    let u_name = mk_name("u");
    let v_name = mk_name("v");
    let prod_name = mk_name("Prod");
    let mk_name_prod = mk_name2("Prod", "mk");

    // Prod.{u,v} : Sort u → Sort v → Sort (max u v)
    // Simplified: Prod (α : Sort u) (β : Sort v) : Sort (max u v)
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
        ctors: vec![mk_name_prod.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );

    // Prod.mk.{u,v} (α : Sort u) (β : Sort v) (fst : α) (snd : β) : Prod α β
    // Type: (α : Sort u) → (β : Sort v) → α → β → Prod α β
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
      mk_name_prod.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: mk_name_prod,
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
  fn infer_proj_fst() {
    // Given p : Prod Nat Nat, (Prod.1 p) : Nat
    // Build: Prod.mk Nat Nat Nat.zero Nat.zero, then project field 0
    let env = mk_prod_env();
    let mut tc = TypeChecker::new(&env);

    let one = Level::succ(Level::zero());
    let pair = Expr::app(
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
        nat_zero(),
      ),
      nat_zero(),
    );

    let proj = Expr::proj(mk_name("Prod"), Nat::from(0u64), pair);
    let ty = tc.infer(&proj).unwrap();
    assert_eq!(ty, nat_type());
  }

  // ==========================================================================
  // Infer: nested let
  // ==========================================================================

  #[test]
  fn infer_nested_let() {
    // let x := Nat.zero in let y := x in y  :  Nat
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let inner = Expr::letE(
      mk_name("y"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)), // x
      Expr::bvar(Nat::from(0u64)), // y
      false,
    );
    let e = Expr::letE(
      mk_name("x"),
      nat_type(),
      nat_zero(),
      inner,
      false,
    );
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, nat_type());
  }

  // ==========================================================================
  // Infer caching
  // ==========================================================================

  #[test]
  fn infer_cache_hit() {
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let e = nat_zero();
    let ty1 = tc.infer(&e).unwrap();
    let ty2 = tc.infer(&e).unwrap();
    assert_eq!(ty1, ty2);
    assert_eq!(tc.infer_cache.len(), 1);
  }

  // ==========================================================================
  // Universe parameter validation
  // ==========================================================================

  #[test]
  fn check_axiom_undeclared_uparam_in_type() {
    // axiom bad.{u} : Sort v — v is not declared
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let ax = ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal {
        name: mk_name("bad"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("v"))),
      },
      is_unsafe: false,
    });
    assert!(tc.check_declar(&ax).is_err());
  }

  #[test]
  fn check_axiom_declared_uparam_in_type() {
    // axiom good.{u} : Sort u — u is declared
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let ax = ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal {
        name: mk_name("good"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      is_unsafe: false,
    });
    assert!(tc.check_declar(&ax).is_ok());
  }

  #[test]
  fn check_defn_undeclared_uparam_in_value() {
    // def bad.{u} : Sort 1 := Sort v — v not declared, in value
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let defn = ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: mk_name("bad"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::succ(Level::zero())),
      },
      value: Expr::sort(Level::param(mk_name("v"))),
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![mk_name("bad")],
    });
    assert!(tc.check_declar(&defn).is_err());
  }

  // ==========================================================================
  // K-flag validation
  // ==========================================================================

  /// Build an env with a Prop inductive + single zero-field ctor (Eq-like).
  fn mk_eq_like_env() -> Env {
    let mut env = mk_nat_env();
    let u = mk_name("u");
    let eq_name = mk_name("MyEq");
    let eq_refl = mk_name2("MyEq", "refl");

    // MyEq.{u} (α : Sort u) (a : α) : α → Prop
    // Simplified: type lives in Prop (Sort 0)
    let eq_ty = Expr::all(
      mk_name("α"),
      Expr::sort(Level::param(u.clone())),
      Expr::all(
        mk_name("a"),
        Expr::bvar(Nat::from(0u64)),
        Expr::all(
          mk_name("b"),
          Expr::bvar(Nat::from(1u64)),
          Expr::sort(Level::zero()),
          BinderInfo::Default,
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    env.insert(
      eq_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: eq_name.clone(),
          level_params: vec![u.clone()],
          typ: eq_ty,
        },
        num_params: Nat::from(2u64),
        num_indices: Nat::from(1u64),
        all: vec![eq_name.clone()],
        ctors: vec![eq_refl.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: true,
      }),
    );
    // MyEq.refl.{u} (α : Sort u) (a : α) : MyEq α a a
    // zero fields
    let refl_ty = Expr::all(
      mk_name("α"),
      Expr::sort(Level::param(u.clone())),
      Expr::all(
        mk_name("a"),
        Expr::bvar(Nat::from(0u64)),
        Expr::app(
          Expr::app(
            Expr::app(
              Expr::cnst(eq_name.clone(), vec![Level::param(u.clone())]),
              Expr::bvar(Nat::from(1u64)),
            ),
            Expr::bvar(Nat::from(0u64)),
          ),
          Expr::bvar(Nat::from(0u64)),
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    env.insert(
      eq_refl.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: eq_refl,
          level_params: vec![u],
          typ: refl_ty,
        },
        induct: eq_name,
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    env
  }

  #[test]
  fn check_rec_k_flag_valid() {
    let env = mk_eq_like_env();
    let mut tc = TypeChecker::new(&env);
    let rec = ConstantInfo::RecInfo(RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("MyEq", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("MyEq")],
      num_params: Nat::from(2u64),
      num_indices: Nat::from(1u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(1u64),
      rules: vec![],
      k: true,
      is_unsafe: false,
    });
    assert!(tc.check_declar(&rec).is_ok());
  }

  #[test]
  fn check_rec_k_flag_invalid_2_ctors() {
    // Nat has 2 constructors — K should fail
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);
    let rec = ConstantInfo::RecInfo(RecursorVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "rec"),
        level_params: vec![mk_name("u")],
        typ: Expr::sort(Level::param(mk_name("u"))),
      },
      all: vec![mk_name("Nat")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![],
      k: true, // invalid: Nat is not in Prop and has 2 ctors
      is_unsafe: false,
    });
    assert!(tc.check_declar(&rec).is_err());
  }

  // ==========================================================================
  // check_declar: Nat.add via Nat.rec
  // ==========================================================================

  #[test]
  fn check_nat_add_via_rec() {
    // Nat.add : Nat → Nat → Nat :=
    //   fun (n m : Nat) => @Nat.rec.{1} (fun _ => Nat) n (fun _ ih => Nat.succ ih) m
    let env = mk_nat_env();
    let mut tc = TypeChecker::new(&env);

    let nat = nat_type();
    let nat_rec_1 = Expr::cnst(
      mk_name2("Nat", "rec"),
      vec![Level::succ(Level::zero())],
    );

    // motive: fun (_ : Nat) => Nat
    let motive = Expr::lam(
      mk_name("_"),
      nat.clone(),
      nat.clone(),
      BinderInfo::Default,
    );

    // step: fun (_ : Nat) (ih : Nat) => Nat.succ ih
    let step = Expr::lam(
      mk_name("_"),
      nat.clone(),
      Expr::lam(
        mk_name("ih"),
        nat.clone(),
        Expr::app(nat_succ_expr(), bvar(0)), // Nat.succ ih
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    // value: fun (n m : Nat) => @Nat.rec.{1} (fun _ => Nat) n (fun _ ih => Nat.succ ih) m
    // = fun n m => Nat.rec motive n step m
    let body = Expr::app(
      Expr::app(
        Expr::app(
          Expr::app(nat_rec_1, motive),
          bvar(1), // n
        ),
        step,
      ),
      bvar(0), // m
    );
    let value = Expr::lam(
      mk_name("n"),
      nat.clone(),
      Expr::lam(
        mk_name("m"),
        nat.clone(),
        body,
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    let typ = Expr::all(
      mk_name("n"),
      nat.clone(),
      Expr::all(mk_name("m"), nat.clone(), nat, BinderInfo::Default),
      BinderInfo::Default,
    );

    let defn = ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: mk_name2("Nat", "add"),
        level_params: vec![],
        typ,
      },
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![mk_name2("Nat", "add")],
    });
    assert!(tc.check_declar(&defn).is_ok());
  }

  /// Build mk_nat_env + Nat.add definition in the env.
  fn mk_nat_add_env() -> Env {
    let mut env = mk_nat_env();
    let nat = nat_type();

    let nat_rec_1 = Expr::cnst(
      mk_name2("Nat", "rec"),
      vec![Level::succ(Level::zero())],
    );

    let motive = Expr::lam(
      mk_name("_"),
      nat.clone(),
      nat.clone(),
      BinderInfo::Default,
    );

    let step = Expr::lam(
      mk_name("_"),
      nat.clone(),
      Expr::lam(
        mk_name("ih"),
        nat.clone(),
        Expr::app(nat_succ_expr(), bvar(0)),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    let body = Expr::app(
      Expr::app(
        Expr::app(
          Expr::app(nat_rec_1, motive),
          bvar(1), // n
        ),
        step,
      ),
      bvar(0), // m
    );
    let value = Expr::lam(
      mk_name("n"),
      nat.clone(),
      Expr::lam(
        mk_name("m"),
        nat.clone(),
        body,
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );

    let typ = Expr::all(
      mk_name("n"),
      nat.clone(),
      Expr::all(mk_name("m"), nat.clone(), nat, BinderInfo::Default),
      BinderInfo::Default,
    );

    env.insert(
      mk_name2("Nat", "add"),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: mk_name2("Nat", "add"),
          level_params: vec![],
          typ,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![mk_name2("Nat", "add")],
      }),
    );

    env
  }

  #[test]
  fn check_nat_add_env() {
    // Verify that the full Nat + Nat.add environment typechecks
    let env = mk_nat_add_env();
    let errors = check_env(&env);
    assert!(errors.is_empty(), "Expected no errors, got: {:?}", errors);
  }

  #[test]
  fn whnf_nat_add_zero_zero() {
    // Nat.add Nat.zero Nat.zero should WHNF to 0 (as nat literal)
    let env = mk_nat_add_env();
    let e = Expr::app(
      Expr::app(
        Expr::cnst(mk_name2("Nat", "add"), vec![]),
        nat_zero(),
      ),
      nat_zero(),
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::lit(Literal::NatVal(Nat::from(0u64))));
  }

  #[test]
  fn whnf_nat_add_lit() {
    // Nat.add 2 3 should WHNF to 5
    let env = mk_nat_add_env();
    let two = Expr::lit(Literal::NatVal(Nat::from(2u64)));
    let three = Expr::lit(Literal::NatVal(Nat::from(3u64)));
    let e = Expr::app(
      Expr::app(
        Expr::cnst(mk_name2("Nat", "add"), vec![]),
        two,
      ),
      three,
    );
    let result = whnf(&e, &env);
    assert_eq!(result, Expr::lit(Literal::NatVal(Nat::from(5u64))));
  }

  #[test]
  fn infer_nat_add_applied() {
    // Nat.add Nat.zero Nat.zero : Nat
    let env = mk_nat_add_env();
    let mut tc = TypeChecker::new(&env);
    let e = Expr::app(
      Expr::app(
        Expr::cnst(mk_name2("Nat", "add"), vec![]),
        nat_zero(),
      ),
      nat_zero(),
    );
    let ty = tc.infer(&e).unwrap();
    assert_eq!(ty, nat_type());
  }
}
