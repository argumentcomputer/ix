//! Type inference.

use std::sync::LazyLock;

use super::constant::KConst;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::subst::subst;
use super::tc::{TypeChecker, collect_app_spine};

/// Emit detailed `[app diff]` trace when `infer`'s App path rejects an
/// argument via `AppTypeMismatch`. Off by default — every rejection in a
/// kernel-check pass would print multiple whnf dumps per failing constant,
/// drowning normal `FAIL` lines. Set `IX_APP_DIFF=1` when investigating
/// why a specific `a_ty` and `dom` don't match after reduction. Pairs
/// with the `a_ty` / `dom` pair already printed by the error display.
static IX_APP_DIFF: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_APP_DIFF").is_ok());

/// When set, log every 100K `infer` entries (total, across cache hits
/// and real calls). A check using millions of infer calls points to a
/// bloated term or a mis-firing cache. Pairs with `IX_DEF_EQ_COUNT_LOG`
/// / `IX_WHNF_COUNT_LOG` for a full picture of per-check hotspots.
static IX_INFER_COUNT_LOG: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_INFER_COUNT_LOG").is_ok());

static INFER_COUNT: std::sync::atomic::AtomicUsize =
  std::sync::atomic::AtomicUsize::new(0);

impl<M: KernelMode> TypeChecker<'_, M> {
  pub fn infer(&mut self, e: &KExpr<M>) -> Result<KExpr<M>, TcError<M>> {
    if *IX_INFER_COUNT_LOG {
      let n = INFER_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
      if n.is_multiple_of(100_000) && n > 0 {
        eprintln!("[infer] count={n}");
      }
    }
    let infer_only = self.infer_only;

    let cache_key = self.infer_key(e);
    // Full-mode results are validated and may be consumed by either mode.
    if let Some(cached) = self.env.infer_cache.get(&cache_key) {
      self.env.perf.record_infer_hit();
      return Ok(cached.clone());
    }
    self.env.perf.record_infer_miss();
    // Infer-only results skipped argument/let validation, so only infer-only
    // callers may reuse them.
    if infer_only {
      if let Some(cached) = self.env.infer_only_cache.get(&cache_key) {
        self.env.perf.record_infer_only_hit();
        return Ok(cached.clone());
      }
      self.env.perf.record_infer_only_miss();
    }

    let ty = match e.data() {
      ExprData::Var(i, _, _) => self.lookup_var(*i)?,

      ExprData::Sort(u, _) => {
        let u2 = KUniv::succ(u.clone());
        self.intern(KExpr::sort(u2))
      },

      ExprData::Const(id, us, _) => {
        let c = self.get_const(id)?;
        if u64_to_usize::<M>(c.lvls())? != us.len() {
          return Err(TcError::UnivParamMismatch {
            expected: c.lvls(),
            got: us.len(),
          });
        }
        let ty = c.ty().clone();
        let us_vec: Vec<_> = us.to_vec();
        self.instantiate_univ_params(&ty, &us_vec)?
      },

      ExprData::App(f, a, _) => {
        let f_ty = self.infer(f)?;
        let (dom, cod) = self.ensure_forall(&f_ty).inspect_err(|_err| {
          eprintln!("[infer App] ensure_forall FAILED");
          eprintln!("  f:    {f}");
          eprintln!("  f_ty: {f_ty}");
          eprintln!("  f_ty addr: {:?}", f_ty.addr());
          eprintln!("  a:    {a}");
          if let ExprData::App(ff, fa, _) = f.data() {
            eprintln!("  ff:    {ff}");
            eprintln!("  ff addr: {:?}", ff.addr());
            if let Ok(ff_ty) = self.infer(ff) {
              eprintln!("  ff_ty: {ff_ty}");
              eprintln!("  ff_ty addr: {:?}", ff_ty.addr());
              if let Ok((dom2, cod2)) = self.ensure_forall(&ff_ty) {
                eprintln!("  ff_ty dom: {dom2}");
                eprintln!("  ff_ty cod: {cod2}");
              }
            }
            eprintln!("  fa:    {fa}");
          }
        })?;
        if !infer_only {
          let a_ty = self.infer(a)?;
          let is_eager = self.is_eager_reduce(a);
          if is_eager {
            self.eager_reduce = true;
          }
          let eq = self.is_def_eq(&a_ty, &dom)?;
          if is_eager {
            self.eager_reduce = false;
          }
          if !eq {
            if *IX_APP_DIFF && self.debug_label_matches_env() {
              // WHNF both sides so we can see where reduction actually
              // terminates. The raw `a_ty` / `dom` are already in the
              // error — what's useful here is the post-whnf forms and
              // whether they converge under `is_def_eq`'s lazy unfold
              // strategy.
              let a_whnf = self.whnf(&a_ty);
              let d_whnf = self.whnf(&dom);
              eprintln!(
                "[app diff] AppTypeMismatch at depth={}",
                self.ctx.len()
              );
              eprintln!("  f:          {}", compact_expr(f));
              eprintln!("  a:          {}", compact_expr(a));
              eprintln!("  a_ty:       {}", compact_expr_deep(&a_ty, 2));
              eprintln!("  dom:        {}", compact_expr_deep(&dom, 2));
              match &a_whnf {
                Ok(w) => eprintln!("  a_ty whnf:  {}", compact_expr_deep(w, 2)),
                Err(e) => eprintln!("  a_ty whnf:  ERR {e}"),
              }
              match &d_whnf {
                Ok(w) => eprintln!("  dom  whnf:  {}", compact_expr_deep(w, 2)),
                Err(e) => eprintln!("  dom  whnf:  ERR {e}"),
              }
            }
            return Err(TcError::AppTypeMismatch {
              a_ty,
              dom,
              depth: self.ctx.len(),
            });
          }
        }
        subst(&mut self.env.intern, &cod, a, 0)
      },

      ExprData::Lam(_, _, ty, body, _) => {
        if !infer_only {
          let t = self.infer(ty)?;
          self.ensure_sort(&t)?;
        }
        self.push_local(ty.clone());
        let body_ty = self.infer(body)?;
        self.pop_local();
        self.intern(KExpr::all(
          M::meta_field(crate::ix::env::Name::anon()),
          M::meta_field(crate::ix::env::BinderInfo::Default),
          ty.clone(),
          body_ty,
        ))
      },

      ExprData::All(_, _, ty, body, _) => {
        let ty_ty = self.infer(ty)?;
        let u1 = self.ensure_sort(&ty_ty)?;
        self.push_local(ty.clone());
        let body_ty = self.infer(body)?;
        let u2 = self.ensure_sort(&body_ty)?;
        self.pop_local();
        let u = KUniv::imax(u1, u2);
        self.intern(KExpr::sort(u))
      },

      ExprData::Let(_, ty, val, body, _, _) => {
        if !infer_only {
          let t = self.infer(ty)?;
          self.ensure_sort(&t)?;
          let val_ty = self.infer(val)?;
          if !self.is_def_eq(&val_ty, ty)? {
            return Err(TcError::DeclTypeMismatch);
          }
        }
        self.push_let(ty.clone(), val.clone());
        let body_ty = self.infer(body)?;
        self.pop_local();
        subst(&mut self.env.intern, &body_ty, val, 0)
      },

      ExprData::Prj(struct_id, field, val, _) => {
        let struct_id = struct_id.clone();
        let val_ty = self.infer(val)?;
        self.infer_proj(&struct_id, *field, val, &val_ty)?
      },

      ExprData::Nat(..) => self.infer_nat_type()?,
      ExprData::Str(..) => self.infer_str_type()?,
    };

    if !infer_only {
      self.env.infer_cache.insert(cache_key, ty.clone());
    } else {
      self.env.infer_only_cache.insert(cache_key, ty.clone());
    }
    Ok(ty)
  }

  fn infer_proj(
    &mut self,
    struct_id: &KId<M>,
    field: u64,
    val: &KExpr<M>,
    val_ty: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    use super::level::univ_eq;
    use super::tc::collect_app_spine;

    let wty = self.whnf(val_ty)?;
    let (head, args) = collect_app_spine(&wty);

    let head_id = match head.data() {
      ExprData::Const(id, _, _) => id,
      _ => {
        return Err(TcError::Other(
          "projection: struct type is not a constant".into(),
        ));
      },
    };
    if head_id.addr != struct_id.addr {
      return Err(TcError::Other(
        "projection: type mismatch with declared struct".into(),
      ));
    }

    let (i_levels, num_params, num_indices, ctors) = match self
      .try_get_const(head_id)?
    {
      Some(KConst::Indc { params, indices, ctors, .. }) => {
        let levels = match head.data() {
          ExprData::Const(_, us, _) => us.clone(),
          _ => unreachable!(),
        };
        (
          levels,
          u64_to_usize::<M>(params)?,
          u64_to_usize::<M>(indices)?,
          ctors.clone(),
        )
      },
      _ => {
        return Err(TcError::Other("projection: not an inductive type".into()));
      },
    };

    if ctors.len() != 1 {
      return Err(TcError::Other(
        "projection: inductive must have exactly one constructor".into(),
      ));
    }

    // Check if the structure lives in Prop. Do this from the inductive
    // declaration's result sort instead of inferring the full applied value
    // type: projection-heavy proof terms otherwise re-infer every parameter
    // and index argument just to recover a universe that is declaration-local.
    let is_prop_struct = self.inductive_app_is_prop(
      head_id,
      &i_levels,
      num_params + num_indices,
    )?;

    let ctor_ty = match self.try_get_const(&ctors[0])? {
      Some(c) => c.ty().clone(),
      None => {
        return Err(TcError::Other("projection: constructor not found".into()));
      },
    };

    let i_levels_vec: Vec<_> = i_levels.to_vec();
    let mut r = self.instantiate_univ_params(&ctor_ty, &i_levels_vec)?;

    for i in 0..num_params {
      let (_, body) = self
        .peel_proj_forall(&r, "projection: expected forall in ctor type")?;
      if i < args.len() {
        r = subst(&mut self.env.intern, &body, &args[i], 0);
      } else {
        return Err(TcError::Other("projection: not enough params".into()));
      }
    }

    for i in 0..=field {
      let (dom, body) =
        self.peel_proj_forall(&r, "projection: not enough fields")?;
      if i == field {
        // For Prop structures, the projected field must be in Prop.
        if is_prop_struct {
          let field_sort_ty = self.infer(&dom)?;
          let field_level = self.ensure_sort(&field_sort_ty)?;
          if !univ_eq(&field_level, &KUniv::zero()) {
            return Err(TcError::Other(
              "projection: cannot project data field from Prop structure"
                .into(),
            ));
          }
        }
        return Ok(dom);
      }
      // For Prop structures, check if this preceding field is a data field
      // that subsequent fields depend on. If so, projection is forbidden.
      if is_prop_struct {
        let field_sort_ty = self.infer(&dom)?;
        let field_level = self.ensure_sort(&field_sort_ty)?;
        let is_data = !univ_eq(&field_level, &KUniv::zero());
        // body.lbr() > 0 means the body references Var(0), i.e., depends on this field
        if is_data && body.lbr() > 0 {
          return Err(TcError::Other(
            "projection: forbidden after dependent data field in Prop structure"
              .into(),
          ));
        }
      }
      let proj = self.intern(KExpr::prj(struct_id.clone(), i, val.clone()));
      r = subst(&mut self.env.intern, &body, &proj, 0);
    }

    Err(TcError::Other("projection: unreachable".into()))
  }

  /// Peel the leading `Π` binder from `e`, returning `(domain, body)`.
  ///
  /// Tries the syntactic fast path first: if `e` is already
  /// `ExprData::All(..)`, no WHNF call is made. Only on miss does it fall
  /// back to full `whnf` and re-check. This is the audit Tier 1 #2 fix
  /// (`infer.rs:218, 281, 299`); the per-iteration full WHNF on a body
  /// mutated by `subst` rarely hits the WHNF cache and re-traverses the
  /// substituted body each iteration.
  ///
  /// `err` is the message used when the binder cannot be peeled even after
  /// WHNF — distinct messages are useful for callers (e.g. "expected forall
  /// in ctor type" vs. "not enough fields") so the helper takes it as a
  /// parameter rather than baking one in.
  fn peel_proj_forall(
    &mut self,
    e: &KExpr<M>,
    err: &'static str,
  ) -> Result<(KExpr<M>, KExpr<M>), TcError<M>> {
    if let ExprData::All(_, _, dom, body, _) = e.data() {
      return Ok((dom.clone(), body.clone()));
    }
    let w = self.whnf(e)?;
    match w.data() {
      ExprData::All(_, _, dom, body, _) => Ok((dom.clone(), body.clone())),
      _ => Err(TcError::Other(err.into())),
    }
  }

  fn infer_nat_type(&mut self) -> Result<KExpr<M>, TcError<M>> {
    Ok(self.intern(KExpr::cnst(self.prims.nat.clone(), Box::new([]))))
  }

  fn infer_str_type(&mut self) -> Result<KExpr<M>, TcError<M>> {
    Ok(self.intern(KExpr::cnst(self.prims.string.clone(), Box::new([]))))
  }

  fn inductive_app_is_prop(
    &mut self,
    ind_id: &KId<M>,
    levels: &[KUniv<M>],
    binders: usize,
  ) -> Result<bool, TcError<M>> {
    use super::level::{KUniv, univ_eq};

    let ind_ty = match self.try_get_const(ind_id)? {
      Some(KConst::Indc { ty, .. }) => ty,
      _ => {
        return Err(TcError::Other("projection: not an inductive type".into()));
      },
    };
    let levels_vec: Vec<_> = levels.to_vec();
    let mut r = self.instantiate_univ_params(&ind_ty, &levels_vec)?;
    for _ in 0..binders {
      let wr = self.whnf(&r)?;
      match wr.data() {
        ExprData::All(_, _, _, body, _) => {
          r = body.clone();
        },
        _ => {
          return Err(TcError::Other(
            "projection: expected forall in inductive type".into(),
          ));
        },
      }
    }
    let sort_ty = self.whnf(&r)?;
    let level = self.ensure_sort(&sort_ty)?;
    Ok(univ_eq(&level, &KUniv::zero()))
  }
}

fn compact_expr<M: KernelMode>(e: &KExpr<M>) -> String {
  compact_expr_deep(e, 1)
}

fn compact_expr_deep<M: KernelMode>(e: &KExpr<M>, depth: usize) -> String {
  if depth > 0 {
    match e.data() {
      ExprData::Lam(_, _, ty, body, _) => {
        return format!(
          "lam(ty={}, body={}) @{} lbr={}",
          compact_expr_deep(ty, depth - 1),
          compact_expr_deep(body, depth - 1),
          short_addr(e),
          e.lbr()
        );
      },
      ExprData::All(_, _, ty, body, _) => {
        return format!(
          "forall(ty={}, body={}) @{} lbr={}",
          compact_expr_deep(ty, depth - 1),
          compact_expr_deep(body, depth - 1),
          short_addr(e),
          e.lbr()
        );
      },
      ExprData::Let(_, ty, val, body, _, _) => {
        return format!(
          "let(ty={}, val={}, body={}) @{} lbr={}",
          compact_expr_deep(ty, depth - 1),
          compact_expr_deep(val, depth - 1),
          compact_expr_deep(body, depth - 1),
          short_addr(e),
          e.lbr()
        );
      },
      _ => {},
    }
  }
  let (head, args) = collect_app_spine(e);
  let mut out = compact_head(&head);
  if !args.is_empty() {
    let shown = args
      .iter()
      .take(8)
      .map(|arg| {
        if depth == 0 {
          compact_head(arg)
        } else {
          compact_expr_deep(arg, depth - 1)
        }
      })
      .collect::<Vec<_>>()
      .join(", ");
    let more = if args.len() > 8 { ", ..." } else { "" };
    out = format!("{out}/{} [{shown}{more}]", args.len());
  }
  format!("{out} @{} lbr={}", short_addr(e), e.lbr())
}

fn compact_head<M: KernelMode>(e: &KExpr<M>) -> String {
  let (head, args) = collect_app_spine(e);
  let base = match head.data() {
    ExprData::Var(i, _, _) => format!("#{i}"),
    ExprData::Sort(u, _) => format!("Sort({u})"),
    ExprData::Const(id, us, _) => format!("{id}.{{{}}}", us.len()),
    ExprData::App(..) => "app".to_string(),
    ExprData::Lam(..) => "lam".to_string(),
    ExprData::All(..) => "forall".to_string(),
    ExprData::Let(..) => "let".to_string(),
    ExprData::Prj(id, field, val, _) => {
      format!("Prj({id}.{field}, {})", compact_head(val))
    },
    ExprData::Nat(v, _, _) => format!("Nat({})", v.0),
    ExprData::Str(v, _, _) => format!("Str(len={})", v.len()),
  };
  if args.is_empty() { base } else { format!("{base}/{}", args.len()) }
}

fn short_addr<M: KernelMode>(e: &KExpr<M>) -> String {
  e.addr().to_hex().chars().take(12).collect()
}

#[cfg(test)]
mod tests {

  use super::super::constant::KConst;
  use super::super::env::KEnv;
  use super::super::error::TcError;
  use super::super::expr::{ExprData, KExpr};
  use super::super::id::KId;
  use super::super::level::KUniv;
  use super::super::mode::Anon;
  use super::super::tc::TypeChecker;
  use crate::ix::address::Address;
  use crate::ix::env::{DefinitionSafety, ReducibilityHints};
  use crate::ix::ixon::constant::DefKind;
  use lean_ffi::nat::Nat;

  type AE = KExpr<Anon>;
  type AU = KUniv<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }
  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }
  fn sort0() -> AE {
    AE::sort(AU::zero())
  }
  fn sort1() -> AE {
    AE::sort(AU::succ(AU::zero()))
  }

  /// Env with: Nat (axiom), id (definition)
  fn test_env() -> KEnv<Anon> {
    let mut env = KEnv::new();
    // Nat : Sort 1
    env.insert(
      mk_id("Nat"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: sort1(),
      },
    );
    // id : Sort 0 → Sort 0 := λ x. x
    let id_ty = AE::all((), (), sort0(), sort0());
    let id_val = AE::lam((), (), sort0(), AE::var(0, ()));
    env.insert(
      mk_id("id"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev,
        lvls: 0,
        ty: id_ty,
        val: id_val,
        lean_all: (),
        block: mk_id("id"),
      },
    );
    env
  }

  #[test]
  fn infer_sort() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    // Sort 0 : Sort 1
    let ty = tc.infer(&sort0()).unwrap();
    assert!(matches!(ty.data(), ExprData::Sort(u, _) if !u.is_zero()));
  }

  #[test]
  fn infer_var() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    tc.push_local(sort0());
    let ty = tc.infer(&AE::var(0, ())).unwrap();
    // Var(0) has type Sort 0 (the type we pushed)
    assert_eq!(ty, sort0());
    tc.pop_local();
  }

  #[test]
  fn infer_const() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let nat = AE::cnst(mk_id("Nat"), Box::new([]));
    let ty = tc.infer(&nat).unwrap();
    // Nat : Sort 1
    assert_eq!(ty, sort1());
  }

  #[test]
  fn infer_lam() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    // λ (x : Sort 0). x : ∀ (x : Sort 0). Sort 0
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    let ty = tc.infer(&lam).unwrap();
    assert!(matches!(ty.data(), ExprData::All(..)));
  }

  #[test]
  fn infer_app() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    // Under a binder with x : Sort 0, id(x) : Sort 0
    tc.push_local(sort0());
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let app = AE::app(id_const, AE::var(0, ()));
    let ty = tc.infer(&app).unwrap();
    assert_eq!(ty, sort0());
    tc.pop_local();
  }

  #[test]
  fn infer_all() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    // ∀ (x : Sort 0). Sort 0 : Sort 1
    let all = AE::all((), (), sort0(), sort0());
    let ty = tc.infer(&all).unwrap();
    assert!(matches!(ty.data(), ExprData::Sort(..)));
  }

  #[test]
  fn infer_nat_lit() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let n = AE::nat(Nat::from(42u64), mk_addr("42"));
    let ty = tc.infer(&n).unwrap();
    // Nat literal type = Nat constant
    assert!(
      matches!(ty.data(), ExprData::Const(id, _, _) if id.addr == tc.prims.nat.addr)
    );
  }

  #[test]
  fn infer_cache() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = sort0();
    let t1 = tc.infer(&e).unwrap();
    let t2 = tc.infer(&e).unwrap();
    assert_eq!(t1, t2);
  }

  #[test]
  fn infer_closed_cache_ignores_context() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = sort0();
    let t1 = tc.infer(&e).unwrap();
    let cache_len = tc.env.infer_cache.len();

    tc.push_local(sort1());
    let t2 = tc.infer(&e).unwrap();
    assert_eq!(t1, t2);
    assert_eq!(tc.env.infer_cache.len(), cache_len);
  }

  #[test]
  fn infer_open_cache_is_context_sensitive() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = AE::var(0, ());

    tc.push_local(sort0());
    let t1 = tc.infer(&e).unwrap();
    let cache_len = tc.env.infer_cache.len();
    tc.pop_local();

    tc.push_local(sort1());
    let t2 = tc.infer(&e).unwrap();
    assert_ne!(t1, t2);
    assert!(tc.env.infer_cache.len() > cache_len);
  }

  // =========================================================================
  // Error paths
  // =========================================================================

  #[test]
  fn infer_unknown_const_errors() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let bogus = AE::cnst(mk_id("DoesNotExist"), Box::new([]));
    match tc.infer(&bogus) {
      Err(TcError::UnknownConst(addr)) => {
        assert_eq!(addr, mk_addr("DoesNotExist"));
      },
      other => panic!("expected UnknownConst, got {other:?}"),
    }
  }

  #[test]
  fn infer_univ_param_count_mismatch() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    // `id` has 0 level params; supplying one should error.
    let wrong = AE::cnst(mk_id("id"), Box::new([AU::zero()]));
    match tc.infer(&wrong) {
      Err(TcError::UnivParamMismatch { expected, got }) => {
        assert_eq!(expected, 0);
        assert_eq!(got, 1);
      },
      other => panic!("expected UnivParamMismatch, got {other:?}"),
    }
  }

  #[test]
  fn infer_var_out_of_range() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    // Empty context, Var(0) → out of range.
    match tc.infer(&AE::var(0, ())) {
      Err(TcError::VarOutOfRange { idx, ctx_len }) => {
        assert_eq!(idx, 0);
        assert_eq!(ctx_len, 0);
      },
      other => panic!("expected VarOutOfRange, got {other:?}"),
    }
  }

  #[test]
  fn infer_app_mismatch_errors() {
    // Applying `id : Sort 0 → Sort 0` to a Nat (which has type Nat, not
    // Sort 0) should error with AppTypeMismatch.
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let nat_lit = AE::nat(Nat::from(0u64), mk_addr("0"));
    let app = AE::app(id_const, nat_lit);
    match tc.infer(&app) {
      Err(TcError::AppTypeMismatch { .. }) => {},
      other => panic!("expected AppTypeMismatch, got {other:?}"),
    }
  }

  #[test]
  fn infer_app_of_non_function_errors() {
    // Nat is not a function — applying it should fail with FunExpected.
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let nat_const = AE::cnst(mk_id("Nat"), Box::new([]));
    let app = AE::app(nat_const, sort0());
    match tc.infer(&app) {
      Err(TcError::FunExpected { .. }) => {},
      other => panic!("expected FunExpected, got {other:?}"),
    }
  }

  // =========================================================================
  // Structural path coverage
  // =========================================================================

  #[test]
  fn infer_all_returns_imax_of_domain_and_codomain_sorts() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    // ∀ (x : Sort 0). Sort 1 → Sort imax(1, 2) = Sort 2
    let all = AE::all((), (), sort0(), sort1());
    let ty = tc.infer(&all).unwrap();
    match ty.data() {
      ExprData::Sort(u, _) => {
        // imax(succ(0), succ(succ(0))) = succ(succ(0)), which is never-zero
        // so imax degenerates to max. Both operands are explicit numerals,
        // result is succ(succ(0)) = 2.
        assert!(!u.is_zero());
      },
      other => panic!("expected Sort, got {other:?}"),
    }
  }

  #[test]
  fn infer_let_substitutes_value_into_body_type() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    // let x : Sort 0 := Sort 0 in x
    let expr = AE::let_(
      (),
      sort1(), // x : Sort 1
      sort0(), // x := Sort 0
      AE::var(0, ()),
      false,
    );
    // Inferred type: body's type with value substituted. Body is Var(0)
    // with type Sort 1, so the type is Sort 1.
    let ty = tc.infer(&expr).unwrap();
    assert_eq!(ty, sort1());
  }

  #[test]
  fn infer_let_value_type_mismatch_errors() {
    // let x : Sort 0 := 42 in x → DeclTypeMismatch (42 is a Nat, not a Sort).
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let nat_val = AE::nat(Nat::from(42u64), mk_addr("42"));
    let expr = AE::let_((), sort0(), nat_val, AE::var(0, ()), false);
    match tc.infer(&expr) {
      Err(TcError::DeclTypeMismatch) => {},
      other => panic!("expected DeclTypeMismatch, got {other:?}"),
    }
  }

  #[test]
  fn infer_str_returns_string_type() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let s = AE::str("hello".into(), mk_addr("hello"));
    let ty = tc.infer(&s).unwrap();
    // Type should be `String` — a constant at the canonical string addr.
    match ty.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.string.addr);
      },
      other => panic!("expected Const(String), got {other:?}"),
    }
  }

  #[test]
  fn infer_with_infer_only_skips_app_type_check() {
    // In infer-only mode, `infer` must skip the arg-type def-eq check,
    // so `id(42)` infers cleanly even though 42's type doesn't match
    // `id`'s domain (Sort 0). This is the key property infer-only has.
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let nat_lit = AE::nat(Nat::from(0u64), mk_addr("0"));
    let app = AE::app(id_const, nat_lit);
    let r = tc.with_infer_only(|tc| tc.infer(&app));
    // In full mode this would error; in infer-only it succeeds.
    assert!(r.is_ok());
  }

  #[test]
  fn infer_only_cache_does_not_validate_full_mode() {
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let nat_lit = AE::nat(Nat::from(0u64), mk_addr("0"));
    let app = AE::app(id_const, nat_lit);

    let key = tc.infer_key(&app);
    assert!(tc.with_infer_only(|tc| tc.infer(&app)).is_ok());
    assert!(!tc.env.infer_only_cache.is_empty());
    assert!(tc.env.infer_cache.get(&key).is_none());

    match tc.infer(&app) {
      Err(TcError::AppTypeMismatch { .. }) => {},
      other => panic!("expected full-mode AppTypeMismatch, got {other:?}"),
    }
  }

  #[test]
  fn infer_is_deterministic_across_contexts() {
    // Inferring the same closed expression twice should always yield
    // the same interned result.
    let mut env = test_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = AE::all((), (), sort0(), sort0());
    let t1 = tc.infer(&e).unwrap();
    let t2 = tc.infer(&e).unwrap();
    assert!(t1.hash_eq(&t2));
  }
}
