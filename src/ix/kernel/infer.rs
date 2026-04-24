//! Type inference.

use std::sync::LazyLock;

use super::constant::KConst;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::subst::subst;
use super::tc::TypeChecker;

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

impl<M: KernelMode> TypeChecker<M> {
  pub fn infer(&mut self, e: &KExpr<M>) -> Result<KExpr<M>, TcError<M>> {
    if *IX_INFER_COUNT_LOG {
      let n = INFER_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
      if n % 100_000 == 0 && n > 0 {
        eprintln!("[infer] count={n}");
      }
    }
    let infer_only = self.infer_only;

    // Single `infer_cache` serves both modes. The cache only holds full-mode
    // results (see write path below), which are strictly stronger than what
    // `infer_only` would have produced — same inferred type, more validation
    // performed. So it's always safe to read from here regardless of mode.
    let cache_key = (e.hash_key(), self.ctx_id.clone());
    if let Some(cached) = self.env.infer_cache.get(&cache_key) {
      return Ok(cached.clone());
    }

    let ty = match e.data() {
      ExprData::Var(i, _, _) => self.lookup_var(*i)?,

      ExprData::Sort(u, _) => {
        let u2 = KUniv::succ(u.clone());
        self.intern(KExpr::sort(u2))
      },

      ExprData::Const(id, us, _) => {
        let c = self
          .env
          .get(id)
          .ok_or_else(|| TcError::UnknownConst(id.addr.clone()))?;
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
        let (dom, cod) = self.ensure_forall(&f_ty).map_err(|err| {
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
          err
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
            if *IX_APP_DIFF {
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
              eprintln!("  f:          {f}");
              eprintln!("  a:          {a}");
              eprintln!("  a_ty:       {a_ty}");
              eprintln!("  dom:        {dom}");
              match &a_whnf {
                Ok(w) => eprintln!("  a_ty whnf:  {w}"),
                Err(e) => eprintln!("  a_ty whnf:  ERR {e}"),
              }
              match &d_whnf {
                Ok(w) => eprintln!("  dom  whnf:  {w}"),
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
        subst(&self.env.intern, &cod, a, 0)
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
        subst(&self.env.intern, &body_ty, val, 0)
      },

      ExprData::Prj(struct_id, field, val, _) => {
        let struct_id = struct_id.clone();
        let val_ty = self.infer(val)?;
        self.infer_proj(&struct_id, *field, val, &val_ty)?
      },

      ExprData::Nat(..) => self.infer_nat_type()?,
      ExprData::Str(..) => self.infer_str_type()?,
    };

    // Only store full-mode results; infer-only skips validation so caching
    // those entries would weaken the cache's "already validated" invariant.
    if !infer_only {
      self.env.infer_cache.insert(cache_key, ty.clone());
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
    use super::level::{KUniv, univ_eq};
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

    let (i_levels, num_params, ctors) = match self.env.get(head_id) {
      Some(KConst::Indc { params, ctors, .. }) => {
        let levels = match head.data() {
          ExprData::Const(_, us, _) => us.clone(),
          _ => unreachable!(),
        };
        (levels, u64_to_usize::<M>(params)?, ctors.clone())
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

    // Check if the structure type is in Prop (Sort 0).
    // If so, projection restrictions apply.
    let struct_sort_ty = self.infer(val_ty)?;
    let struct_level = self.ensure_sort(&struct_sort_ty)?;
    let is_prop_struct = univ_eq(&struct_level, &KUniv::zero());

    let ctor_ty = match self.env.get(&ctors[0]) {
      Some(c) => c.ty().clone(),
      None => {
        return Err(TcError::Other("projection: constructor not found".into()));
      },
    };

    let i_levels_vec: Vec<_> = i_levels.to_vec();
    let mut r = self.instantiate_univ_params(&ctor_ty, &i_levels_vec)?;

    for i in 0..num_params {
      let wr = self.whnf(&r)?;
      match wr.data() {
        ExprData::All(_, _, _, body, _) => {
          if i < args.len() {
            r = subst(&self.env.intern, body, &args[i], 0);
          } else {
            return Err(TcError::Other("projection: not enough params".into()));
          }
        },
        _ => {
          return Err(TcError::Other(
            "projection: expected forall in ctor type".into(),
          ));
        },
      }
    }

    for i in 0..=field {
      let wr = self.whnf(&r)?;
      match wr.data() {
        ExprData::All(_, _, dom, body, _) => {
          if i == field {
            // For Prop structures, the projected field must be in Prop.
            if is_prop_struct {
              let field_sort_ty = self.infer(dom)?;
              let field_level = self.ensure_sort(&field_sort_ty)?;
              if !univ_eq(&field_level, &KUniv::zero()) {
                return Err(TcError::Other(
                  "projection: cannot project data field from Prop structure"
                    .into(),
                ));
              }
            }
            return Ok(dom.clone());
          }
          // For Prop structures, check if this preceding field is a data field
          // that subsequent fields depend on. If so, projection is forbidden.
          if is_prop_struct {
            let field_sort_ty = self.infer(dom)?;
            let field_level = self.ensure_sort(&field_sort_ty)?;
            let is_data = !univ_eq(&field_level, &KUniv::zero());
            // body.lbr() > 0 means the body references Var(0), i.e., depends on this field
            if is_data && body.lbr() > 0 {
              return Err(TcError::Other(
                "projection: forbidden after dependent data field in Prop structure".into(),
              ));
            }
          }
          let proj = self.intern(KExpr::prj(struct_id.clone(), i, val.clone()));
          r = subst(&self.env.intern, body, &proj, 0);
        },
        _ => {
          return Err(TcError::Other("projection: not enough fields".into()));
        },
      }
    }

    Err(TcError::Other("projection: unreachable".into()))
  }

  fn infer_nat_type(&mut self) -> Result<KExpr<M>, TcError<M>> {
    Ok(self.intern(KExpr::cnst(self.prims.nat.clone(), Box::new([]))))
  }

  fn infer_str_type(&mut self) -> Result<KExpr<M>, TcError<M>> {
    Ok(self.intern(KExpr::cnst(self.prims.string.clone(), Box::new([]))))
  }
}

#[cfg(test)]
mod tests {
  use std::sync::Arc;

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
  fn test_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // Sort 0 : Sort 1
    let ty = tc.infer(&sort0()).unwrap();
    assert!(matches!(ty.data(), ExprData::Sort(u, _) if !u.is_zero()));
  }

  #[test]
  fn infer_var() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.push_local(sort0());
    let ty = tc.infer(&AE::var(0, ())).unwrap();
    // Var(0) has type Sort 0 (the type we pushed)
    assert_eq!(ty, sort0());
    tc.pop_local();
  }

  #[test]
  fn infer_const() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let nat = AE::cnst(mk_id("Nat"), Box::new([]));
    let ty = tc.infer(&nat).unwrap();
    // Nat : Sort 1
    assert_eq!(ty, sort1());
  }

  #[test]
  fn infer_lam() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // λ (x : Sort 0). x : ∀ (x : Sort 0). Sort 0
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    let ty = tc.infer(&lam).unwrap();
    assert!(matches!(ty.data(), ExprData::All(..)));
  }

  #[test]
  fn infer_app() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // ∀ (x : Sort 0). Sort 0 : Sort 1
    let all = AE::all((), (), sort0(), sort0());
    let ty = tc.infer(&all).unwrap();
    assert!(matches!(ty.data(), ExprData::Sort(..)));
  }

  #[test]
  fn infer_nat_lit() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let n = AE::nat(Nat::from(42u64), mk_addr("42"));
    let ty = tc.infer(&n).unwrap();
    // Nat literal type = Nat constant
    assert!(
      matches!(ty.data(), ExprData::Const(id, _, _) if id.addr == tc.prims.nat.addr)
    );
  }

  #[test]
  fn infer_cache() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let e = sort0();
    let t1 = tc.infer(&e).unwrap();
    let t2 = tc.infer(&e).unwrap();
    assert_eq!(t1, t2);
  }

  // =========================================================================
  // Error paths
  // =========================================================================

  #[test]
  fn infer_unknown_const_errors() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let nat_val = AE::nat(Nat::from(42u64), mk_addr("42"));
    let expr = AE::let_((), sort0(), nat_val, AE::var(0, ()), false);
    match tc.infer(&expr) {
      Err(TcError::DeclTypeMismatch) => {},
      other => panic!("expected DeclTypeMismatch, got {other:?}"),
    }
  }

  #[test]
  fn infer_str_returns_string_type() {
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let nat_lit = AE::nat(Nat::from(0u64), mk_addr("0"));
    let app = AE::app(id_const, nat_lit);
    let r = tc.with_infer_only(|tc| tc.infer(&app));
    // In full mode this would error; in infer-only it succeeds.
    assert!(r.is_ok());
  }

  #[test]
  fn infer_is_deterministic_across_contexts() {
    // Inferring the same closed expression twice should always yield
    // the same interned result.
    let env = test_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let e = AE::all((), (), sort0(), sort0());
    let t1 = tc.infer(&e).unwrap();
    let t2 = tc.infer(&e).unwrap();
    assert!(t1.hash_eq(&t2));
  }
}
