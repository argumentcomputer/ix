//! Type inference.

use super::constant::KConst;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::subst::subst;
use super::tc::TypeChecker;

impl<M: KernelMode> TypeChecker<M> {
  pub fn infer(&mut self, e: &KExpr<M>) -> Result<KExpr<M>, TcError<M>> {
    let infer_only = self.infer_only;

    // Cache: infer-only results use a separate cache since they skip validation.
    // A full-check result can serve an infer-only lookup, so check both.
    let cache_key = (e.hash_key(), self.ctx_id.clone());
    if let Some(cached) = self.env.infer_cache.get(&cache_key) {
      return Ok(cached.clone());
    }
    if infer_only
      && let Some(cached) = self.env.infer_only_cache.get(&cache_key)
    {
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
        self.instantiate_univ_params(&ty, &us_vec)
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

    if infer_only {
      self.env.infer_only_cache.insert(cache_key, ty.clone());
    } else {
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
    let mut r = self.instantiate_univ_params(&ctor_ty, &i_levels_vec);

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
}
