//! Type inference and checking.
//!
//! Implements `infer` (type inference), `check` (type checking against an
//! expected type), and related utilities.

use crate::ix::env::{Literal, Name};

use super::error::TcError;
use super::level::{self, reduce, reduce_imax};
use super::tc::{TcResult, TypeChecker};
use super::types::{MetaMode, *};
use super::value::*;
use super::whnf::inst_levels_expr;

impl<M: MetaMode> TypeChecker<'_, M> {
  /// Infer the type of a kernel expression.
  /// Returns a (TypedExpr, type_as_val) pair.
  pub fn infer(
    &mut self,
    term: &KExpr<M>,
  ) -> TcResult<(TypedExpr<M>, Val<M>), M> {
    self.stats.infer_calls += 1;

    self.heartbeat()?;
    self.infer_core(term)
  }

  fn infer_core(
    &mut self,
    term: &KExpr<M>,
  ) -> TcResult<(TypedExpr<M>, Val<M>), M> {
    match term.data() {
      KExprData::BVar(idx, _) => {
        let level = self
          .depth()
          .checked_sub(1 + idx)
          .ok_or(TcError::FreeBoundVariable { idx: *idx })?;
        let ty = self
          .types
          .get(level)
          .ok_or(TcError::FreeBoundVariable { idx: *idx })?
          .clone();
        let info = self.info_from_type(&ty)?;
        Ok((TypedExpr { info, body: term.clone() }, ty))
      }

      KExprData::Sort(l) => {
        let succ_l = KLevel::<M>::succ(l.clone());
        let ty = Val::mk_sort(succ_l.clone());
        let info = TypeInfo::Sort(l.clone());
        Ok((TypedExpr { info, body: term.clone() }, ty))
      }

      KExprData::Lit(Literal::NatVal(_)) => {
        let nat_addr = self
          .prims
          .nat
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "Nat type not found".to_string(),
          })?;
        let ty = Val::mk_const(
          nat_addr.clone(),
          Vec::new(),
          M::Field::<Name>::default(),
        );
        Ok((
          TypedExpr {
            info: TypeInfo::None,
            body: term.clone(),
          },
          ty,
        ))
      }

      KExprData::Lit(Literal::StrVal(_)) => {
        let str_addr = self
          .prims
          .string
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "String type not found".to_string(),
          })?;
        let ty = Val::mk_const(
          str_addr.clone(),
          Vec::new(),
          M::Field::<Name>::default(),
        );
        Ok((
          TypedExpr {
            info: TypeInfo::None,
            body: term.clone(),
          },
          ty,
        ))
      }

      KExprData::Const(addr, levels, name) => {
        // Ensure the constant has been type-checked
        self.ensure_typed_const(addr)?;

        // Validate universe level count
        let ci = self.deref_const(addr)?;
        let expected = ci.cv().num_levels;
        if levels.len() != expected {
          return Err(TcError::KernelException {
            msg: format!(
              "universe level count mismatch for {}: expected {}, got {}",
              format!("{:?}", name),
              expected,
              levels.len()
            ),
          });
        }

        let tc = self
          .typed_consts
          .get(addr)
          .ok_or_else(|| TcError::UnknownConst {
            msg: format!("{:?}", name),
          })?
          .clone();
        let type_expr = tc.typ().body.clone();

        // Instantiate universe levels
        let type_inst = self.instantiate_levels(&type_expr, levels);
        let type_val = self.eval_in_ctx(&type_inst)?;

        let info = self.info_from_type(&type_val)?;
        Ok((TypedExpr { info, body: term.clone() }, type_val))
      }

      KExprData::App(_, _) => {
        let (head, args) = term.get_app_args();
        let (_, mut fn_type) = self.infer(head)?;

        for arg in &args {
          let fn_type_whnf = self.whnf_val(&fn_type, 0)?;
          match fn_type_whnf.inner() {
            ValInner::Pi {
              dom,
              body,
              env,
              ..
            } => {
              // Check argument type if not in infer-only mode
              if !self.infer_only {
                let (_, arg_type) = self.infer(arg)?;
                if !self.is_def_eq(&arg_type, dom)? {
                  let dom_expr =
                    self.quote(dom, self.depth())?;
                  let arg_type_expr =
                    self.quote(&arg_type, self.depth())?;
                  return Err(TcError::TypeMismatch {
                    expected: dom_expr,
                    found: arg_type_expr,
                    expr: (*arg).clone(),
                  });
                }
              }

              // Evaluate the argument and push into codomain
              let arg_val =
                self.eval(arg, &self.build_ctx_env())?;
              let mut new_env = env.clone();
              new_env.push(arg_val);
              fn_type = self.eval(body, &new_env)?;
            }
            _ => {
              let fn_type_expr =
                self.quote(&fn_type_whnf, self.depth())?;
              return Err(TcError::FunctionExpected {
                expr: (*arg).clone(),
                inferred: fn_type_expr,
              });
            }
          }
        }

        let info = self.info_from_type(&fn_type)?;
        Ok((TypedExpr { info, body: term.clone() }, fn_type))
      }

      KExprData::Lam(ty, body, name, bi) => {
        // Ensure domain type is a sort (unless infer-only)
        if !self.infer_only {
          let _ = self.is_sort(ty)?;
        }
        let dom_val = self.eval_in_ctx(ty)?;

        // Enter binder
        let (_body_te, body_type) =
          self.with_binder(dom_val.clone(), name.clone(), |tc| {
            tc.infer(body)
          })?;

        // Quote the body type back to build the Pi type
        let body_type_expr =
          self.quote(&body_type, self.depth() + 1)?;
        let pi_type = Val::mk_pi(
          name.clone(),
          bi.clone(),
          dom_val,
          body_type_expr,
          self.build_ctx_env(),
        );

        let info = self.info_from_type(&pi_type)?;
        Ok((TypedExpr { info, body: term.clone() }, pi_type))
      }

      KExprData::ForallE(ty, body, name, _bi) => {
        // Check domain is a sort
        let (_, dom_level) = self.is_sort(ty)?;
        let dom_val = self.eval_in_ctx(ty)?;

        // Enter binder
        let (_, body_level) =
          self.with_binder(dom_val, name.clone(), |tc| {
            tc.is_sort(body)
          })?;

        // Result level = imax(dom_level, body_level)
        let result_level =
          reduce(&reduce_imax(&dom_level, &body_level));
        let ty = Val::mk_sort(result_level);
        let info = self.info_from_type(&ty)?;
        Ok((TypedExpr { info, body: term.clone() }, ty))
      }

      KExprData::LetE(ty, val_expr, body, name) => {
        // Check the type annotation is a sort
        let _ = self.is_sort(ty)?;
        let ty_val = self.eval_in_ctx(ty)?;

        // Infer/check the value
        if !self.infer_only {
          let (_, val_type) = self.infer(val_expr)?;
          if !self.is_def_eq(&val_type, &ty_val)? {
            let ty_expr =
              self.quote(&ty_val, self.depth())?;
            let val_type_expr =
              self.quote(&val_type, self.depth())?;
            return Err(TcError::TypeMismatch {
              expected: ty_expr,
              found: val_type_expr,
              expr: val_expr.clone(),
            });
          }
        }

        // Evaluate the value and enter binder
        let val_val = self.eval_in_ctx(val_expr)?;
        let (body_te, body_type) = self.with_let_binder(
          ty_val,
          val_val,
          name.clone(),
          |tc| tc.infer(body),
        )?;

        Ok((
          TypedExpr {
            info: body_te.info,
            body: term.clone(),
          },
          body_type,
        ))
      }

      KExprData::Proj(type_addr, idx, strct, _type_name) => {
        // Infer the struct type
        let (struct_te, struct_type) = self.infer(strct)?;

        // Get struct info: ctor type expr, universe levels, num_params, param vals
        let (ctor_type_expr, ctor_univs, _num_params, params) =
          self.get_struct_info_val(&struct_type)?;

        // Evaluate constructor type with instantiated universes
        let inst_ctor = inst_levels_expr(&ctor_type_expr, &ctor_univs);
        let mut ct = self.eval_in_ctx(&inst_ctor)?;

        // Walk past params: apply each param to the codomain closure
        for param_val in &params {
          let ct_whnf = self.whnf_val(&ct, 0)?;
          match ct_whnf.inner() {
            ValInner::Pi { body, env, .. } => {
              let mut new_env = env.clone();
              new_env.push(param_val.clone());
              ct = self.eval(body, &new_env)?;
            }
            _ => {
              return Err(TcError::KernelException {
                msg: "Structure constructor has too few parameters".to_string(),
              });
            }
          }
        }

        // Walk past fields before idx
        let struct_val = self.eval_in_ctx(strct)?;
        let struct_thunk = mk_thunk_val(struct_val);
        for i in 0..*idx {
          let ct_whnf = self.whnf_val(&ct, 0)?;
          match ct_whnf.inner() {
            ValInner::Pi { body, env, .. } => {
              let proj_val = Val::mk_proj(
                type_addr.clone(),
                i,
                struct_thunk.clone(),
                M::Field::<Name>::default(),
                Vec::new(),
              );
              let mut new_env = env.clone();
              new_env.push(proj_val);
              ct = self.eval(body, &new_env)?;
            }
            _ => {
              return Err(TcError::KernelException {
                msg: "Structure type does not have enough fields".to_string(),
              });
            }
          }
        }

        // Get the type at field idx
        let ct_whnf = self.whnf_val(&ct, 0)?;
        match ct_whnf.inner() {
          ValInner::Pi { dom, .. } => {
            let info = self.info_from_type(dom)?;
            let te = TypedExpr {
              info,
              body: KExpr::proj(
                type_addr.clone(),
                *idx,
                struct_te.body,
                M::Field::<Name>::default(),
              ),
            };
            Ok((te, dom.clone()))
          }
          _ => Err(TcError::KernelException {
            msg: "Structure type does not have enough fields".to_string(),
          }),
        }
      }
    }
  }

  /// Check that `term` has type `expected_type`.
  pub fn check(
    &mut self,
    term: &KExpr<M>,
    expected_type: &Val<M>,
  ) -> TcResult<TypedExpr<M>, M> {
    let (te, inferred_type) = self.infer(term)?;
    if !self.is_def_eq(&inferred_type, expected_type)? {
      let expected_expr =
        self.quote(expected_type, self.depth())?;
      let inferred_expr =
        self.quote(&inferred_type, self.depth())?;
      return Err(TcError::TypeMismatch {
        expected: expected_expr,
        found: inferred_expr,
        expr: term.clone(),
      });
    }
    Ok(te)
  }

  /// Infer the type of `expr` and ensure it is a sort.
  /// Returns (TypedExpr, level).
  pub fn is_sort(
    &mut self,
    expr: &KExpr<M>,
  ) -> TcResult<(TypedExpr<M>, KLevel<M>), M> {
    let (te, ty) = self.infer(expr)?;
    let ty_whnf = self.whnf_val(&ty, 0)?;
    match ty_whnf.inner() {
      ValInner::Sort(l) => Ok((te, l.clone())),
      _ => {
        let ty_expr = self.quote(&ty_whnf, self.depth())?;
        Err(TcError::TypeExpected {
          expr: expr.clone(),
          inferred: ty_expr,
        })
      }
    }
  }

  /// Infer the type of a Val directly (without quoting to KExpr first).
  pub fn infer_type_of_val(&mut self, v: &Val<M>) -> TcResult<Val<M>, M> {
    match v.inner() {
      ValInner::Sort(l) => Ok(Val::mk_sort(KLevel::<M>::succ(l.clone()))),
      ValInner::Lit(Literal::NatVal(_)) => {
        let addr = self
          .prims
          .nat
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "Nat not found".to_string(),
          })?;
        Ok(Val::mk_const(addr.clone(), Vec::new(), M::Field::<Name>::default()))
      }
      ValInner::Lit(Literal::StrVal(_)) => {
        let addr = self
          .prims
          .string
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "String not found".to_string(),
          })?;
        Ok(Val::mk_const(addr.clone(), Vec::new(), M::Field::<Name>::default()))
      }
      ValInner::Neutral {
        head: Head::FVar { ty, .. },
        spine,
      } => {
        let mut result_type = ty.clone();
        for thunk in spine {
          let result_type_whnf = self.whnf_val(&result_type, 0)?;
          match result_type_whnf.inner() {
            ValInner::Pi { body, env, .. } => {
              let arg_val = self.force_thunk(thunk)?;
              let mut new_env = env.clone();
              new_env.push(arg_val);
              result_type = self.eval(body, &new_env)?;
            }
            _ => {
              return Err(TcError::KernelException {
                msg: "infer_type_of_val: expected Pi".to_string(),
              });
            }
          }
        }
        Ok(result_type)
      }
      ValInner::Neutral {
        head: Head::Const { addr, levels, name },
        spine,
      } => {
        self.ensure_typed_const(addr)?;
        let tc = self
          .typed_consts
          .get(addr)
          .ok_or_else(|| TcError::UnknownConst {
            msg: format!("{:?}", name),
          })?
          .clone();
        let type_expr = tc.typ().body.clone();
        let type_inst = self.instantiate_levels(&type_expr, levels);
        let mut result_type = self.eval_in_ctx(&type_inst)?;
        for thunk in spine {
          let result_type_whnf =
            self.whnf_val(&result_type, 0)?;
          match result_type_whnf.inner() {
            ValInner::Pi { body, env, .. } => {
              let arg_val = self.force_thunk(thunk)?;
              let mut new_env = env.clone();
              new_env.push(arg_val);
              result_type = self.eval(body, &new_env)?;
            }
            _ => {
              return Err(TcError::KernelException {
                msg: "infer_type_of_val: expected Pi".to_string(),
              });
            }
          }
        }
        Ok(result_type)
      }
      ValInner::Pi { .. } => {
        // A Pi type has type Sort(imax(dom_level, body_level))
        // For simplicity, quote and infer
        let expr = self.quote(v, self.depth())?;
        let (_, ty) = self.infer(&expr)?;
        Ok(ty)
      }
      ValInner::Lam { .. } => {
        // Quote and infer
        let expr = self.quote(v, self.depth())?;
        let (_, ty) = self.infer(&expr)?;
        Ok(ty)
      }
      ValInner::Ctor {
        addr,
        levels,
        spine,
        ..
      } => {
        self.ensure_typed_const(addr)?;
        let tc = self
          .typed_consts
          .get(addr)
          .cloned()
          .ok_or_else(|| TcError::UnknownConst {
            msg: format!("ctor {}", addr.hex()),
          })?;
        let type_expr = tc.typ().body.clone();
        let type_inst = self.instantiate_levels(&type_expr, levels);
        let mut result_type = self.eval_in_ctx(&type_inst)?;
        for thunk in spine {
          let result_type_whnf =
            self.whnf_val(&result_type, 0)?;
          match result_type_whnf.inner() {
            ValInner::Pi { body, env, .. } => {
              let arg_val = self.force_thunk(thunk)?;
              let mut new_env = env.clone();
              new_env.push(arg_val);
              result_type = self.eval(body, &new_env)?;
            }
            _ => {
              return Err(TcError::KernelException {
                msg: "infer_type_of_val: expected Pi for ctor"
                  .to_string(),
              });
            }
          }
        }
        Ok(result_type)
      }
      ValInner::Proj { .. } => {
        let expr = self.quote(v, self.depth())?;
        let (_, ty) = self.infer(&expr)?;
        Ok(ty)
      }
    }
  }

  /// Check if a Val's type is Prop (Sort 0).
  pub fn is_prop_val(&mut self, v: &Val<M>) -> TcResult<bool, M> {
    let ty = self.infer_type_of_val(v)?;
    let ty_whnf = self.whnf_val(&ty, 0)?;
    Ok(matches!(
      ty_whnf.inner(),
      ValInner::Sort(l) if level::is_zero(l)
    ))
  }

  /// Classify a type for optimization (proof, sort, unit, or none).
  pub fn info_from_type(
    &mut self,
    typ: &Val<M>,
  ) -> TcResult<TypeInfo<M>, M> {
    let typ_whnf = self.whnf_val(typ, 0)?;
    match typ_whnf.inner() {
      ValInner::Sort(l) if level::is_zero(l) => {
        Ok(TypeInfo::Proof)
      }
      ValInner::Sort(l) => Ok(TypeInfo::Sort(l.clone())),
      _ => Ok(TypeInfo::None),
    }
  }

  /// Get structure info from a type Val.
  /// Returns (ctor type expr, universe levels, num_params, param vals).
  pub fn get_struct_info_val(
    &mut self,
    struct_type: &Val<M>,
  ) -> TcResult<(KExpr<M>, Vec<KLevel<M>>, usize, Vec<Val<M>>), M> {
    let struct_type_whnf = self.whnf_val(struct_type, 0)?;
    match struct_type_whnf.inner() {
      ValInner::Neutral {
        head: Head::Const { addr: ind_addr, levels: univs, .. },
        spine,
      } => {
        let ci = self.deref_const(ind_addr)?.clone();
        match &ci {
          KConstantInfo::Inductive(iv) => {
            if iv.ctors.len() != 1 {
              return Err(TcError::KernelException {
                msg: "Expected a structure type (single constructor)".to_string(),
              });
            }
            // Force spine params
            let mut params = Vec::with_capacity(spine.len());
            for thunk in spine {
              params.push(self.force_thunk(thunk)?);
            }
            let ctor_addr = &iv.ctors[0];
            self.ensure_typed_const(ctor_addr)?;
            match self.deref_typed_const(ctor_addr) {
              Some(TypedConst::Constructor { typ, .. }) => {
                Ok((typ.body.clone(), univs.clone(), iv.num_params, params))
              }
              _ => Err(TcError::KernelException {
                msg: "Constructor not in typedConsts".to_string(),
              }),
            }
          }
          _ => Err(TcError::KernelException {
            msg: format!("Expected a structure type, got {}", ci.kind_name()),
          }),
        }
      }
      _ => Err(TcError::KernelException {
        msg: "Expected a structure type (neutral const head)".to_string(),
      }),
    }
  }

  /// Build a Vec<Val> from the current context, with fvars for lambda-bound
  /// and values for let-bound.
  pub fn build_ctx_env(&self) -> Vec<Val<M>> {
    let mut env = Vec::with_capacity(self.depth());
    for level in 0..self.depth() {
      if let Some(Some(val)) = self.let_values.get(level) {
        env.push(val.clone());
      } else {
        let ty = self.types[level].clone();
        env.push(Val::mk_fvar(level, ty));
      }
    }
    env
  }
}
