//! Declaration-level type checking.
//!
//! Implements `check_const` (per-constant type checking), `check_ind_block`
//! (inductive block validation), and `typecheck_all` (whole environment).

use crate::ix::address::Address;
use crate::ix::env::{DefinitionSafety, Name};

use super::error::TcError;
use super::helpers;
use super::level;
use super::tc::{TcResult, TypeChecker};
use super::types::{MetaMode, *};
use super::value::*;

impl<M: MetaMode> TypeChecker<'_, M> {
  /// Type-check a single constant by address.
  pub fn check_const(&mut self, addr: &Address) -> TcResult<(), M> {
    let ci = self.deref_const(addr)?.clone();
    let decl_safety = ci.safety();

    self.with_reset_ctx(|tc| {
      tc.reset_caches();
      tc.with_safety(decl_safety, |tc| {
        tc.check_const_inner(addr, &ci)
      })
    })
  }

  fn check_const_inner(
    &mut self,
    addr: &Address,
    ci: &KConstantInfo<M>,
  ) -> TcResult<(), M> {
    match ci {
      KConstantInfo::Axiom(v) => {
        let (te, _level) = self.is_sort(&v.cv.typ)?;
        self.typed_consts.insert(
          addr.clone(),
          TypedConst::Axiom { typ: te },
        );
        Ok(())
      }

      KConstantInfo::Opaque(v) => {
        let (te, _level) = self.is_sort(&v.cv.typ)?;
        let type_val = self.eval_in_ctx(&v.cv.typ)?;
        let value_te = self.with_rec_addr(addr.clone(), |tc| {
          tc.check(&v.value, &type_val)
        })?;
        self.typed_consts.insert(
          addr.clone(),
          TypedConst::Opaque {
            typ: te,
            value: value_te,
          },
        );
        Ok(())
      }

      KConstantInfo::Theorem(v) => {
        let (te, level) = self.with_infer_only(|tc| {
          tc.is_sort(&v.cv.typ)
        })?;
        // Check theorem type is in Prop
        if !super::level::is_zero(&level) {
          return Err(TcError::KernelException {
            msg: "theorem type must be in Prop".to_string(),
          });
        }
        let type_val = self.eval_in_ctx(&v.cv.typ)?;
        let value_te = self.with_rec_addr(addr.clone(), |tc| {
          tc.with_infer_only(|tc| {
            tc.check(&v.value, &type_val)
          })
        })?;
        self.typed_consts.insert(
          addr.clone(),
          TypedConst::Theorem {
            typ: TypedExpr {
              info: TypeInfo::Proof,
              body: te.body,
            },
            value: TypedExpr {
              info: TypeInfo::Proof,
              body: value_te.body,
            },
          },
        );
        Ok(())
      }

      KConstantInfo::Definition(v) => {
        let (te, _level) = self.is_sort(&v.cv.typ)?;
        let type_val = self.eval_in_ctx(&v.cv.typ)?;

        let value_te = if v.safety == DefinitionSafety::Partial {
          // Set up self-referencing neutral for partial defs
          let a = addr.clone();
          let n = v.cv.name.clone();
          let def_val_fn = move |levels: &[KLevel<M>]| -> Val<M> {
            Val::mk_const(a.clone(), levels.to_vec(), n.clone())
          };
          let mut mt = std::collections::BTreeMap::new();
          mt.insert(
            0,
            (
              addr.clone(),
              Box::new(def_val_fn)
                as Box<dyn Fn(&[KLevel<M>]) -> Val<M>>,
            ),
          );
          self.with_mut_types(mt, |tc| {
            tc.with_rec_addr(addr.clone(), |tc| {
              tc.check(&v.value, &type_val)
            })
          })?
        } else {
          self.with_rec_addr(addr.clone(), |tc| {
            tc.check(&v.value, &type_val)
          })?
        };

        // Validate primitive
        self.validate_primitive(addr)?;

        self.typed_consts.insert(
          addr.clone(),
          TypedConst::Definition {
            typ: te,
            value: value_te,
            is_partial: v.safety == DefinitionSafety::Partial,
          },
        );
        Ok(())
      }

      KConstantInfo::Quotient(v) => {
        let (te, _level) = self.is_sort(&v.cv.typ)?;
        if self.quot_init {
          self.validate_quotient()?;
        }
        self.typed_consts.insert(
          addr.clone(),
          TypedConst::Quotient {
            typ: te,
            kind: v.kind,
          },
        );
        Ok(())
      }

      KConstantInfo::Inductive(_) => {
        self.check_ind_block(addr)
      }

      KConstantInfo::Constructor(v) => {
        self.check_ind_block(&v.induct)
      }

      KConstantInfo::Recursor(v) => {
        // Find the major inductive using proper type walking
        let induct_addr = helpers::get_major_induct(
          &v.cv.typ,
          v.num_params,
          v.num_motives,
          v.num_minors,
          v.num_indices,
        )
        .ok_or_else(|| TcError::KernelException {
          msg: "recursor has no inductive: getMajorInduct failed"
            .to_string(),
        })?;

        self.ensure_typed_const(&induct_addr)?;

        let (te, _level) = self.is_sort(&v.cv.typ)?;

        // Validate K flag
        if v.k {
          self.validate_k_flag(v, &induct_addr)?;
        }

        // Validate recursor rules
        self.validate_recursor_rules(v, &induct_addr)?;

        // Validate elimination level
        self.check_elim_level(&v.cv.typ, v, &induct_addr)?;

        // Check each recursor rule type
        let ci_ind = self.deref_const(&induct_addr)?.clone();
        if let KConstantInfo::Inductive(iv) = &ci_ind {
          for i in 0..v.rules.len() {
            if i < iv.ctors.len() {
              self.check_recursor_rule_type(
                &v.cv.typ,
                v,
                &iv.ctors[i],
                v.rules[i].nfields,
                &v.rules[i].rhs,
              )?;
            }
          }
        }

        // Infer typed rules
        let rules: Vec<(usize, TypedExpr<M>)> = v
          .rules
          .iter()
          .map(|r| {
            let (rhs_te, _) = self.infer(&r.rhs)?;
            Ok((r.nfields, rhs_te))
          })
          .collect::<TcResult<Vec<_>, M>>()?;

        self.typed_consts.insert(
          addr.clone(),
          TypedConst::Recursor {
            typ: te,
            num_params: v.num_params,
            num_motives: v.num_motives,
            num_minors: v.num_minors,
            num_indices: v.num_indices,
            k: v.k,
            induct_addr,
            rules,
          },
        );
        Ok(())
      }
    }
  }

  /// Check an inductive block (inductive type + constructors).
  pub fn check_ind_block(
    &mut self,
    addr: &Address,
  ) -> TcResult<(), M> {
    // Resolve to the inductive
    let ci = self.deref_const(addr)?.clone();
    let iv = match &ci {
      KConstantInfo::Inductive(v) => v.clone(),
      KConstantInfo::Constructor(v) => {
        match self.deref_const(&v.induct)?.clone() {
          KConstantInfo::Inductive(iv) => iv,
          _ => {
            return Err(TcError::KernelException {
              msg: "constructor's inductive not found"
                .to_string(),
            });
          }
        }
      }
      _ => {
        return Err(TcError::KernelException {
          msg: "expected inductive or constructor".to_string(),
        });
      }
    };

    let ind_addr = if matches!(&ci, KConstantInfo::Constructor(_)) {
      match &ci {
        KConstantInfo::Constructor(v) => v.induct.clone(),
        _ => unreachable!(),
      }
    } else {
      addr.clone()
    };

    // Already checked?
    if self.typed_consts.contains_key(&ind_addr) {
      return Ok(());
    }

    // Type-check the inductive type
    let (te, _level) = self.is_sort(&iv.cv.typ)?;

    // Validate primitive
    self.validate_primitive(&ind_addr)?;

    // Determine struct-like
    let is_struct = !iv.is_rec
      && iv.num_indices == 0
      && iv.ctors.len() == 1
      && {
        match self.env.get(&iv.ctors[0]) {
          Some(KConstantInfo::Constructor(cv)) => {
            cv.num_fields > 0
          }
          _ => false,
        }
      };

    self.typed_consts.insert(
      ind_addr.clone(),
      TypedConst::Inductive {
        typ: te,
        is_struct,
      },
    );

    let ind_addrs = &iv.all;
    let ind_result_level = helpers::get_ind_result_level(&iv.cv.typ);

    // Check each constructor
    for (_cidx, ctor_addr) in iv.ctors.iter().enumerate() {
      let ctor_ci = self.deref_const(ctor_addr)?.clone();
      if let KConstantInfo::Constructor(cv) = &ctor_ci {
        let (ctor_te, _) = self.is_sort(&cv.cv.typ)?;
        self.typed_consts.insert(
          ctor_addr.clone(),
          TypedConst::Constructor {
            typ: ctor_te,
            cidx: cv.cidx,
            num_fields: cv.num_fields,
          },
        );

        // Check parameter count
        if cv.num_params != iv.num_params {
          return Err(TcError::KernelException {
            msg: format!(
              "constructor {} has {} params but inductive has {}",
              ctor_addr.hex(),
              cv.num_params,
              iv.num_params
            ),
          });
        }

        if !iv.is_unsafe {
          // Check parameter domain agreement
          self.check_param_domain_agreement(
            &iv.cv.typ,
            &cv.cv.typ,
            iv.num_params,
            ctor_addr,
          )?;

          // Check strict positivity
          if let Some(msg) = self.check_ctor_fields(
            &cv.cv.typ,
            cv.num_params,
            ind_addrs,
          )? {
            return Err(TcError::KernelException {
              msg: format!("Constructor {}: {}", ctor_addr.hex(), msg),
            });
          }

          // Check field universes
          if let Some(ind_lvl) = &ind_result_level {
            self.check_field_universes(
              &cv.cv.typ,
              cv.num_params,
              ctor_addr,
              ind_lvl,
            )?;
          }

          // Check return type
          let ret_type = helpers::get_ctor_return_type(
            &cv.cv.typ,
            cv.num_params,
            cv.num_fields,
          );
          let ret_head = ret_type.get_app_fn();
          match ret_head.const_addr() {
            Some(ret_addr) => {
              if !ind_addrs.iter().any(|a| a == ret_addr) {
                return Err(TcError::KernelException {
                  msg: format!(
                    "Constructor {} return type head is not the inductive being defined",
                    ctor_addr.hex()
                  ),
                });
              }
            }
            None => {
              return Err(TcError::KernelException {
                msg: format!(
                  "Constructor {} return type is not an inductive application",
                  ctor_addr.hex()
                ),
              });
            }
          }

          // Check return type params are correct bvars
          let ret_args = ret_type.get_app_args_owned();
          for i in 0..iv.num_params {
            if i < ret_args.len() {
              let expected_bvar =
                cv.num_fields + iv.num_params - 1 - i;
              match ret_args[i].data() {
                KExprData::BVar(idx, _) => {
                  if *idx != expected_bvar {
                    return Err(TcError::KernelException {
                      msg: format!(
                        "Constructor {} return type has wrong parameter at position {}",
                        ctor_addr.hex(), i
                      ),
                    });
                  }
                }
                _ => {
                  return Err(TcError::KernelException {
                    msg: format!(
                      "Constructor {} return type parameter {} is not a bound variable",
                      ctor_addr.hex(), i
                    ),
                  });
                }
              }
            }
          }

          // Check index arguments don't mention the inductive
          for i in iv.num_params..ret_args.len() {
            for ind_addr in ind_addrs {
              if helpers::expr_mentions_const(&ret_args[i], ind_addr)
              {
                return Err(TcError::KernelException {
                  msg: format!(
                    "Constructor {} index argument mentions the inductive (unsound)",
                    ctor_addr.hex()
                  ),
                });
              }
            }
          }
        }
      } else {
        return Err(TcError::KernelException {
          msg: format!("Constructor {} not found", ctor_addr.hex()),
        });
      }
    }

    Ok(())
  }

  /// Check parameter domain agreement between inductive and constructor.
  fn check_param_domain_agreement(
    &mut self,
    ind_type: &KExpr<M>,
    ctor_type: &KExpr<M>,
    num_params: usize,
    ctor_addr: &Address,
  ) -> TcResult<(), M> {
    let mut ind_ty = ind_type.clone();
    let mut ctor_ty = ctor_type.clone();

    // Save context state for walking
    let saved_depth = self.depth();

    for i in 0..num_params {
      match (ind_ty.data(), ctor_ty.data()) {
        (
          KExprData::ForallE(ind_dom, ind_body, ind_name, _),
          KExprData::ForallE(ctor_dom, ctor_body, _, _),
        ) => {
          let ind_dom_val = self.eval_in_ctx(ind_dom)?;
          let ctor_dom_val = self.eval_in_ctx(ctor_dom)?;
          if !self.is_def_eq(&ind_dom_val, &ctor_dom_val)? {
            // Restore context
            while self.depth() > saved_depth {
              self.types.pop();
              self.let_values.pop();
              self.binder_names.pop();
            }
            return Err(TcError::KernelException {
              msg: format!(
                "Constructor {} parameter {} domain doesn't match inductive parameter domain",
                ctor_addr.hex(), i
              ),
            });
          }
          self.types.push(ind_dom_val);
          self.let_values.push(None);
          self.binder_names.push(ind_name.clone());
          ind_ty = ind_body.clone();
          ctor_ty = ctor_body.clone();
        }
        _ => {
          // Restore context
          while self.depth() > saved_depth {
            self.types.pop();
            self.let_values.pop();
            self.binder_names.pop();
          }
          return Err(TcError::KernelException {
            msg: format!(
              "Constructor {} has fewer Pi binders than expected parameters",
              ctor_addr.hex()
            ),
          });
        }
      }
    }

    // Restore context
    while self.depth() > saved_depth {
      self.types.pop();
      self.let_values.pop();
      self.binder_names.pop();
    }
    Ok(())
  }

  /// Walk a Pi chain, skip numParams binders, then check positivity of each
  /// field.
  fn check_ctor_fields(
    &mut self,
    ctor_type: &KExpr<M>,
    num_params: usize,
    ind_addrs: &[Address],
  ) -> TcResult<Option<String>, M> {
    self.check_ctor_fields_go(ctor_type, num_params, ind_addrs)
  }

  fn check_ctor_fields_go(
    &mut self,
    ty: &KExpr<M>,
    remaining_params: usize,
    ind_addrs: &[Address],
  ) -> TcResult<Option<String>, M> {
    let ty_val = self.eval_in_ctx(ty)?;
    let ty_whnf = self.whnf_val(&ty_val, 0)?;
    let d = self.depth();
    let ty_expr = self.quote(&ty_whnf, d)?;
    match ty_expr.data() {
      KExprData::ForallE(dom, body, name, _) => {
        let dom_val = self.eval_in_ctx(dom)?;
        if remaining_params > 0 {
          self.with_binder(dom_val, name.clone(), |tc| {
            tc.check_ctor_fields_go(body, remaining_params - 1, ind_addrs)
          })
        } else {
          if !self.check_positivity(dom, ind_addrs)? {
            return Ok(Some(
              "inductive occurs in negative position (strict positivity violation)".to_string(),
            ));
          }
          self.with_binder(dom_val, name.clone(), |tc| {
            tc.check_ctor_fields_go(body, 0, ind_addrs)
          })
        }
      }
      _ => Ok(None),
    }
  }

  /// Check strict positivity of a field type w.r.t. inductive addresses.
  fn check_positivity(
    &mut self,
    ty: &KExpr<M>,
    ind_addrs: &[Address],
  ) -> TcResult<bool, M> {
    let ty_val = self.eval_in_ctx(ty)?;
    let ty_whnf = self.whnf_val(&ty_val, 0)?;
    let d = self.depth();
    let ty_expr = self.quote(&ty_whnf, d)?;
    if !ind_addrs
      .iter()
      .any(|a| helpers::expr_mentions_const(&ty_expr, a))
    {
      return Ok(true);
    }
    match ty_expr.data() {
      KExprData::ForallE(dom, body, _, _) => {
        if ind_addrs
          .iter()
          .any(|a| helpers::expr_mentions_const(dom, a))
        {
          return Ok(false);
        }
        self.check_positivity(body, ind_addrs)
      }
      _ => {
        let fn_head = ty_expr.get_app_fn();
        match fn_head.const_addr() {
          Some(head_addr) => {
            if ind_addrs.iter().any(|a| a == head_addr) {
              return Ok(true);
            }
            // Check nested inductive
            match self.env.get(head_addr).cloned() {
              Some(KConstantInfo::Inductive(fv)) => {
                if fv.is_unsafe {
                  return Ok(false);
                }
                let args = ty_expr.get_app_args_owned();
                // Non-param args must not mention the inductive
                for i in fv.num_params..args.len() {
                  if ind_addrs.iter().any(|a| {
                    helpers::expr_mentions_const(&args[i], a)
                  }) {
                    return Ok(false);
                  }
                }
                // Check nested constructors
                let param_args: Vec<_> =
                  args[..fv.num_params].to_vec();
                let mut augmented: Vec<Address> =
                  ind_addrs.to_vec();
                augmented.extend(fv.all.iter().cloned());
                for ctor_addr in &fv.ctors {
                  match self.env.get(ctor_addr).cloned() {
                    Some(KConstantInfo::Constructor(cv)) => {
                      if !self
                        .check_nested_ctor_fields(
                          &cv.cv.typ,
                          fv.num_params,
                          &param_args,
                          &augmented,
                        )?
                      {
                        return Ok(false);
                      }
                    }
                    _ => return Ok(false),
                  }
                }
                Ok(true)
              }
              _ => Ok(false),
            }
          }
          None => Ok(false),
        }
      }
    }
  }

  /// Check nested inductive constructor fields for positivity.
  fn check_nested_ctor_fields(
    &mut self,
    ctor_type: &KExpr<M>,
    num_params: usize,
    param_args: &[KExpr<M>],
    ind_addrs: &[Address],
  ) -> TcResult<bool, M> {
    let mut ty = ctor_type.clone();
    for _ in 0..num_params {
      match ty.data() {
        KExprData::ForallE(_, body, _, _) => ty = body.clone(),
        _ => return Ok(true),
      }
    }
    // Instantiate param args (reverse because de Bruijn)
    let reversed: Vec<_> = param_args.iter().rev().cloned().collect();
    ty = self.instantiate_expr(&ty, &reversed);
    self.check_nested_ctor_fields_loop(&ty, ind_addrs)
  }

  fn check_nested_ctor_fields_loop(
    &mut self,
    ty: &KExpr<M>,
    ind_addrs: &[Address],
  ) -> TcResult<bool, M> {
    let ty_val = self.eval_in_ctx(ty)?;
    let ty_whnf = self.whnf_val(&ty_val, 0)?;
    let d = self.depth();
    let ty_expr = self.quote(&ty_whnf, d)?;
    match ty_expr.data() {
      KExprData::ForallE(dom, body, _, _) => {
        if !self.check_positivity(dom, ind_addrs)? {
          return Ok(false);
        }
        self.check_nested_ctor_fields_loop(body, ind_addrs)
      }
      _ => Ok(true),
    }
  }

  /// Instantiate bound variables in an expression with the given values.
  /// `vals[0]` replaces the outermost bvar (i.e., reverse de Bruijn).
  fn instantiate_expr(
    &self,
    e: &KExpr<M>,
    vals: &[KExpr<M>],
  ) -> KExpr<M> {
    if vals.is_empty() {
      return e.clone();
    }
    self.inst_go(e, vals, 0)
  }

  fn inst_go(
    &self,
    e: &KExpr<M>,
    vals: &[KExpr<M>],
    depth: usize,
  ) -> KExpr<M> {
    match e.data() {
      KExprData::BVar(idx, n) => {
        if *idx >= depth {
          let adjusted = idx - depth;
          if adjusted < vals.len() {
            helpers::lift_bvars(&vals[adjusted], depth, 0)
          } else {
            KExpr::bvar(idx - vals.len(), n.clone())
          }
        } else {
          e.clone()
        }
      }
      KExprData::App(f, a) => KExpr::app(
        self.inst_go(f, vals, depth),
        self.inst_go(a, vals, depth),
      ),
      KExprData::Lam(ty, body, n, bi) => KExpr::lam(
        self.inst_go(ty, vals, depth),
        self.inst_go(body, vals, depth + 1),
        n.clone(),
        bi.clone(),
      ),
      KExprData::ForallE(ty, body, n, bi) => KExpr::forall_e(
        self.inst_go(ty, vals, depth),
        self.inst_go(body, vals, depth + 1),
        n.clone(),
        bi.clone(),
      ),
      KExprData::LetE(ty, val, body, n) => KExpr::let_e(
        self.inst_go(ty, vals, depth),
        self.inst_go(val, vals, depth),
        self.inst_go(body, vals, depth + 1),
        n.clone(),
      ),
      KExprData::Proj(ta, idx, s, tn) => KExpr::proj(
        ta.clone(),
        *idx,
        self.inst_go(s, vals, depth),
        tn.clone(),
      ),
      _ => e.clone(),
    }
  }

  /// Check that constructor field types have sorts <= the inductive's
  /// result sort.
  fn check_field_universes(
    &mut self,
    ctor_type: &KExpr<M>,
    num_params: usize,
    ctor_addr: &Address,
    ind_lvl: &KLevel<M>,
  ) -> TcResult<(), M> {
    self.check_field_universes_go(
      ctor_type, num_params, ctor_addr, ind_lvl,
    )
  }

  fn check_field_universes_go(
    &mut self,
    ty: &KExpr<M>,
    remaining_params: usize,
    ctor_addr: &Address,
    ind_lvl: &KLevel<M>,
  ) -> TcResult<(), M> {
    let ty_val = self.eval_in_ctx(ty)?;
    let ty_whnf = self.whnf_val(&ty_val, 0)?;
    let d = self.depth();
    let ty_expr = self.quote(&ty_whnf, d)?;
    match ty_expr.data() {
      KExprData::ForallE(dom, body, pi_name, _) => {
        if remaining_params > 0 {
          let _ = self.is_sort(dom)?;
          let dom_val = self.eval_in_ctx(dom)?;
          self.with_binder(dom_val, pi_name.clone(), |tc| {
            tc.check_field_universes_go(
              body,
              remaining_params - 1,
              ctor_addr,
              ind_lvl,
            )
          })
        } else {
          let (_, field_sort_lvl) = self.is_sort(dom)?;
          let field_reduced = level::reduce(&field_sort_lvl);
          let ind_reduced = level::reduce(ind_lvl);
          if !level::leq(&field_reduced, &ind_reduced, 0)
            && !level::is_zero(&ind_reduced)
          {
            return Err(TcError::KernelException {
              msg: format!(
                "Constructor {} field type lives in a universe larger than the inductive's universe",
                ctor_addr.hex()
              ),
            });
          }
          let dom_val = self.eval_in_ctx(dom)?;
          self.with_binder(dom_val, pi_name.clone(), |tc| {
            tc.check_field_universes_go(body, 0, ctor_addr, ind_lvl)
          })
        }
      }
      _ => Ok(()),
    }
  }

  /// Validate K-flag: requires non-mutual, Prop, single ctor, zero fields.
  fn validate_k_flag(
    &mut self,
    _rec: &KRecursorVal<M>,
    induct_addr: &Address,
  ) -> TcResult<(), M> {
    let ci = self.deref_const(induct_addr)?.clone();
    let iv = match &ci {
      KConstantInfo::Inductive(v) => v,
      _ => {
        return Err(TcError::KernelException {
          msg: format!(
            "recursor claims K but {} is not an inductive",
            induct_addr.hex()
          ),
        })
      }
    };
    if iv.all.len() != 1 {
      return Err(TcError::KernelException {
        msg: "recursor claims K but inductive is mutual".to_string(),
      });
    }
    match helpers::get_ind_result_level(&iv.cv.typ) {
      Some(lvl) => {
        if level::is_nonzero(&lvl) {
          return Err(TcError::KernelException {
            msg: "recursor claims K but inductive is not in Prop"
              .to_string(),
          });
        }
      }
      None => {
        return Err(TcError::KernelException {
          msg: "recursor claims K but cannot determine inductive's result sort".to_string(),
        })
      }
    }
    if iv.ctors.len() != 1 {
      return Err(TcError::KernelException {
        msg: format!(
          "recursor claims K but inductive has {} constructors (need 1)",
          iv.ctors.len()
        ),
      });
    }
    let ctor_ci = self.deref_const(&iv.ctors[0])?.clone();
    match &ctor_ci {
      KConstantInfo::Constructor(cv) => {
        if cv.num_fields != 0 {
          return Err(TcError::KernelException {
            msg: format!(
              "recursor claims K but constructor has {} fields (need 0)",
              cv.num_fields
            ),
          });
        }
      }
      _ => {
        return Err(TcError::KernelException {
          msg: "recursor claims K but constructor not found"
            .to_string(),
        })
      }
    }
    Ok(())
  }

  /// Validate recursor rules: rule count, ctor membership, field counts.
  fn validate_recursor_rules(
    &mut self,
    rec: &KRecursorVal<M>,
    induct_addr: &Address,
  ) -> TcResult<(), M> {
    let ci = self.deref_const(induct_addr)?.clone();
    if let KConstantInfo::Inductive(iv) = &ci {
      if rec.rules.len() != iv.ctors.len() {
        return Err(TcError::KernelException {
          msg: format!(
            "recursor has {} rules but inductive has {} constructors",
            rec.rules.len(),
            iv.ctors.len()
          ),
        });
      }
      for i in 0..rec.rules.len() {
        let rule = &rec.rules[i];
        let ctor_ci = self.deref_const(&iv.ctors[i])?.clone();
        if let KConstantInfo::Constructor(cv) = &ctor_ci {
          if rule.nfields != cv.num_fields {
            return Err(TcError::KernelException {
              msg: format!(
                "recursor rule for {:?} has nfields={} but constructor has {} fields",
                iv.ctors[i].hex(),
                rule.nfields,
                cv.num_fields
              ),
            });
          }
        } else {
          return Err(TcError::KernelException {
            msg: format!(
              "constructor {} not found",
              iv.ctors[i].hex()
            ),
          });
        }
      }
    }
    Ok(())
  }

  /// Validate that the recursor's elimination level is appropriate.
  fn check_elim_level(
    &mut self,
    rec_type: &KExpr<M>,
    rec: &KRecursorVal<M>,
    induct_addr: &Address,
  ) -> TcResult<(), M> {
    let ci = self.deref_const(induct_addr)?.clone();
    let iv = match &ci {
      KConstantInfo::Inductive(v) => v,
      _ => return Ok(()),
    };
    let ind_lvl = match helpers::get_ind_result_level(&iv.cv.typ) {
      Some(l) => l,
      None => return Ok(()),
    };
    if level::is_nonzero(&ind_lvl) {
      return Ok(()); // Not Prop, large elim always ok
    }
    let motive_sort =
      match helpers::get_motive_sort(rec_type, rec.num_params) {
        Some(l) => l,
        None => return Ok(()),
      };
    if level::is_zero(&motive_sort) {
      return Ok(()); // Motive is Prop, no large elim
    }
    // Large elimination from Prop
    if iv.all.len() != 1 {
      return Err(TcError::KernelException {
        msg: "recursor claims large elimination but mutual Prop inductive only allows Prop elimination".to_string(),
      });
    }
    if iv.ctors.is_empty() {
      return Ok(());
    }
    if iv.ctors.len() != 1 {
      return Err(TcError::KernelException {
        msg: "recursor claims large elimination but Prop inductive with multiple constructors only allows Prop elimination".to_string(),
      });
    }
    let ctor_ci = self.deref_const(&iv.ctors[0])?.clone();
    if let KConstantInfo::Constructor(cv) = &ctor_ci {
      let allowed = self.check_large_elim_single_ctor(
        &cv.cv.typ,
        iv.num_params,
        cv.num_fields,
      )?;
      if !allowed {
        return Err(TcError::KernelException {
          msg: "recursor claims large elimination but inductive has non-Prop fields not appearing in indices".to_string(),
        });
      }
    }
    Ok(())
  }

  /// Check if a single-ctor Prop inductive allows large elimination.
  fn check_large_elim_single_ctor(
    &mut self,
    ctor_type: &KExpr<M>,
    num_params: usize,
    num_fields: usize,
  ) -> TcResult<bool, M> {
    self.check_large_elim_go(
      ctor_type,
      num_params,
      num_fields,
      &mut Vec::new(),
    )
  }

  fn check_large_elim_go(
    &mut self,
    ty: &KExpr<M>,
    remaining_params: usize,
    remaining_fields: usize,
    non_prop_bvars: &mut Vec<usize>,
  ) -> TcResult<bool, M> {
    let ty_val = self.eval_in_ctx(ty)?;
    let ty_whnf = self.whnf_val(&ty_val, 0)?;
    let d = self.depth();
    let ty_expr = self.quote(&ty_whnf, d)?;
    match ty_expr.data() {
      KExprData::ForallE(dom, body, name, _) => {
        if remaining_params > 0 {
          let dom_val = self.eval_in_ctx(dom)?;
          self.with_binder(dom_val, name.clone(), |tc| {
            tc.check_large_elim_go(
              body,
              remaining_params - 1,
              remaining_fields,
              non_prop_bvars,
            )
          })
        } else if remaining_fields > 0 {
          let (_, field_sort_lvl) = self.is_sort(dom)?;
          if !level::is_zero(&field_sort_lvl) {
            non_prop_bvars.push(remaining_fields - 1);
          }
          let dom_val = self.eval_in_ctx(dom)?;
          self.with_binder(dom_val, name.clone(), |tc| {
            tc.check_large_elim_go(
              body,
              0,
              remaining_fields - 1,
              non_prop_bvars,
            )
          })
        } else {
          Ok(true)
        }
      }
      _ => {
        if non_prop_bvars.is_empty() {
          return Ok(true);
        }
        let args = ty_expr.get_app_args_owned();
        for &bvar_idx in non_prop_bvars.iter() {
          let mut found = false;
          for i in remaining_params..args.len() {
            if let KExprData::BVar(idx, _) = args[i].data() {
              if *idx == bvar_idx {
                found = true;
              }
            }
          }
          if !found {
            return Ok(false);
          }
        }
        Ok(true)
      }
    }
  }

  /// Check a single recursor rule RHS has the expected type.
  fn check_recursor_rule_type(
    &mut self,
    rec_type: &KExpr<M>,
    rec: &KRecursorVal<M>,
    ctor_addr: &Address,
    nf: usize,
    rule_rhs: &KExpr<M>,
  ) -> TcResult<(), M> {
    let np = rec.num_params;
    let nm = rec.num_motives;
    let nk = rec.num_minors;
    let shift = nm + nk;
    let ctor_ci = self.deref_const(ctor_addr)?.clone();
    let ctor_type = ctor_ci.typ().clone();

    // Extract recursor param+motive+minor domains
    let mut rec_ty = rec_type.clone();
    let mut rec_doms: Vec<KExpr<M>> = Vec::new();
    for _ in 0..(np + nm + nk) {
      match rec_ty.data() {
        KExprData::ForallE(dom, body, _, _) => {
          rec_doms.push(dom.clone());
          rec_ty = body.clone();
        }
        _ => {
          return Err(TcError::KernelException {
            msg: "recursor type has too few Pi binders for params+motives+minors".to_string(),
          })
        }
      }
    }

    let ni = rec.num_indices;

    // Find which motive position the recursor returns
    let motive_pos: usize = {
      let mut ty = rec_ty.clone();
      for _ in 0..(ni + 1) {
        match ty.data() {
          KExprData::ForallE(_, body, _, _) => ty = body.clone(),
          _ => break,
        }
      }
      match ty.get_app_fn().data() {
        KExprData::BVar(idx, _) => {
          if *idx <= ni + nk + nm {
            ni + nk + nm - idx
          } else {
            0
          }
        }
        _ => 0,
      }
    };

    let cnp = match &ctor_ci {
      KConstantInfo::Constructor(cv) => cv.num_params,
      _ => np,
    };

    // Extract major premise domain
    let major_premise_dom: Option<KExpr<M>> = {
      let mut ty = rec_ty.clone();
      for _ in 0..ni {
        match ty.data() {
          KExprData::ForallE(_, body, _, _) => ty = body.clone(),
          _ => break,
        }
      }
      match ty.data() {
        KExprData::ForallE(dom, _, _, _) => Some(dom.clone()),
        _ => None,
      }
    };

    // Compute level substitution
    let rec_level_count = rec.cv.num_levels;
    let ctor_level_count = ctor_ci.cv().num_levels;
    let level_subst: Vec<KLevel<M>> = if cnp > np {
      match &major_premise_dom {
        Some(dom) => match dom.get_app_fn().const_levels() {
          Some(lvls) => lvls.clone(),
          None => Vec::new(),
        },
        None => Vec::new(),
      }
    } else {
      let level_offset = rec_level_count.saturating_sub(ctor_level_count);
      (0..ctor_level_count)
        .map(|i| {
          KLevel::param(
            level_offset + i,
            M::Field::<Name>::default(),
          )
        })
        .collect()
    };

    let ctor_levels = level_subst.clone();

    // Compute nested params
    let nested_params: Vec<KExpr<M>> = if cnp > np {
      match &major_premise_dom {
        Some(dom) => {
          let args = dom.get_app_args_owned();
          (0..(cnp - np))
            .map(|i| {
              if np + i < args.len() {
                helpers::shift_ctor_to_rule(
                  &args[np + i],
                  0,
                  nf,
                  &[],
                )
              } else {
                KExpr::bvar(0, M::Field::<Name>::default())
              }
            })
            .collect()
        }
        None => Vec::new(),
      }
    } else {
      Vec::new()
    };

    // Peel constructor params
    let mut cty = ctor_type.clone();
    for _ in 0..cnp {
      match cty.data() {
        KExprData::ForallE(_, body, _, _) => cty = body.clone(),
        _ => {
          return Err(TcError::KernelException {
            msg: "constructor type has too few Pi binders for params"
              .to_string(),
          })
        }
      }
    }

    // Extract field domains and return type
    let mut field_doms: Vec<KExpr<M>> = Vec::new();
    let mut ctor_ret_type = cty.clone();
    for _ in 0..nf {
      match ctor_ret_type.data() {
        KExprData::ForallE(dom, body, _, _) => {
          field_doms.push(dom.clone());
          ctor_ret_type = body.clone();
        }
        _ => {
          return Err(TcError::KernelException {
            msg: "constructor type has too few Pi binders for fields"
              .to_string(),
          })
        }
      }
    }

    // Apply nested param substitution
    let ctor_ret = if cnp > np {
      helpers::subst_nested_params(
        &ctor_ret_type,
        nf,
        cnp - np,
        &nested_params,
      )
    } else {
      ctor_ret_type
    };

    let field_doms_adj: Vec<KExpr<M>> = if cnp > np {
      field_doms
        .iter()
        .enumerate()
        .map(|(i, dom)| {
          helpers::subst_nested_params(
            dom,
            i,
            cnp - np,
            &nested_params,
          )
        })
        .collect()
    } else {
      field_doms
    };

    // Shift constructor return type for rule context
    let ctor_ret_shifted = helpers::shift_ctor_to_rule(
      &ctor_ret,
      nf,
      shift,
      &level_subst,
    );

    // Build expected return type: motive applied to indices and ctor app
    let motive_idx = nf + nk + nm - 1 - motive_pos;
    let mut ret =
      KExpr::bvar(motive_idx, M::Field::<Name>::default());
    let ctor_ret_args = ctor_ret_shifted.get_app_args_owned();
    for i in cnp..ctor_ret_args.len() {
      ret = KExpr::app(ret, ctor_ret_args[i].clone());
    }

    // Build constructor application
    let mut ctor_app =
      KExpr::cnst(ctor_addr.clone(), ctor_levels, M::Field::<Name>::default());
    for i in 0..np {
      ctor_app = KExpr::app(
        ctor_app,
        KExpr::bvar(
          nf + shift + np - 1 - i,
          M::Field::<Name>::default(),
        ),
      );
    }
    for v in &nested_params {
      ctor_app = KExpr::app(ctor_app, v.clone());
    }
    for k in 0..nf {
      ctor_app = KExpr::app(
        ctor_app,
        KExpr::bvar(nf - 1 - k, M::Field::<Name>::default()),
      );
    }
    ret = KExpr::app(ret, ctor_app);

    // Build full expected type with Pi binders
    let mut full_type = ret;
    for i in 0..nf {
      let j = nf - 1 - i;
      let dom = helpers::shift_ctor_to_rule(
        &field_doms_adj[j],
        j,
        shift,
        &level_subst,
      );
      full_type = KExpr::forall_e(
        dom,
        full_type,
        M::Field::<Name>::default(),
        M::Field::<BinderInfo>::default(),
      );
    }
    for i in 0..(np + nm + nk) {
      let j = np + nm + nk - 1 - i;
      full_type = KExpr::forall_e(
        rec_doms[j].clone(),
        full_type,
        M::Field::<Name>::default(),
        M::Field::<BinderInfo>::default(),
      );
    }

    // Compare inferred RHS type against expected
    let (_, rhs_type) =
      self.with_infer_only(|tc| tc.infer(rule_rhs))?;
    let d = self.depth();
    let rhs_type_expr = self.quote(&rhs_type, d)?;
    let rhs_type_val = self.eval_in_ctx(&rhs_type_expr)?;
    let full_type_val = self.eval_in_ctx(&full_type)?;
    if !self.with_infer_only(|tc| {
      tc.is_def_eq(&rhs_type_val, &full_type_val)
    })? {
      return Err(TcError::KernelException {
        msg: format!(
          "recursor rule RHS type mismatch for constructor {}",
          ctor_addr.hex()
        ),
      });
    }
    Ok(())
  }
}

/// Type-check a single constant in a fresh TypeChecker.
pub fn typecheck_const<M: MetaMode>(
  env: &KEnv<M>,
  prims: &Primitives,
  addr: &Address,
  quot_init: bool,
) -> Result<(), TcError<M>> {
  let mut tc = TypeChecker::new(env, prims);
  tc.quot_init = quot_init;
  tc.check_const(addr)
}

/// Type-check a single constant, returning stats on success or failure.
pub fn typecheck_const_with_stats<M: MetaMode>(
  env: &KEnv<M>,
  prims: &Primitives,
  addr: &Address,
  quot_init: bool,
) -> (Result<(), TcError<M>>, usize, super::tc::Stats) {
  typecheck_const_with_stats_trace(env, prims, addr, quot_init, false, "")
}

pub fn typecheck_const_with_stats_trace<M: MetaMode>(
  env: &KEnv<M>,
  prims: &Primitives,
  addr: &Address,
  quot_init: bool,
  trace: bool,
  name: &str,
) -> (Result<(), TcError<M>>, usize, super::tc::Stats) {
  let mut tc = TypeChecker::new(env, prims);
  tc.quot_init = quot_init;
  tc.trace = trace;
  if !name.is_empty() {
    tc.trace_prefix = format!("[{name}] ");
  }
  let result = tc.check_const(addr);
  (result, tc.heartbeats, tc.stats.clone())
}

/// Type-check all constants in the environment.
pub fn typecheck_all<M: MetaMode>(
  env: &KEnv<M>,
  prims: &Primitives,
  quot_init: bool,
) -> Result<(), String> {
  for (addr, ci) in env {
    if let Err(e) = typecheck_const(env, prims, addr, quot_init) {
      return Err(format!(
        "constant {:?} ({}, {}): {}",
        ci.name(),
        ci.kind_name(),
        addr.hex(),
        e
      ));
    }
  }
  Ok(())
}
