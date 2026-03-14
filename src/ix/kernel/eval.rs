//! Core Krivine machine evaluator.
//!
//! This implements the eval/apply/force cycle of the call-by-need
//! Krivine machine:
//! - `eval`: expression + environment → Val (creates thunks, doesn't force)
//! - `apply_val_thunk`: O(1) beta reduction for closures
//! - `force_thunk`: call-by-need forcing with memoization




use std::rc::Rc;

use super::error::TcError;
use super::helpers::reduce_val_proj_forced;
use super::tc::{TcResult, TypeChecker};
use super::types::{MetaMode, *};
use super::value::*;

impl<M: MetaMode> TypeChecker<'_, M> {
  /// Evaluate a kernel expression under an environment to produce a Val.
  ///
  /// This is the core Krivine machine transition: it creates closures for
  /// lambda/pi, thunks for application arguments, and eagerly zeta-reduces
  /// let bindings.
  pub fn eval(
    &mut self,
    expr: &KExpr<M>,
    env: &Env<M>,
  ) -> TcResult<Val<M>, M> {
    self.stats.eval_calls += 1;

    match expr.data() {
      KExprData::BVar(idx, _) => {
        // Look up in the local environment first
        let env_idx = env.len().checked_sub(1 + idx);
        if let Some(i) = env_idx {
          if let Some(v) = env.get(i) {
            return Ok(v.clone());
          }
        }
        // Fall through to context
        let level = if env.is_empty() {
          self.depth().checked_sub(1 + idx)
        } else {
          // The idx is relative to env + context
          let remaining = idx - env.len();
          self.depth().checked_sub(1 + remaining)
        };
        if let Some(lvl) = level {
          // Check for let-bound value (zeta reduction)
          if let Some(Some(val)) = self.let_values.get(lvl) {
            return Ok(val.clone());
          }
          // Return free variable
          if let Some(ty) = self.types.get(lvl) {
            return Ok(Val::mk_fvar(lvl, ty.clone()));
          }
        }
        Err(TcError::FreeBoundVariable { idx: *idx })
      }

      KExprData::Sort(level) => Ok(Val::mk_sort(level.clone())),

      KExprData::Lit(l) => Ok(Val::mk_lit(l.clone())),

      KExprData::Const(id, levels) => {
        // Check if it's a constructor
        if let Some(KConstantInfo::Constructor(cv)) = self.env.get(id)
        {
          return Ok(Val::mk_ctor(
            id.clone(),
            levels.clone(),
            cv.cidx,
            cv.num_params,
            cv.num_fields,
            cv.induct.addr.clone(),
            Vec::new(),
          ));
        }
        // Check mut_types for partial/mutual definitions
        // (This requires matching addr against recAddr)
        if let Some(rec_addr) = &self.rec_addr {
          if id.addr == *rec_addr {
            if let Some((_, factory)) = self.mut_types.get(&0) {
              return Ok(factory(levels));
            }
          }
        }
        // Otherwise, return as neutral constant
        Ok(Val::mk_const(id.clone(), levels.clone()))
      }

      KExprData::App(_f, _a) => {
        // Collect spine of arguments
        let (head_expr, args) = expr.get_app_args();
        let mut val = self.eval(head_expr, env)?;

        for arg in args {
          // Eager beta: if head is lambda, skip thunk allocation
          match val.inner() {
            ValInner::Lam { body, env: lam_env, .. } => {
              let arg_val = self.eval(&arg, env)?;
              let body = body.clone();
              let new_env = env_push(lam_env, arg_val);
              val = self.eval(&body, &new_env)?;
            }
            _ => {
              let thunk = mk_thunk(arg.clone(), env.clone());
              self.stats.thunk_count += 1;
              val = self.apply_val_thunk(val, thunk)?;
            }
          }
        }
        Ok(val)
      }

      KExprData::Lam(ty, body, name, bi) => {
        let dom = self.eval(ty, env)?;
        Ok(Val::mk_lam(
          name.clone(),
          bi.clone(),
          dom,
          body.clone(),
          env.clone(),
        ))
      }

      KExprData::ForallE(ty, body, name, bi) => {
        let dom = self.eval(ty, env)?;
        Ok(Val::mk_pi(
          name.clone(),
          bi.clone(),
          dom,
          body.clone(),
          env.clone(),
        ))
      }

      KExprData::LetE(_ty, val_expr, body, _name) => {
        // Eager zeta reduction: evaluate the value and push onto env
        let val = self.eval(val_expr, env)?;
        let new_env = env_push(env, val);
        self.eval(body, &new_env)
      }

      KExprData::Proj(type_id, idx, strct_expr) => {
        let strct_val = self.eval(strct_expr, env)?;
        // Try immediate projection reduction
        if let Some(field_thunk) =
          reduce_val_proj_forced(&strct_val, *idx, &type_id.addr)
        {
          return self.force_thunk(&field_thunk);
        }
        // Create stuck projection
        let strct_thunk = mk_thunk_val(strct_val);
        Ok(Val::mk_proj(
          type_id.addr.clone(),
          *idx,
          strct_thunk,
          type_id.name.clone(),
          Vec::new(),
        ))
      }
    }
  }

  /// Evaluate an expression using the current context as the initial
  /// environment. Lambda-bound variables become fvars, let-bound variables
  /// use their values.
  pub fn eval_in_ctx(&mut self, expr: &KExpr<M>) -> TcResult<Val<M>, M> {
    let mut env_vec = Vec::with_capacity(self.depth());
    for level in 0..self.depth() {
      if let Some(Some(val)) = self.let_values.get(level) {
        env_vec.push(val.clone());
      } else {
        let ty = self.types[level].clone();
        env_vec.push(Val::mk_fvar(level, ty));
      }
    }
    let env = Rc::new(env_vec);
    self.eval(expr, &env)
  }

  /// Apply a Val to a thunk argument. This is the Krivine machine's
  /// "apply" transition.
  ///
  /// - Lambda: force thunk, push arg onto closure env, eval body (O(1) beta)
  /// - Neutral: push thunk onto spine
  /// - Ctor: push thunk onto spine
  /// - Proj: try to reduce, otherwise accumulate spine
  pub fn apply_val_thunk(
    &mut self,
    fun: Val<M>,
    arg: Thunk<M>,
  ) -> TcResult<Val<M>, M> {
    match fun.inner() {
      ValInner::Lam { body, env, .. } => {
        // O(1) beta reduction: push arg value onto closure env
        let arg_val = self.force_thunk(&arg)?;
        let new_env = env_push(env, arg_val);
        self.eval(body, &new_env)
      }

      ValInner::Neutral { head, spine } => {
        let mut new_spine = spine.clone();
        new_spine.push(arg);
        Ok(Val::mk_neutral(clone_head(head), new_spine))
      }

      ValInner::Ctor {
        id,
        levels,
        cidx,
        num_params,
        num_fields,
        induct_addr,
        spine,
      } => {
        let mut new_spine = spine.clone();
        new_spine.push(arg);
        Ok(Val::mk_ctor(
          id.clone(),
          levels.clone(),
          *cidx,
          *num_params,
          *num_fields,
          induct_addr.clone(),
          new_spine,
        ))
      }

      ValInner::Proj {
        type_addr,
        idx,
        strct,
        type_name,
        spine,
      } => {
        // Force struct and WHNF to reveal constructor (including delta)
        let struct_val = self.force_thunk(strct)?;
        let struct_whnf = self.whnf_val(&struct_val, 0)?;
        if let Some(field_thunk) =
          reduce_val_proj_forced(&struct_whnf, *idx, type_addr)
        {
          // Projection reduced! Apply accumulated spine + new arg
          let mut result = self.force_thunk(&field_thunk)?;
          for s in spine {
            result = self.apply_val_thunk(result, s.clone())?;
          }
          result = self.apply_val_thunk(result, arg)?;
          Ok(result)
        } else {
          let mut new_spine = spine.clone();
          new_spine.push(arg);
          Ok(Val::mk_proj(
            type_addr.clone(),
            *idx,
            strct.clone(),
            type_name.clone(),
            new_spine,
          ))
        }
      }

      _ => {
        let arg_val = self.force_thunk(&arg)?;
        Err(TcError::KernelException {
          msg: format!(
            "cannot apply non-function value\n  fun: {fun}\n  fun kind: {}\n  arg: {arg_val}",
            match fun.inner() {
              ValInner::Sort(_) => "Sort",
              ValInner::Lit(_) => "Lit",
              ValInner::Pi { .. } => "Pi",
              _ => "unknown",
            }
          ),
        })
      }
    }
  }

  /// Force a thunk: if unevaluated, evaluate and memoize; if evaluated,
  /// return cached value.
  pub fn force_thunk(&mut self, thunk: &Thunk<M>) -> TcResult<Val<M>, M> {
    self.stats.force_calls += 1;

    // Check if already evaluated
    {
      let entry = thunk.borrow();
      if let ThunkEntry::Evaluated(val) = &*entry {
        self.stats.thunk_hits += 1;
        return Ok(val.clone());
      }
    }

    // Extract expr and env (clone to release borrow)
    let (expr, env) = {
      let entry = thunk.borrow();
      match &*entry {
        ThunkEntry::Unevaluated { expr, env } => {
          (expr.clone(), env.clone())
        }
        ThunkEntry::Evaluated(val) => {
          // Race condition guard (shouldn't happen in single-threaded)
          self.stats.thunk_hits += 1;
          return Ok(val.clone());
        }
      }
    };

    self.stats.thunk_forces += 1;
    let val = self.eval(&expr, &env)?;

    // Memoize
    *thunk.borrow_mut() = ThunkEntry::Evaluated(val.clone());

    Ok(val)
  }
}

/// Clone a Head value.
fn clone_head<M: MetaMode>(head: &Head<M>) -> Head<M> {
  match head {
    Head::FVar { level, ty } => Head::FVar {
      level: *level,
      ty: ty.clone(),
    },
    Head::Const {
      id,
      levels,
    } => Head::Const {
      id: id.clone(),
      levels: levels.clone(),
    },
  }
}
