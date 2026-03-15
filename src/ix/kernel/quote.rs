//! Quote: readback from Val to KExpr.
//!
//! Converts semantic values back to syntactic expressions, using fresh
//! free variables to open closures (standard NbE readback).

use super::tc::{TcResult, TypeChecker};
use super::types::{KExpr, MetaId, MetaMode};
use super::value::*;

impl<M: MetaMode> TypeChecker<'_, M> {
  /// Quote a Val back to a KExpr at the given depth.
  /// `depth` is the number of binders we are under (for level-to-index
  /// conversion).
  pub fn quote(&mut self, v: &Val<M>, depth: usize) -> TcResult<KExpr<M>, M> {
    match v.inner() {
      ValInner::Sort(level) => Ok(KExpr::sort(level.clone())),

      ValInner::Lit(l) => Ok(KExpr::lit(l.clone())),

      ValInner::Lam {
        name,
        bi,
        dom,
        body,
        env,
      } => {
        let dom_expr = self.quote(dom, depth)?;
        // Create fresh fvar at current depth
        let fvar = Val::mk_fvar(depth, dom.clone());
        let new_env = env_push(env, fvar);
        let body_val = self.eval(body, &new_env)?;
        let body_expr = self.quote(&body_val, depth + 1)?;
        Ok(KExpr::lam(dom_expr, body_expr, name.clone(), bi.clone()))
      }

      ValInner::Pi {
        name,
        bi,
        dom,
        body,
        env,
      } => {
        let dom_expr = self.quote(dom, depth)?;
        let fvar = Val::mk_fvar(depth, dom.clone());
        let new_env = env_push(env, fvar);
        let body_val = self.eval(body, &new_env)?;
        let body_expr = self.quote(&body_val, depth + 1)?;
        Ok(KExpr::forall_e(
          dom_expr,
          body_expr,
          name.clone(),
          bi.clone(),
        ))
      }

      ValInner::Neutral { head, spine, .. } => {
        let mut result = quote_head(head, depth, &self.binder_names);
        for thunk in spine {
          let arg_val = self.force_thunk(thunk)?;
          let arg_expr = self.quote(&arg_val, depth)?;
          result = KExpr::app(result, arg_expr);
        }
        Ok(result)
      }

      ValInner::Ctor {
        id,
        levels,
        spine,
        ..
      } => {
        let mut result =
          KExpr::cnst(id.clone(), levels.clone());
        for thunk in spine {
          let arg_val = self.force_thunk(thunk)?;
          let arg_expr = self.quote(&arg_val, depth)?;
          result = KExpr::app(result, arg_expr);
        }
        Ok(result)
      }

      ValInner::Proj {
        type_addr,
        idx,
        strct,
        type_name,
        spine,
        ..
      } => {
        let struct_val = self.force_thunk(strct)?;
        let struct_expr = self.quote(&struct_val, depth)?;
        let mut result = KExpr::proj(
          MetaId::new(type_addr.clone(), type_name.clone()),
          *idx,
          struct_expr,
        );
        for thunk in spine {
          let arg_val = self.force_thunk(thunk)?;
          let arg_expr = self.quote(&arg_val, depth)?;
          result = KExpr::app(result, arg_expr);
        }
        Ok(result)
      }
    }
  }
}

/// Convert a de Bruijn level to a de Bruijn index given the current depth.
pub fn level_to_index(depth: usize, level: usize) -> usize {
  depth - 1 - level
}

/// Quote a Head to a KExpr, using binder names from context if available.
pub fn quote_head<M: MetaMode>(
  head: &Head<M>,
  depth: usize,
  binder_names: &[M::Field<crate::ix::env::Name>],
) -> KExpr<M> {
  match head {
    Head::FVar { level, .. } => {
      let name = binder_names
        .get(*level)
        .cloned()
        .unwrap_or_default();
      KExpr::bvar(level_to_index(depth, *level), name)
    }
    Head::Const {
      id,
      levels,
    } => KExpr::cnst(id.clone(), levels.clone()),
  }
}
