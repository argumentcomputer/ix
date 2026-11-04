//! Local context for free-variable based binder opening.
//!
//! Mirrors `refs/lean4/src/Lean/LocalContext.lean` and the C++ kernel's
//! `local_ctx`. During type checking, when a binder (`Lam`/`All`/`Let`) is
//! recursed into, we open it by replacing the bound `Var(0)` with a fresh
//! [`FVar`](super::expr::ExprData::FVar) and pushing a [`LocalDecl`] into the
//! [`LocalContext`].
//!
//! Each fvar's [`FVarId`] participates in structural interning, so distinct
//! locals remain distinct in expression-keyed caches. Binder contracts are
//! retained here for reconstruction; conversion compares input contracts
//! separately from the resource validator.

use rustc_hash::FxHashMap;

use ix_common::env::{BinderInfo, Name};
use ixon::contract::{BinderContract, LetContract, ValueContract};

use super::env::InternTable;
use super::expr::{FVarId, KExpr};
use super::mode::KernelMode;
use super::subst::abstract_fvars;

/// A single local-context entry. Either a regular binder (`CDecl`, from a
/// lambda or forall) or a let-binding (`LDecl`, with an associated value).
#[derive(Clone, Debug)]
pub enum LocalDecl<M: KernelMode> {
  /// Regular binder declaration: type and the original scalar contracts.
  /// Lambda inference supplies the default result contract.
  CDecl {
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    ty: KExpr<M>,
    contract: BinderContract,
    result: ValueContract,
  },
  /// Let-binding declaration: carries both type and value. WHNF zeta-reduces
  /// `FVar(id)` to `val` when the lookup hits an `LDecl`. Mirrors
  /// `Lean.LocalDecl.ldecl`.
  LDecl {
    name: M::MField<Name>,
    ty: KExpr<M>,
    val: KExpr<M>,
    contract: LetContract,
  },
}

impl<M: KernelMode> LocalDecl<M> {
  /// Fresh ordinary-Lean local; source binders provide explicit payloads.
  pub fn cdecl(
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    ty: KExpr<M>,
  ) -> Self {
    Self::CDecl {
      name,
      bi,
      ty,
      contract: BinderContract::default(),
      result: ValueContract::shared(),
    }
  }

  pub fn ldecl(name: M::MField<Name>, ty: KExpr<M>, val: KExpr<M>) -> Self {
    Self::LDecl { name, ty, val, contract: LetContract::plain(false) }
  }

  pub fn ty(&self) -> &KExpr<M> {
    match self {
      LocalDecl::CDecl { ty, .. } | LocalDecl::LDecl { ty, .. } => ty,
    }
  }

  pub fn name(&self) -> &M::MField<Name> {
    match self {
      LocalDecl::CDecl { name, .. } | LocalDecl::LDecl { name, .. } => name,
    }
  }

  /// `Some(val)` for let-bindings, `None` otherwise.
  pub fn val(&self) -> Option<&KExpr<M>> {
    match self {
      LocalDecl::CDecl { .. } => None,
      LocalDecl::LDecl { val, .. } => Some(val),
    }
  }

  pub fn is_let(&self) -> bool {
    matches!(self, LocalDecl::LDecl { .. })
  }
}

/// Insertion-ordered local context indexed by [`FVarId`].
///
/// Push/pop is O(1) via `Vec` operations on `decls`. Lookup by `FVarId` is
/// O(1) via the parallel `index` map. The two structures are kept in sync
/// by `push` and `truncate`.
#[derive(Clone, Debug)]
pub struct LocalContext<M: KernelMode> {
  /// Insertion-ordered fvars and their declarations.
  decls: Vec<(FVarId, LocalDecl<M>)>,
  /// Position lookup: `index[fv_id] == i` iff `decls[i].0 == fv_id`.
  index: FxHashMap<FVarId, usize>,
}

impl<M: KernelMode> Default for LocalContext<M> {
  fn default() -> Self {
    Self::new()
  }
}

impl<M: KernelMode> LocalContext<M> {
  pub fn new() -> Self {
    LocalContext { decls: Vec::new(), index: FxHashMap::default() }
  }

  pub fn len(&self) -> usize {
    self.decls.len()
  }

  pub fn is_empty(&self) -> bool {
    self.decls.is_empty()
  }

  /// Look up a declaration by its [`FVarId`]. Returns `None` if the fvar is
  /// not bound in this context.
  pub fn find(&self, id: FVarId) -> Option<&LocalDecl<M>> {
    self.index.get(&id).map(|&i| &self.decls[i].1)
  }

  /// Push a declaration. The caller is responsible for ensuring `id` is
  /// fresh (typically from [`NameGenerator::fresh`]).
  pub fn push(&mut self, id: FVarId, decl: LocalDecl<M>) {
    let pos = self.decls.len();
    self.decls.push((id, decl));
    self.index.insert(id, pos);
  }

  /// Truncate the context to the given length, dropping any declarations
  /// pushed since. The dropped fvars become unresolvable via [`Self::find`].
  pub fn truncate(&mut self, len: usize) {
    while self.decls.len() > len {
      let (id, _) = self.decls.pop().expect("len > 0 by loop guard");
      self.index.remove(&id);
    }
  }

  /// Iterate decls in insertion order.
  pub fn iter(&self) -> impl Iterator<Item = (FVarId, &LocalDecl<M>)> {
    self.decls.iter().map(|(id, d)| (*id, d))
  }

  /// Abstract `body` over `fvars` and wrap it in a chain of `Lam` (or `Let`
  /// for `LDecl` entries) binders, innermost-first.
  ///
  /// The result has all of the listed fvars replaced by de Bruijn indices
  /// (`fvars[0]` becomes the outermost binder, `fvars[n-1]` the innermost).
  /// This is the inverse of the binder-opening pattern used during type
  /// checking: open with [`NameGenerator::fresh`], recurse, close back
  /// here so the result no longer mentions any of the opened fvars.
  ///
  /// Mirrors `Lean.LocalContext.mkLambda`.
  pub fn mk_lambda(
    &self,
    intern: &mut InternTable<M>,
    fvars: &[FVarId],
    body: &KExpr<M>,
  ) -> KExpr<M> {
    let abstracted = abstract_fvars(intern, body, fvars);
    self.wrap_binders(intern, fvars, abstracted, /* as_lambda */ true)
  }

  /// Abstract `body` over `fvars` and wrap it in a chain of `All` (or `Let`
  /// for `LDecl` entries) binders, innermost-first.
  ///
  /// Same shape as [`Self::mk_lambda`] but emits `All` for `CDecl` entries.
  /// Mirrors `Lean.LocalContext.mkForall`.
  pub fn mk_pi(
    &self,
    intern: &mut InternTable<M>,
    fvars: &[FVarId],
    body: &KExpr<M>,
  ) -> KExpr<M> {
    let abstracted = abstract_fvars(intern, body, fvars);
    self.wrap_binders(intern, fvars, abstracted, /* as_lambda */ false)
  }

  fn wrap_binders(
    &self,
    intern: &mut InternTable<M>,
    fvars: &[FVarId],
    body: KExpr<M>,
    as_lambda: bool,
  ) -> KExpr<M> {
    // Wrap from innermost to outermost: rightmost fvar is the innermost
    // binder, so iterate fvars in reverse.
    let mut acc = body;
    for (i, fv) in fvars.iter().enumerate().rev() {
      let decl = self
        .find(*fv)
        .expect("LocalContext::wrap_binders: fvar not in context");
      acc = match decl {
        LocalDecl::CDecl { name, bi, ty, contract, result } => {
          let ty = abstract_fvars(intern, ty, &fvars[..i]);
          if as_lambda {
            intern.intern_expr(KExpr::lam_contract(
              name.clone(),
              bi.clone(),
              *contract,
              ty,
              acc,
            ))
          } else {
            intern.intern_expr(KExpr::all_contract(
              name.clone(),
              bi.clone(),
              *contract,
              *result,
              ty,
              acc,
            ))
          }
        },
        LocalDecl::LDecl { name, ty, val, contract } => {
          let ty = abstract_fvars(intern, ty, &fvars[..i]);
          let val = abstract_fvars(intern, val, &fvars[..i]);
          // Let-bindings always close as `Let`, regardless of `as_lambda`.
          // Fresh ordinary locals use nonDep=false; an opened source let
          // retains its complete original payload.
          intern.intern_expr(KExpr::let_contract(
            name.clone(),
            *contract,
            ty,
            val,
            acc,
          ))
        },
      };
    }
    acc
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::level::KUniv;
  use crate::mode::Anon;

  type AE = KExpr<Anon>;
  type AU = KUniv<Anon>;

  /// Anon-mode `M::MField<Name>` is `()`; tests construct it with this
  /// trivially-named alias to make the call sites read like the meta
  /// equivalents (`ANON_NAME` ↔ `Name::anon()`).
  const ANON_NAME: () = ();
  const ANON_BI: () = ();

  #[test]
  fn lctx_push_find_truncate() {
    let mut lctx: LocalContext<Anon> = LocalContext::new();

    let id1 = FVarId(0);
    let id2 = FVarId(1);
    let ty1 = AE::sort(AU::zero());
    let ty2 = AE::sort(AU::succ(AU::zero()));

    lctx.push(id1, LocalDecl::cdecl(ANON_NAME, ANON_BI, ty1.clone()));
    lctx.push(id2, LocalDecl::cdecl(ANON_NAME, ANON_BI, ty2.clone()));

    assert_eq!(lctx.len(), 2);
    assert_eq!(lctx.find(id1).map(|d| d.ty()), Some(&ty1));
    assert_eq!(lctx.find(id2).map(|d| d.ty()), Some(&ty2));

    lctx.truncate(1);
    assert_eq!(lctx.len(), 1);
    assert!(lctx.find(id2).is_none());
    assert_eq!(lctx.find(id1).map(|d| d.ty()), Some(&ty1));

    lctx.truncate(0);
    assert!(lctx.is_empty());
    assert!(lctx.find(id1).is_none());
  }

  #[test]
  fn fvar_distinct_ids_distinct_hashes() {
    let id1 = FVarId(0);
    let id2 = FVarId(1);
    let fv1: AE = AE::fvar(id1, ANON_NAME);
    let fv2: AE = AE::fvar(id2, ANON_NAME);
    assert_ne!(fv1.addr(), fv2.addr());
    assert!(fv1.has_fvars());
    assert!(fv2.has_fvars());
    assert_eq!(fv1.lbr(), 0);
    assert_eq!(fv2.lbr(), 0);
  }
}
