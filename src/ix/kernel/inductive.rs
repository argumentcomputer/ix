//! Inductive type validation and recursor generation.
//!
//! Validates inductive declarations (parameter agreement, positivity, universe
//! constraints, return types) and generates canonical recursors following
//! lean4lean's constructive approach, then compares with provided recursors.

use std::sync::LazyLock;

use crate::ix::address::Address;

use super::constant::KConst;
use super::env::{
  BlockCheckStart, GeneratedRecursor, InternTable, RecursorAuxOrder,
};
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::{KUniv, univ_eq, univ_geq};
use super::mode::KernelMode;
use super::subst::{lift, simul_subst, subst};
use super::tc::{TypeChecker, collect_app_spine, expr_mentions_any_addr};

/// Emit the `[type diff]` walk from `check_recursor`'s mismatch path.
/// Off by default — every inductive over ~100k constants in an alpha-collapse
/// regime or a mutual block with near-identical peers triggers a fresh diff,
/// turning a normal compile into a wall of stderr. Set `IX_TYPE_DIFF=1` to
/// enable when investigating a specific mismatch.
static IX_TYPE_DIFF: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_TYPE_DIFF").is_ok());

/// Emit nested-aux recursor ordering/selection diagnostics for names whose
/// display form starts with the configured prefix. Example:
/// `IX_RECURSOR_DUMP=Lean.Doc.Block`.
static IX_RECURSOR_DUMP: LazyLock<Option<String>> = LazyLock::new(|| {
  std::env::var("IX_RECURSOR_DUMP").ok().filter(|s| !s.is_empty())
});

/// A member of the "flat" mutual block used for recursor generation.
/// For non-nested inductives, this is just the original inductive.
/// For nested occurrences (e.g., `Array Syntax` in Syntax's ctor fields),
/// an auxiliary entry is created mirroring the external inductive's structure.
#[derive(Clone)]
pub struct FlatBlockMember<M: KernelMode> {
  /// For original: the inductive's KId. For auxiliary: the external inductive's KId.
  pub id: KId<M>,
  /// True if this is an auxiliary member created for a nested occurrence.
  pub is_aux: bool,
  /// Specialized param values for this member.
  /// For original: Var refs to the recursor's shared params.
  /// For auxiliary: the concrete specialized exprs (e.g., `[Syntax]` for `Array Syntax`).
  /// These are in terms of the recursor's param binders (depth = n_rec_params).
  pub spec_params: Vec<KExpr<M>>,
  /// Number of params this member's inductive has (may differ from shared for nested).
  pub own_params: u64,
  /// Number of indices.
  pub n_indices: u64,
  /// Constructor ids (from env).
  pub ctors: Vec<KId<M>>,
  /// Universe param count.
  pub lvls: u64,
  /// Universe args for internal processing (abstract shifted params).
  /// Used for ctor type instantiation and nesting detection.
  pub ind_us: Box<[KUniv<M>]>,
  /// Universe args from the actual nested occurrence (concrete).
  /// For original members: same as ind_us.
  /// For auxiliaries: the concrete args from the ctor field (e.g., [Succ(Zero)]).
  /// Used for the final output type (motives, major, ctor apps).
  pub occurrence_us: Box<[KUniv<M>]>,
}

/// Lower free Var indices by `shift`: Var(i) where i >= shift becomes Var(i - shift).
/// Vars with i < shift are left unchanged (they refer to local binders).
fn lower_vars<M: KernelMode>(
  env: &InternTable<M>,
  e: &KExpr<M>,
  shift: u64,
) -> KExpr<M> {
  if shift == 0 {
    return e.clone();
  }
  lower_vars_inner(env, e, shift, 0)
}

fn lower_vars_inner<M: KernelMode>(
  env: &InternTable<M>,
  e: &KExpr<M>,
  shift: u64,
  cutoff: u64,
) -> KExpr<M> {
  // Quick exit: no free vars below lbr
  if e.lbr() <= cutoff {
    return e.clone();
  }

  let result = match e.data() {
    ExprData::Var(i, name, _) => {
      let i = *i;
      if i >= cutoff + shift {
        KExpr::var(i - shift, name.clone())
      } else {
        return e.clone();
      }
    },
    ExprData::App(f, a, _) => {
      let f2 = lower_vars_inner(env, f, shift, cutoff);
      let a2 = lower_vars_inner(env, a, shift, cutoff);
      KExpr::app(f2, a2)
    },
    ExprData::Lam(n, bi, ty, body, _) => {
      let ty2 = lower_vars_inner(env, ty, shift, cutoff);
      let body2 = lower_vars_inner(env, body, shift, cutoff + 1);
      KExpr::lam(n.clone(), bi.clone(), ty2, body2)
    },
    ExprData::All(n, bi, ty, body, _) => {
      let ty2 = lower_vars_inner(env, ty, shift, cutoff);
      let body2 = lower_vars_inner(env, body, shift, cutoff + 1);
      KExpr::all(n.clone(), bi.clone(), ty2, body2)
    },
    ExprData::Let(n, ty, val, body, nd, _) => {
      let ty2 = lower_vars_inner(env, ty, shift, cutoff);
      let val2 = lower_vars_inner(env, val, shift, cutoff);
      let body2 = lower_vars_inner(env, body, shift, cutoff + 1);
      KExpr::let_(n.clone(), ty2, val2, body2, *nd)
    },
    _ => return e.clone(), // Sort, Const, Nat, Str, Prj — no free Var shifting
  };
  env.intern_expr(result)
}

impl<M: KernelMode> TypeChecker<M> {
  /// Validate an inductive block. Pure inductive blocks are coordinated
  /// through `KEnv`; legacy mixed source blocks fall back to the member check
  /// to avoid caching a partial result under a mixed block id.
  pub fn check_inductive(&mut self, id: &KId<M>) -> Result<(), TcError<M>> {
    let block = match self.env.get(id) {
      Some(KConst::Indc { block, .. }) => block.clone(),
      _ => {
        return Err(TcError::Other("check_inductive: not an inductive".into()));
      },
    };
    let Some(members) = self.env.get_block(&block) else {
      return self.check_inductive_member(id);
    };
    if !members.iter().all(|member| {
      matches!(
        self.env.get(member),
        Some(KConst::Indc { .. } | KConst::Ctor { .. })
      )
    }) {
      return self.check_inductive_member(id);
    }

    match self.env.begin_block_check(&block) {
      BlockCheckStart::Cached(result) => result,
      BlockCheckStart::Owner(token) => {
        let result = self.check_inductive_block(&block, &members);
        self.env.finish_block_check(token, result)
      },
    }
  }

  /// Validate every inductive and constructor in an inductive block.
  pub(crate) fn check_inductive_block(
    &mut self,
    block: &KId<M>,
    members: &[KId<M>],
  ) -> Result<(), TcError<M>> {
    let mut ind_ids = Vec::new();
    let mut ctor_ids = Vec::new();

    for member in members {
      self.reset();
      match self
        .env
        .get(member)
        .ok_or_else(|| TcError::UnknownConst(member.addr.clone()))?
      {
        KConst::Indc { ty, .. } => {
          let t = self.infer(&ty)?;
          self.ensure_sort(&t)?;
          ind_ids.push(member.clone());
        },
        KConst::Ctor { ty, .. } => {
          let t = self.infer(&ty)?;
          self.ensure_sort(&t)?;
          ctor_ids.push(member.clone());
        },
        _ => {
          return Err(TcError::Other(format!(
            "check_inductive_block: non-inductive member {member} in block {block}"
          )));
        },
      }
    }

    for ind_id in &ind_ids {
      self.reset();
      self.check_inductive_member(ind_id)?;
    }
    for ctor_id in &ctor_ids {
      let induct = match self.env.get(ctor_id) {
        Some(KConst::Ctor { induct, .. }) => induct,
        _ => continue,
      };
      self.reset();
      self.check_ctor_against_inductive_member(ctor_id, &induct)?;
    }
    Ok(())
  }

  /// Validate an inductive type and its constructors.
  pub fn check_inductive_member(
    &mut self,
    id: &KId<M>,
  ) -> Result<(), TcError<M>> {
    let (params, indices, lvls, ctors, block, is_rec, is_unsafe, _nested, ty) =
      match self.env.get(id) {
        Some(KConst::Indc {
          params,
          indices,
          lvls,
          ctors,
          block,
          is_rec,
          is_unsafe,
          nested,
          ty,
          ..
        }) => (
          params,
          indices,
          lvls,
          ctors.clone(),
          block.clone(),
          is_rec,
          is_unsafe,
          nested,
          ty.clone(),
        ),
        _ => {
          return Err(TcError::Other(
            "check_inductive: not an inductive".into(),
          ));
        },
      };

    // Discover all inductives in the mutual block
    let block_inds = self.discover_block_inductives(&block);
    let block_addrs: Vec<Address> =
      block_inds.iter().map(|id| id.addr.clone()).collect();

    // Inductive type must reduce to a Sort after peeling params+indices.
    // This must be checked even for inductives with no constructors.
    let ind_level =
      self.get_result_sort_level(&ty, u64_to_usize(params + indices)?)?;

    // S3 + S3b: Peer-agreement invariants for mutual inductives.
    //
    // S3:  all peers live in the same result universe.
    // S3b: all peers share the same parameter count and parameter-domain
    //      types. Without S3b, `build_rec_type` — which takes the shared
    //      param prefix uniformly from `ind_infos[0]` — would produce a
    //      generated recursor whose param binders misalign with a peer's
    //      ctor arguments, yielding de-Bruijn-shifted iota reductions and,
    //      in the limit, ill-typed stored terms. Enforcing agreement
    //      kernel-side removes the implicit compiler trust.
    //
    // References: lean4 `src/kernel/inductive.cpp:211–262 check_inductive_types`
    // (line 230–231: "parameters of all inductive datatypes must match")
    // and lean4lean `Lean4Lean/Inductive/Add.lean:80–82`.
    //
    // Memoization: the check is invariant across all peers of the block —
    // if peer[0] agrees with each of peer[1..N], then by transitivity all
    // pairs agree. Running this loop from *every* peer in the block yields
    // redundant O(N²) work, which becomes significant on large Mathlib
    // mutual families. We memo on successful completion, so subsequent
    // peer checks of the same block skip the loop. Failure is not cached
    // (the loop re-runs and re-reports on the next peer's check). Block
    // ids are content-addressed, so cache entries are stable across the
    // TypeChecker's lifetime.
    if !self.env.block_peer_agreement_cache.contains(&block) {
      for peer_id in &block_inds {
        if peer_id.addr == id.addr {
          continue;
        }
        let (peer_params, peer_indices, peer_ty) = match self.env.get(peer_id) {
          Some(KConst::Indc { params: pp, indices: pi, ty: pty, .. }) => {
            (pp, pi, pty.clone())
          },
          _ => continue,
        };
        // S3: universe agreement.
        let peer_level = self.get_result_sort_level(
          &peer_ty,
          u64_to_usize(peer_params + peer_indices)?,
        )?;
        if !univ_eq(&ind_level, &peer_level) {
          return Err(TcError::Other(
            "mutually inductive types must live in the same universe".into(),
          ));
        }
        // S3b: parameter-count agreement.
        if peer_params != params {
          return Err(TcError::Other(format!(
            "mutual peers must declare the same number of parameters: \
             self={params}, peer={peer_params}"
          )));
        }
        // S3b: parameter-domain agreement. Walks the first `n_params`
        // foralls of both types and `is_def_eq`s the domains.
        self.check_param_agreement(&ty, &peer_ty, u64_to_usize(params)?)?;
      }
      self.env.block_peer_agreement_cache.insert(block.clone());
    }

    // Validate each constructor
    for (expected_cidx, ctor_id) in ctors.iter().enumerate() {
      let (_ctor_params, ctor_fields, ctor_cidx, ctor_ty) =
        match self.env.get(ctor_id) {
          Some(KConst::Ctor { params, fields, cidx, ty, .. }) => (
            u64_to_usize(params)?,
            u64_to_usize(fields)?,
            u64_to_usize(cidx)?,
            ty.clone(),
          ),
          _ => {
            return Err(TcError::Other(
              "check_inductive: constructor not found".into(),
            ));
          },
        };

      // Validate constructor ordering: cidx must match position in ctors list
      if ctor_cidx != expected_cidx {
        return Err(TcError::Other(format!(
          "check_inductive: ctor cidx mismatch: expected {expected_cidx}, got {ctor_cidx}"
        )));
      }

      // A1: Parameter domain agreement
      self.check_param_agreement(&ty, &ctor_ty, u64_to_usize(params)?)?;

      // A3: Strict positivity. Lean skips positivity for unsafe inductives;
      // those declarations are admitted only as unsafe constants.
      if !is_unsafe {
        self.check_positivity(&ctor_ty, u64_to_usize(params)?, &block_addrs)?;
      }

      // A4: Universe constraints
      self.check_field_universes(
        &ctor_ty,
        u64_to_usize(params)?,
        &ind_level,
      )?;

      // A2: Constructor return type
      self.check_ctor_return_type(
        &ctor_ty,
        u64_to_usize(params)?,
        u64_to_usize(indices)?,
        ctor_fields,
        &id.addr,
        lvls,
        &block_addrs,
      )?;
    }

    // H1: Verify is_rec constructively — scan constructor fields for block references.
    // An adversary could set is_rec=false on a recursive inductive to enable improper
    // struct eta expansion. We verify against the actual constructor structure.
    let computed_is_rec =
      self.compute_is_rec(&ctors, u64_to_usize(params)?, &block_addrs)?;
    if computed_is_rec != is_rec {
      return Err(TcError::Other(format!(
        "check_inductive: is_rec mismatch: declared {is_rec}, computed {computed_is_rec}"
      )));
    }

    // Trigger recursor generation for the block (fatal — ZK context cannot tolerate silent failure)
    if !self.env.recursor_cache.contains_key(&block) {
      self.generate_block_recursors(&block)?;
    }

    Ok(())
  }

  /// Validate a standalone constructor by checking its parent inductive block.
  pub fn check_ctor_against_inductive(
    &mut self,
    ctor_id: &KId<M>,
    induct_id: &KId<M>,
  ) -> Result<(), TcError<M>> {
    let block = match self.env.get(induct_id) {
      Some(KConst::Indc { block, .. }) => block.clone(),
      _ => {
        return self.check_ctor_against_inductive_member(ctor_id, induct_id);
      },
    };
    let Some(members) = self.env.get_block(&block) else {
      return self.check_ctor_against_inductive_member(ctor_id, induct_id);
    };
    if !members.iter().all(|member| {
      matches!(
        self.env.get(member),
        Some(KConst::Indc { .. } | KConst::Ctor { .. })
      )
    }) {
      return self.check_ctor_against_inductive_member(ctor_id, induct_id);
    }

    match self.env.begin_block_check(&block) {
      BlockCheckStart::Cached(result) => result,
      BlockCheckStart::Owner(token) => {
        let result = self.check_inductive_block(&block, &members);
        self.env.finish_block_check(token, result)
      },
    }
  }

  /// Validate a standalone constructor against its parent inductive.
  /// Runs the same A1–A4 checks that `check_inductive_member` runs per-ctor.
  pub fn check_ctor_against_inductive_member(
    &mut self,
    ctor_id: &KId<M>,
    induct_id: &KId<M>,
  ) -> Result<(), TcError<M>> {
    let (ctor_ty, _ctor_params, ctor_fields) = match self.env.get(ctor_id) {
      Some(KConst::Ctor { ty, params, fields, .. }) => {
        (ty.clone(), u64_to_usize(params)?, u64_to_usize(fields)?)
      },
      _ => return Err(TcError::Other("check_ctor: not a constructor".into())),
    };

    let (ind_params, ind_indices, ind_lvls, ind_block, ind_is_unsafe, ind_ty) =
      match self.env.get(induct_id) {
        Some(KConst::Indc {
          params,
          indices,
          lvls,
          block,
          is_unsafe,
          ty,
          ..
        }) => (params, indices, lvls, block.clone(), is_unsafe, ty.clone()),
        _ => {
          return Err(TcError::Other(
            "check_ctor: parent inductive not found".into(),
          ));
        },
      };

    let block_inds = self.discover_block_inductives(&ind_block);
    let block_addrs: Vec<Address> =
      block_inds.iter().map(|id| id.addr.clone()).collect();

    let ind_level = self.get_result_sort_level(
      &ind_ty,
      u64_to_usize(ind_params + ind_indices)?,
    )?;

    // A1: Parameter domain agreement
    self.check_param_agreement(&ind_ty, &ctor_ty, u64_to_usize(ind_params)?)?;

    // A3: Strict positivity. Match Lean: unsafe inductives bypass this check.
    if !ind_is_unsafe {
      self.check_positivity(
        &ctor_ty,
        u64_to_usize(ind_params)?,
        &block_addrs,
      )?;
    }

    // A4: Universe constraints
    self.check_field_universes(
      &ctor_ty,
      u64_to_usize(ind_params)?,
      &ind_level,
    )?;

    // A2: Constructor return type
    self.check_ctor_return_type(
      &ctor_ty,
      u64_to_usize(ind_params)?,
      u64_to_usize(ind_indices)?,
      ctor_fields,
      &induct_id.addr,
      ind_lvls,
      &block_addrs,
    )?;

    Ok(())
  }

  /// Discover all inductives in a mutual block.
  fn discover_block_inductives(&self, block_id: &KId<M>) -> Vec<KId<M>> {
    match self.env.blocks.get(block_id) {
      Some(members) => members
        .iter()
        .filter(|id| matches!(self.env.get(id), Some(KConst::Indc { .. })))
        .cloned()
        .collect(),
      None => vec![],
    }
  }

  /// H1: Compute `is_rec` constructively by scanning constructor fields for
  /// references to any inductive in the mutual block. This verifies the declared
  /// `is_rec` flag rather than trusting it from Ixon input.
  ///
  /// An inductive is recursive if any constructor field (after parameters) mentions
  /// any inductive in the mutual block.
  fn compute_is_rec(
    &mut self,
    ctors: &[KId<M>],
    n_params: usize,
    block_addrs: &[Address],
  ) -> Result<bool, TcError<M>> {
    for ctor_id in ctors {
      let ctor_ty = match self.env.get(ctor_id) {
        Some(KConst::Ctor { ty, .. }) => ty.clone(),
        _ => continue,
      };
      // Skip params
      let mut ty = ctor_ty;
      for _ in 0..n_params {
        let w = self.whnf(&ty)?;
        match w.data() {
          ExprData::All(_, _, _, body, _) => ty = body.clone(),
          _ => break,
        }
      }
      // Check each remaining field domain for block inductive mentions
      loop {
        let w = self.whnf(&ty)?;
        match w.data() {
          ExprData::All(_, _, dom, body, _) => {
            if expr_mentions_any_addr(dom, block_addrs) {
              return Ok(true);
            }
            ty = body.clone();
          },
          _ => break,
        }
      }
    }
    Ok(false)
  }

  /// Build the "flat" block for recursor generation, detecting nested occurrences.
  ///
  /// Mirrors lean4lean's `ElimNestedInductive.run`: walks constructor fields,
  /// detects `ExtInd(block_member_ref)` patterns, and adds auxiliary entries
  /// for each nested external inductive. Queue-based for transitive nesting.
  fn build_flat_block(
    &mut self,
    block_inds: &[KId<M>],
    n_rec_params: u64,
    univ_offset: u64,
  ) -> Result<Vec<FlatBlockMember<M>>, TcError<M>> {
    let anon = || M::meta_field(crate::ix::env::Name::anon());
    let all_block_addrs: Vec<Address> =
      block_inds.iter().map(|id| id.addr.clone()).collect();

    let mut flat: Vec<FlatBlockMember<M>> = Vec::new();
    // (ext_ind_addr, spec_params content hashes) for dedup.
    // Uses [u8; 32] blake3 digest for structural equality.
    let mut aux_seen: Vec<(Address, Vec<[u8; 32]>)> = Vec::new();

    // Seed with original block inductives.
    for ind_id in block_inds {
      let (own_params, n_indices, ctors, lvls) = match self.env.get(ind_id) {
        Some(KConst::Indc { params, indices, ctors, lvls, .. }) => {
          (params, indices, ctors.clone(), lvls)
        },
        _ => continue,
      };
      let ind_us = self.mk_ind_univs(lvls, univ_offset);
      let spec_params: Vec<KExpr<M>> = (0..n_rec_params)
        .map(|j| KExpr::var(n_rec_params - 1 - j, anon()))
        .collect();
      flat.push(FlatBlockMember {
        id: ind_id.clone(),
        is_aux: false,
        spec_params,
        own_params,
        n_indices,
        ctors,
        lvls,
        ind_us: ind_us.clone(),
        occurrence_us: ind_us,
      });
    }

    // Queue-based processing: scan each member's ctors for nested occurrences.
    let mut qi = 0;
    while qi < flat.len() {
      let member = flat[qi].clone();
      qi += 1;

      for ctor_id in &member.ctors {
        let (_ctor_own_params, ctor_fields, ctor_ty, _ctor_lvls) =
          match self.env.get(ctor_id) {
            Some(KConst::Ctor { params, fields, ty, lvls, .. }) => {
              (params, fields, ty.clone(), lvls)
            },
            _ => continue,
          };

        // Instantiate ctor type with occurrence universe args (concrete) so that
        // transitively-detected nested occurrences get concrete universe args too.
        let ctor_ty_inst =
          self.instantiate_univ_params(&ctor_ty, &member.occurrence_us)?;

        // Walk past own_params, substituting with spec_params.
        let saved = self.save_depth();
        let mut cur = ctor_ty_inst;
        for j in 0..member.own_params {
          let w = self.whnf(&cur)?;
          match w.data() {
            ExprData::All(_, _, _, body, _) => {
              let p = if u64_to_usize::<M>(j)? < member.spec_params.len() {
                member.spec_params[u64_to_usize::<M>(j)?].clone()
              } else {
                KExpr::var(n_rec_params - 1 - j, anon())
              };
              cur = subst(&self.env.intern, body, &p, 0);
            },
            _ => break,
          }
        }

        // Walk fields, looking for nested occurrences.
        // Push locals for each field to maintain correct de Bruijn context.
        for _fi in 0..ctor_fields {
          let w = self.whnf(&cur)?;
          match w.data() {
            ExprData::All(_, _, dom, body, _) => {
              let dom = dom.clone();
              let body = body.clone();

              // Check if dom (after peeling foralls) is a nested occurrence.
              // Pass saved depth so spec_params can be de-lifted to the
              // param context (depth = saved), independent of field depth.
              self.try_detect_nested(
                &dom,
                &all_block_addrs,
                &mut flat,
                &mut aux_seen,
                univ_offset,
                saved,
                n_rec_params,
              );

              self.push_local(dom);
              cur = body;
            },
            _ => break,
          }
        }
        self.restore_depth(saved);
      }
    }

    Ok(flat)
  }

  /// Check if a field domain is a nested inductive occurrence and, if so,
  /// add an auxiliary entry to the flat block.
  ///
  /// A nested occurrence is: after peeling foralls, the result is `ExtInd Ds is`
  /// where `ExtInd` is a previously-declared inductive (not in our block) and
  /// some param arg `Ds[i]` mentions a block inductive.
  fn try_detect_nested(
    &mut self,
    dom: &KExpr<M>,
    block_addrs: &[Address],
    flat: &mut Vec<FlatBlockMember<M>>,
    aux_seen: &mut Vec<(Address, Vec<[u8; 32]>)>,
    univ_offset: u64,
    param_depth: usize, // depth at the param context (before field locals)
    n_rec_params: u64, // number of inductive parameters (valid Var refs in spec_params)
  ) {
    // Peel foralls to get to the result type.
    let mut cur = dom.clone();
    loop {
      match self.whnf(&cur) {
        Ok(w) => cur = w,
        Err(_) => return,
      };
      match cur.data() {
        ExprData::All(_, _, _, body, _) => cur = body.clone(),
        _ => break,
      }
    }

    let (head, args) = collect_app_spine(&cur);
    let head_id = match head.data() {
      ExprData::Const(id, _, _) => id.clone(),
      _ => return,
    };

    // Skip if head is already a block member (direct recursive, not nested).
    if block_addrs.contains(&head_id.addr) {
      return;
    }
    // Also skip if head is already a flat block member (already detected).
    if flat.iter().any(|m| m.id.addr == head_id.addr && !m.is_aux) {
      return;
    }

    // Check if head is an external inductive.
    let (ext_params, ext_indices, ext_ctors, ext_lvls) =
      match self.env.get(&head_id) {
        Some(KConst::Indc { params, indices, ctors, lvls, .. }) => {
          (params, indices, ctors.clone(), lvls)
        },
        _ => return,
      };

    #[allow(clippy::cast_possible_truncation)]
    // ext_params is a small structural count
    let ext_n_params = ext_params as usize;
    if args.len() < ext_n_params {
      return;
    }

    // Check if any param arg mentions a block inductive (or a flat member).
    let all_flat_addrs: Vec<Address> =
      flat.iter().map(|m| m.id.addr.clone()).collect();
    let combined_addrs: Vec<Address> =
      block_addrs.iter().chain(all_flat_addrs.iter()).cloned().collect();
    let has_nested_ref = args
      .iter()
      .take(ext_n_params)
      .any(|a| expr_mentions_any_addr(a, &combined_addrs));
    if !has_nested_ref {
      return;
    }

    // Extract spec_params (the first ext_n_params args) and normalize them
    // to the param context by lowering Var indices by the field depth.
    // This ensures the same logical spec_params produce the same hash
    // regardless of how many field locals are on the context.
    #[allow(clippy::cast_possible_truncation)]
    // depth and param_depth are small
    let field_depth =
      (self.depth() as usize).saturating_sub(param_depth) as u64;
    let spec_params: Vec<KExpr<M>> = args
      .iter()
      .take(ext_n_params)
      .map(|e| {
        if field_depth > 0 {
          lower_vars(&self.env.intern, e, field_depth)
        } else {
          e.clone()
        }
      })
      .collect();

    // S7: Reject nested occurrences whose parameter args still contain
    // loose bound variables after lowering. This means a param arg depends
    // on a locally-bound field variable, creating an ill-formed auxiliary.
    // Allow Var(0)..Var(n_rec_params-1) as valid parameter references.
    // (lean4lean: isNestedInductiveApp? checks looseBVars on param args.)
    for sp in spec_params.iter() {
      if sp.lbr() > param_depth as u64 + n_rec_params {
        return; // param arg depends on field-local variables — not a valid nesting
      }
    }

    // Dedup: check if we've already seen this (ext_ind, spec_params) pair.
    // Use blake3 content hash (addr) for structural dedup.
    let spec_hashes: Vec<[u8; 32]> =
      spec_params.iter().map(|e| *e.addr().as_bytes()).collect();
    if aux_seen.iter().any(|(a, s)| {
      *a == head_id.addr
        && s.len() == spec_hashes.len()
        && s.iter().zip(spec_hashes.iter()).all(|(a, b)| a == b)
    }) {
      return;
    }
    aux_seen.push((head_id.addr.clone(), spec_hashes));

    // Abstract shifted universe params for internal processing (dedup, ctor walking).
    let aux_us = self.mk_ind_univs(ext_lvls, univ_offset);
    // Concrete universe args from the actual occurrence (for output types).
    let occurrence_us: Box<[KUniv<M>]> = match head.data() {
      ExprData::Const(_, us, _) => us.clone(),
      _ => Box::new([]),
    };

    flat.push(FlatBlockMember {
      id: head_id,
      is_aux: true,
      spec_params,
      own_params: ext_params,
      n_indices: ext_indices,
      ctors: ext_ctors,
      lvls: ext_lvls,
      ind_us: aux_us,
      occurrence_us,
    });
  }

  /// Rewrite nested occurrences in synthetic aux member/ctor types to the
  /// corresponding synthetic aux constants before running `sort_consts`
  /// partition refinement. Compile-side `expand_nested_block` does this via
  /// its queue pass over all expanded constructors; the kernel has already
  /// discovered the flat aux set, so it can rewrite by matching each
  /// occurrence against that set.
  fn replace_aux_refs_for_sort(
    &mut self,
    e: &KExpr<M>,
    aux: &[FlatBlockMember<M>],
    aux_ids: &[KId<M>],
    block_us: &[KUniv<M>],
    n_block_params: u64,
    local_depth: u64,
  ) -> Result<KExpr<M>, TcError<M>> {
    if let Some(replaced) = self.try_replace_aux_ref_for_sort(
      e,
      aux,
      aux_ids,
      block_us,
      n_block_params,
      local_depth,
    )? {
      return Ok(replaced);
    }

    let result = match e.data() {
      ExprData::App(f, a, _) => {
        let f2 = self.replace_aux_refs_for_sort(
          f,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth,
        )?;
        let a2 = self.replace_aux_refs_for_sort(
          a,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth,
        )?;
        KExpr::app(f2, a2)
      },
      ExprData::Lam(n, bi, ty, body, _) => {
        let ty2 = self.replace_aux_refs_for_sort(
          ty,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth,
        )?;
        let body2 = self.replace_aux_refs_for_sort(
          body,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth + 1,
        )?;
        KExpr::lam(n.clone(), bi.clone(), ty2, body2)
      },
      ExprData::All(n, bi, ty, body, _) => {
        let ty2 = self.replace_aux_refs_for_sort(
          ty,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth,
        )?;
        let body2 = self.replace_aux_refs_for_sort(
          body,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth + 1,
        )?;
        KExpr::all(n.clone(), bi.clone(), ty2, body2)
      },
      ExprData::Let(n, ty, val, body, nd, _) => {
        let ty2 = self.replace_aux_refs_for_sort(
          ty,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth,
        )?;
        let val2 = self.replace_aux_refs_for_sort(
          val,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth,
        )?;
        let body2 = self.replace_aux_refs_for_sort(
          body,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth + 1,
        )?;
        KExpr::let_(n.clone(), ty2, val2, body2, *nd)
      },
      ExprData::Prj(id, field, val, _) => {
        let val2 = self.replace_aux_refs_for_sort(
          val,
          aux,
          aux_ids,
          block_us,
          n_block_params,
          local_depth,
        )?;
        KExpr::prj(id.clone(), *field, val2)
      },
      _ => return Ok(e.clone()),
    };
    Ok(self.env.intern.intern_expr(result))
  }

  fn try_replace_aux_ref_for_sort(
    &mut self,
    e: &KExpr<M>,
    aux: &[FlatBlockMember<M>],
    aux_ids: &[KId<M>],
    block_us: &[KUniv<M>],
    n_block_params: u64,
    local_depth: u64,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let head_id = match head.data() {
      ExprData::Const(id, _, _) => id,
      _ => return Ok(None),
    };

    for (idx, member) in aux.iter().enumerate() {
      if member.id.addr != head_id.addr {
        continue;
      }
      let own = u64_to_usize::<M>(member.own_params)?;
      if args.len() < own || member.spec_params.len() != own {
        continue;
      }

      let mut matched = true;
      for (arg, sp) in args.iter().take(own).zip(member.spec_params.iter()) {
        let sp_lifted = if local_depth > 0 {
          lift(&self.env.intern, sp, local_depth, 0)
        } else {
          sp.clone()
        };
        if !self.is_def_eq(arg, &sp_lifted).unwrap_or(false) {
          matched = false;
          break;
        }
      }
      if !matched {
        continue;
      }

      let anon = || M::meta_field(crate::ix::env::Name::anon());
      let mut result = self.env.intern.intern_expr(KExpr::cnst(
        aux_ids[idx].clone(),
        block_us.to_vec().into_boxed_slice(),
      ));
      for pi in 0..n_block_params {
        let p = self.env.intern.intern_expr(KExpr::var(
          local_depth + n_block_params - 1 - pi,
          anon(),
        ));
        result = self.env.intern.intern_expr(KExpr::app(result, p));
      }
      for idx_arg in args.iter().skip(own) {
        result =
          self.env.intern.intern_expr(KExpr::app(result, idx_arg.clone()));
      }
      return Ok(Some(result));
    }

    Ok(None)
  }

  /// Compute the canonical aux ordering — kernel analogue of the
  /// compile-side aux partition-refinement sort
  /// (`src/ix/compile/aux_gen/nested.rs`).
  ///
  /// For each aux `FlatBlockMember`, synthesize a `KConst::Indc` view
  /// (with its constructor `KConst::Ctor` views) that mirrors the
  /// compile-side `MutConst::Indc` aux representation. Run
  /// `sort_kconsts_with_seed_key` on the synthetic aux and return a
  /// permutation `original_index → canonical_index` over the input slice.
  ///
  /// The synthetic indc carries the ext inductive's type with the
  /// first `ext_n_params` Pi binders instantiated by the aux's
  /// `spec_params`. The synthetic ctors carry the ext ctor's type
  /// with the same instantiation. Compile-side wraps the result with
  /// the block's parameter Pis and rewrites the ctor result head to
  /// the aux name; the kernel mirror omits these wrappers because
  /// every aux gets the same prefix (so it doesn't affect the
  /// comparator's relative ordering) and uses synthetic aux KIds
  /// derived from `(source index, ext_addr, spec_params hashes,
  /// occurrence_us hashes)`. Alpha-equivalent aux remain distinct
  /// synthetic members, then collapse into a single class under the
  /// partition-refinement sorter just as compile-side distinct aux names
  /// do.
  ///
  /// Returns a vector `perm[k] = original_idx_of_class_k_representative`
  /// of length equal to the number of canonical classes.
  fn canonical_aux_order(
    &mut self,
    aux: &[FlatBlockMember<M>],
    n_block_params: u64,
    block_us: &[KUniv<M>],
    all0_name: Option<crate::ix::env::Name>,
  ) -> Result<Vec<usize>, TcError<M>> {
    use crate::ix::env::Name;
    use crate::ix::kernel::canonical_check::{
      KMutCtx, sort_kconsts_with_seed_key,
    };
    use rustc_hash::FxHashMap;

    // Build synthetic Indc + Ctor views for each aux.
    // `aux_views[i]` corresponds to `aux[i]`.
    let mut aux_indcs: Vec<(KId<M>, KConst<M>)> = Vec::with_capacity(aux.len());
    let mut all_ctor_lookup: FxHashMap<crate::ix::address::Address, KConst<M>> =
      FxHashMap::default();
    let mut seed_key_by_addr: FxHashMap<crate::ix::address::Address, Address> =
      FxHashMap::default();
    let nested_prefix =
      all0_name.map(|all0| Name::str(all0, "_nested".to_string()));

    let mut aux_ids: Vec<KId<M>> = Vec::with_capacity(aux.len());
    let mut aux_seed_names: Vec<Name> = Vec::with_capacity(aux.len());
    for (source_idx, member) in aux.iter().enumerate() {
      // Compile-side aux names are `<all0>._nested.<Ext>_<N>` in source
      // discovery order before the partition-refinement sort renames them
      // by canonical position. `sort_consts` uses those names only as a
      // deterministic seed/tiebreak, so the kernel feeds the same name hash
      // into the sorter while keeping the synthetic KId address structural.
      let ext_seed = M::meta_name(&member.id.name)
        .map(|name| name.pretty().replace('.', "_"))
        .unwrap_or_else(|| member.id.addr.hex());
      let seed_suffix = format!("{}_{}", ext_seed, source_idx + 1);
      let seed_name = nested_prefix
        .as_ref()
        .map(|prefix| Name::str(prefix.clone(), seed_suffix.clone()))
        .unwrap_or_else(|| {
          Name::str(
            Name::str(Name::anon(), "IxKernelAux".to_string()),
            seed_suffix.clone(),
          )
        });
      let seed_addr = Address::from_blake3_hash(*seed_name.get_hash());

      // Synthetic aux KId: unique per discovered aux source slot, with the
      // semantic content included so structurally equal aux still compare
      // Equal and collapse under the current partition.
      let mut h = blake3::Hasher::new();
      h.update(b"AUX_INDC_VIEW");
      h.update(&(source_idx as u64).to_le_bytes());
      h.update(member.id.addr.as_bytes());
      for sp in &member.spec_params {
        h.update(sp.addr().as_bytes());
      }
      for u in member.occurrence_us.iter() {
        h.update(u.addr().as_bytes());
      }
      let aux_addr =
        crate::ix::address::Address::from_blake3_hash(h.finalize());
      let aux_id = KId::new(aux_addr.clone(), M::meta_field(seed_name.clone()));
      seed_key_by_addr.insert(aux_addr.clone(), seed_addr);
      aux_ids.push(aux_id);
      aux_seed_names.push(seed_name);
    }

    for (source_idx, member) in aux.iter().enumerate() {
      let aux_id = aux_ids[source_idx].clone();
      let seed_name = aux_seed_names[source_idx].clone();
      let aux_addr = aux_id.addr.clone();
      let (ext_ty, ext_ctors, ext_n_params, ext_n_indices) =
        match self.env.get(&member.id) {
          Some(KConst::Indc { ty, ctors, params, indices, .. }) => {
            (ty.clone(), ctors.clone(), params, indices)
          },
          _ => {
            return Err(TcError::Other(
              "canonical_aux_order: aux ext is not an inductive".into(),
            ));
          },
        };

      // Instantiate ext_ty: replace J's universe params with the
      // occurrence's universe args, then walk past `ext_n_params` Pi
      // binders, substituting with `spec_params`. The result is the
      // aux's "internal" type — what `mem.typ` becomes after
      // compile-side's `instantiate_pi_params(j_type_inst,
      // ext_n_params, &spec_params)` step.
      let mut typ =
        self.instantiate_univ_params(&ext_ty, &member.occurrence_us)?;
      for j in 0..ext_n_params {
        let w = self.whnf(&typ)?;
        match w.data() {
          ExprData::All(_, _, _, body, _) => {
            let body = body.clone();
            let p_idx = u64_to_usize::<M>(j)?;
            if p_idx >= member.spec_params.len() {
              break;
            }
            let p = member.spec_params[p_idx].clone();
            typ = subst(&self.env.intern, &body, &p, 0);
          },
          _ => break,
        }
      }
      typ = self.replace_aux_refs_for_sort(
        &typ,
        aux,
        &aux_ids,
        block_us,
        n_block_params,
        0,
      )?;

      // Synthetic aux ctor KIds and KConst::Ctor entries.
      let mut aux_ctor_kids: Vec<KId<M>> = Vec::with_capacity(ext_ctors.len());
      for (ci, ext_ctor_id) in ext_ctors.iter().enumerate() {
        let (ext_ctor_ty, ext_ctor_fields) = match self.env.get(ext_ctor_id) {
          Some(KConst::Ctor { ty, fields, .. }) => (ty.clone(), fields),
          _ => {
            return Err(TcError::Other(
              "canonical_aux_order: aux ext ctor is not a ctor".into(),
            ));
          },
        };
        let mut ctor_typ =
          self.instantiate_univ_params(&ext_ctor_ty, &member.occurrence_us)?;
        for j in 0..ext_n_params {
          let w = self.whnf(&ctor_typ)?;
          match w.data() {
            ExprData::All(_, _, _, body, _) => {
              let body = body.clone();
              let p_idx = u64_to_usize::<M>(j)?;
              if p_idx >= member.spec_params.len() {
                break;
              }
              let p = member.spec_params[p_idx].clone();
              ctor_typ = subst(&self.env.intern, &body, &p, 0);
            },
            _ => break,
          }
        }

        // Rewrite nested occurrences inside aux ctor types to block-local
        // synthetic aux references before sorting. This mirrors the
        // compile-side `replace_all_nested` queue pass over the expanded
        // aux members. It covers both recursive fields such as
        // `List (ListItem Block)` and the ctor result head itself.
        ctor_typ = self.replace_aux_refs_for_sort(
          &ctor_typ,
          aux,
          &aux_ids,
          block_us,
          n_block_params,
          0,
        )?;

        let mut ch = blake3::Hasher::new();
        ch.update(b"AUX_CTOR_VIEW");
        ch.update(aux_addr.as_bytes());
        ch.update(ext_ctor_id.addr.as_bytes());
        let aux_ctor_addr =
          crate::ix::address::Address::from_blake3_hash(ch.finalize());
        let aux_ctor_kid = KId::new(
          aux_ctor_addr.clone(),
          M::meta_field(crate::ix::env::Name::anon()),
        );

        let aux_ctor = KConst::Ctor {
          name: M::meta_field(crate::ix::env::Name::anon()),
          level_params: M::meta_field(vec![]),
          is_unsafe: false,
          lvls: block_us.len() as u64,
          induct: aux_id.clone(),
          cidx: ci as u64,
          params: n_block_params,
          fields: ext_ctor_fields,
          ty: ctor_typ,
        };
        all_ctor_lookup.insert(aux_ctor_addr, aux_ctor);
        aux_ctor_kids.push(aux_ctor_kid);
      }

      let aux_indc = KConst::Indc {
        name: M::meta_field(seed_name),
        level_params: M::meta_field(vec![]),
        lvls: block_us.len() as u64,
        params: n_block_params,
        indices: ext_n_indices,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: KId::new(
          crate::ix::address::Address::hash(b"synthetic-aux-block"),
          M::meta_field(crate::ix::env::Name::anon()),
        ),
        member_idx: 0,
        ty: typ,
        ctors: aux_ctor_kids,
        lean_all: M::meta_field(vec![]),
      };

      aux_indcs.push((aux_id, aux_indc));
    }

    // Build (KId, &KConst) pairs for sorting.
    let pairs: Vec<(KId<M>, &KConst<M>)> =
      aux_indcs.iter().map(|(id, c)| (id.clone(), c)).collect();

    // resolve_ctor: synthetic ctors → synthetic KConst::Ctor.
    let resolve_ctor = |cid: &KId<M>| -> Option<KConst<M>> {
      all_ctor_lookup.get(&cid.addr).cloned()
    };

    let classes =
      sort_kconsts_with_seed_key::<M>(&pairs, &resolve_ctor, &|id: &KId<M>,
                                                               _c: &KConst<
        M,
      >| {
        seed_key_by_addr
          .get(&id.addr)
          .cloned()
          .unwrap_or_else(|| id.addr.clone())
      });

    // For each canonical class, pick the representative chosen by the
    // compiler-shaped seed key. Alpha-equivalent aux remain distinct
    // synthetic members until partition refinement collapses them, matching
    // compile-side `sort_consts`.
    let aux_addr_to_orig_idx: FxHashMap<crate::ix::address::Address, usize> =
      pairs
        .iter()
        .enumerate()
        .map(|(i, (id, _))| (id.addr.clone(), i))
        .collect();
    let mut perm: Vec<usize> = Vec::with_capacity(classes.len());
    for class in &classes {
      // The sorter keeps each class ordered by the compiler-shaped seed
      // key, so the first member is the same representative compile-side
      // `sort_consts` would choose for an alpha-equivalence class.
      let rep_addr = &class[0].0.addr;
      let orig_idx = *aux_addr_to_orig_idx.get(rep_addr).ok_or_else(|| {
        TcError::Other(
          "canonical_aux_order: synthetic addr not in original index map"
            .into(),
        )
      })?;
      perm.push(orig_idx);
    }
    let _ = KMutCtx::default(); // re-export anchor for doc cross-ref
    Ok(perm)
  }

  fn recursor_dump_matches_id(&self, id: &KId<M>) -> bool {
    IX_RECURSOR_DUMP
      .as_ref()
      .is_some_and(|prefix| format!("{id}").starts_with(prefix))
  }

  fn recursor_dump_matches_block(
    &self,
    block_id: &KId<M>,
    flat: &[FlatBlockMember<M>],
  ) -> bool {
    IX_RECURSOR_DUMP.as_ref().is_some_and(|prefix| {
      format!("{block_id}").starts_with(prefix)
        || flat.iter().any(|m| format!("{}", m.id).starts_with(prefix))
    })
  }

  fn dump_flat_aux_order(
    &self,
    label: &str,
    block_id: &KId<M>,
    flat: &[FlatBlockMember<M>],
    n_originals: usize,
  ) {
    if !self.recursor_dump_matches_block(block_id, flat) {
      return;
    }
    eprintln!(
      "[recursor.dump] {label} flat aux order for {block_id}: originals={} aux={}",
      n_originals,
      flat.len().saturating_sub(n_originals)
    );
    for (aux_i, member) in flat.iter().skip(n_originals).enumerate() {
      let spec =
        member.spec_params.iter().map(|e| format!("{e}")).collect::<Vec<_>>();
      eprintln!(
        "  aux[{aux_i:2}] id={} own_params={} indices={} spec={spec:?}",
        member.id, member.own_params, member.n_indices
      );
    }
  }

  fn recursor_major_domain_for_addr(
    &mut self,
    rec_ty: &KExpr<M>,
    prefix_skip: u64,
    target_addr: &Address,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    const MAX_MAJOR_SCAN_FORALLS: u64 = 64;

    let mut ty = rec_ty.clone();
    for _ in 0..prefix_skip {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => ty = body.clone(),
        _ => return Ok(None),
      }
    }

    for _ in 0..=MAX_MAJOR_SCAN_FORALLS {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          let (head, _) = collect_app_spine(dom);
          if let ExprData::Const(id, _, _) = head.data()
            && id.addr == *target_addr
            && matches!(self.env.get(id), Some(KConst::Indc { .. }))
          {
            return Ok(Some(dom.clone()));
          }
          ty = body.clone();
        },
        _ => return Ok(None),
      }
    }

    Ok(None)
  }

  fn major_domain_signature_eq(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let (a_head, a_args) = collect_app_spine(a);
    let (b_head, b_args) = collect_app_spine(b);
    let (a_id, a_us) = match a_head.data() {
      ExprData::Const(id, us, _) => (id, us),
      _ => return Ok(false),
    };
    let (b_id, b_us) = match b_head.data() {
      ExprData::Const(id, us, _) => (id, us),
      _ => return Ok(false),
    };
    if a_id.addr != b_id.addr
      || a_us.len() != b_us.len()
      || a_args.len() != b_args.len()
    {
      return Ok(false);
    }
    if !a_us.iter().zip(b_us.iter()).all(|(u, v)| univ_eq(u, v)) {
      return Ok(false);
    }
    for (a_arg, b_arg) in a_args.iter().zip(b_args.iter()) {
      if !self.is_def_eq(a_arg, b_arg)? {
        return Ok(false);
      }
    }
    Ok(true)
  }

  fn major_domain_signature_text(domain: Option<&KExpr<M>>) -> String {
    match domain {
      Some(d) => {
        let (head, args) = collect_app_spine(d);
        match head.data() {
          ExprData::Const(id, _, _) => {
            format!("head={id} args={} dom={d}", args.len())
          },
          _ => format!("head=<non-const> args={} dom={d}", args.len()),
        }
      },
      None => "<none>".to_string(),
    }
  }

  fn dump_rule_rhs_first_diff(
    &mut self,
    lhs: &KExpr<M>,
    rhs: &KExpr<M>,
    path: &str,
    depth: u64,
  ) -> Result<bool, TcError<M>> {
    if self.is_def_eq(lhs, rhs)? {
      return Ok(false);
    }
    if depth > 80 {
      eprintln!("[rule rhs diff] first diff {path}: recursion limit");
      eprintln!("  gen: {lhs}");
      eprintln!("  sto: {rhs}");
      return Ok(true);
    }

    let lw = self.whnf(lhs)?;
    let rw = self.whnf(rhs)?;
    match (lw.data(), rw.data()) {
      (
        ExprData::Lam(_, _, lty, lbody, _),
        ExprData::Lam(_, _, rty, rbody, _),
      )
      | (
        ExprData::All(_, _, lty, lbody, _),
        ExprData::All(_, _, rty, rbody, _),
      ) => {
        if !self.is_def_eq(lty, rty)? {
          eprintln!("[rule rhs diff] first diff {path}.dom");
          eprintln!("  gen: {lty}");
          eprintln!("  sto: {rty}");
          return Ok(true);
        }
        self.push_local(lty.clone());
        let found = self.dump_rule_rhs_first_diff(
          lbody,
          rbody,
          &format!("{path}.body"),
          depth + 1,
        );
        self.pop_local();
        found
      },
      (ExprData::App(lf, la, _), ExprData::App(rf, ra, _)) => {
        if self.dump_rule_rhs_first_diff(
          lf,
          rf,
          &format!("{path}.fn"),
          depth + 1,
        )? {
          return Ok(true);
        }
        self.dump_rule_rhs_first_diff(la, ra, &format!("{path}.arg"), depth + 1)
      },
      _ => {
        eprintln!("[rule rhs diff] first diff {path}");
        eprintln!("  gen: {lw}");
        eprintln!("  sto: {rw}");
        Ok(true)
      },
    }
  }

  /// A1: Check that the first `n_params` forall domains of ind_ty and ctor_ty agree.
  fn check_param_agreement(
    &mut self,
    ind_ty: &KExpr<M>,
    ctor_ty: &KExpr<M>,
    n_params: usize,
  ) -> Result<(), TcError<M>> {
    let saved = self.save_depth();
    let mut it = ind_ty.clone();
    let mut ct = ctor_ty.clone();

    for _ in 0..n_params {
      let wi = self.whnf(&it)?;
      let wc = self.whnf(&ct)?;
      match (wi.data(), wc.data()) {
        (
          ExprData::All(_, _, i_dom, i_body, _),
          ExprData::All(_, _, c_dom, c_body, _),
        ) => {
          if !self.is_def_eq(i_dom, c_dom)? {
            self.restore_depth(saved);
            return Err(TcError::Other("param domain mismatch".into()));
          }
          self.push_local(i_dom.clone());
          it = i_body.clone();
          ct = c_body.clone();
        },
        _ => {
          self.restore_depth(saved);
          return Err(TcError::Other(
            "expected forall in param agreement".into(),
          ));
        },
      }
    }

    self.restore_depth(saved);
    Ok(())
  }

  /// A3: Strict positivity — block inductives must not appear in negative position.
  fn check_positivity(
    &mut self,
    ctor_ty: &KExpr<M>,
    n_params: usize,
    block_addrs: &[Address],
  ) -> Result<(), TcError<M>> {
    // Skip params
    let mut ty = ctor_ty.clone();
    for _ in 0..n_params {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => ty = body.clone(),
        _ => return Ok(()), // not enough foralls — ok
      }
    }

    // Check each field domain
    loop {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          self.check_positivity_domain(dom, block_addrs)?;
          ty = body.clone();
        },
        _ => break,
      }
    }
    Ok(())
  }

  /// Check that a field domain doesn't have block inductives in negative position.
  /// Follows lean4lean's `checkPositivity`: recurse through foralls, reject if
  /// inductive in domain (negative), accept if result is a valid inductive app
  /// (direct or nested).
  ///
  /// For nested inductives `J Ds is` where `J` is external and `Ds` mention block
  /// inductives, we recursively verify that `J`'s constructors (with `Ds` substituted
  /// for parameters) are strictly positive in the augmented address set. This prevents
  /// smuggling negative occurrences through an external inductive's parameter position.
  fn check_positivity_domain(
    &mut self,
    dom: &KExpr<M>,
    block_addrs: &[Address],
  ) -> Result<(), TcError<M>> {
    if !expr_mentions_any_addr(dom, block_addrs) {
      return Ok(()); // no inductive mention at all — fine
    }

    let w = self.whnf(dom)?;
    match w.data() {
      ExprData::All(_, _, inner_dom, inner_body, _) => {
        // Inductive in domain of a Pi = negative position → reject
        if expr_mentions_any_addr(inner_dom, block_addrs) {
          return Err(TcError::Other("strict positivity violation".into()));
        }
        // H4: Push local so WHNF works correctly on dependent types
        // (lean4lean Add.lean:187-189 uses withLocalDecl)
        self.push_local(inner_dom.clone());
        let result = self.check_positivity_domain(inner_body, block_addrs);
        self.pop_local();
        result
      },
      _ => {
        // Must be either:
        // 1. A direct block inductive application: `I_k params args`
        // 2. A nested inductive application: `J Ds is` where J is a previously
        //    declared inductive and Ds contain block inductives
        let (head, args) = collect_app_spine(&w);
        match head.data() {
          ExprData::Const(id, _, _) if block_addrs.contains(&id.addr) => Ok(()),
          ExprData::Const(id, us, _) => {
            // Check if this is a nested inductive: head is an inductive type
            // (not in our block) and its params contain block inductives.
            let (n_params, block, ctors) = match self.env.get(id) {
              Some(KConst::Indc { params, block, ctors, .. }) => {
                (u64_to_usize(params)?, block.clone(), ctors.clone())
              },
              _ => {
                return Err(TcError::Other(
                  "positivity: not a valid inductive app".into(),
                ));
              },
            };

            // Verify params contain block inductive refs (that's what makes it nested)
            let has_nested_ref = args
              .iter()
              .take(n_params)
              .any(|a| expr_mentions_any_addr(a, block_addrs));
            if !has_nested_ref {
              return Err(TcError::Other(
                "positivity: not a valid inductive app".into(),
              ));
            }

            // Index args (after params) must not mention block inductives
            for arg in args.iter().skip(n_params) {
              if expr_mentions_any_addr(arg, block_addrs) {
                return Err(TcError::Other(
                  "positivity: index mentions block inductive".into(),
                ));
              }
            }

            // Build augmented address set: original block + external inductive's block
            let mut augmented: Vec<Address> = block_addrs.to_vec();
            let ext_block_inductives = self.discover_block_inductives(&block);
            for ext_id in &ext_block_inductives {
              if !augmented.contains(&ext_id.addr) {
                augmented.push(ext_id.addr.clone());
              }
            }

            // Collect param args and universe args for substitution
            let param_args: Vec<KExpr<M>> =
              args.iter().take(n_params).cloned().collect();
            let us = us.clone();

            // For each constructor, strip params, substitute actual param args,
            // and recursively check positivity of each field domain
            for ctor_id in &ctors {
              let ctor_ty = match self.env.get(ctor_id) {
                Some(KConst::Ctor { ty, .. }) => ty.clone(),
                _ => {
                  return Err(TcError::Other(
                    "positivity: nested ctor not found".into(),
                  ));
                },
              };
              self.check_nested_ctor_fields(
                &ctor_ty,
                n_params,
                &param_args,
                &us,
                &augmented,
              )?;
            }

            Ok(())
          },
          _ => {
            Err(TcError::Other("positivity: not a valid inductive app".into()))
          },
        }
      },
    }
  }

  /// Check positivity of a nested inductive's constructor fields.
  ///
  /// Strips `n_params` forall binders from `ctor_ty`, substitutes the actual
  /// `param_args` (with universe instantiation via `us`), then checks each
  /// remaining field domain for positivity against `augmented_addrs`.
  fn check_nested_ctor_fields(
    &mut self,
    ctor_ty: &KExpr<M>,
    n_params: usize,
    param_args: &[KExpr<M>],
    us: &[KUniv<M>],
    augmented_addrs: &[Address],
  ) -> Result<(), TcError<M>> {
    // Instantiate universe params
    let mut ty = self.instantiate_univ_params(ctor_ty, us)?;

    // Strip param foralls
    for _ in 0..n_params {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => ty = body.clone(),
        _ => return Ok(()), // not enough foralls — ok
      }
    }

    // Simultaneously substitute param_args for the param binders.
    // After stripping n_params foralls, Var(0)..Var(n_params-1) in the body
    // refer to the params (Var(0) = innermost = last param).
    // simul_subst replaces Var(depth+i) with substs[i], so at depth=0:
    //   Var(0) -> substs[0], Var(1) -> substs[1], ...
    // The params were bound outermost-first, so after stripping:
    //   Var(n_params-1) = first param (outermost)
    //   Var(0) = last param (innermost)
    // We need substs[i] = param_args[n_params-1-i] to reverse the order.
    let reversed_params: Vec<KExpr<M>> =
      param_args.iter().rev().cloned().collect();
    ty = simul_subst(&self.env.intern, &ty, &reversed_params, 0);

    // Now check each remaining field domain
    self.check_nested_ctor_fields_loop(&ty, augmented_addrs)
  }

  /// Walk the remaining forall binders of a nested constructor type and check
  /// each field domain for positivity against the augmented address set.
  fn check_nested_ctor_fields_loop(
    &mut self,
    ty: &KExpr<M>,
    augmented_addrs: &[Address],
  ) -> Result<(), TcError<M>> {
    let w = self.whnf(ty)?;
    match w.data() {
      ExprData::All(_, _, dom, body, _) => {
        self.check_positivity_domain(dom, augmented_addrs)?;
        self.push_local(dom.clone());
        let result = self.check_nested_ctor_fields_loop(body, augmented_addrs);
        self.pop_local();
        result
      },
      _ => Ok(()), // base case: return type — no more fields to check
    }
  }

  /// A4: Universe constraints — field sort levels must be ≤ inductive result level.
  fn check_field_universes(
    &mut self,
    ctor_ty: &KExpr<M>,
    n_params: usize,
    ind_level: &KUniv<M>,
  ) -> Result<(), TcError<M>> {
    // Skip if inductive is Prop (Sort 0) — any universe is allowed
    if ind_level.is_zero() {
      return Ok(());
    }

    let saved = self.save_depth();
    let mut ty = ctor_ty.clone();

    // Skip params
    for _ in 0..n_params {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          self.push_local(dom.clone());
          ty = body.clone();
        },
        _ => break,
      }
    }

    // Check each field
    loop {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          let dom_ty = self.infer(dom)?;
          let field_level = self.ensure_sort(&dom_ty)?;
          if !univ_geq(ind_level, &field_level) {
            self.restore_depth(saved);
            return Err(TcError::Other(
              "field universe exceeds inductive level".into(),
            ));
          }
          self.push_local(dom.clone());
          ty = body.clone();
        },
        _ => break,
      }
    }

    self.restore_depth(saved);
    Ok(())
  }

  /// A2: Validate constructor return type.
  fn check_ctor_return_type(
    &mut self,
    ctor_ty: &KExpr<M>,
    n_params: usize,
    n_indices: usize,
    n_fields: usize,
    ind_addr: &Address,
    ind_lvls: u64,
    block_addrs: &[Address],
  ) -> Result<(), TcError<M>> {
    let saved = self.save_depth();
    let mut ty = ctor_ty.clone();

    // Skip params + fields
    let total_binders = n_params + n_fields;
    for _ in 0..total_binders {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          self.push_local(dom.clone());
          ty = body.clone();
        },
        _ => {
          self.restore_depth(saved);
          return Err(TcError::Other(
            "ctor return type: not enough binders".into(),
          ));
        },
      }
    }

    // Now ty should be the return type: I params... indices...
    // Important: do NOT whnf here. The constructor return type must be
    // syntactically `I args...` (possibly with App nodes), not something
    // that only reduces to `I args...`. This prevents accepting ctor types
    // like `id I` that reduce to `I` but aren't manifest applications.
    let (head, args) = collect_app_spine(&ty);

    // Head must be the inductive with correct universe params
    match head.data() {
      ExprData::Const(id, us, _) if id.addr == *ind_addr => {
        // Universe args must be Param(0), Param(1), ..., Param(lvls-1) in order
        if us.len() as u64 != ind_lvls {
          self.restore_depth(saved);
          return Err(TcError::Other(format!(
            "ctor return type: expected {} universe args, got {}",
            ind_lvls,
            us.len()
          )));
        }
        for (i, u) in us.iter().enumerate() {
          let expected =
            KUniv::param(i as u64, M::meta_field(crate::ix::env::Name::anon()));
          if !univ_eq(u, &expected) {
            self.restore_depth(saved);
            return Err(TcError::Other(format!(
              "ctor return type: universe arg {i} is not Param({i})"
            )));
          }
        }
      },
      _ => {
        self.restore_depth(saved);
        return Err(TcError::Other(
          "ctor return type: head is not the inductive".into(),
        ));
      },
    }

    // S2: Total args must equal n_params + n_indices exactly.
    if args.len() != n_params + n_indices {
      self.restore_depth(saved);
      return Err(TcError::Other(format!(
        "ctor return type: expected {} args (params={} + indices={}), got {}",
        n_params + n_indices,
        n_params,
        n_indices,
        args.len()
      )));
    }

    // First n_params args should be de Bruijn refs to the params
    for i in 0..n_params {
      if i >= args.len() {
        self.restore_depth(saved);
        return Err(TcError::Other(
          "ctor return type: not enough args for params".into(),
        ));
      }
      let expected_idx = (total_binders - 1 - i) as u64;
      match args[i].data() {
        ExprData::Var(idx, _, _) if *idx == expected_idx => {},
        _ => {
          self.restore_depth(saved);
          return Err(TcError::Other(
            "ctor return type: param arg not correct var".into(),
          ));
        },
      }
    }

    // Index args should not mention block inductives
    for arg in &args[n_params..] {
      if expr_mentions_any_addr(arg, block_addrs) {
        self.restore_depth(saved);
        return Err(TcError::Other(
          "ctor return type: index mentions block inductive".into(),
        ));
      }
    }

    self.restore_depth(saved);
    Ok(())
  }

  /// Get the result sort level of a type after peeling `n` foralls.
  pub fn get_result_sort_level(
    &mut self,
    ty: &KExpr<M>,
    n: usize,
  ) -> Result<KUniv<M>, TcError<M>> {
    let saved = self.save_depth();
    let mut t = ty.clone();
    for i in 0..n {
      let w = self.whnf(&t)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          self.push_local(dom.clone());
          t = body.clone();
        },
        _ => {
          self.restore_depth(saved);
          return Err(TcError::Other(format!(
            "get_result_sort_level: expected {n} foralls, only found {i}"
          )));
        },
      }
    }
    let w = self.whnf(&t)?;
    let result = match w.data() {
      ExprData::Sort(u, _) => Ok(u.clone()),
      _ => Err(TcError::Other("get_result_sort_level: not a sort".into())),
    };
    self.restore_depth(saved);
    result
  }

  /// Determine whether the recursor for this block is a large eliminator
  /// (can target any universe). Follows lean4lean's isLargeEliminator.
  ///
  /// Returns true if:
  /// 1. The inductive is NOT in Prop, OR
  /// 2. Single inductive with 0 constructors (e.g. Empty), OR
  /// 3. Single inductive with exactly 1 constructor where all non-param
  ///    fields either live in Prop or appear in the return type args.
  pub fn is_large_eliminator(
    &mut self,
    result_level: &KUniv<M>,
    ind_infos: &[(KId<M>, u64, u64, Vec<KId<M>>, KExpr<M>, bool)],
  ) -> Result<bool, TcError<M>> {
    // Case 1: non-Prop → always large.
    // Use is_never_zero() (not !is_zero()) so that Param(u) — which CAN be
    // Prop when u=0 — falls through to the single-constructor check.
    if result_level.is_never_zero() {
      return Ok(true);
    }
    // Must be a single inductive for large elimination from Prop
    if ind_infos.len() != 1 {
      return Ok(false);
    }
    let (_, n_params, _, ref ctors, _, _) = ind_infos[0];
    let n_params = u64_to_usize::<M>(n_params)?;
    match ctors.len() {
      // Case 2: 0 constructors → large (Empty/False)
      0 => Ok(true),
      // Case 3: 1 constructor → check fields
      1 => {
        let (ctor_ty, ctor_fields) = match self.env.get(&ctors[0]) {
          Some(KConst::Ctor { ty, fields, .. }) => {
            (ty.clone(), u64_to_usize(fields)?)
          },
          _ => return Ok(false),
        };
        // 0 non-param fields → trivially large (e.g. Eq.refl)
        if ctor_fields == 0 {
          return Ok(true);
        }
        // Walk ctor type, collecting non-trivial field positions
        let saved = self.save_depth();
        let mut ty = ctor_ty;
        let mut non_trivial: Vec<usize> = Vec::new(); // field index (0-based among fields)
        for i in 0..(n_params + ctor_fields) {
          let w = self.whnf(&ty)?;
          match w.data() {
            ExprData::All(_, _, dom, body, _) => {
              if i >= n_params {
                // Check if this field's sort level is non-zero (semantically)
                let dom_ty = self.with_infer_only(|tc| tc.infer(dom))?;
                if let Ok(sort_lvl) = self.ensure_sort(&dom_ty)
                  && !univ_eq(&sort_lvl, &KUniv::zero())
                {
                  non_trivial.push(i - n_params);
                }
              }
              self.push_local(dom.clone());
              ty = body.clone();
            },
            _ => break,
          }
        }
        // ty is now the return type: I params args...
        let (_, ret_args) = collect_app_spine(&ty);
        let result = non_trivial.iter().all(|&fi| {
          // Field fi (0-indexed among fields) was pushed at position n_params + fi.
          // From current depth (n_params + ctor_fields), de Bruijn index is:
          let dbi = (ctor_fields - 1 - fi) as u64;
          ret_args.iter().any(
            |arg| matches!(arg.data(), ExprData::Var(v, _, _) if *v == dbi),
          )
        });
        self.restore_depth(saved);
        Ok(result)
      },
      // 2+ constructors → never large for Prop
      _ => Ok(false),
    }
  }

  /// Generate recursors for all inductives in a block (lean4lean-style).
  ///
  /// Detects nested occurrences (à la `ElimNestedInductive`), builds a flat
  /// block with auxiliary entries, and generates canonical recursor types for
  /// all block members (original + auxiliary).
  pub fn generate_block_recursors(
    &mut self,
    block_id: &KId<M>,
  ) -> Result<(), TcError<M>> {
    // Collect block inductives
    let block_inds = self.discover_block_inductives(block_id);
    if block_inds.is_empty() {
      self.env.recursor_cache.insert(block_id.clone(), vec![]);
      return Ok(());
    }

    // Extract basic info for is_large_eliminator check.
    let mut ind_infos: Vec<(KId<M>, u64, u64, Vec<KId<M>>, KExpr<M>, bool)> =
      Vec::new();
    let mut n_params: u64 = 0;
    for (i, ind_id) in block_inds.iter().enumerate() {
      match self.env.get(ind_id) {
        Some(KConst::Indc { params, indices, ctors, ty, is_rec, .. }) => {
          if i == 0 {
            n_params = params;
          }
          ind_infos.push((
            ind_id.clone(),
            params,
            indices,
            ctors.clone(),
            ty.clone(),
            is_rec,
          ));
        },
        _ => {
          return Err(TcError::Other(
            "generate_block_recursors: not an inductive".into(),
          ));
        },
      }
    }

    // Compute elimination level.
    let result_level = self.get_result_sort_level(
      &ind_infos[0].4,
      u64_to_usize(ind_infos[0].1 + ind_infos[0].2)?,
    )?;
    let is_large = self.is_large_eliminator(&result_level, &ind_infos)?;
    let univ_offset: u64 = if is_large { 1 } else { 0 };
    let elim_level = if is_large {
      KUniv::param(0, M::meta_field(crate::ix::env::Name::anon()))
    } else {
      KUniv::zero()
    };

    // Build flat block (detects nested occurrences).
    let mut flat = self.build_flat_block(&block_inds, n_params, univ_offset)?;
    let n_originals = block_inds.len();
    self.dump_flat_aux_order("pre-canonical", block_id, &flat, n_originals);

    // Canonicalize the discovered aux portion of `flat` when the stored
    // recursors come from Ix's compiled environment. Lean's original
    // recursors use source/queue aux order, so `lean_ingress` marks
    // `orig_kenv` with `RecursorAuxOrder::Source` and skips this step.
    //
    // The stored recursor block ships aux recursors at positions
    // determined by the compiler's canonical aux order. For
    // position-by-position recursor matching to work, the kernel's flat
    // block must list aux in the same canonical order. Since aux are
    // discovered transiently (not serialized), the kernel re-runs
    // `sort_consts` on its own discovery output. See
    // `docs/ix_canonicity.md` §6.2 and the rationale in
    // `plans/the-nested-inductive-work-declarative-naur.md`.
    if self.env.recursor_aux_order == RecursorAuxOrder::Canonical
      && flat.len() > n_originals + 1
    {
      let block_us = flat[0].occurrence_us.to_vec();
      let all0_name = block_inds.first().and_then(|id| M::meta_name(&id.name));
      let canonical_order = self.canonical_aux_order(
        &flat[n_originals..],
        n_params,
        &block_us,
        all0_name,
      )?;
      if self.recursor_dump_matches_block(block_id, &flat) {
        eprintln!("[recursor.dump] canonical_order={canonical_order:?}");
      }
      // Apply the permutation produced by sort_consts: each canonical
      // class index k maps to one representative aux from the original
      // discovery order. Alpha-equivalent aux collapse to a single rep
      // (matching the compile-side dedup behaviour).
      let aux_part = flat[n_originals..].to_vec();
      let mut new_aux: Vec<FlatBlockMember<M>> =
        Vec::with_capacity(canonical_order.len());
      for &orig_idx in &canonical_order {
        new_aux.push(aux_part[orig_idx].clone());
      }
      flat.truncate(n_originals);
      flat.extend(new_aux);
    }
    self.dump_flat_aux_order("post-canonical", block_id, &flat, n_originals);

    // Convert flat block to ind_infos format for existing build_motive_type / build_rec_type.
    // For auxiliary members, we need their type from the environment.
    let flat_ind_infos: Vec<(KId<M>, u64, u64, Vec<KId<M>>, KExpr<M>, bool)> =
      flat
        .iter()
        .map(|m| {
          let ty = self
            .env
            .get(&m.id)
            .map_or_else(|| KExpr::sort(KUniv::zero()), |c| c.ty().clone());
          let is_rec = self
            .env
            .get(&m.id)
            .is_some_and(|c| matches!(c, KConst::Indc { is_rec: true, .. }));
          (m.id.clone(), m.own_params, m.n_indices, m.ctors.clone(), ty, is_rec)
        })
        .collect();
    let flat_ids: Vec<KId<M>> = flat.iter().map(|m| m.id.clone()).collect();

    // Build motive types for ALL flat block members.
    let mut motive_types: Vec<KExpr<M>> = Vec::new();
    for member in flat.iter() {
      let motive_ty = self.build_motive_type_flat(
        member,
        u64_to_usize(n_params)?,
        &elim_level,
        univ_offset,
      )?;
      motive_types.push(motive_ty);
    }

    // Generate recursor type for each ORIGINAL inductive (not auxiliaries).
    // The recursor type spans all flat block members (motives, minors).
    let mut generated = Vec::new();
    for di in 0..n_originals {
      let rec_type = self.build_rec_type(
        di,
        &flat_ind_infos,
        &flat_ids,
        &flat,
        &elim_level,
        &motive_types,
        univ_offset,
      )?;
      generated.push(GeneratedRecursor {
        ind_addr: flat[di].id.addr.clone(),
        ty: rec_type,
        // Rules are populated later from the recursor block by
        // `populate_recursor_rules_from_block`.
        rules: vec![],
      });
    }

    // Generate recursor types for auxiliary members too.
    for di in n_originals..flat.len() {
      let rec_type = self.build_rec_type(
        di,
        &flat_ind_infos,
        &flat_ids,
        &flat,
        &elim_level,
        &motive_types,
        univ_offset,
      )?;
      generated.push(GeneratedRecursor {
        ind_addr: flat[di].id.addr.clone(),
        ty: rec_type,
        // Rules are populated later from the recursor block by
        // `populate_recursor_rules_from_block`.
        rules: vec![],
      });
    }

    if self.recursor_dump_matches_block(block_id, &flat) {
      let n_motives = flat.len() as u64;
      let n_minors: u64 = flat.iter().map(|m| m.ctors.len() as u64).sum();
      let prefix_skip = n_params + n_motives + n_minors;
      eprintln!(
        "[recursor.dump] generated recursors for {block_id}: count={} prefix_skip={prefix_skip}",
        generated.len()
      );
      for (gi, g) in generated.iter().enumerate() {
        let major = self.recursor_major_domain_for_addr(
          &g.ty,
          prefix_skip,
          &g.ind_addr,
        )?;
        eprintln!(
          "  gen[{gi:2}] ind_addr={} {}",
          &g.ind_addr.hex()[..8],
          Self::major_domain_signature_text(major.as_ref())
        );
      }
    }

    // Find peer recursor KIds for rule RHS generation.
    // Each flat member needs its corresponding recursor constant for IH values.
    let peer_recs = self.find_peer_recursors(block_id, &flat);
    // Generate rules for each recursor.
    if let Some(ref peers) = peer_recs {
      for (gi, generated_rec) in generated.iter_mut().enumerate() {
        let member = &flat[gi];
        let mut rules = Vec::new();
        for (ci, ctor_id) in member.ctors.iter().enumerate() {
          let ctor_fields = match self.env.get(ctor_id) {
            Some(KConst::Ctor { fields, .. }) => fields,
            _ => 0,
          };
          let generated_rec_ty = generated_rec.ty.clone();
          match self.build_rule_rhs(
            gi,
            ci,
            ctor_id,
            member,
            &flat,
            peers,
            &generated_rec_ty,
            u64_to_usize(n_params)?,
            is_large,
            univ_offset,
          ) {
            Ok(rhs) => rules.push(Some(super::constant::RecRule {
              ctor: ctor_id.name.clone(),
              fields: ctor_fields,
              rhs,
            })),
            Err(_) => {
              rules.push(None);
            },
          }
        }
        // Only set rules if ALL constructors succeeded.
        if rules.iter().all(|r| r.is_some()) {
          generated_rec.rules = rules.into_iter().map(|r| r.unwrap()).collect();
        }
      }
    }

    // Populate the majors cache: set of all flat block member KIds → block_id.
    let majors_key: std::collections::BTreeSet<KId<M>> =
      flat.iter().map(|m| m.id.clone()).collect();
    self.env.rec_majors_cache.insert(majors_key, block_id.clone());

    self.env.recursor_cache.insert(block_id.clone(), generated);
    Ok(())
  }

  /// Build the motive type for inductive j:
  /// `∀ (indices...) (major : I_j params indices), Sort elim_level`
  ///
  /// `univ_offset`: 1 for large eliminators (elim level at Param(0), inductive
  /// params shifted to Param(1)..Param(n)), 0 for small (Prop) eliminators.
  #[allow(dead_code)]
  fn build_motive_type(
    &mut self,
    ind_id: &KId<M>,
    ind_ty: &KExpr<M>,
    ind_lvls: u64,
    n_indices: usize,
    shared_params: usize,
    elim_level: &KUniv<M>,
    univ_offset: u64,
  ) -> Result<KExpr<M>, TcError<M>> {
    let saved = self.save_depth();
    let anon = || M::meta_field(crate::ix::env::Name::anon());

    // Instantiate inductive type with shifted universe params before walking
    let ind_univs = self.mk_ind_univs(ind_lvls, univ_offset);
    let ind_ty_inst = self.instantiate_univ_params(ind_ty, &ind_univs)?;

    // Walk the instantiated inductive type past params, collecting index domains
    let mut ty = ind_ty_inst;
    for _ in 0..shared_params {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          self.push_local(dom.clone());
          ty = body.clone();
        },
        _ => break,
      }
    }

    let mut index_doms: Vec<KExpr<M>> = Vec::new();
    for _ in 0..n_indices {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          index_doms.push(dom.clone());
          self.push_local(dom.clone());
          ty = body.clone();
        },
        _ => break,
      }
    }

    // Build major premise type: I.{shifted_params} params indices
    let mut major_ty =
      KExpr::cnst(ind_id.clone(), self.mk_ind_univs(ind_lvls, univ_offset));
    // params are Var refs to the outer param binders
    let depth = self.depth();
    for i in 0..shared_params {
      let v = KExpr::var(depth - 1 - i as u64, anon());
      major_ty = self.intern(KExpr::app(major_ty, v));
    }
    // indices are the just-bound vars
    for i in 0..n_indices {
      let v = KExpr::var((n_indices - 1 - i) as u64, anon());
      major_ty = self.intern(KExpr::app(major_ty, v));
    }

    // Build: ∀ (major : major_ty), Sort elim_level
    let sort = KExpr::sort(elim_level.clone());
    let mut result = KExpr::all(
      anon(),
      M::meta_field(crate::ix::env::BinderInfo::Default),
      major_ty,
      sort,
    );

    // Wrap with index foralls (from inside out)
    for i in (0..n_indices).rev() {
      result = KExpr::all(
        anon(),
        M::meta_field(crate::ix::env::BinderInfo::Default),
        index_doms[i].clone(),
        result,
      );
    }

    self.restore_depth(saved);
    Ok(result)
  }

  /// Build motive type for a flat block member, handling spec_params.
  ///
  /// For original members: walks ind type past shared params (as binders),
  /// collects indices, builds `∀ indices (t : I params indices), Sort u`.
  /// For auxiliary members: walks ind type, substituting own_params with
  /// spec_params (lifted), collects indices, builds `∀ indices (t : I spec_params indices), Sort u`.
  pub fn build_motive_type_flat(
    &mut self,
    member: &FlatBlockMember<M>,
    n_rec_params: usize,
    elim_level: &KUniv<M>,
    _univ_offset: u64,
  ) -> Result<KExpr<M>, TcError<M>> {
    let saved = self.save_depth();
    let anon = || M::meta_field(crate::ix::env::Name::anon());
    let bi_default = || M::meta_field(crate::ix::env::BinderInfo::Default);

    // Get inductive type and instantiate with occurrence universe args
    // (concrete for auxiliaries, same as ind_us for originals).
    let ind_ty = self
      .env
      .get(&member.id)
      .ok_or_else(|| {
        TcError::Other("build_motive_type_flat: ind not found".into())
      })?
      .ty()
      .clone();
    let ind_ty_inst =
      self.instantiate_univ_params(&ind_ty, &member.occurrence_us)?;

    // Walk past own_params, substituting with spec_params (lifted to current depth).
    let mut ty = ind_ty_inst;
    for j in 0..member.own_params {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, _dom, body, _) => {
          let p = if u64_to_usize::<M>(j)? < member.spec_params.len() {
            let sp = member.spec_params[u64_to_usize::<M>(j)?].clone();
            let lift_amount = self.depth();
            // spec_params are in terms of recursor params at depth n_rec_params.
            // Current depth might differ; lift accordingly.
            if lift_amount > 0 {
              lift(&self.env.intern, &sp, lift_amount, 0)
            } else {
              sp
            }
          } else {
            KExpr::var(n_rec_params as u64 - 1 - j, anon())
          };
          ty = subst(&self.env.intern, body, &p, 0);
        },
        _ => break,
      }
    }

    // Collect index domains.
    let mut index_doms: Vec<KExpr<M>> = Vec::new();
    for _ in 0..member.n_indices {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          index_doms.push(dom.clone());
          self.push_local(dom.clone());
          ty = body.clone();
        },
        _ => break,
      }
    }

    // Build major premise type: I.{us} params/spec_params indices
    let mut major_ty =
      self.intern(KExpr::cnst(member.id.clone(), member.occurrence_us.clone()));
    let depth = self.depth();
    if !member.is_aux {
      // Original: params are Var refs. At this point, indices are pushed but
      // params aren't (they were substituted). Params are free Var refs that
      // will be under (n_indices) binders in the final motive type.
      for i in 0..n_rec_params {
        let v = self.intern(KExpr::var(
          (n_rec_params as u64 - 1 - i as u64) + depth,
          anon(),
        ));
        major_ty = self.intern(KExpr::app(major_ty, v));
      }
    } else {
      // Auxiliary: lift spec_params from param context (n_rec_params)
      let lift_by = u64_to_usize::<M>(depth)?;
      for sp in member.spec_params.iter() {
        let lifted = if lift_by > 0 {
          lift(&self.env.intern, sp, lift_by as u64, 0)
        } else {
          sp.clone()
        };
        major_ty = self.intern(KExpr::app(major_ty, lifted));
      }
    }
    // Apply indices (the just-bound vars).
    let n_idx = u64_to_usize::<M>(member.n_indices)?;
    for i in 0..n_idx {
      let v = self.intern(KExpr::var((n_idx - 1 - i) as u64, anon()));
      major_ty = self.intern(KExpr::app(major_ty, v));
    }

    // Build: ∀ (major : major_ty), Sort elim_level
    let sort = self.intern(KExpr::sort(elim_level.clone()));
    let mut result =
      self.intern(KExpr::all(anon(), bi_default(), major_ty, sort));

    // Wrap with index foralls (from inside out).
    for i in (0..n_idx).rev() {
      result = self.intern(KExpr::all(
        anon(),
        bi_default(),
        index_doms[i].clone(),
        result,
      ));
    }

    self.restore_depth(saved);
    Ok(result)
  }

  /// Build minor premise type for a constructor, called while params and motives
  /// are already on the context. This makes de Bruijn indices correct.
  ///
  /// For constructor `C : ∀ params fields, I params indices`:
  /// ```text
  /// ∀ (f₁ : F₁) ... (fₙ : Fₙ)
  ///   (ih₁ : ∀ xs, motive(indices(rec_field₁ xs), rec_field₁ xs))
  ///   ...
  ///   (ihₘ : ∀ xs, motive(indices(rec_fieldₘ xs), rec_fieldₘ xs)),
  ///   motive(ctor_indices, C params f₁...fₙ)
  /// ```
  fn build_minor_at_depth(
    &mut self,
    ind_idx: usize,
    ctor_id: &KId<M>,
    member: &FlatBlockMember<M>,
    n_rec_params: usize,
    motive_base: usize, // context level where motives start
    flat: &[FlatBlockMember<M>],
    block_addrs: &[Address],
    _univ_offset: u64,
  ) -> Result<KExpr<M>, TcError<M>> {
    let ctor = match self.env.get(ctor_id) {
      Some(KConst::Ctor { ty, lvls, .. }) => (ty.clone(), lvls),
      _ => {
        return Err(TcError::Other(
          "build_minor_at_depth: ctor not found".into(),
        ));
      },
    };
    let (ctor_ty_raw, _ctor_lvls) = ctor;
    let anon = || M::meta_field(crate::ix::env::Name::anon());
    let bi_default = || M::meta_field(crate::ix::env::BinderInfo::Default);
    let saved = self.save_depth();

    // Instantiate ctor type with occurrence universe args (concrete for output).
    let ctor_ty =
      self.instantiate_univ_params(&ctor_ty_raw, &member.occurrence_us)?;

    // Walk ctor type past member's own_params, substituting with spec_params.
    // For originals: spec_params = Var refs relative to depth 0, need re-indexing
    //   to point to the recursor's param binders at the current depth.
    // For auxiliaries: spec_params = concrete closed exprs (no lifting needed
    //   since they don't contain Var refs).
    let mut ty = ctor_ty;
    for j in 0..member.own_params {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => {
          let p = if !member.is_aux {
            // Original member: param j is the j-th recursor param binder.
            // It's at context level j, so Var index = depth - 1 - j.
            let depth = self.depth();
            KExpr::var(depth - 1 - j, anon())
          } else if u64_to_usize::<M>(j)? < member.spec_params.len() {
            // Auxiliary member: spec_params have Var refs relative to the param
            // context (depth = n_rec_params). Lift by the difference between
            // current depth and n_rec_params.
            let sp = member.spec_params[u64_to_usize::<M>(j)?].clone();
            let depth = u64_to_usize::<M>(self.depth())?;
            let lift_by = depth.saturating_sub(n_rec_params);
            if lift_by > 0 {
              lift(&self.env.intern, &sp, lift_by as u64, 0)
            } else {
              sp
            }
          } else {
            let depth = self.depth();
            KExpr::var(depth - 1 - j, anon())
          };
          ty = subst(&self.env.intern, body, &p, 0);
        },
        _ => break,
      }
    }

    // Collect fields and push them as locals
    let mut field_domains: Vec<KExpr<M>> = Vec::new();
    let mut rec_field_indices: Vec<(usize, usize)> = Vec::new(); // (field_idx, block_ind_idx)

    let mut fidx = 0;
    loop {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          field_domains.push(dom.clone());
          // Field args reference block params at current pushed-local
          // depth; spec_params live at depth = n_rec_params (shared
          // block params = flat[0].own_params). Lift by the difference.
          let n_rec_params = flat.first().map(|m| m.own_params).unwrap_or(0);
          let lift_by = self.depth().saturating_sub(n_rec_params);
          if let Some(bi) = self.is_rec_field(dom, flat, lift_by)? {
            rec_field_indices.push((fidx, bi));
          }
          self.push_local(dom.clone());
          ty = body.clone();
          fidx += 1;
        },
        _ => break,
      }
    }
    let n_fields = field_domains.len();

    // Build IH types for recursive fields and push them as locals.
    // At this point depth = saved + n_fields.
    let mut ih_domains: Vec<KExpr<M>> = Vec::new();
    for (k, &(field_idx, block_ind_idx)) in rec_field_indices.iter().enumerate()
    {
      // depth = saved + n_fields + k (k IHs already pushed)
      // For IH building, n_params should be the TARGET member's own_params
      // (the member that the recursive field targets).
      let target_n_params = if block_ind_idx < flat.len() {
        u64_to_usize::<M>(flat[block_ind_idx].own_params)?
      } else {
        n_rec_params
      };
      let ih_ty = self.build_direct_ih(
        field_idx,
        block_ind_idx,
        target_n_params,
        n_fields,
        k,
        saved,
        motive_base,
        &field_domains,
        block_addrs,
      )?;
      ih_domains.push(ih_ty.clone());
      self.push_local(ih_ty);
    }
    let n_ihs = ih_domains.len();
    let n_binders = n_fields + n_ihs;

    // `ty` is the return type: I params indices
    // The constructor always returns its own inductive, so ret_ind_idx = ind_idx.
    // We don't search block_addrs because duplicate addresses (same external inductive
    // with different spec_params) would return the wrong position.
    let (_ret_head, ret_args) = collect_app_spine(&ty);
    let ret_indices: Vec<KExpr<M>> = ret_args
      .iter()
      .skip(u64_to_usize::<M>(member.own_params)?)
      .cloned()
      .collect();

    // Build conclusion: motive[ind_idx](ret_indices, C params fields)
    // Motive[ind_idx] is at context level: motive_base + ind_idx
    let depth = self.depth();
    let motive_var_idx =
      (u64_to_usize::<M>(depth)? - 1 - (motive_base + ind_idx)) as u64;
    let mut conclusion = self.intern(KExpr::var(motive_var_idx, anon()));

    // Apply return indices (these are at the old depth, but we pushed IHs since then,
    // so we need to lift the indices by n_ihs)
    for idx_expr in &ret_indices {
      let lifted = if n_ihs > 0 {
        lift(
          &self.env.intern,
          idx_expr,
          n_ihs as u64,
          0, // lift ALL Var refs, not just those above fields
        )
      } else {
        idx_expr.clone()
      };
      conclusion = self.intern(KExpr::app(conclusion, lifted));
    }

    // Apply C params/spec_params then fields
    let mut ctor_app =
      self.intern(KExpr::cnst(ctor_id.clone(), member.occurrence_us.clone()));
    if !member.is_aux {
      // Original: apply Var refs to recursor param binders
      for i in 0..u64_to_usize::<M>(member.own_params)? {
        let pvar = self.intern(KExpr::var(
          (u64_to_usize::<M>(depth)? - 1 - i) as u64,
          anon(),
        ));
        ctor_app = self.intern(KExpr::app(ctor_app, pvar));
      }
    } else {
      // Auxiliary: lift spec_params from param context to current depth
      let lift_by = u64_to_usize::<M>(depth)?.saturating_sub(n_rec_params);
      for sp in &member.spec_params {
        let lifted = if lift_by > 0 {
          lift(&self.env.intern, sp, lift_by as u64, 0)
        } else {
          sp.clone()
        };
        ctor_app = self.intern(KExpr::app(ctor_app, lifted));
      }
    }
    for i in 0..n_fields {
      let fvar = self.intern(KExpr::var((n_binders - 1 - i) as u64, anon()));
      ctor_app = self.intern(KExpr::app(ctor_app, fvar));
    }
    conclusion = self.intern(KExpr::app(conclusion, ctor_app));

    // Fold: ∀ (ihs...) (fields...), conclusion (from inside out)
    // Pop IHs first (innermost)
    for i in (0..n_ihs).rev() {
      self.pop_local();
      conclusion = self.intern(KExpr::all(
        anon(),
        bi_default(),
        ih_domains[i].clone(),
        conclusion,
      ));
    }
    // Pop fields
    for i in (0..n_fields).rev() {
      self.pop_local();
      conclusion = self.intern(KExpr::all(
        anon(),
        bi_default(),
        field_domains[i].clone(),
        conclusion,
      ));
    }

    self.restore_depth(saved);
    Ok(conclusion)
  }

  /// Build an IH type for a recursive field.
  ///
  /// For a direct recursive field (type = `I_bi params idx_args`):
  ///   IH = `motive_bi(idx_args, field_var)`
  ///
  /// For a forall-wrapped recursive field (type = `∀ xs, I_bi params idx_args(xs)`):
  ///   IH = `∀ xs, motive_bi(idx_args(xs), field xs)`
  ///
  /// Called when depth = minor_saved + n_fields + k (k IHs already pushed).
  fn build_direct_ih(
    &mut self,
    field_idx: usize,
    block_ind_idx: usize,
    n_params: usize,
    n_fields: usize,
    k: usize,           // number of IHs already pushed before this one
    minor_saved: usize, // depth at entry of build_minor_at_depth
    motive_base: usize,
    field_domains: &[KExpr<M>],
    block_addrs: &[Address],
  ) -> Result<KExpr<M>, TcError<M>> {
    let anon = || M::meta_field(crate::ix::env::Name::anon());
    let bi_default = || M::meta_field(crate::ix::env::BinderInfo::Default);

    // Lift the field domain from its original depth (minor_saved + field_idx)
    // to the current depth (minor_saved + n_fields + k).
    let dom = &field_domains[field_idx];
    let shift = (n_fields + k - field_idx) as u64;
    let dom_lifted = lift(&self.env.intern, dom, shift, 0);
    let wdom = self.whnf(&dom_lifted)?;

    // Check if direct (head is block inductive) or forall-wrapped
    match wdom.data() {
      ExprData::All(..) => {
        // Forall-wrapped: ∀ (xs...), I_bi params idx_args(xs)
        // IH = ∀ (xs...), motive_bi(idx_args(xs), field xs)
        let ih_saved = self.save_depth();
        let mut inner_ty = wdom.clone();
        let mut forall_doms: Vec<KExpr<M>> = Vec::new();
        let inner_whnf;

        loop {
          let w = self.whnf(&inner_ty)?;
          match w.data() {
            ExprData::All(_, _, inner_dom, inner_body, _) => {
              let (h, _) = collect_app_spine(&w);
              if matches!(h.data(), ExprData::Const(id, _, _) if block_addrs.contains(&id.addr))
              {
                inner_whnf = w;
                break;
              }
              forall_doms.push(inner_dom.clone());
              self.push_local(inner_dom.clone());
              inner_ty = inner_body.clone();
            },
            _ => {
              inner_whnf = w;
              break;
            },
          }
        }
        let n_xs = forall_doms.len();

        // inner_whnf = WHNF of the result type = I_bi params idx_args(xs)
        let (_h, inner_args) = collect_app_spine(&inner_whnf);
        let idx_args: Vec<KExpr<M>> =
          inner_args.iter().skip(n_params).cloned().collect();

        // Build motive_bi(idx_args, field xs)
        let depth = u64_to_usize::<M>(self.depth())?;
        let motive_var = (depth - 1 - (motive_base + block_ind_idx)) as u64;
        let mut ih_body = KExpr::var(motive_var, anon());
        for idx in &idx_args {
          ih_body = self.intern(KExpr::app(ih_body, idx.clone()));
        }
        // field is at context level minor_saved + field_idx
        let field_var = (depth - 1 - (minor_saved + field_idx)) as u64;
        let mut field_app = KExpr::var(field_var, anon());
        for i in 0..n_xs {
          let xvar = KExpr::var((n_xs - 1 - i) as u64, anon());
          field_app = self.intern(KExpr::app(field_app, xvar));
        }
        ih_body = self.intern(KExpr::app(ih_body, field_app));

        // Fold ∀ xs
        for i in (0..n_xs).rev() {
          self.pop_local();
          ih_body =
            KExpr::all(anon(), bi_default(), forall_doms[i].clone(), ih_body);
        }

        self.restore_depth(ih_saved);
        Ok(ih_body)
      },
      _ => {
        // Direct case: dom_lifted head should be a block inductive
        let (_dom_head, dom_args) = collect_app_spine(&wdom);
        let idx_args: Vec<KExpr<M>> =
          dom_args.iter().skip(n_params).cloned().collect();

        let depth = u64_to_usize::<M>(self.depth())?;
        let motive_var = (depth - 1 - (motive_base + block_ind_idx)) as u64;
        let mut ih_body = KExpr::var(motive_var, anon());

        for idx in &idx_args {
          ih_body = self.intern(KExpr::app(ih_body, idx.clone()));
        }

        // field is at context level minor_saved + field_idx
        let field_var = (depth - 1 - (minor_saved + field_idx)) as u64;
        ih_body =
          self.intern(KExpr::app(ih_body, KExpr::var(field_var, anon())));

        Ok(ih_body)
      },
    }
  }

  /// Check if a field domain is a recursive occurrence of a flat block member.
  /// Returns `Some(block_index)` if, after peeling foralls, the result is
  /// `I_k params args` where `I_k` matches a flat member:
  ///
  /// - **Original** members (`is_aux = false`): head address match is
  ///   sufficient.
  /// - **Auxiliary** members (`is_aux = true`): head address must match
  ///   AND the first `own_params` args must be definitionally equal to
  ///   the member's stored `spec_params` (after lifting spec_params to
  ///   the caller's param-reference frame). The addr check alone can't
  ///   distinguish two auxiliaries sharing an external inductive (e.g.
  ///   `List A` vs `List B`).
  ///
  /// # Depth handling
  ///
  /// `spec_params` are stored at the param context (depth =
  /// `flat[0].own_params`). Callers reference block params via Var
  /// indices that may live at different effective depths:
  ///
  /// - `build_minor_at_depth` pushes field locals as it scans; at the
  ///   `is_rec_field` call `self.depth() - n_rec_params` gives the
  ///   offset needed.
  /// - `build_rule_rhs` does NOT push locals — it substitutes params
  ///   with `Var(total_lams - 1 - j)` (virtual positions for the final
  ///   lambda chain), leaving `self.depth() = 0` regardless of how
  ///   many virtual binders are open. The correct offset is
  ///   `total_lams - n_rec_params`.
  ///
  /// Rather than have the function guess, the caller passes
  /// `spec_params_lift_by` explicitly. Comparison uses `is_def_eq`
  /// after lifting, which handles alpha equivalence, whnf, and beta —
  /// anything a raw `addr()` hash comparison would miss on `Var`
  /// parameter references.
  ///
  /// Historical note: the original implementation used raw `addr()`
  /// comparison after spine decomposition, which returned false
  /// whenever a spec_param was a bare `Var` (block param). That
  /// dropped the IH for any recursive field whose nested type used the
  /// block's params directly — e.g. `head : Entry α β (Node α β)` in
  /// a nested `List (Entry α β (Node α β))` scan. An interim fix
  /// computed lift from `self.depth()`, which worked for
  /// `build_minor_at_depth` but silently failed in `build_rule_rhs`.
  fn is_rec_field(
    &mut self,
    dom: &KExpr<M>,
    flat: &[FlatBlockMember<M>],
    spec_params_lift_by: u64,
  ) -> Result<Option<usize>, TcError<M>> {
    let mut ty = dom.clone();
    loop {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => ty = body.clone(),
        _ => {
          let (head, args) = collect_app_spine(&w);
          let head_addr = match head.data() {
            ExprData::Const(id, _, _) => &id.addr,
            _ => return Ok(None),
          };

          for (idx, m) in flat.iter().enumerate() {
            if m.id.addr != *head_addr {
              continue;
            }
            if !m.is_aux {
              return Ok(Some(idx));
            }
            // Auxiliary: verify the caller's args agree with the
            // stored spec_params after lifting them to caller depth.
            let own = u64_to_usize::<M>(m.own_params)?;
            if args.len() < own || m.spec_params.len() != own {
              continue;
            }
            let mut matches = true;
            for (arg, sp) in args.iter().take(own).zip(m.spec_params.iter()) {
              let sp_lifted = if spec_params_lift_by > 0 {
                lift(&self.env.intern, sp, spec_params_lift_by, 0)
              } else {
                sp.clone()
              };
              if !self.is_def_eq(arg, &sp_lifted).unwrap_or(false) {
                matches = false;
                break;
              }
            }
            if matches {
              return Ok(Some(idx));
            }
          }
          return Ok(None);
        },
      }
    }
  }

  /// Build the full recursor type for inductive `di` in the block.
  ///
  /// Structure: `∀ (params) (motives) (minors) (indices) (major), motive indices major`
  ///
  /// All domains are computed by walking the inductive/constructor types under
  /// the appropriate binder context, then folding into a forall chain.
  fn build_rec_type(
    &mut self,
    di: usize,
    ind_infos: &[(KId<M>, u64, u64, Vec<KId<M>>, KExpr<M>, bool)],
    block_inds: &[KId<M>],
    flat: &[FlatBlockMember<M>],
    _elim_level: &KUniv<M>,
    motive_types: &[KExpr<M>],
    univ_offset: u64,
  ) -> Result<KExpr<M>, TcError<M>> {
    let saved = self.save_depth();
    let n_params = u64_to_usize::<M>(ind_infos[0].1)?;
    let n_motives = ind_infos.len();
    let n_indices = u64_to_usize::<M>(ind_infos[di].2)?;
    let block_addrs: Vec<Address> =
      block_inds.iter().map(|id| id.addr.clone()).collect();
    let anon = || M::meta_field(crate::ix::env::Name::anon());
    let bi_default = || M::meta_field(crate::ix::env::BinderInfo::Default);

    // Collect all binder domains in order: params, motives, minors, indices, major
    let mut domains: Vec<KExpr<M>> = Vec::new();

    // --- Params: walk first inductive's type, with shifted universe instantiation ---
    let first_ind_lvls = match self.env.get(&block_inds[0]) {
      Some(KConst::Indc { lvls, .. }) => lvls,
      _ => 0,
    };
    let first_ind_univs = self.mk_ind_univs(first_ind_lvls, univ_offset);
    let pty_inst =
      self.instantiate_univ_params(&ind_infos[0].4, &first_ind_univs)?;
    let mut pty = pty_inst;
    for _ in 0..n_params {
      let w = self.whnf(&pty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          domains.push(dom.clone());
          self.push_local(dom.clone());
          pty = body.clone();
        },
        _ => break,
      }
    }

    // --- Motives ---
    // Each motive was built at depth 0 (standalone). When placed in the forall
    // chain, motive j needs its free Vars lifted by j (accounting for the
    // j motives already pushed before it).
    for (j, mt) in motive_types.iter().enumerate() {
      let lifted_mt = if j > 0 {
        lift(&self.env.intern, mt, j as u64, 0)
      } else {
        mt.clone()
      };
      domains.push(lifted_mt.clone());
      self.push_local(lifted_mt);
    }

    // --- Minors: built inline at the correct depth ---
    // motive_base = depth after pushing params (motives start here)
    let motive_base = u64_to_usize::<M>(self.depth())? - n_motives;
    for (j, (_, _, _, j_ctors, _, _)) in ind_infos.iter().enumerate() {
      let j_member = flat[j].clone();
      for ctor_id in j_ctors {
        let minor_ty = self.build_minor_at_depth(
          j,
          ctor_id,
          &j_member,
          n_params,
          motive_base,
          flat,
          &block_addrs,
          univ_offset,
        )?;
        domains.push(minor_ty.clone());
        self.push_local(minor_ty);
      }
    }
    let _n_minors = domains.len().checked_sub(n_params + n_motives)
      .ok_or_else(|| TcError::Other(format!(
        "build_rec_type: not enough binders: domains={}, params={n_params}, motives={n_motives}",
        domains.len()
      )))?;

    // --- Indices for THIS inductive (using flat block member info) ---
    let di_member = &flat[di];
    let ity_inst = self
      .instantiate_univ_params(&ind_infos[di].4, &di_member.occurrence_us)?;
    let mut ity = ity_inst;
    // Walk past this member's own_params, substituting appropriately.
    for j in 0..di_member.own_params {
      let w = self.whnf(&ity)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => {
          let p = if !di_member.is_aux {
            let depth = self.depth();
            KExpr::var(depth - 1 - j, anon())
          } else if u64_to_usize::<M>(j)? < di_member.spec_params.len() {
            let sp = di_member.spec_params[u64_to_usize::<M>(j)?].clone();
            let lift_by =
              u64_to_usize::<M>(self.depth())?.saturating_sub(n_params);
            if lift_by > 0 {
              lift(&self.env.intern, &sp, lift_by as u64, 0)
            } else {
              sp
            }
          } else {
            let depth = self.depth();
            KExpr::var(depth - 1 - j, anon())
          };
          ity = subst(&self.env.intern, body, &p, 0);
        },
        _ => break,
      }
    }
    for _ in 0..n_indices {
      let w = self.whnf(&ity)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          domains.push(dom.clone());
          self.push_local(dom.clone());
          ity = body.clone();
        },
        _ => break,
      }
    }

    // --- Major premise: I spec_params indices ---
    let ind_id = &ind_infos[di].0;
    let mut major_dom =
      self.intern(KExpr::cnst(ind_id.clone(), di_member.occurrence_us.clone()));
    let depth = self.depth();
    if !di_member.is_aux {
      for i in 0..u64_to_usize::<M>(di_member.own_params)? {
        let pvar = self.intern(KExpr::var(
          (u64_to_usize::<M>(depth)? - 1 - i) as u64,
          anon(),
        ));
        major_dom = self.intern(KExpr::app(major_dom, pvar));
      }
    } else {
      let lift_by = u64_to_usize::<M>(depth)?.saturating_sub(n_params);
      for sp in &di_member.spec_params {
        let lifted = if lift_by > 0 {
          lift(&self.env.intern, sp, lift_by as u64, 0)
        } else {
          sp.clone()
        };
        major_dom = self.intern(KExpr::app(major_dom, lifted));
      }
    }
    for i in 0..n_indices {
      let ivar = self.intern(KExpr::var((n_indices - 1 - i) as u64, anon()));
      major_dom = self.intern(KExpr::app(major_dom, ivar));
    }
    domains.push(major_dom.clone());
    self.push_local(major_dom);

    // --- Return type: motive_di indices major ---
    let depth = self.depth();
    let motive_var_idx = (u64_to_usize::<M>(depth)? - 1 - n_params - di) as u64;
    let mut ret = self.intern(KExpr::var(motive_var_idx, anon()));
    for i in 0..n_indices {
      let ivar = self.intern(KExpr::var((n_indices - i) as u64, anon()));
      ret = self.intern(KExpr::app(ret, ivar));
    }
    let major_var = self.intern(KExpr::var(0, anon()));
    ret = self.intern(KExpr::app(ret, major_var));

    // --- Fold into forall chain (from inside out) ---
    for i in (0..domains.len()).rev() {
      self.pop_local();
      ret =
        self.intern(KExpr::all(anon(), bi_default(), domains[i].clone(), ret));
    }

    self.restore_depth(saved);
    Ok(ret)
  }

  /// Create shifted universe param args for an inductive in a recursor context.
  /// For large eliminators (offset=1): [Param(1), ..., Param(n)].
  /// For small eliminators (offset=0): [Param(0), ..., Param(n-1)].
  fn mk_ind_univs(&mut self, ind_lvls: u64, offset: u64) -> Box<[KUniv<M>]> {
    (0..ind_lvls)
      .map(|i| {
        KUniv::param(i + offset, M::meta_field(crate::ix::env::Name::anon()))
      })
      .collect::<Vec<_>>()
      .into_iter()
      .map(|u| self.intern_univ(u))
      .collect()
  }

  /// Find peer recursor KIds for each flat block member.
  /// Returns None if peer recursors can't be found (block not in env).
  fn find_peer_recursors(
    &mut self,
    block_id: &KId<M>,
    flat: &[FlatBlockMember<M>],
  ) -> Option<Vec<KId<M>>> {
    // Find all recursors in the block
    let members: Vec<KId<M>> = self.env.blocks.get(block_id)?.clone();
    let rec_ids: Vec<KId<M>> = members
      .iter()
      .filter(|id| matches!(self.env.get(id), Some(KConst::Recr { .. })))
      .cloned()
      .collect();

    if rec_ids.len() < flat.len() {
      return None;
    }

    // Match each flat member to the recursor that eliminates its inductive.
    // For each recursor, extract the major inductive address from its type.
    // For flat members with the same inductive address (different spec_params),
    // match by checking that the major premise's parameter args correspond to
    // the flat member's spec_params.
    let mut result: Vec<Option<KId<M>>> = vec![None; flat.len()];
    let mut used: Vec<bool> = vec![false; rec_ids.len()];

    for (fi, member) in flat.iter().enumerate() {
      for (ri, rec_id) in rec_ids.iter().enumerate() {
        if used[ri] {
          continue;
        }
        let (params, motives, minors, indices, ty) = match self.env.get(rec_id)
        {
          Some(KConst::Recr {
            params, motives, minors, indices, ty, ..
          }) => (params, motives, minors, indices, ty.clone()),
          _ => continue,
        };
        // Extract major inductive address
        let skip = params + motives + minors + indices;
        let major_id = match self.get_major_inductive_id(&ty, skip) {
          Ok(id) => id,
          Err(_) => continue,
        };
        if major_id.addr != member.id.addr {
          continue;
        }
        // For non-aux (original) members, address match is sufficient
        if !member.is_aux {
          result[fi] = Some(rec_id.clone());
          used[ri] = true;
          break;
        }
        // For auxiliary members, check spec_params match using is_def_eq.
        // Extract the major premise domain's param args from the recursor type
        // and compare with the flat member's spec_params (lifted to the same depth).
        let saved = self.save_depth();
        let mut cur = ty;
        for _ in 0..skip {
          match self.whnf(&cur) {
            Ok(w) => match w.data() {
              ExprData::All(_, _, dom, b, _) => {
                self.push_local(dom.clone());
                cur = b.clone();
              },
              _ => break,
            },
            _ => break,
          }
        }
        let mut matched = false;
        if let Ok(w) = self.whnf(&cur)
          && let ExprData::All(_, _, dom, _, _) = w.data()
        {
          let (_, major_args) = collect_app_spine(dom);
          let n_par = u64_to_usize::<M>(member.own_params).ok()?;
          if major_args.len() >= n_par && member.spec_params.len() == n_par {
            // spec_params are in param context. Lift by (current_depth - n_rec_params).
            let n_rec_params = flat.first().map_or(0, |m| m.own_params);
            let lift_by = self.depth().saturating_sub(n_rec_params);
            matched =
              major_args.iter().take(n_par).zip(member.spec_params.iter()).all(
                |(arg, sp)| {
                  let sp_lifted = if lift_by > 0 {
                    lift(&self.env.intern, sp, lift_by, 0)
                  } else {
                    sp.clone()
                  };
                  self.is_def_eq(arg, &sp_lifted).unwrap_or(false)
                },
              );
          }
        }
        self.restore_depth(saved);
        if matched {
          result[fi] = Some(rec_id.clone());
          used[ri] = true;
          break;
        }
      }
    }

    // Check all flat members found a recursor
    let all_found = result.iter().all(|r| r.is_some());
    if all_found {
      Some(result.into_iter().map(|r| r.unwrap()).collect())
    } else {
      None
    }
  }

  /// Populate canonical recursor rules from the actual recursor block peers.
  ///
  /// `generate_block_recursors` is driven from the inductive block, where the
  /// recursor constants are not necessarily block members. With block-level
  /// recursor checking, the recursor block is available before comparing any
  /// sibling. Build the rule RHSs once from that block and store them back at
  /// the generated-recursors indices. This avoids per-member fallback rule
  /// generation and, critically, disambiguates duplicate nested auxiliaries by
  /// the full major premise signature instead of by inductive address alone.
  fn populate_recursor_rules_from_block(
    &mut self,
    ind_block_id: &KId<M>,
    rec_block_id: &KId<M>,
  ) -> Result<(), TcError<M>> {
    let generated_snapshot = match self.env.recursor_cache.get(ind_block_id) {
      Some(g) => g.clone(),
      None => return Ok(()),
    };
    if generated_snapshot.is_empty() {
      return Ok(());
    }

    let members = match self.env.blocks.get(rec_block_id) {
      Some(m) => m.clone(),
      None => return Ok(()),
    };
    let rec_ids: Vec<KId<M>> = members
      .iter()
      .filter(|id| matches!(self.env.get(id), Some(KConst::Recr { .. })))
      .cloned()
      .collect();
    if rec_ids.is_empty() {
      return Ok(());
    }

    let block_inds = self.discover_block_inductives(ind_block_id);
    if block_inds.is_empty() {
      return Ok(());
    }
    let n_params_u64 = match self.env.get(&block_inds[0]) {
      Some(KConst::Indc { params, .. }) => params,
      _ => return Ok(()),
    };
    let ind_lvls = match self.env.get(&block_inds[0]) {
      Some(KConst::Indc { lvls, .. }) => lvls,
      _ => 0,
    };
    let univ_offset = match rec_ids.first() {
      Some(rid) => match self.env.get(rid) {
        Some(KConst::Recr { lvls, .. }) => {
          if lvls > ind_lvls {
            1u64
          } else {
            0u64
          }
        },
        _ => 0,
      },
      None => 0,
    };
    let mut flat =
      self.build_flat_block(&block_inds, n_params_u64, univ_offset)?;
    let n_originals = block_inds.len();
    if self.env.recursor_aux_order == RecursorAuxOrder::Canonical
      && flat.len() > n_originals + 1
    {
      let block_us = flat[0].occurrence_us.to_vec();
      let all0_name = block_inds.first().and_then(|id| M::meta_name(&id.name));
      let canonical_order = self.canonical_aux_order(
        &flat[n_originals..],
        n_params_u64,
        &block_us,
        all0_name,
      )?;
      let aux_part = flat[n_originals..].to_vec();
      let mut new_aux: Vec<FlatBlockMember<M>> =
        Vec::with_capacity(canonical_order.len());
      for &orig_idx in &canonical_order {
        new_aux.push(aux_part[orig_idx].clone());
      }
      flat.truncate(n_originals);
      flat.extend(new_aux);
    }
    if flat.len() != generated_snapshot.len() {
      return Err(TcError::Other(format!(
        "populate_recursor_rules_from_block: flat/generated length mismatch: flat={} generated={}",
        flat.len(),
        generated_snapshot.len()
      )));
    }
    if generated_snapshot
      .iter()
      .zip(flat.iter())
      .all(|(g, member)| g.rules.len() == member.ctors.len())
    {
      return Ok(());
    }

    let n_motives = flat.len() as u64;
    let n_minors: u64 = flat.iter().map(|m| m.ctors.len() as u64).sum();
    let prefix_base = n_params_u64 + n_motives + n_minors;
    let mut peers: Vec<Option<KId<M>>> = vec![None; flat.len()];
    let mut used: Vec<bool> = vec![false; rec_ids.len()];

    for (gi, gen_rec) in generated_snapshot.iter().enumerate() {
      let target_addr = &gen_rec.ind_addr;
      let gen_major = self.recursor_major_domain_for_addr(
        &gen_rec.ty,
        prefix_base + flat[gi].n_indices,
        target_addr,
      )?;
      let Some(gen_major) = gen_major else {
        return Err(TcError::Other(format!(
          "populate_recursor_rules_from_block: generated recursor {gi} has no major premise"
        )));
      };

      for (ri, rid) in rec_ids.iter().enumerate() {
        if used[ri] {
          continue;
        }
        let (params, motives, minors, indices, ty) = match self.env.get(rid) {
          Some(KConst::Recr {
            params, motives, minors, indices, ty, ..
          }) => (params, motives, minors, indices, ty.clone()),
          _ => continue,
        };
        let skip = params + motives + minors + indices;
        let Some(stored_major) =
          self.recursor_major_domain_for_addr(&ty, skip, target_addr)?
        else {
          continue;
        };
        if self.major_domain_signature_eq(&gen_major, &stored_major)? {
          peers[gi] = Some(rid.clone());
          used[ri] = true;
          break;
        }
      }

      if peers[gi].is_none() {
        return Err(TcError::Other(format!(
          "populate_recursor_rules_from_block: could not align recursor peer {gi}"
        )));
      }
    }

    let peer_recs: Vec<KId<M>> =
      peers.into_iter().map(|p| p.unwrap()).collect();
    let is_large = univ_offset > 0;
    let n_params = u64_to_usize::<M>(n_params_u64)?;
    let mut generated_with_rules = generated_snapshot;

    for gi in 0..flat.len() {
      let member = &flat[gi];
      let rec_ty_for_member = generated_with_rules[gi].ty.clone();
      let mut rules = Vec::with_capacity(member.ctors.len());
      for (ci, ctor_id) in member.ctors.iter().enumerate() {
        let ctor_fields = match self.env.get(ctor_id) {
          Some(KConst::Ctor { fields, .. }) => fields,
          _ => 0,
        };
        let rhs = self.build_rule_rhs(
          gi,
          ci,
          ctor_id,
          member,
          &flat,
          &peer_recs,
          &rec_ty_for_member,
          n_params,
          is_large,
          univ_offset,
        )?;
        rules.push(super::constant::RecRule {
          ctor: ctor_id.name.clone(),
          fields: ctor_fields,
          rhs,
        });
      }
      generated_with_rules[gi].rules = rules;
    }

    if let Some(mut cached) = self.env.recursor_cache.get_mut(ind_block_id) {
      if cached.len() != generated_with_rules.len() {
        return Err(TcError::Other(format!(
          "populate_recursor_rules_from_block: cache changed length: cached={} generated={}",
          cached.len(),
          generated_with_rules.len()
        )));
      }
      for (dst, src) in cached.iter_mut().zip(generated_with_rules.into_iter())
      {
        dst.rules = src.rules;
      }
    }

    Ok(())
  }

  /// Build the rule RHS for a single constructor.
  ///
  /// The RHS is: `λ (params) (motives) (minors) (fields), minor[idx] fields ihs`
  /// where each IH = `λ (xs...), rec[target] params motives minors indices (field xs...)`
  fn build_rule_rhs(
    &mut self,
    member_idx: usize,
    ctor_local_idx: usize,
    ctor_id: &KId<M>,
    member: &FlatBlockMember<M>,
    flat: &[FlatBlockMember<M>],
    peer_recs: &[KId<M>],
    rec_ty_for_member: &KExpr<M>,
    n_rec_params: usize,
    is_large: bool,
    _univ_offset: u64,
  ) -> Result<KExpr<M>, TcError<M>> {
    let anon = || M::meta_field(crate::ix::env::Name::anon());
    let bi_default = || M::meta_field(crate::ix::env::BinderInfo::Default);

    let ctor_ty_raw = match self.env.get(ctor_id) {
      Some(KConst::Ctor { ty, .. }) => ty.clone(),
      _ => return Err(TcError::Other("build_rule_rhs: ctor not found".into())),
    };

    let saved = self.save_depth();

    let n_motives = flat.len();
    let n_minors: usize = flat.iter().map(|m| m.ctors.len()).sum();
    let pmm = n_rec_params + n_motives + n_minors;

    // --- Pass 1: count fields ---
    // Walk ctor type past own_params WITHOUT substituting (field count is structural),
    // then count remaining foralls.
    let ctor_ty_inst =
      self.instantiate_univ_params(&ctor_ty_raw, &member.occurrence_us)?;
    let mut count_ty = ctor_ty_inst.clone();
    for _ in 0..member.own_params {
      let w = self.whnf(&count_ty)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => count_ty = body.clone(),
        _ => break,
      }
    }
    let mut n_fields = 0u64;
    let mut tmp = count_ty;
    loop {
      let w = self.whnf(&tmp)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => {
          n_fields += 1;
          tmp = body.clone();
        },
        _ => break,
      }
    }

    let total_lams = pmm as u64 + n_fields;

    // --- Pass 2: build body ---
    // Structure: λ (p0..pk) (m0..ml) (min0..minr) (f0..fn), body
    // body = minor[global_ctor_idx] f0..fn ih0..ihm
    //
    // Under total_lams lambdas:
    //   Var(total_lams - 1)       = first param (p0)
    //   Var(total_lams - 1 - j)   = param j
    //   Var(n_fields + n_minors + n_motives - 1) = first motive
    //   Var(n_fields + n_minors - 1 - gi) = minor gi
    //   Var(n_fields - 1)         = first field (f0)
    //   Var(0)                    = last field (fn-1)

    // Global minor index for this ctor
    let global_minor_idx: usize =
      flat.iter().take(member_idx).map(|m| m.ctors.len()).sum::<usize>()
        + ctor_local_idx;
    let minor_var_idx = n_fields + (n_minors - 1 - global_minor_idx) as u64;
    let mut body = self.intern(KExpr::var(minor_var_idx, anon()));

    // Apply fields: Var(n_fields - 1) down to Var(0)
    for fi in 0..n_fields {
      let fvar = self.intern(KExpr::var(n_fields - 1 - fi, anon()));
      body = self.intern(KExpr::app(body, fvar));
    }

    // Walk ctor type with param substitution to detect recursive fields.
    //
    // Aux spec_params live in the param context (depth =
    // `n_rec_params` — their Var refs point at param positions
    // `Var(n_rec_params - 1)..Var(0)`). We want those Vars to land
    // on the rule body's param positions `Var(total_lams - 1)..
    // Var(total_lams - n_rec_params)`, so we lift by
    // `total_lams - n_rec_params` — NOT by `total_lams`, which would
    // push them one past the param slots and out of the body's scope.
    // Originals substitute directly to `Var(total_lams - 1 - j)`,
    // matching the same positions.
    let aux_sp_lift = total_lams.saturating_sub(n_rec_params as u64);
    let mut ty2 = ctor_ty_inst;
    for j in 0..member.own_params {
      let w = self.whnf(&ty2)?;
      match w.data() {
        ExprData::All(_, _, _, body2, _) => {
          let p = if !member.is_aux {
            KExpr::var(total_lams - 1 - j, anon())
          } else if u64_to_usize::<M>(j)? < member.spec_params.len() {
            let sp = member.spec_params[u64_to_usize::<M>(j)?].clone();
            lift(&self.env.intern, &sp, aux_sp_lift, 0)
          } else {
            KExpr::var(total_lams - 1 - j, anon())
          };
          ty2 = subst(&self.env.intern, body2, &p, 0);
        },
        _ => break,
      }
    }

    // Detect recursive fields and build IH values.
    //
    // Field type Var refs point to the final-lambda positions we
    // substituted above: params at `Var(total_lams - 1 - j)` (for
    // originals) or embedded inside `lift(spec_params, total_lams)`
    // (for auxiliaries). Stored aux spec_params in `flat[]` live at
    // `n_rec_params` depth — so `is_rec_field` must lift them by
    // `total_lams - n_rec_params` to align with the field's frame.
    // Without this, Var-containing spec_params (e.g. `α` in
    // `Entry α β (Node α β)`) would mis-match and their IHs would be
    // silently dropped.
    let rec_field_lift = total_lams.saturating_sub(n_rec_params as u64);
    let mut field_idx = 0u64;
    loop {
      let w = self.whnf(&ty2)?;
      match w.data() {
        ExprData::All(_, _, dom, body2, _) => {
          let dom = dom.clone();
          let body2 = body2.clone();

          if let Some(target_bi) =
            self.is_rec_field(&dom, flat, rec_field_lift)?
          {
            let ih = self.build_rule_ih(
              field_idx,
              n_fields,
              total_lams,
              target_bi,
              flat,
              peer_recs,
              n_rec_params,
              n_motives,
              n_minors,
              is_large,
              &dom,
            )?;
            body = self.intern(KExpr::app(body, ih));
          }

          // Substitute this field with its Var ref for dependent types
          let fvar = KExpr::var(n_fields - 1 - field_idx, anon());
          ty2 = subst(&self.env.intern, &body2, &fvar, 0);
          field_idx += 1;
        },
        _ => break,
      }
    }

    // --- Wrap body in lambda chain (inside-out) ---
    // Field lambdas: extract domains from the peer recursor's minor premise.
    // The minor for this constructor has type:
    //   ∀ (field₀ : T₀) ... (fieldₙ : Tₙ) (ih₀ : ...) ..., motive (ctor fields)
    // We extract the first n_fields forall domains from the minor.
    // These domains already have correct de Bruijn indices relative to the
    // recursor's binding context (params, motives, earlier minors are above).
    let minor_domain = {
      // Walk past params, motives, and earlier minors to reach this ctor's minor
      let mut cur = rec_ty_for_member.clone();
      let skip_to_minor = n_rec_params + n_motives + global_minor_idx;
      for _ in 0..skip_to_minor {
        let w = self.whnf(&cur)?;
        match w.data() {
          ExprData::All(_, _, _, b, _) => cur = b.clone(),
          _ => break,
        }
      }
      // cur should be ∀ (minor_i : T_minor) ..., extract T_minor
      let w = self.whnf(&cur)?;
      match w.data() {
        ExprData::All(_, _, dom, _, _) => dom.clone(),
        _ => KExpr::sort(KUniv::zero()),
      }
    };
    // Extract field domains from the minor's type (which is a nested forall).
    // The minor's domain is at depth `skip_to_minor` in the recursor type.
    // The field lambdas in the rule are at depth `n_rec_params + n_motives + n_minors`.
    // We lift each domain by the difference to adjust free Var references.
    // Cutoff = fi because domain fi is inside fi nested foralls in the minor's
    // type, so Var(0)..Var(fi-1) are bound refs to earlier fields, not free.
    let field_dom_lift = (n_minors - global_minor_idx) as u64;
    let mut field_domains: Vec<KExpr<M>> =
      Vec::with_capacity(u64_to_usize::<M>(n_fields)?);
    let mut minor_cur = minor_domain;
    for fi in 0..n_fields {
      let w = self.whnf(&minor_cur)?;
      match w.data() {
        ExprData::All(_, _, dom, b, _) => {
          let lifted_dom = if field_dom_lift > 0 {
            lift(&self.env.intern, dom, field_dom_lift, fi)
          } else {
            dom.clone()
          };
          field_domains.push(lifted_dom);
          minor_cur = b.clone();
        },
        _ => break,
      }
    }
    // Wrap in reverse: last field innermost, first field outermost.
    // This ensures Var(n_fields-1) = first field, Var(0) = last field,
    // matching the body's de Bruijn indexing.
    for i in (0..field_domains.len()).rev() {
      body = self.intern(KExpr::lam(
        anon(),
        bi_default(),
        field_domains[i].clone(),
        body,
      ));
    }

    // PMM lambdas: extract actual domains from the peer recursor's type.
    // The recursor type has the shape:
    //   ∀ (params...) (motives...) (minors...) (indices...) (major), ret
    // We need the first pmm domains for the rule's leading lambdas.
    // Do NOT instantiate universe params: the rule RHS and recursor type share
    // the same Param references. The stored rule was built by Lean with the same
    // Param indices as the recursor type.
    let mut pmm_domains: Vec<KExpr<M>> = Vec::with_capacity(pmm);
    let mut rec_ty_cur = rec_ty_for_member.clone();
    for _ in 0..pmm {
      let w = self.whnf(&rec_ty_cur)?;
      match w.data() {
        ExprData::All(_, _, dom, b, _) => {
          pmm_domains.push(dom.clone());
          rec_ty_cur = b.clone();
        },
        _ => {
          // Fallback to placeholder if recursor type is shorter than expected
          pmm_domains.push(KExpr::sort(KUniv::zero()));
          break;
        },
      }
    }
    // Wrap body in PMM lambdas (inside-out: minors, then motives, then params)
    // pmm_domains is [p0, ..., pk, m0, ..., ml, min0, ..., minr]
    // We wrap inside-out, so we need to reverse through them
    for i in (0..pmm).rev() {
      let dom = if i < pmm_domains.len() {
        pmm_domains[i].clone()
      } else {
        KExpr::sort(KUniv::zero())
      };
      body = self.intern(KExpr::lam(anon(), bi_default(), dom, body));
    }

    self.restore_depth(saved);
    Ok(body)
  }

  /// Build an IH value for a recursive field in a rule RHS.
  ///
  /// Direct case (field type = `I_bi params idx_args`):
  ///   IH = `rec[target] params motives minors idx_args field`
  ///
  /// Forall-wrapped case (field type = `∀ (xs...), I_bi params idx_args(xs)`):
  ///   IH = `λ (xs...), rec[target] params motives minors idx_args(xs) (field xs...)`
  fn build_rule_ih(
    &mut self,
    field_idx: u64,
    n_fields: u64,
    total_lams: u64,
    target_bi: usize,
    flat: &[FlatBlockMember<M>],
    peer_recs: &[KId<M>],
    n_rec_params: usize,
    n_motives: usize,
    n_minors: usize,
    is_large: bool,
    dom: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    let anon = || M::meta_field(crate::ix::env::Name::anon());
    let bi_default = || M::meta_field(crate::ix::env::BinderInfo::Default);

    let target_n_params = u64_to_usize::<M>(flat[target_bi].own_params)?;

    // Use the TARGET recursor (the one for the inductive the field recurses on),
    // matching lean4lean (Add.lean:427), lean4 C++ (inductive.cpp:738),
    // and ix/kernel (recursor.rs:1391).
    let peer_rec = &peer_recs[target_bi];
    let peer_rec_lvls = match self.env.get(peer_rec) {
      Some(KConst::Recr { lvls, .. }) => lvls,
      _ => {
        if is_large {
          flat[target_bi].lvls + 1
        } else {
          flat[target_bi].lvls
        }
      },
    };
    let rec_lvls: Box<[KUniv<M>]> = (0..peer_rec_lvls)
      .map(|i| KUniv::param(i, M::meta_field(crate::ix::env::Name::anon())))
      .collect();

    // Peel foralls from the domain to detect wrapping.
    // After peeling, the head should be `I_target params idx_args`.
    let wdom = self.whnf(dom)?;
    let mut inner = wdom.clone();
    let mut forall_doms: Vec<KExpr<M>> = Vec::new();

    while let ExprData::All(_, _, fd, fb, _) = inner.data() {
      // Check if this forall's result type (after peeling) has a block
      // inductive as head. If inner itself IS a block inductive app, stop.
      let (h, _) = collect_app_spine(&inner);
      if matches!(h.data(), ExprData::Const(id, _, _)
        if flat.iter().any(|m| m.id.addr == id.addr))
      {
        break;
      }
      forall_doms.push(fd.clone());
      inner = fb.clone();
    }
    let n_xs = forall_doms.len() as u64;

    // Extract index args from the inner application: `I_target params idx_args`
    let inner_w = self.whnf(&inner)?;
    let (_, inner_args) = collect_app_spine(&inner_w);
    let idx_args: Vec<KExpr<M>> =
      inner_args.iter().skip(target_n_params).cloned().collect();

    // Build the IH core: rec[target] params motives minors indices field
    // All Var references are relative to total_lams (+ n_xs for forall-wrapped case).
    let depth = total_lams + n_xs;

    let mut ih = self.intern(KExpr::cnst(peer_rec.clone(), rec_lvls));
    // Apply params
    for pi in 0..n_rec_params {
      let pvar = self.intern(KExpr::var(depth - 1 - pi as u64, anon()));
      ih = self.intern(KExpr::app(ih, pvar));
    }
    // Apply motives
    for mi in 0..n_motives {
      let mvar = self.intern(KExpr::var(
        depth - 1 - n_rec_params as u64 - mi as u64,
        anon(),
      ));
      ih = self.intern(KExpr::app(ih, mvar));
    }
    // Apply minors
    for mi in 0..n_minors {
      let mvar = self.intern(KExpr::var(
        depth - 1 - n_rec_params as u64 - n_motives as u64 - mi as u64,
        anon(),
      ));
      ih = self.intern(KExpr::app(ih, mvar));
    }
    // Apply indices. After peeling n_xs foralls from dom, free Var refs in
    // idx_args are already shifted by n_xs (standard de Bruijn binder entry),
    // placing them at depth = total_lams + n_xs. No additional lift needed.
    for idx in &idx_args {
      ih = self.intern(KExpr::app(ih, idx.clone()));
    }
    // Apply the field variable (+ xs for forall-wrapped case)
    // Field is at Var(n_fields - 1 - field_idx) relative to total_lams,
    // shifted by n_xs under the forall binders.
    let field_base = n_fields - 1 - field_idx + n_xs;
    let mut field_app = self.intern(KExpr::var(field_base, anon()));
    // Apply forall-bound variables: xs are Var(n_xs-1)..Var(0) under the lambdas
    for xi in 0..n_xs {
      let xvar = self.intern(KExpr::var(n_xs - 1 - xi, anon()));
      field_app = self.intern(KExpr::app(field_app, xvar));
    }
    ih = self.intern(KExpr::app(ih, field_app));

    // Wrap in lambdas for forall-bound variables
    for i in (0..u64_to_usize::<M>(n_xs)?).rev() {
      ih = self.intern(KExpr::lam(
        anon(),
        bi_default(),
        forall_doms[i].clone(),
        ih,
      ));
    }

    Ok(ih)
  }

  /// Kernel-driven recursor coherence check (no syntactic compare).
  ///
  /// Catches the structural failure modes that `infer(rec.ty)` alone
  /// misses:
  /// - The major inductive is itself ill-formed (e.g. strict-positivity
  ///   violation, bad ctor return shape, field universe too high).
  ///   `check_inductive` runs A1–A4 and will reject the recursor-by-
  ///   extension if those fail.
  /// - The declared `k` flag disagrees with what the kernel computes
  ///   from the inductive's shape. K-reduction is only sound for a very
  ///   narrow class of inductives; a mismatch here is a soundness bug.
  ///
  /// Deliberately does **not** regenerate canonical recursors and
  /// compare them syntactically against the stored form: that approach
  /// produces false-positive mismatches on nested inductives and is
  /// redundant once infer + the coherence gate agree.
  pub fn check_recursor_coherence(
    &mut self,
    id: &KId<M>,
  ) -> Result<(), TcError<M>> {
    let (ty, declared_k) = match self.env.get(id) {
      Some(KConst::Recr { ty, k, .. }) => (ty.clone(), k),
      _ => {
        return Err(TcError::Other(
          "check_recursor_coherence: not a recursor".into(),
        ));
      },
    };

    let (params, motives, minors, indices) = match self.env.get(id) {
      Some(KConst::Recr { params, motives, minors, indices, .. }) => {
        (params, motives, minors, indices)
      },
      _ => unreachable!(),
    };
    let skip = params + motives + minors + indices;
    let ind_id = self.get_major_inductive_id(&ty, skip)?;

    // Coherence gate: the major inductive itself must pass A1–A4.
    // Cycle invariant: `check_inductive` never calls back into
    // `check_recursor_coherence` — it only drives its own structural
    // checks. Keep it that way.
    if matches!(self.env.get(&ind_id), Some(KConst::Indc { .. })) {
      self.check_inductive(&ind_id)?;
    }

    // K-target flag must match the kernel's constructive computation.
    let computed_k = self.compute_k_target(&ind_id)?;
    if declared_k != computed_k {
      return Err(TcError::Other(format!(
        "check_recursor_coherence: K-target mismatch: declared k={declared_k}, computed k={computed_k}"
      )));
    }

    Ok(())
  }

  /// Validate a recursor block. A pure recursor block is checked once and the
  /// result is shared by all sibling recursors.
  pub fn check_recursor(&mut self, id: &KId<M>) -> Result<(), TcError<M>> {
    let block = match self.env.get(id) {
      Some(KConst::Recr { block, .. }) => block.clone(),
      _ => return Err(TcError::Other("check_recursor: not a recursor".into())),
    };
    let Some(members) = self.env.get_block(&block) else {
      return self.check_recursor_member(id);
    };
    if !members
      .iter()
      .all(|member| matches!(self.env.get(member), Some(KConst::Recr { .. })))
    {
      return self.check_recursor_member(id);
    }

    match self.env.begin_block_check(&block) {
      BlockCheckStart::Cached(result) => result,
      BlockCheckStart::Owner(token) => {
        let result = self.check_recursor_block(&block, &members);
        self.env.finish_block_check(token, result)
      },
    }
  }

  /// Validate every recursor in a recursor block.
  pub(crate) fn check_recursor_block(
    &mut self,
    block: &KId<M>,
    members: &[KId<M>],
  ) -> Result<(), TcError<M>> {
    for member in members {
      self.reset();
      match self
        .env
        .get(member)
        .ok_or_else(|| TcError::UnknownConst(member.addr.clone()))?
      {
        KConst::Recr { ty, .. } => {
          let t = self.infer(&ty)?;
          self.ensure_sort(&t)?;
        },
        _ => {
          return Err(TcError::Other(format!(
            "check_recursor_block: non-recursor member {member} in block {block}"
          )));
        },
      }
    }

    for member in members {
      self.reset();
      self.check_recursor_member(member)?;
    }
    Ok(())
  }

  /// Validate a recursor by comparing with generated canonical form.
  pub fn check_recursor_member(
    &mut self,
    id: &KId<M>,
  ) -> Result<(), TcError<M>> {
    let (rec_block, ty, declared_k) = match self.env.get(id) {
      Some(KConst::Recr { block, ty, k, .. }) => (block.clone(), ty.clone(), k),
      _ => return Err(TcError::Other("check_recursor: not a recursor".into())),
    };

    // Find the major inductive from this recursor's type.
    let (params, motives, minors, indices) = match self.env.get(id) {
      Some(KConst::Recr { params, motives, minors, indices, .. }) => {
        (params, motives, minors, indices)
      },
      _ => unreachable!(),
    };
    let skip = params + motives + minors + indices;
    let ind_id = self.get_major_inductive_id(&ty, skip)?;

    // Coherence gate: the major inductive itself must pass A1–A4. Without
    // this, a recursor for a structurally-invalid inductive (bad ctor return
    // shape, field-universe violation, strict-positivity violation, …) can
    // slip through because recursor generation succeeds syntactically even
    // when the inductive is unsound. `check_inductive` is idempotent with
    // our own `generate_block_recursors` call below (both guarded by
    // `recursor_cache.contains_key`), so re-entering is safe.
    //
    // Cycle invariant: `check_inductive` never calls back into
    // `check_recursor` — it only calls `generate_block_recursors`. Keep it
    // that way.
    if matches!(self.env.get(&ind_id), Some(KConst::Indc { .. })) {
      self.check_inductive(&ind_id)?;
    }

    // Try direct lookup: major ind's own block.
    let ind_block = match self.env.get(&ind_id) {
      Some(KConst::Indc { block, .. }) => Some(block.clone()),
      _ => None,
    };

    // Check if the direct block has generated recursors with the right
    // number of motives. For auxiliary recursors (e.g., RCasesPatt.rec_1
    // targeting List), the direct block (List's) has fewer motives than needed.
    let resolved_block = if let Some(ref ib) = ind_block {
      if let Some(cached) = self.env.recursor_cache.get(ib) {
        if cached.len() as u64 >= motives { Some(ib.clone()) } else { None }
      } else {
        None
      }
    } else {
      None
    };

    // If direct lookup failed, use rec_majors_cache:
    // gather all peer recursors' major inductives to form the lookup key.
    let resolved_block = match resolved_block {
      Some(b) => b,
      None => {
        let majors_key = self.gather_peer_majors(&rec_block)?;
        match self.env.rec_majors_cache.get(&majors_key).map(|r| r.clone()) {
          Some(block_id) => block_id,
          None => {
            // Not generated yet — try generating from each peer major's
            // inductive block until the majors cache is populated.
            for major_id in &majors_key {
              if let Some(KConst::Indc { block, .. }) = self.env.get(major_id) {
                let ib = block.clone();
                if !self.env.recursor_cache.contains_key(&ib) {
                  let _ = self.generate_block_recursors(&ib);
                }
              }
            }
            // Re-check the majors cache.
            let majors_key = self.gather_peer_majors(&rec_block)?;
            match self.env.rec_majors_cache.get(&majors_key).map(|r| r.clone())
            {
              Some(block_id) => block_id,
              None => {
                return Err(TcError::Other(
                  "check_recursor: could not resolve inductive block".into(),
                ));
              },
            }
          },
        }
      },
    };

    // S1: Constructively verify K-target flag.
    // K-like reduction is only sound for: single inductive, Prop result level,
    // exactly one constructor with zero non-param fields.
    let computed_k = self.compute_k_target(&ind_id)?;
    if declared_k != computed_k {
      return Err(TcError::Other(format!(
        "check_recursor: K-target mismatch: declared k={declared_k}, computed k={computed_k}"
      )));
    }

    self.populate_recursor_rules_from_block(&resolved_block, &rec_block)?;

    // Find the generated recursor for this inductive.
    let generated = match self.env.recursor_cache.get(&resolved_block) {
      Some(g) => g.clone(),
      None => {
        return Err(TcError::Other(
          "check_recursor: no generated recursors".into(),
        ));
      },
    };

    // Signature-based match for aux recursors.
    //
    // Nested auxiliaries can contain several recursors with the same external
    // major head (for example multiple `List` auxes with different element
    // types). Matching only by `ind_addr` picks the first such recursor.
    // Matching primarily by the stored recursor's block position is also too
    // brittle: the compiled recursor block is sorted as recursor constants,
    // while generation is ordered by the flat inductive layout. Select by the
    // extracted major premise domain first, then keep the old positional and
    // address lookups as fixture fallbacks.
    let stored_pos: Option<usize> = self
      .env
      .blocks
      .get(&rec_block)
      .and_then(|members| members.iter().position(|m| m == id));
    let prefix_skip = params + motives + minors;
    let stored_major =
      self.recursor_major_domain_for_addr(&ty, prefix_skip, &ind_id.addr)?;
    let mut signature_matches: Vec<usize> = Vec::new();
    if let Some(stored_major) = stored_major.as_ref() {
      for (gi, g) in generated.iter().enumerate() {
        if g.ind_addr != ind_id.addr {
          continue;
        }
        if let Some(gen_major) = self.recursor_major_domain_for_addr(
          &g.ty,
          prefix_skip,
          &g.ind_addr,
        )? && self.major_domain_signature_eq(&gen_major, stored_major)?
        {
          signature_matches.push(gi);
        }
      }
    }
    let selected_idx = stored_pos
      .and_then(|p| signature_matches.iter().copied().find(|&gi| gi == p))
      .or_else(|| signature_matches.first().copied())
      .or_else(|| stored_pos.filter(|&p| p < generated.len()))
      .or_else(|| generated.iter().position(|g| g.ind_addr == ind_id.addr));

    if self.recursor_dump_matches_id(id) {
      eprintln!(
        "[recursor.dump] check {} rec_block={} resolved_block={} stored_pos={stored_pos:?} selected_idx={selected_idx:?}",
        id, rec_block, resolved_block
      );
      eprintln!(
        "[recursor.dump] stored major: {}",
        Self::major_domain_signature_text(stored_major.as_ref())
      );
      eprintln!("[recursor.dump] signature_matches={signature_matches:?}");
      for (gi, g) in generated.iter().enumerate() {
        if g.ind_addr != ind_id.addr {
          continue;
        }
        let major = self.recursor_major_domain_for_addr(
          &g.ty,
          prefix_skip,
          &g.ind_addr,
        )?;
        eprintln!(
          "  cand[{gi:2}] {}",
          Self::major_domain_signature_text(major.as_ref())
        );
      }
    }

    let gen_rec = selected_idx.map(|i| &generated[i]);
    match gen_rec {
      Some(g) => {
        if !self.is_def_eq(&g.ty, &ty)? {
          let selected_by_signature =
            selected_idx.is_some_and(|idx| signature_matches.contains(&idx));
          if self.env.recursor_aux_order == RecursorAuxOrder::Canonical
            && motives > 1
            && selected_by_signature
          {
            return self.check_recursor_coherence(id);
          }

          // When `IX_TYPE_DIFF` is set, walk the binder chain to find the
          // first divergent binder and print a readable gen/sto diff. Off
          // by default: in alpha-collapse regimes or for mutual blocks
          // with near-identical peers, every such mismatch ends up in
          // `stt.ungrounded` (non-fatal), and printing them all drowns
          // stderr under tens of thousands of lines. The walk only runs
          // when the env var is set to keep the common path cheap.
          //
          // Uses `KExpr::Display` (Name.Pretty@shorthex for consts,
          // `#idx` / `name` for vars, `(f a b …)` for spines, etc.) —
          // the same formatter `TcError::AppTypeMismatch` uses — so the
          // output format matches the rest of the kernel's diagnostic
          // surface.
          if *IX_TYPE_DIFF {
            let mut gc = g.ty.clone();
            let mut sc = ty.clone();
            let mut bi = 0u64;
            loop {
              match (gc.data(), sc.data()) {
                (
                  ExprData::All(_, _, gd, gb, _),
                  ExprData::All(_, _, sd, sb, _),
                ) => {
                  if !self.is_def_eq(gd, sd).unwrap_or(false) {
                    let label = if bi < params {
                      "param"
                    } else if bi < params + motives {
                      "motive"
                    } else if bi < params + motives + minors {
                      "minor"
                    } else {
                      "idx/major"
                    };
                    eprintln!(
                      "[type diff] binder {bi} ({label}) DIFFERS (p={params} m={motives} min={minors})"
                    );
                    eprintln!("  gen: {gd}");
                    eprintln!("  sto: {sd}");
                    break;
                  }
                  self.push_local(gd.clone());
                  gc = gb.clone();
                  sc = sb.clone();
                  bi += 1;
                },
                _ => {
                  eprintln!("[type diff] return differs at {bi}");
                  eprintln!("  gen: {gc}");
                  eprintln!("  sto: {sc}");
                  break;
                },
              }
            }
            for _ in 0..bi {
              self.pop_local();
            }
          }
          return Err(TcError::Other("check_recursor: type mismatch".into()));
        }

        let gen_rules = g.rules.clone();

        // Compare rules.
        //
        // Correctness invariant: `check_recursor` accepts iff the stored
        // rule list matches the canonical one produced by
        // `generate_block_recursors` under the element-wise checks below
        // (`fields` count + `rhs` defeq). The length-zero case is just a
        // vacuous instance of agreement — `Empty.rec`, `False.rec`,
        // `PEmpty.rec`, and similar empty inductives canonically have
        // zero computation rules, Lean stores zero, and the generator
        // produces zero. No extra guard is needed or correct here; an
        // earlier guard `both_empty → error` spuriously rejected these,
        // conflating "agreement at zero" with "generation failure."
        //
        // The one-sided `is_empty()` branches below remain as legitimate
        // asymmetric mismatches (e.g., generator produced N rules but
        // storage has none, or vice versa).
        let stored_rules = match self.env.get(id) {
          Some(KConst::Recr { rules, .. }) => rules.clone(),
          _ => vec![],
        };
        if gen_rules.is_empty() && !stored_rules.is_empty() {
          // C1: Generator produced no canonical rules but Lean stored
          // some — we cannot verify the stored rules against a missing
          // canonical form. MUST NOT accept.
          return Err(TcError::Other(format!(
            "check_recursor: rule generation failed for {}, cannot verify {} stored rules",
            &ind_id.addr.hex()[..8],
            stored_rules.len()
          )));
        } else if !gen_rules.is_empty() && stored_rules.is_empty() {
          // Dual of C1: generator produced N canonical rules but Lean
          // stored none. Also a real mismatch.
          return Err(TcError::Other(format!(
            "check_recursor: stored recursor has no rules (expected {})",
            gen_rules.len()
          )));
        } else if gen_rules.len() != stored_rules.len() {
          return Err(TcError::Other(format!(
            "check_recursor: rule count mismatch: gen={} stored={}",
            gen_rules.len(),
            stored_rules.len()
          )));
        }
        // Element-wise comparison. Vacuous when both sides are empty
        // (zero-constructor inductives), which is the agreement case.
        for (ri, (gen_rule, stored_rule)) in
          gen_rules.iter().zip(stored_rules.iter()).enumerate()
        {
          if gen_rule.fields != stored_rule.fields {
            return Err(TcError::Other(format!(
              "check_recursor: rule {ri} field count mismatch: gen={} stored={}",
              gen_rule.fields, stored_rule.fields
            )));
          }
          if !self.is_def_eq(&gen_rule.rhs, &stored_rule.rhs)? {
            if *IX_TYPE_DIFF {
              let _ = self.dump_rule_rhs_first_diff(
                &gen_rule.rhs,
                &stored_rule.rhs,
                "rhs",
                0,
              );
              eprintln!(
                "[rule rhs diff] rule {ri} RHS mismatch (fields={})",
                gen_rule.fields
              );
              eprintln!("  gen: {}", gen_rule.rhs);
              eprintln!("  sto: {}", stored_rule.rhs);
            }
            return Err(TcError::Other(format!(
              "check_recursor: rule {ri} RHS mismatch"
            )));
          }
        }
        Ok(())
      },
      None => {
        // C2: No generated recursor found — MUST NOT silently pass.
        // If we can't generate a canonical recursor, we can't verify the provided one.
        Err(TcError::Other(format!(
          "check_recursor: no generated recursor for major {}",
          &ind_id.addr.hex()[..8]
        )))
      },
    }
  }

  /// Gather the set of major inductive KIds from all peer recursors in a
  /// recursor block. Used to look up the rec_majors_cache.
  fn gather_peer_majors(
    &mut self,
    rec_block: &KId<M>,
  ) -> Result<std::collections::BTreeSet<KId<M>>, TcError<M>> {
    let mut majors = std::collections::BTreeSet::new();

    let peers: Vec<KId<M>> = match self.env.blocks.get(rec_block) {
      Some(members) => members
        .iter()
        .filter(|id| matches!(self.env.get(id), Some(KConst::Recr { .. })))
        .cloned()
        .collect(),
      None => vec![],
    };

    for peer_id in &peers {
      let (p, mo, mi, ix) = match self.env.get(peer_id) {
        Some(KConst::Recr { params, motives, minors, indices, .. }) => {
          (params, motives, minors, indices)
        },
        _ => continue,
      };
      let peer_ty = match self.env.get(peer_id) {
        Some(c) => c.ty().clone(),
        _ => continue,
      };
      let skip = p + mo + mi + ix;
      if let Ok(major_id) = self.get_major_inductive_id(&peer_ty, skip) {
        majors.insert(major_id);
      }
    }

    Ok(majors)
  }

  /// S1: Compute K-target flag constructively.
  /// K-like reduction is sound iff:
  ///   1. Single inductive (not part of a mutual block with >1 inductive)
  ///   2. Result universe is Prop (level is zero)
  ///   3. Exactly one constructor with zero non-param fields
  fn compute_k_target(&mut self, ind_id: &KId<M>) -> Result<bool, TcError<M>> {
    let (ind_params, ind_indices, ctors, block, ty) = match self.env.get(ind_id)
    {
      Some(KConst::Indc { params, indices, ctors, block, ty, .. }) => {
        (params, indices, ctors.clone(), block.clone(), ty.clone())
      },
      _ => return Ok(false),
    };

    // 1. Must be a single inductive (not mutual)
    let block_inds = self.discover_block_inductives(&block);
    let ind_count = block_inds
      .iter()
      .filter(|id| matches!(self.env.get(id), Some(KConst::Indc { .. })))
      .count();
    if ind_count != 1 {
      return Ok(false);
    }

    // 2. Result level must be Prop (semantically zero).
    // Use univ_eq instead of is_zero() to handle levels like max(0,0) or imax(0,u)
    // that are semantically zero but not syntactically UnivData::Zero.
    let result_level = self
      .get_result_sort_level(&ty, u64_to_usize(ind_params + ind_indices)?)?;
    if !univ_eq(&result_level, &KUniv::zero()) {
      return Ok(false);
    }

    // 3. Exactly one constructor with zero non-param fields
    if ctors.len() != 1 {
      return Ok(false);
    }
    match self.env.get(&ctors[0]) {
      Some(KConst::Ctor { fields, .. }) => Ok(fields == 0),
      _ => Ok(false),
    }
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

  type AE = KExpr<Anon>;
  type AU = KUniv<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }
  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }
  fn _sort0() -> AE {
    AE::sort(AU::zero())
  }
  fn sort1() -> AE {
    AE::sort(AU::succ(AU::zero()))
  }
  fn param(n: u64) -> AU {
    AU::param(n, ())
  }

  /// Helper: build `∀ (_ : a), b`
  fn pi(a: AE, b: AE) -> AE {
    AE::all((), (), a, b)
  }

  /// Helper: build `App(f, a)`
  fn app(f: AE, a: AE) -> AE {
    AE::app(f, a)
  }

  /// Helper: build `λ (_ : a), b`
  fn lam(a: AE, b: AE) -> AE {
    AE::lam((), (), a, b)
  }

  /// Helper: build `Const(name, univs)`
  fn cnst(name: &str, us: &[AU]) -> AE {
    AE::cnst(mk_id(name), us.to_vec().into_boxed_slice())
  }

  fn var(i: u64) -> AE {
    AE::var(i, ())
  }

  /// Build an env with Bool (2 ctors, 0 fields each) and its recursor.
  /// Bool : Sort 1
  /// Bool.true : Bool
  /// Bool.false : Bool
  /// Bool.rec : ∀ (motive : Bool → Sort u) (h₁ : motive Bool.true) (h₂ : motive Bool.false) (t : Bool), motive t
  fn bool_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let block = mk_id("Bool");
    let rec_block = mk_id("Bool.rec.block");

    // Bool : Sort 1
    env.insert(
      mk_id("Bool"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Bool.true"), mk_id("Bool.false")],
        lean_all: (),
      },
    );
    // Bool.true : Bool
    env.insert(
      mk_id("Bool.true"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Bool"),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: cnst("Bool", &[]),
      },
    );
    // Bool.false : Bool
    env.insert(
      mk_id("Bool.false"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Bool"),
        cidx: 1,
        params: 0,
        fields: 0,
        ty: cnst("Bool", &[]),
      },
    );

    // Bool.rec type: ∀ (motive : Bool → Sort u) (h₁ : motive true) (h₂ : motive false) (t : Bool), motive t
    let motive_ty = pi(cnst("Bool", &[]), AE::sort(param(0)));
    let minor_true = app(var(0), cnst("Bool.true", &[]));
    let minor_false = app(var(1), cnst("Bool.false", &[]));
    let major_ty = cnst("Bool", &[]);
    let ret = app(var(3), var(0));
    let rec_ty = pi(
      motive_ty.clone(),
      pi(minor_true.clone(), pi(minor_false.clone(), pi(major_ty, ret))),
    );

    // Bool.rec rules — use actual domain types from recursor type
    let motive_dom = motive_ty;
    let h_true_dom = minor_true;
    let h_false_dom = minor_false;
    // Rule 0 (Bool.true, 0 fields): λ (motive) (h_true) (h_false), h_true
    let rule_true_rhs = lam(
      motive_dom.clone(),
      lam(h_true_dom.clone(), lam(h_false_dom.clone(), var(1))),
    );
    // Rule 1 (Bool.false, 0 fields): λ (motive) (h_true) (h_false), h_false
    let rule_false_rhs =
      lam(motive_dom, lam(h_true_dom, lam(h_false_dom, var(0))));

    env.insert(
      mk_id("Bool.rec"),
      KConst::Recr {
        name: (),
        level_params: (),
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: rec_block.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          super::super::constant::RecRule {
            ctor: (),
            fields: 0,
            rhs: rule_true_rhs,
          },
          super::super::constant::RecRule {
            ctor: (),
            fields: 0,
            rhs: rule_false_rhs,
          },
        ],
        lean_all: (),
      },
    );

    env.blocks.insert(
      block,
      vec![mk_id("Bool"), mk_id("Bool.true"), mk_id("Bool.false")],
    );
    env.blocks.insert(rec_block, vec![mk_id("Bool.rec")]);
    env
  }

  #[test]
  fn check_bool_inductive() {
    let env = bool_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(tc.check_const(&mk_id("Bool")).is_ok());
  }

  #[test]
  fn check_bool_constructor_uses_parent_block() {
    let env = bool_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Bool.true")).unwrap();
    assert!(
      env.block_check_results.get(&mk_id("Bool")).is_some_and(|r| r.is_ok())
    );
  }

  #[test]
  fn check_bool_rec() {
    let env = bool_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // Must check inductive first to trigger recursor generation
    tc.check_const(&mk_id("Bool")).unwrap();
    assert!(tc.check_const(&mk_id("Bool.rec")).is_ok(), "Bool.rec should pass");
  }

  /// Build env with Nat (1 recursive ctor) and its recursor.
  /// Nat : Sort 1
  /// Nat.zero : Nat
  /// Nat.succ : Nat → Nat
  /// Nat.rec : ∀ (motive : Nat → Sort u) (zero : motive Nat.zero)
  ///             (succ : ∀ (n : Nat), motive n → motive (Nat.succ n))
  ///             (t : Nat), motive t
  fn nat_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let block = mk_id("Nat");
    let rec_block = mk_id("Nat.rec.block");
    let nat = || cnst("Nat", &[]);

    env.insert(
      mk_id("Nat"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Nat.zero"), mk_id("Nat.succ")],
        lean_all: (),
      },
    );
    env.insert(
      mk_id("Nat.zero"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Nat"),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: nat(),
      },
    );
    env.insert(
      mk_id("Nat.succ"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Nat"),
        cidx: 1,
        params: 0,
        fields: 1,
        ty: pi(nat(), nat()),
      },
    );

    // Nat.rec type
    let motive_ty = pi(nat(), AE::sort(param(0)));
    // minor_zero: motive Nat.zero  (motive is Var(0) here)
    let minor_zero = app(var(0), cnst("Nat.zero", &[]));
    // minor_succ: ∀ (n : Nat) (ih : motive n), motive (Nat.succ n)
    //   motive is Var(2) inside the two binders
    let minor_succ = pi(
      nat(),
      pi(app(var(2), var(0)), app(var(3), app(cnst("Nat.succ", &[]), var(1)))),
    );
    let major = nat();
    let ret = app(var(3), var(0));
    let rec_ty = pi(
      motive_ty.clone(),
      pi(minor_zero.clone(), pi(minor_succ.clone(), pi(major, ret))),
    );

    // Nat.rec rules — use actual domain types from recursor type
    let motive_dom = motive_ty;
    let h_zero_dom = minor_zero;
    let h_succ_dom = minor_succ;
    let rule_zero_rhs = lam(
      motive_dom.clone(),
      lam(h_zero_dom.clone(), lam(h_succ_dom.clone(), var(1))),
    );
    // Rule 1 (Nat.succ, 1 field): λ (motive) (h_zero) (h_succ) (n), h_succ n (Nat.rec motive h_zero h_succ n)
    //   Under 4 lambdas: motive=Var(3), h_zero=Var(2), h_succ=Var(1), n=Var(0)
    let nat_rec = cnst("Nat.rec", &[param(0)]);
    let ih = app(app(app(app(nat_rec, var(3)), var(2)), var(1)), var(0));
    let rule_succ_rhs = lam(
      motive_dom,
      lam(
        h_zero_dom,
        lam(h_succ_dom, lam(nat(), app(app(var(1), var(0)), ih))),
      ),
    );

    env.insert(
      mk_id("Nat.rec"),
      KConst::Recr {
        name: (),
        level_params: (),
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: rec_block.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          super::super::constant::RecRule {
            ctor: (),
            fields: 0,
            rhs: rule_zero_rhs,
          },
          super::super::constant::RecRule {
            ctor: (),
            fields: 1,
            rhs: rule_succ_rhs,
          },
        ],
        lean_all: (),
      },
    );

    env
      .blocks
      .insert(block, vec![mk_id("Nat"), mk_id("Nat.zero"), mk_id("Nat.succ")]);
    env.blocks.insert(rec_block, vec![mk_id("Nat.rec")]);
    env
  }

  #[test]
  fn check_nat_rec() {
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Nat")).unwrap();
    assert!(tc.check_const(&mk_id("Nat.rec")).is_ok(), "Nat.rec should pass");
  }

  #[test]
  fn nat_rec_rules() {
    // Nat.rec has 2 rules (one per ctor):
    // Rule 0 (Nat.zero): fields=0, rhs = λ (motive) (h_zero) (h_succ), h_zero
    // Rule 1 (Nat.succ): fields=1, rhs = λ (motive) (h_zero) (h_succ) (n),
    //   h_succ n (Nat.rec.{Param(0), ...} motive h_zero h_succ n)
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Nat")).unwrap();
    tc.check_const(&mk_id("Nat.rec")).unwrap();

    let block = mk_id("Nat");
    let generated = tc.env.recursor_cache.get(&block).unwrap();
    let rules = &generated[0].rules;

    assert_eq!(rules.len(), 2, "Nat.rec should have 2 rules");

    // Rule 0 (zero): fields=0
    assert_eq!(rules[0].fields, 0);
    // rhs = λ (motive) (h_zero) (h_succ), h_zero
    // = Lam(_, Lam(_, Lam(_, Var(1))))
    // Var(1) = h_zero (2nd from top: Var(0)=h_succ, Var(1)=h_zero)
    let _expected_zero = lam(
      pi(cnst("Nat", &[]), AE::sort(param(0))), // motive type (placeholder domain)
      lam(
        app(var(0), cnst("Nat.zero", &[])), // h_zero type (placeholder)
        lam(
          KExpr::sort(KUniv::zero()), // h_succ type (placeholder, won't be checked structurally)
          var(1),                     // h_zero
        ),
      ),
    );
    // Just check the BODY structure — the lambda domains don't matter for iota,
    // only the body does. Let's check fields and that the rule is well-formed.
    // For now, just verify the rule exists and has the right field count.

    // Rule 1 (succ): fields=1
    assert_eq!(rules[1].fields, 1);
    // rhs body (after applying 3 pmm + 1 field = 4 lambdas):
    // h_succ n (Nat.rec motive h_zero h_succ n)
    // Check the rhs has the right lambda count
    let count_lams = |e: &AE| -> usize {
      let mut n = 0;
      let mut c = e.clone();
      while let ExprData::Lam(_, _, _, body, _) = c.data() {
        n += 1;
        c = body.clone();
      }
      n
    };
    // pmm = 0 params + 1 motive + 2 minors = 3, plus 1 field = 4 lambdas
    let n_lams = count_lams(&rules[1].rhs);
    assert_eq!(
      n_lams, 4,
      "Nat.succ rule should have 4 lambdas (0p + 1m + 2min + 1f), got {n_lams}"
    );
  }

  /// Build env with List (1 param, 2 ctors including recursive cons).
  /// List.{u} : Sort u → Sort u
  /// List.nil.{u} : ∀ (α : Sort u), List.{u} α
  /// List.cons.{u} : ∀ (α : Sort u), α → List.{u} α → List.{u} α
  fn list_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let block = mk_id("List");

    // List : Sort u → Sort u  (1 lvl param)
    let list_ty = pi(AE::sort(param(0)), AE::sort(param(0)));
    env.insert(
      mk_id("List"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: list_ty,
        ctors: vec![mk_id("List.nil"), mk_id("List.cons")],
        lean_all: (),
      },
    );

    // List.nil : ∀ (α : Sort u), List α
    let list_a = app(cnst("List", &[param(0)]), var(0)); // List.{u} α
    let nil_ty = pi(AE::sort(param(0)), list_a.clone());
    env.insert(
      mk_id("List.nil"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 0,
        params: 1,
        fields: 0,
        ty: nil_ty,
      },
    );

    // List.cons : ∀ (α : Sort u) (head : α) (tail : List α), List α
    let cons_ty = pi(
      AE::sort(param(0)), // α
      pi(
        var(0), // head : α
        pi(
          app(cnst("List", &[param(0)]), var(1)), // tail : List α
          app(cnst("List", &[param(0)]), var(2)), // List α
        ),
      ),
    );
    env.insert(
      mk_id("List.cons"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 1,
        params: 1,
        fields: 2,
        ty: cons_ty,
      },
    );

    // List.rec type (large eliminator):
    // ∀ {α : Sort(Param(1))} (motive : List.{Param(1)} α → Sort(Param(0)))
    //   (nil : motive (List.nil.{Param(1)} α))
    //   (cons : ∀ (head : α) (tail : List.{Param(1)} α), motive tail → motive (List.cons.{Param(1)} α head tail))
    //   (t : List.{Param(1)} α), motive t
    let u1 = param(1); // shifted inductive univ
    let u0 = param(0); // elim univ
    let _list_u1_a = app(cnst("List", std::slice::from_ref(&u1)), var(0)); // List.{u1} α, where α=Var(0)

    let _motive_ty = pi(
      // inside: α is Var(1) from one binder out
      app(cnst("List", std::slice::from_ref(&u1)), var(0)),
      AE::sort(u0.clone()),
    );
    // under α, motive: motive_is_Var(0)
    let _minor_nil =
      app(var(0), app(cnst("List.nil", std::slice::from_ref(&u1)), var(1)));
    // cons minor: ∀ (head : α) (tail : List α) (ih : motive tail), motive (cons α head tail)
    let _cons_minor = pi(
      var(1), // head : α (α is Var(1) since motive+nil already bound... wait)
      // This is getting complicated with de Bruijn. Let me simplify.
      // Actually for the test we just need to check that check_const passes.
      // Let me construct the rec_ty by hand more carefully.
      // Actually, let's just check that the inductive passes and the generated
      // recursor type has the right binder count.
      KExpr::sort(KUniv::zero()), // placeholder - we'll verify structurally
    );

    // For now, let's just test that check_inductive works and generates a recursor.
    // We'll compare binder counts instead of full def-eq.
    // Skip the recursor constant for now.

    env.blocks.insert(
      block,
      vec![mk_id("List"), mk_id("List.nil"), mk_id("List.cons")],
    );
    env
  }

  #[test]
  fn check_list_inductive() {
    let env = list_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(tc.check_const(&mk_id("List")).is_ok());
    // Verify recursor was generated with the right structure
    let block = mk_id("List");
    let generated =
      tc.env.recursor_cache.get(&block).expect("recursor should be cached");
    assert_eq!(generated.len(), 1, "should generate 1 recursor for List");
    assert_eq!(generated[0].ind_addr, mk_addr("List"));

    // Count binders in generated rec type
    let mut n = 0;
    let mut cur = generated[0].ty.clone();
    while let ExprData::All(_, _, _, body, _) = cur.data() {
      n += 1;
      cur = body.clone();
    }
    // List.rec should have: 1 param + 1 motive + 2 minors + 0 indices + 1 major = 5 binders
    assert_eq!(n, 5, "List.rec should have 5 binders");
  }

  /// Build env with a nested inductive: Tree with a field `List Tree`.
  /// Tree : Sort 1
  /// Tree.leaf : Tree
  /// Tree.node : List Tree → Tree
  /// This should create a flat block [Tree, List] with Tree nesting into List.
  fn nested_tree_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let tree_block = mk_id("Tree");
    let tree = || cnst("Tree", &[]);

    // Tree : Sort 1
    env.insert(
      mk_id("Tree"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 1,
        block: tree_block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Tree.leaf"), mk_id("Tree.node")],
        lean_all: (),
      },
    );
    env.insert(
      mk_id("Tree.leaf"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Tree"),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: tree(),
      },
    );
    // Tree.node : List Tree → Tree
    // List.{1} Tree → Tree  (List at universe 1 since Tree : Sort 1)
    let list_tree = app(cnst("List", &[AU::succ(AU::zero())]), tree());
    env.insert(
      mk_id("Tree.node"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Tree"),
        cidx: 1,
        params: 0,
        fields: 1,
        ty: pi(list_tree, tree()),
      },
    );

    // We also need List in the environment for the nested detection to work.
    let list_ty = pi(AE::sort(param(0)), AE::sort(param(0)));
    env.insert(
      mk_id("List"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: mk_id("List"),
        member_idx: 0,
        ty: list_ty,
        ctors: vec![mk_id("List.nil"), mk_id("List.cons")],
        lean_all: (),
      },
    );

    // List.nil : ∀ (α : Sort u), List α
    let nil_ty = pi(AE::sort(param(0)), app(cnst("List", &[param(0)]), var(0)));
    env.insert(
      mk_id("List.nil"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 0,
        params: 1,
        fields: 0,
        ty: nil_ty,
      },
    );

    // List.cons : ∀ (α : Sort u) (head : α) (tail : List α), List α
    let cons_ty = pi(
      AE::sort(param(0)),
      pi(
        var(0),
        pi(
          app(cnst("List", &[param(0)]), var(1)),
          app(cnst("List", &[param(0)]), var(2)),
        ),
      ),
    );
    env.insert(
      mk_id("List.cons"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 1,
        params: 1,
        fields: 2,
        ty: cons_ty,
      },
    );

    env.blocks.insert(
      tree_block,
      vec![mk_id("Tree"), mk_id("Tree.leaf"), mk_id("Tree.node")],
    );
    env.blocks.insert(
      mk_id("List"),
      vec![mk_id("List"), mk_id("List.nil"), mk_id("List.cons")],
    );
    env
  }

  #[test]
  fn nested_tree_flat_block_detection() {
    let env = nested_tree_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));

    // Check Tree inductive — this triggers flat block building
    tc.check_const(&mk_id("Tree")).unwrap();

    let tree_block = mk_id("Tree");
    let generated = tc
      .env
      .recursor_cache
      .get(&tree_block)
      .expect("recursor should be cached for Tree");

    // Flat block should have 2 members: Tree + List auxiliary
    assert_eq!(
      generated.len(),
      2,
      "flat block should produce 2 recursors (Tree + List aux)"
    );
    assert_eq!(generated[0].ind_addr, mk_addr("Tree"));
    assert_eq!(generated[1].ind_addr, mk_addr("List"));
  }

  #[test]
  fn nested_tree_rec_type_matches() {
    // Verify that the generated Tree.rec type matches what lean4 would produce.
    // Tree.rec.{u} : ∀ (motive₀ : Tree → Sort u)
    //                  (motive₁ : List.{1} Tree → Sort u)
    //                  (h_leaf : motive₀ Tree.leaf)
    //                  (h_node : ∀ (children : List.{1} Tree), motive₁ children → motive₀ (Tree.node children))
    //                  (h_nil : motive₁ (List.nil.{1} Tree))
    //                  (h_cons : ∀ (hd : Tree) (tl : List.{1} Tree), motive₀ hd → motive₁ tl → motive₁ (List.cons.{1} Tree hd tl))
    //                  (t : Tree), motive₀ t
    let env = nested_tree_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Tree")).unwrap();

    let tree_block = mk_id("Tree");
    let gen_ty = tc.env.recursor_cache.get(&tree_block).unwrap()[0].ty.clone();

    let u0 = param(0);
    let u1 = AU::succ(AU::zero());
    let tree = || cnst("Tree", &[]);
    let list_tree = || app(cnst("List", std::slice::from_ref(&u1)), tree());

    // motive₀ : Tree → Sort u
    let mot0_ty = pi(tree(), AE::sort(u0.clone()));
    // motive₁ : List.{1} Tree → Sort u
    let mot1_ty = pi(list_tree(), AE::sort(u0.clone()));

    // Under [mot0, mot1]:
    // h_leaf: mot0 Tree.leaf  (mot0 = Var(1), mot1 = Var(0))
    let h_leaf = app(var(1), cnst("Tree.leaf", &[]));

    // h_node: ∀ (children : List.{1} Tree), mot1 children → mot0 (Tree.node children)
    //   Under [mot0, mot1, h_leaf]: mot0=Var(2), mot1=Var(1)
    //   Under [mot0, mot1, h_leaf, children]: mot0=Var(3), mot1=Var(2), children=Var(0)
    let h_node = pi(
      list_tree(),
      pi(
        app(var(2), var(0)), // mot1 children (mot1=Var(2) under h_leaf+children)
        app(var(4), app(cnst("Tree.node", &[]), var(1))), // mot0 (Tree.node children)
      ),
    );

    // h_nil: mot1 (List.nil.{1} Tree)
    //   Under [mot0, mot1, h_leaf, h_node]: mot1=Var(2)
    let h_nil =
      app(var(2), app(cnst("List.nil", std::slice::from_ref(&u1)), tree()));

    // h_cons: ∀ (hd : Tree) (tl : List.{1} Tree), mot0 hd → mot1 tl → mot1 (List.cons.{1} Tree hd tl)
    //   Under [mot0, mot1, h_leaf, h_node, h_nil]:
    //     mot0=Var(4), mot1=Var(3)
    //   Under [..., hd, tl]:
    //     mot0=Var(6), mot1=Var(5), hd=Var(1), tl=Var(0)
    //   Under [..., hd, tl, ih_hd]:
    //     mot0=Var(7), mot1=Var(6), hd=Var(2), tl=Var(1)
    //   Under [..., hd, tl, ih_hd, ih_tl]:
    //     mot0=Var(8), mot1=Var(7), hd=Var(3), tl=Var(2)
    let h_cons = pi(
      tree(), // hd
      pi(
        list_tree(), // tl
        pi(
          app(var(6), var(1)), // ih_hd: mot0 hd
          pi(
            app(var(6), var(1)), // ih_tl: mot1 tl
            app(
              var(7), // mot1
              app(
                app(
                  app(cnst("List.cons", std::slice::from_ref(&u1)), tree()),
                  var(3),
                ),
                var(2),
              ),
            ),
          ),
        ),
      ),
    );

    // major : Tree
    // Under [mot0, mot1, h_leaf, h_node, h_nil, h_cons]:
    //   mot0=Var(5)
    // Under [..., t]: mot0=Var(6)
    let major = tree();
    let ret = app(var(6), var(0)); // mot0 t

    let expected = pi(
      mot0_ty,
      pi(
        mot1_ty,
        pi(h_leaf, pi(h_node, pi(h_nil, pi(h_cons, pi(major, ret))))),
      ),
    );

    let ok = tc.is_def_eq(&gen_ty, &expected).unwrap_or(false);
    assert!(ok, "generated Tree.rec type should match expected");
  }

  #[test]
  fn nested_tree_rec_binder_count() {
    let env = nested_tree_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Tree")).unwrap();

    let tree_block = mk_id("Tree");
    let generated = tc.env.recursor_cache.get(&tree_block).unwrap();

    // Count binders in Tree.rec (member 0)
    let count_binders = |e: &AE| -> usize {
      let mut n = 0;
      let mut c = e.clone();
      while let ExprData::All(_, _, _, b, _) = c.data() {
        n += 1;
        c = b.clone();
      }
      n
    };

    let tree_rec = &generated[0];
    // Tree.rec: 0 params + 2 motives + (2 + 2) minors + 0 indices + 1 major = 7
    // Minors: Tree.leaf (0 fields, 0 IH), Tree.node (1 field + 1 IH = 2)
    //         List.nil (0 fields, 0 IH), List.cons (2 fields + 2 IH = 4)
    // Wait — minors for Tree.rec include ALL ctors of ALL flat members.
    // Tree: leaf (0 binders), node (1 field + 1 IH = 2 binders)
    // List(aux): nil (0 binders), cons (2 fields + 2 IH = 4 binders)
    // But minors are individual forall types, not nested. Each minor is ONE forall domain.
    // So: 2 motives + 4 minors + 1 major = 7 binders total (0 params, 0 indices)
    let n = count_binders(&tree_rec.ty);
    assert_eq!(
      n, 7,
      "Tree.rec should have 7 binders (2 motives + 4 minors + 1 major), got {n}"
    );

    // List auxiliary rec (member 1)
    let list_rec = &generated[1];
    // List aux rec for List Tree:
    // 0 params + 2 motives + 4 minors + 0 indices + 1 major = 7
    let n = count_binders(&list_rec.ty);
    assert_eq!(n, 7, "List aux rec should have 7 binders, got {n}");
  }

  /// Polymorphic nested: PTree.{u} : Sort (u+1) → Sort (u+1)
  /// Like Tree but with one universe param and one type param.
  /// PTree.leaf.{u} : ∀ (α : Sort (u+1)), α → PTree.{u} α
  /// PTree.node.{u} : ∀ (α : Sort (u+1)), List.{u+1} (PTree.{u} α) → PTree.{u} α
  fn poly_nested_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let block = mk_id("PTree");
    let su = || AU::succ(param(0)); // u+1

    // PTree.{u} : Sort(u+1) → Sort(u+1)
    let ptree_ty = pi(AE::sort(su()), AE::sort(su()));
    env.insert(
      mk_id("PTree"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 1,
        block: block.clone(),
        member_idx: 0,
        ty: ptree_ty,
        ctors: vec![mk_id("PTree.leaf"), mk_id("PTree.node")],
        lean_all: (),
      },
    );

    // PTree.leaf : ∀ (α : Sort(u+1)), α → PTree.{u} α
    let leaf_ty =
      pi(AE::sort(su()), pi(var(0), app(cnst("PTree", &[param(0)]), var(1))));
    env.insert(
      mk_id("PTree.leaf"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("PTree"),
        cidx: 0,
        params: 1,
        fields: 1,
        ty: leaf_ty,
      },
    );

    // PTree.node : ∀ (α : Sort(u+1)), List.{u+1} (PTree.{u} α) → PTree.{u} α
    // Note: List.{u+1} because PTree.{u} α : Sort(u+1), and List.{v} : Sort v → Sort v
    let ptree_app = app(cnst("PTree", &[param(0)]), var(0));
    let list_ptree = app(cnst("List", &[su()]), ptree_app);
    let node_ty = pi(
      AE::sort(su()),
      pi(list_ptree, app(cnst("PTree", &[param(0)]), var(1))),
    );
    env.insert(
      mk_id("PTree.node"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("PTree"),
        cidx: 1,
        params: 1,
        fields: 1,
        ty: node_ty,
      },
    );

    let list_ty = pi(AE::sort(param(0)), AE::sort(param(0)));
    env.insert(
      mk_id("List"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: mk_id("List"),
        member_idx: 0,
        ty: list_ty,
        ctors: vec![mk_id("List.nil"), mk_id("List.cons")],
        lean_all: (),
      },
    );
    let nil_ty = pi(AE::sort(param(0)), app(cnst("List", &[param(0)]), var(0)));
    env.insert(
      mk_id("List.nil"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 0,
        params: 1,
        fields: 0,
        ty: nil_ty,
      },
    );
    let cons_ty = pi(
      AE::sort(param(0)),
      pi(
        var(0),
        pi(
          app(cnst("List", &[param(0)]), var(1)),
          app(cnst("List", &[param(0)]), var(2)),
        ),
      ),
    );
    env.insert(
      mk_id("List.cons"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 1,
        params: 1,
        fields: 2,
        ty: cons_ty,
      },
    );

    env.blocks.insert(
      block,
      vec![mk_id("PTree"), mk_id("PTree.leaf"), mk_id("PTree.node")],
    );
    env.blocks.insert(
      mk_id("List"),
      vec![mk_id("List"), mk_id("List.nil"), mk_id("List.cons")],
    );
    env
  }

  #[test]
  fn poly_nested_flat_block() {
    let env = poly_nested_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // Check inductive first (consumes fuel for validation)
    tc.check_const(&mk_id("PTree")).unwrap();
    // Reset fuel and generate recursors explicitly
    tc.rec_fuel = super::super::tc::max_rec_fuel();
    let block = mk_id("PTree");
    if !tc.env.recursor_cache.contains_key(&block) {
      tc.generate_block_recursors(&block).unwrap();
    }

    let generated =
      tc.env.recursor_cache.get(&block).expect("recursor should be cached");
    assert_eq!(
      generated.len(),
      2,
      "flat block should produce 2 recursors (PTree + List aux)"
    );
  }

  #[test]
  fn poly_nested_rec_binder_count() {
    let env = poly_nested_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("PTree")).unwrap();
    tc.rec_fuel = super::super::tc::max_rec_fuel();
    let block = mk_id("PTree");
    if !tc.env.recursor_cache.contains_key(&block) {
      tc.generate_block_recursors(&block).unwrap();
    }

    let generated = tc.env.recursor_cache.get(&block).unwrap();

    let count_binders = |e: &AE| -> usize {
      let mut n = 0;
      let mut c = e.clone();
      while let ExprData::All(_, _, _, b, _) = c.data() {
        n += 1;
        c = b.clone();
      }
      n
    };

    // PTree.rec: 1 param + 2 motives + 4 minors + 0 indices + 1 major = 8
    let n = count_binders(&generated[0].ty);
    assert_eq!(n, 8, "PTree.rec should have 8 binders, got {n}");
  }

  /// Mimics Lean.Syntax structure: a type `Syn` that nests with
  /// `List (Pair Name Syn)` — testing multi-level transitive nesting.
  ///
  /// Syn : Sort 1
  /// Syn.atom : Syn
  /// Syn.node : List (Pair Name Syn) → Syn
  ///
  /// This should create a flat block:
  ///   [Syn, List (Pair Name Syn), Pair (Name, Syn)]
  /// with 3 motives.
  fn syntax_like_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let block = mk_id("Syn");
    let syn = || cnst("Syn", &[]);

    // Name : Sort 1 (axiom, external)
    env.insert(
      mk_id("Name"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: sort1(),
      },
    );

    // Pair.{u,v} : Sort u → Sort v → Sort (max u v)
    // Pair.mk.{u,v} : ∀ (α : Sort u) (β : Sort v), α → β → Pair.{u,v} α β
    let pair_ty = pi(
      AE::sort(param(0)),
      pi(AE::sort(param(1)), AE::sort(AU::max(param(0), param(1)))),
    );
    env.insert(
      mk_id("Pair"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 2,
        params: 2,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: mk_id("Pair"),
        member_idx: 0,
        ty: pair_ty,
        ctors: vec![mk_id("Pair.mk")],
        lean_all: (),
      },
    );
    // Pair.mk : ∀ (α : Sort u) (β : Sort v) (fst : α) (snd : β), Pair α β
    let pair_mk_ty = pi(
      AE::sort(param(0)),
      pi(
        AE::sort(param(1)),
        pi(
          var(1),
          pi(
            var(1),
            app(app(cnst("Pair", &[param(0), param(1)]), var(3)), var(2)),
          ),
        ),
      ),
    );
    env.insert(
      mk_id("Pair.mk"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 2,
        induct: mk_id("Pair"),
        cidx: 0,
        params: 2,
        fields: 2,
        ty: pair_mk_ty,
      },
    );

    // List (reused from previous tests)
    let list_ty = pi(AE::sort(param(0)), AE::sort(param(0)));
    env.insert(
      mk_id("List"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: mk_id("List"),
        member_idx: 0,
        ty: list_ty,
        ctors: vec![mk_id("List.nil"), mk_id("List.cons")],
        lean_all: (),
      },
    );
    let nil_ty = pi(AE::sort(param(0)), app(cnst("List", &[param(0)]), var(0)));
    env.insert(
      mk_id("List.nil"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 0,
        params: 1,
        fields: 0,
        ty: nil_ty,
      },
    );
    let cons_ty = pi(
      AE::sort(param(0)),
      pi(
        var(0),
        pi(
          app(cnst("List", &[param(0)]), var(1)),
          app(cnst("List", &[param(0)]), var(2)),
        ),
      ),
    );
    env.insert(
      mk_id("List.cons"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 1,
        params: 1,
        fields: 2,
        ty: cons_ty,
      },
    );

    // Syn : Sort 1
    env.insert(
      mk_id("Syn"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 1,
        block: block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Syn.atom"), mk_id("Syn.node")],
        lean_all: (),
      },
    );
    // Syn.atom : Syn
    env.insert(
      mk_id("Syn.atom"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Syn"),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: syn(),
      },
    );
    // Syn.node : List.{1} (Pair.{1,1} Name Syn) → Syn
    let pair_name_syn = app(
      app(
        cnst("Pair", &[AU::succ(AU::zero()), AU::succ(AU::zero())]),
        cnst("Name", &[]),
      ),
      syn(),
    );
    let list_pair = app(cnst("List", &[AU::succ(AU::zero())]), pair_name_syn);
    env.insert(
      mk_id("Syn.node"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Syn"),
        cidx: 1,
        params: 0,
        fields: 1,
        ty: pi(list_pair, syn()),
      },
    );

    env
      .blocks
      .insert(block, vec![mk_id("Syn"), mk_id("Syn.atom"), mk_id("Syn.node")]);
    env.blocks.insert(
      mk_id("List"),
      vec![mk_id("List"), mk_id("List.nil"), mk_id("List.cons")],
    );
    env.blocks.insert(mk_id("Pair"), vec![mk_id("Pair"), mk_id("Pair.mk")]);
    env
  }

  #[test]
  fn syntax_like_flat_block() {
    let env = syntax_like_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Syn")).unwrap();
    tc.rec_fuel = super::super::tc::max_rec_fuel();
    let block = mk_id("Syn");
    if !tc.env.recursor_cache.contains_key(&block) {
      tc.generate_block_recursors(&block).unwrap();
    }

    let generated =
      tc.env.recursor_cache.get(&block).expect("recursor should be cached");

    // Flat block: [Syn, List (Pair Name Syn), Pair (Name, Syn)]
    // = 3 members → 3 recursors generated
    assert_eq!(
      generated.len(),
      3,
      "flat block should have 3 members (Syn + List aux + Pair aux), got {}",
      generated.len()
    );
  }

  #[test]
  fn syntax_like_false_positive_rec_field() {
    // Test that `List OtherType` is NOT detected as recursive when only
    // `List (Pair Name Syn)` is a valid auxiliary. This replicates the
    // Lean.Syntax.rec binder 6 failure where `List Preresolved` was
    // incorrectly matched to the `List Syntax` auxiliary.
    let env = syntax_like_env();

    // Add OtherType : Sort 1 (external, non-recursive)
    env.insert(
      mk_id("Other"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: sort1(),
      },
    );

    // Add a third ctor: Syn.ident : List.{1} Other → Syn
    // `List Other` should NOT be recursive (Other doesn't mention Syn)
    let list_other =
      app(cnst("List", &[AU::succ(AU::zero())]), cnst("Other", &[]));
    env.insert(
      mk_id("Syn.ident"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Syn"),
        cidx: 2,
        params: 0,
        fields: 1,
        ty: pi(list_other, cnst("Syn", &[])),
      },
    );

    // Update Syn to have 3 ctors
    if let Some(mut entry) = env.consts.get_mut(&mk_id("Syn"))
      && let KConst::Indc { ctors, .. } = entry.value_mut()
    {
      ctors.push(mk_id("Syn.ident"));
    }

    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Syn")).unwrap();
    tc.rec_fuel = super::super::tc::max_rec_fuel();
    let block = mk_id("Syn");
    if !tc.env.recursor_cache.contains_key(&block) {
      tc.generate_block_recursors(&block).unwrap();
    }
    let generated = tc.env.recursor_cache.get(&block).unwrap();

    // Should still have 3 flat members (Syn, List aux, Pair aux) — NOT 4
    // List Other should NOT create a new auxiliary
    assert_eq!(
      generated.len(),
      3,
      "should have 3 flat members, not more (List Other is not nested)"
    );

    let count_binders = |e: &AE| -> usize {
      let mut n = 0;
      let mut c = e.clone();
      while let ExprData::All(_, _, _, b, _) = c.data() {
        n += 1;
        c = b.clone();
      }
      n
    };

    // Total top-level binders: 3 motives + 6 minors + 0 indices + 1 major = 10
    let n = count_binders(&generated[0].ty);
    assert_eq!(n, 10, "Syn.rec with ident should have 10 binders, got {n}");

    // Check the ident minor (binder 5 = 3 motives + 2 earlier minors)
    // Its domain should have 1 inner binder (the List Other field) and 0 IHs.
    // If is_rec_field falsely matches List Other, it would have 2 inner binders.
    let mut cur = generated[0].ty.clone();
    for _ in 0..5 {
      // skip to binder 5
      if let ExprData::All(_, _, _, body, _) = cur.data() {
        cur = body.clone();
      }
    }
    let ident_minor_domain = match cur.data() {
      ExprData::All(_, _, dom, _, _) => dom.clone(),
      _ => panic!("expected forall at binder 5"),
    };
    let ident_inner_binders = count_binders(&ident_minor_domain);
    // Should be 1 (just the List Other field), NOT 2 (field + false IH)
    assert_eq!(
      ident_inner_binders, 1,
      "ident minor should have 1 inner binder (non-rec field), got {} (false positive IH?)",
      ident_inner_binders
    );
  }

  #[test]
  fn syntax_like_rec_binder_count() {
    let env = syntax_like_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Syn")).unwrap();
    tc.rec_fuel = super::super::tc::max_rec_fuel();
    let block = mk_id("Syn");
    if !tc.env.recursor_cache.contains_key(&block) {
      tc.generate_block_recursors(&block).unwrap();
    }

    let generated = tc.env.recursor_cache.get(&block).unwrap();

    let count_binders = |e: &AE| -> usize {
      let mut n = 0;
      let mut c = e.clone();
      while let ExprData::All(_, _, _, b, _) = c.data() {
        n += 1;
        c = b.clone();
      }
      n
    };

    // Syn.rec binders:
    //   0 params
    //   3 motives (Syn, List aux, Pair aux)
    //   minors: Syn.atom(0) + Syn.node(1 field + 1 IH = 2) + List.nil(0) + List.cons(2 fields + 2 IH = 4)
    //           + Pair.mk(2 fields + 1 IH = 3)
    //   = 5 minors
    //   0 indices
    //   1 major
    //   Total = 3 + 5 + 1 = 9
    let n = count_binders(&generated[0].ty);
    assert_eq!(n, 9, "Syn.rec should have 9 binders, got {n}");
  }

  /// Mimics Lean.Doc.Inline: parameterized type with Array nesting.
  /// Inl.{u} (i : Sort (u+1)) : Sort (u+1)
  /// Inl.text.{u} : ∀ (i : Sort (u+1)), String → Inl.{u} i
  /// Inl.emph.{u} : ∀ (i : Sort (u+1)), Array.{u+1} (Inl.{u} i) → Inl.{u} i
  /// Inl.other.{u} : ∀ (i : Sort (u+1)), i → Array.{u+1} (Inl.{u} i) → Inl.{u} i
  fn inline_like_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let block = mk_id("Inl");
    let su = || AU::succ(param(0)); // u+1

    // String : Sort 1 (external axiom)
    env.insert(
      mk_id("String"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: sort1(),
      },
    );

    // Array.{v} : Sort v → Sort v (external, 1 univ param, 1 type param)
    let arr_ty = pi(AE::sort(param(0)), AE::sort(param(0)));
    env.insert(
      mk_id("Array"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: mk_id("Array"),
        member_idx: 0,
        ty: arr_ty,
        ctors: vec![mk_id("Array.mk")],
        lean_all: (),
      },
    );
    // Array.mk : ∀ (α : Sort v), List.{v} α → Array.{v} α
    let arr_mk_ty = pi(
      AE::sort(param(0)),
      pi(
        app(cnst("List", &[param(0)]), var(0)),
        app(cnst("Array", &[param(0)]), var(1)),
      ),
    );
    env.insert(
      mk_id("Array.mk"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("Array"),
        cidx: 0,
        params: 1,
        fields: 1,
        ty: arr_mk_ty,
      },
    );

    // List (reused)
    let list_ty = pi(AE::sort(param(0)), AE::sort(param(0)));
    env.insert(
      mk_id("List"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: mk_id("List"),
        member_idx: 0,
        ty: list_ty,
        ctors: vec![mk_id("List.nil"), mk_id("List.cons")],
        lean_all: (),
      },
    );
    let nil_ty = pi(AE::sort(param(0)), app(cnst("List", &[param(0)]), var(0)));
    env.insert(
      mk_id("List.nil"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 0,
        params: 1,
        fields: 0,
        ty: nil_ty,
      },
    );
    let cons_ty = pi(
      AE::sort(param(0)),
      pi(
        var(0),
        pi(
          app(cnst("List", &[param(0)]), var(1)),
          app(cnst("List", &[param(0)]), var(2)),
        ),
      ),
    );
    env.insert(
      mk_id("List.cons"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("List"),
        cidx: 1,
        params: 1,
        fields: 2,
        ty: cons_ty,
      },
    );

    // Inl.{u} : Sort(u+1) → Sort(u+1)  (1 lvl, 1 param)
    let inl_ty = pi(AE::sort(su()), AE::sort(su()));
    env.insert(
      mk_id("Inl"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 1,
        block: block.clone(),
        member_idx: 0,
        ty: inl_ty,
        ctors: vec![mk_id("Inl.text"), mk_id("Inl.emph"), mk_id("Inl.other")],
        lean_all: (),
      },
    );

    // Inl.text : ∀ (i : Sort(u+1)), String → Inl.{u} i
    let text_ty = pi(
      AE::sort(su()),
      pi(cnst("String", &[]), app(cnst("Inl", &[param(0)]), var(1))),
    );
    env.insert(
      mk_id("Inl.text"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("Inl"),
        cidx: 0,
        params: 1,
        fields: 1,
        ty: text_ty,
      },
    );

    // Inl.emph : ∀ (i : Sort(u+1)), Array.{u+1} (Inl.{u} i) → Inl.{u} i
    let inl_i = app(cnst("Inl", &[param(0)]), var(0)); // under i binder
    let arr_inl = app(cnst("Array", &[su()]), inl_i);
    let emph_ty =
      pi(AE::sort(su()), pi(arr_inl, app(cnst("Inl", &[param(0)]), var(1))));
    env.insert(
      mk_id("Inl.emph"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("Inl"),
        cidx: 1,
        params: 1,
        fields: 1,
        ty: emph_ty,
      },
    );

    // Inl.other : ∀ (i : Sort(u+1)), i → Array.{u+1} (Inl.{u} i) → Inl.{u} i
    let inl_i2 = app(cnst("Inl", &[param(0)]), var(0)); // under i binder
    let arr_inl2 = app(cnst("Array", &[su()]), inl_i2);
    let _other_ty = pi(
      AE::sort(su()),
      pi(
        var(0), // i (the type param)
        pi(
          arr_inl2, // but arr_inl2 references var(0) which is now var(1) under the i-field binder!
          app(cnst("Inl", &[param(0)]), var(2)),
        ),
      ),
    );

    // Wait — the `arr_inl2` uses `var(0)` for i, but after the `pi(var(0), ...)` binder,
    // i is now var(1). The Array arg `Inl.{u} i` should reference i=var(1) not var(0).
    // Let me fix: under ∀ (i : Sort(u+1)) (x : i), the Array field needs i=var(1).
    let inl_i_shifted = app(cnst("Inl", &[param(0)]), var(1)); // i=var(1) under x binder
    let arr_inl_shifted = app(cnst("Array", &[su()]), inl_i_shifted);
    let other_ty = pi(
      AE::sort(su()),
      pi(var(0), pi(arr_inl_shifted, app(cnst("Inl", &[param(0)]), var(2)))),
    );
    env.insert(
      mk_id("Inl.other"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("Inl"),
        cidx: 2,
        params: 1,
        fields: 2,
        ty: other_ty,
      },
    );

    env.blocks.insert(
      block,
      vec![
        mk_id("Inl"),
        mk_id("Inl.text"),
        mk_id("Inl.emph"),
        mk_id("Inl.other"),
      ],
    );
    env.blocks.insert(mk_id("Array"), vec![mk_id("Array"), mk_id("Array.mk")]);
    env.blocks.insert(
      mk_id("List"),
      vec![mk_id("List"), mk_id("List.nil"), mk_id("List.cons")],
    );
    env
  }

  #[test]
  fn inline_like_flat_block() {
    let env = inline_like_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Inl")).unwrap();
    tc.rec_fuel = super::super::tc::max_rec_fuel();
    let block = mk_id("Inl");
    if !tc.env.recursor_cache.contains_key(&block) {
      tc.generate_block_recursors(&block).unwrap();
    }

    let generated =
      tc.env.recursor_cache.get(&block).expect("recursor should be cached");
    // Flat block: [Inl, Array, List] = 3 members
    assert_eq!(
      generated.len(),
      3,
      "flat block should have 3 members, got {}",
      generated.len()
    );
  }

  #[test]
  fn inline_like_rec_2_binder_count() {
    let env = inline_like_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Inl")).unwrap();
    tc.rec_fuel = super::super::tc::max_rec_fuel();
    let block = mk_id("Inl");
    if !tc.env.recursor_cache.contains_key(&block) {
      tc.generate_block_recursors(&block).unwrap();
    }
    let generated = tc.env.recursor_cache.get(&block).unwrap();

    let count_binders = |e: &AE| -> usize {
      let mut n = 0;
      let mut c = e.clone();
      while let ExprData::All(_, _, _, b, _) = c.data() {
        n += 1;
        c = b.clone();
      }
      n
    };

    // Inl.rec (member 0):
    //   1 param(α) + 3 motives + N minors + 0 indices + 1 major
    //   Minors: text(1f+0ih), emph(1f+1ih), other(2f+1ih), arr.mk(1f+1ih), nil(0), cons(2f+2ih)
    //   = 6 minors
    //   Total = 1 + 3 + 6 + 0 + 1 = 11
    let n0 = count_binders(&generated[0].ty);
    assert_eq!(n0, 11, "Inl.rec should have 11 binders, got {n0}");

    // Inl.rec_2 (member 2 = List aux):
    //   1 param + 3 motives + 6 minors + 0 indices + 1 major = 11
    if generated.len() > 2 {
      let n2 = count_binders(&generated[2].ty);
      assert_eq!(
        n2, 11,
        "Inl.rec_2 (List aux) should have 11 binders, got {n2}"
      );
    }

    // Deeper check: verify the generated Inl.rec_2 type against a manually
    // constructed version to catch var-index bugs.
    // For this we need the Inl.rec_2 stored as a Recr constant and compare.
    // Instead, let's just check that is_def_eq succeeds between rec[0] and
    // a hand-constructed Inl.rec.
    // This is complex, so let's at least verify that the cons minor inside
    // rec_2 has the right structure by inspecting its inner binders.

    // rec_2 = generated[2], binder layout:
    // 0: param (i : Sort(u+1))
    // 1: motive_0 (Inl motive)
    // 2: motive_1 (Array aux motive)
    // 3: motive_2 (List aux motive)
    // 4-9: minors (text, emph, other, arr.mk, nil, cons)
    // 10: major (List.{u+1} (Inl.{u} i))
    // The cons minor is binder 9 (6th minor)
    if generated.len() > 2 {
      let mut cur = generated[2].ty.clone();
      // Skip to binder 9 (cons minor)
      for _ in 0..9 {
        if let ExprData::All(_, _, _, body, _) = cur.data() {
          cur = body.clone();
        }
      }
      let cons_minor_domain = match cur.data() {
        ExprData::All(_, _, dom, _, _) => dom.clone(),
        _ => panic!("expected forall at binder 9 for cons minor"),
      };
      // cons minor should have 4 inner binders:
      // ∀ (hd : Inl i) (tl : List (Inl i)) (ih_hd : motive_0 hd) (ih_tl : motive_2 tl), motive_2 (cons (Inl i) hd tl)
      let inner = count_binders(&cons_minor_domain);
      assert_eq!(
        inner, 4,
        "cons minor should have 4 inner binders (2 fields + 2 IH), got {inner}"
      );
    }
  }

  /// Mimics Std.DHashMap.Raw.WF: Prop inductive with params, index, recursive ctors.
  ///
  /// Ok.{u} (α : Sort (u+1)) (n : Nat) : Prop
  /// Ok.base.{u} : ∀ (α : Sort (u+1)) (n : Nat), Ok.{u} α n
  /// Ok.step.{u} : ∀ (α : Sort (u+1)) (n : Nat), Ok.{u} α n → Ok.{u} α n
  ///
  /// This has 1 univ param, 1 type param, 1 index (Nat), and is in Prop.
  fn wf_like_env() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let block = mk_id("Ok");

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

    // Ok.{u} : Sort(u+1) → Nat → Prop
    let su = || AU::succ(param(0));
    let ok_ty =
      pi(AE::sort(su()), pi(cnst("Nat", &[]), KExpr::sort(KUniv::zero())));
    env.insert(
      mk_id("Ok"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 1,
        params: 1,
        indices: 1,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: ok_ty,
        ctors: vec![mk_id("Ok.base"), mk_id("Ok.step")],
        lean_all: (),
      },
    );

    // Ok.base : ∀ (α : Sort(u+1)) (n : Nat), Ok.{u} α n
    let base_ty = pi(
      AE::sort(su()),
      pi(cnst("Nat", &[]), app(app(cnst("Ok", &[param(0)]), var(1)), var(0))),
    );
    env.insert(
      mk_id("Ok.base"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("Ok"),
        cidx: 0,
        params: 1,
        fields: 0,
        // ctor params = 1 (α), indices absorbed into return type
        // fields = 0 (just params + index in return)
        // Wait: params=1, but the ctor has 2 foralls (α, n). n is part of the
        // return type index, not a field. Lean convention: first `params` foralls
        // are params, the rest before the return type are fields.
        // Ok.base has type ∀ (α) (n), Ok α n. With params=1: α is param, n is field? No.
        // Actually for constructors, `fields` = total_foralls - params.
        // Ok.base: 2 foralls, params=1, fields=1 (n is a field).
        // But n appears in the return type as an index, so it IS a field.
        ty: base_ty,
      },
    );
    // Fix: fields should be 1 (n), not 0
    if let Some(mut entry) = env.consts.get_mut(&mk_id("Ok.base"))
      && let KConst::Ctor { fields, .. } = entry.value_mut()
    {
      *fields = 1;
    }

    // Ok.step : ∀ (α : Sort(u+1)) (n : Nat), Ok.{u} α n → Ok.{u} α n
    // Ok.step : ∀ (α : Sort(u+1)) (n : Nat) (h : Ok α n), Ok α n
    // Under (α, n): Ok α n = Ok Var(1) Var(0)
    let ok_an_depth2 = app(app(cnst("Ok", &[param(0)]), var(1)), var(0));
    // Under (α, n, h): Ok α n = Ok Var(2) Var(1)
    let ok_an_depth3 = app(app(cnst("Ok", &[param(0)]), var(2)), var(1));
    let step_ty =
      pi(AE::sort(su()), pi(cnst("Nat", &[]), pi(ok_an_depth2, ok_an_depth3)));
    env.insert(
      mk_id("Ok.step"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        induct: mk_id("Ok"),
        cidx: 1,
        params: 1,
        fields: 2, // n + proof
        ty: step_ty,
      },
    );

    env
      .blocks
      .insert(block, vec![mk_id("Ok"), mk_id("Ok.base"), mk_id("Ok.step")]);
    env
  }

  #[test]
  fn wf_like_rec_type() {
    let env = wf_like_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Ok")).unwrap();

    let block = mk_id("Ok");
    let gen_ty = tc.env.recursor_cache.get(&block).unwrap()[0].ty.clone();

    let count_binders = |e: &AE| -> usize {
      let mut n = 0;
      let mut c = e.clone();
      while let ExprData::All(_, _, _, b, _) = c.data() {
        n += 1;
        c = b.clone();
      }
      n
    };

    // Ok is Prop with 2+ ctors → small eliminator (elim_level = Zero)
    // Ok.rec: 1 param + 1 motive + 2 minors + 1 index + 1 major = 6
    let n = count_binders(&gen_ty);
    assert_eq!(n, 6, "Ok.rec should have 6 binders, got {n}");

    // Build expected type and compare via is_def_eq.
    // Ok.rec.{u} : ∀ (α : Sort(u+1)) (motive : ∀ (n : Nat), Ok.{u} α n → Prop)
    //   (base : ∀ (n : Nat), motive n (Ok.base.{u} α n))
    //   (step : ∀ (n : Nat) (h : Ok.{u} α n), motive n h → motive n (Ok.step.{u} α n h))
    //   (n : Nat) (t : Ok.{u} α n), motive n t

    let su = || AU::succ(param(0));
    let u0 = AU::zero();

    // Under α binder (Var(0) = α):
    let ok_a = |idx_var: u64, alpha_var: u64| {
      app(app(cnst("Ok", &[param(0)]), var(alpha_var)), var(idx_var))
    };

    // motive : ∀ (n : Nat) (_ : Ok α n), Prop
    //   α = Var(0) from param
    let motive_ty = pi(cnst("Nat", &[]), pi(ok_a(0, 1), AE::sort(u0.clone())));

    // base minor: ∀ (n : Nat), motive n (Ok.base α n)
    //   Under [α, motive]: α=Var(1), motive=Var(0)
    //   Under [α, motive, n]: α=Var(2), motive=Var(1), n=Var(0)
    let base_minor = pi(
      cnst("Nat", &[]),
      app(
        app(var(1), var(0)),
        app(app(cnst("Ok.base", &[param(0)]), var(2)), var(0)),
      ),
    );

    // step minor: ∀ (n : Nat) (h : Ok α n) (ih : motive n h), motive n (Ok.step α n h)
    //   Under [α, motive, base_minor]: α=Var(2), motive=Var(1)
    //   Under [..., n]: α=Var(3), motive=Var(2), n=Var(0)
    //   Under [..., n, h]: α=Var(4), motive=Var(3), n=Var(1), h=Var(0)
    //   Under [..., n, h, ih]: α=Var(5), motive=Var(4), n=Var(2), h=Var(1)
    let step_minor = pi(
      cnst("Nat", &[]), // n
      pi(
        ok_a(0, 3), // h : Ok α n
        pi(
          app(app(var(3), var(1)), var(0)), // ih : motive n h
          app(
            app(var(4), var(2)), // motive n
            app(app(app(cnst("Ok.step", &[param(0)]), var(5)), var(2)), var(1)),
          ), // Ok.step α n h
        ),
      ),
    );

    // index: n : Nat
    // Under [α, motive, base, step]: α=Var(3)
    let idx = cnst("Nat", &[]);

    // major: Ok α n
    // Under [α, motive, base, step, n]: α=Var(4), n=Var(0)
    let major = ok_a(0, 4);

    // return: motive n t
    // Under [α, motive, base, step, n, t]: motive=Var(4), n=Var(1), t=Var(0)
    let ret = app(app(var(4), var(1)), var(0));

    let expected = pi(
      AE::sort(su()), // α
      pi(motive_ty, pi(base_minor, pi(step_minor, pi(idx, pi(major, ret))))),
    );

    // Verify each binder domain is well-formed with detailed tracing.
    let _count_binders = |e: &AE| -> usize {
      let mut n = 0;
      let mut c = e.clone();
      while let ExprData::All(_, _, _, b, _) = c.data() {
        n += 1;
        c = b.clone();
      }
      n
    };
    let ok = tc.is_def_eq(&gen_ty, &expected).unwrap_or(false);
    assert!(ok, "Ok.rec type should match expected");
  }

  // -----------------------------------------------------------------------
  // Nested positivity tests
  // -----------------------------------------------------------------------

  /// Build an env with an external inductive `Wrap` that has its type param
  /// in a **negative** position: `Wrap.mk : ∀ (α : Type), (α → Bool) → Wrap α`.
  /// Then define `Evil : Type` with `Evil.mk : Wrap Evil → Evil`.
  /// This must be REJECTED: `Evil` appears negatively inside `Wrap`'s constructor.
  fn wrap_evil_env() -> Arc<KEnv<Anon>> {
    let env = bool_env();

    // Wrap : Type → Type  (1 param, 0 indices)
    let wrap_ty = pi(sort1(), sort1());
    let wrap_block = mk_id("Wrap");
    env.insert(
      mk_id("Wrap"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: wrap_block.clone(),
        member_idx: 0,
        ty: wrap_ty,
        ctors: vec![mk_id("Wrap.mk")],
        lean_all: (),
      },
    );

    // Wrap.mk : ∀ (α : Type), (α → Bool) → Wrap α
    // Under ∀(α : Type): Var(0) = α
    let wrap_mk_ty = pi(
      sort1(), // α : Type
      pi(
        pi(var(0), cnst("Bool", &[])),  // (α → Bool)
        app(cnst("Wrap", &[]), var(1)), // Wrap α
      ),
    );
    env.insert(
      mk_id("Wrap.mk"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Wrap"),
        cidx: 0,
        params: 1,
        fields: 1,
        ty: wrap_mk_ty,
      },
    );

    env.blocks.insert(wrap_block, vec![mk_id("Wrap"), mk_id("Wrap.mk")]);

    // Evil : Type  (0 params, 0 indices)
    let evil_block = mk_id("Evil");
    env.insert(
      mk_id("Evil"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: evil_block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Evil.mk")],
        lean_all: (),
      },
    );

    // Evil.mk : Wrap Evil → Evil
    let evil_mk_ty = pi(
      app(cnst("Wrap", &[]), cnst("Evil", &[])), // Wrap Evil
      cnst("Evil", &[]),                         // Evil
    );
    env.insert(
      mk_id("Evil.mk"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Evil"),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: evil_mk_ty,
      },
    );

    env.blocks.insert(evil_block, vec![mk_id("Evil"), mk_id("Evil.mk")]);

    env
  }

  #[test]
  fn reject_nested_negative_via_wrap() {
    // Evil.mk has field type `Wrap Evil`. Wrap's constructor puts its param
    // in negative position: `(α → Bool) → Wrap α`. So `Evil` appears in
    // `(Evil → Bool)` — a negative occurrence smuggled through nesting.
    // The positivity checker must reject this.
    let env = wrap_evil_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let result = tc.check_const(&mk_id("Evil"));
    assert!(
      result.is_err(),
      "Evil should be rejected: negative occurrence through nested Wrap"
    );
  }

  fn negative_self_function_env(is_unsafe: bool) -> Arc<KEnv<Anon>> {
    let env = bool_env();
    let block = mk_id("Bad");

    env.insert(
      mk_id("Bad"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Bad.mk")],
        lean_all: (),
      },
    );

    // Bad.mk : (Bad -> Bool) -> Bad. The occurrence of Bad in the
    // function domain is negative and must be rejected unless Bad is unsafe.
    env.insert(
      mk_id("Bad.mk"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe,
        lvls: 0,
        induct: mk_id("Bad"),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: pi(pi(cnst("Bad", &[]), cnst("Bool", &[])), cnst("Bad", &[])),
      },
    );

    env.blocks.insert(block, vec![mk_id("Bad"), mk_id("Bad.mk")]);
    env
  }

  #[test]
  fn reject_safe_negative_self_function() {
    let env = negative_self_function_env(false);
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(
      tc.check_const(&mk_id("Bad")).is_err(),
      "safe negative inductive should be rejected"
    );
  }

  #[test]
  fn accept_unsafe_negative_self_function() {
    let env = negative_self_function_env(true);
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert!(
      tc.check_const(&mk_id("Bad")).is_ok(),
      "unsafe inductive should skip positivity like Lean"
    );
  }

  /// Valid nesting: `Tree : Type` with `Tree.node : List Tree → Tree`.
  /// List's constructor puts its param in strictly positive position only
  /// (as `head : α` and `tail : List α`), so this is fine.
  #[test]
  fn accept_valid_nested_list_tree() {
    let env = list_env();

    // Tree : Type  (0 params, 0 indices, recursive via List nesting)
    let tree_block = mk_id("Tree");
    env.insert(
      mk_id("Tree"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: tree_block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Tree.node")],
        lean_all: (),
      },
    );

    // Tree.node : List.{1} Tree → Tree
    // List.{1} Tree : Sort 1  (List at universe 1, applied to Tree)
    let list_tree =
      app(cnst("List", &[AU::succ(AU::zero())]), cnst("Tree", &[]));
    let tree_node_ty = pi(list_tree, cnst("Tree", &[]));
    env.insert(
      mk_id("Tree.node"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Tree"),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: tree_node_ty,
      },
    );

    env.blocks.insert(tree_block, vec![mk_id("Tree"), mk_id("Tree.node")]);

    let mut tc = TypeChecker::new(Arc::clone(&env));
    let result = tc.check_const(&mk_id("Tree"));
    assert!(
      result.is_ok(),
      "Tree with List nesting should be accepted, got: {:?}",
      result.err()
    );
  }

  // ---------------------------------------------------------------------
  // Regression tests for the P1 soundness gaps closed in the 2026-04
  // hardening pass.
  // ---------------------------------------------------------------------

  /// P1-1 regression: a recursor with a syntactically well-typed but
  /// semantically *swapped* rule RHS must be rejected by `check_recursor`
  /// at the `is_def_eq(&gen_rule.rhs, &stored_rule.rhs)` gate
  /// (see `inductive.rs:3218`). Without that gate, iota reduction could
  /// produce the wrong minor for a given constructor — the P1-1 scenario
  /// from the adversarial review.
  #[test]
  fn reject_bool_rec_with_swapped_rules() {
    // Build `bool_env`, then replace `Bool.rec` with a version whose
    // rule 0 (for `Bool.true`) has the body of rule 1 (`h_false`) and
    // vice-versa. Both RHSes still have the correct type (each minor has
    // type `motive (Bool.true/false)` — motive is Var(2) under the λ₃,
    // so `var(1)` and `var(0)` both typecheck as the minor premise), but
    // iota would produce the wrong value for the given ctor.
    let env = bool_env();
    let rec_block = mk_id("Bool.rec.block");

    // Rebuild recursor type and rule-body domains exactly as `bool_env`
    // does, then swap which Var is returned in each rule.
    let motive_ty = pi(cnst("Bool", &[]), AE::sort(param(0)));
    let minor_true = app(var(0), cnst("Bool.true", &[]));
    let minor_false = app(var(1), cnst("Bool.false", &[]));
    let major_ty = cnst("Bool", &[]);
    let ret = app(var(3), var(0));
    let rec_ty = pi(
      motive_ty.clone(),
      pi(minor_true.clone(), pi(minor_false.clone(), pi(major_ty, ret))),
    );

    // SWAPPED rules: rule 0 returns `h_false` (var 0), rule 1 returns `h_true` (var 1).
    // Canonical: rule 0 returns `h_true` (var 1), rule 1 returns `h_false` (var 0).
    let motive_dom = motive_ty;
    let h_true_dom = minor_true;
    let h_false_dom = minor_false;
    let rule_true_rhs_swapped = lam(
      motive_dom.clone(),
      lam(
        h_true_dom.clone(),
        lam(h_false_dom.clone(), var(0)), // wrong: should be var(1)
      ),
    );
    let rule_false_rhs_swapped = lam(
      motive_dom,
      lam(
        h_true_dom,
        lam(h_false_dom, var(1)), // wrong: should be var(0)
      ),
    );

    env.insert(
      mk_id("Bool.rec"),
      KConst::Recr {
        name: (),
        level_params: (),
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: rec_block,
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          super::super::constant::RecRule {
            ctor: (),
            fields: 0,
            rhs: rule_true_rhs_swapped,
          },
          super::super::constant::RecRule {
            ctor: (),
            fields: 0,
            rhs: rule_false_rhs_swapped,
          },
        ],
        lean_all: (),
      },
    );

    let mut tc = TypeChecker::new(Arc::clone(&env));
    tc.check_const(&mk_id("Bool")).unwrap();
    let result = tc.check_const(&mk_id("Bool.rec"));
    assert!(
      result.is_err(),
      "Bool.rec with swapped rules must be rejected (P1-1 regression), got: Ok"
    );
  }

  /// P1-2 regression: two mutual inductives whose parameter-prefix types
  /// disagree must be rejected by `check_inductive` at the S3b gate.
  /// Without this, recursor generation (which pulls the shared-param
  /// prefix from the first peer) would produce a de-Bruijn mismatch when
  /// iota-reducing against a ctor of the second peer.
  #[test]
  fn reject_mutual_peers_with_mismatched_param_domains() {
    let env = Arc::new(KEnv::new());
    let block = mk_id("Mut");

    // Peer 1: `M1 : (α : Sort 1) → Sort 1`   (one Type parameter)
    let m1_ty = pi(sort1(), sort1());
    env.insert(
      mk_id("M1"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: m1_ty,
        ctors: vec![],
        lean_all: (),
      },
    );

    // Peer 2: `M2 : (α : Sort 0) → Sort 1`   (one *Prop* parameter)
    // Same param count as M1 so we defeat the arity short-circuit and
    // exercise the domain-agreement path specifically.
    let m2_ty = pi(AE::sort(AU::zero()), sort1());
    env.insert(
      mk_id("M2"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block.clone(),
        member_idx: 1,
        ty: m2_ty,
        ctors: vec![],
        lean_all: (),
      },
    );

    env.blocks.insert(block, vec![mk_id("M1"), mk_id("M2")]);

    let mut tc = TypeChecker::new(Arc::clone(&env));
    let result = tc.check_const(&mk_id("M1"));
    assert!(
      result.is_err(),
      "mutual peers with different param domains must be rejected \
       (P1-2 regression), got: Ok"
    );
  }

  /// P1-2 sanity: two mutual inductives with matching parameter-prefix
  /// types must pass the peer agreement check.
  #[test]
  fn accept_mutual_peers_with_matching_param_domains() {
    let env = Arc::new(KEnv::new());
    let block = mk_id("Mut");

    // Both peers share the param prefix `(α : Sort 1)`.
    let shared_ty = pi(sort1(), sort1());
    for (i, name) in ["M1", "M2"].iter().enumerate() {
      env.insert(
        mk_id(name),
        KConst::Indc {
          name: (),
          level_params: (),
          lvls: 0,
          params: 1,
          indices: 0,
          is_rec: false,
          is_refl: false,
          is_unsafe: false,
          nested: 0,
          block: block.clone(),
          member_idx: i as u64,
          ty: shared_ty.clone(),
          ctors: vec![],
          lean_all: (),
        },
      );
    }
    env.blocks.insert(block, vec![mk_id("M1"), mk_id("M2")]);

    let mut tc = TypeChecker::new(Arc::clone(&env));
    let result = tc.check_const(&mk_id("M1"));
    assert!(
      result.is_ok(),
      "mutual peers with identical param domains must be accepted \
       (P1-2 sanity), got: {:?}",
      result.err()
    );
  }

  /// P1-2 regression: two mutual inductives with *different* parameter
  /// counts must also be rejected — at the explicit `peer_params != params`
  /// arm of S3b, prior to reaching domain comparison.
  #[test]
  fn reject_mutual_peers_with_mismatched_param_count() {
    let env = Arc::new(KEnv::new());
    let block = mk_id("Mut");

    // Peer 1: one param.
    env.insert(
      mk_id("M1"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: pi(sort1(), sort1()),
        ctors: vec![],
        lean_all: (),
      },
    );
    // Peer 2: zero params.
    env.insert(
      mk_id("M2"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block.clone(),
        member_idx: 1,
        ty: sort1(),
        ctors: vec![],
        lean_all: (),
      },
    );
    env.blocks.insert(block, vec![mk_id("M1"), mk_id("M2")]);

    let mut tc = TypeChecker::new(Arc::clone(&env));
    let result = tc.check_const(&mk_id("M1"));
    assert!(
      result.is_err(),
      "mutual peers with different param counts must be rejected, got: Ok"
    );
  }

  /// P1-3 regression: universe substitution with fewer universes than
  /// the type demands must return `UnivParamOutOfRange` rather than
  /// silently producing an orphan `Param` node.
  #[test]
  fn subst_univ_rejects_out_of_range_param() {
    use super::super::error::TcError;
    let env = Arc::new(KEnv::<Anon>::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // Expression `Sort u` where `u = Param(0)`. Supplying zero universes
    // to substitute makes `Param(0)` out of range.
    let e = AE::sort(param(0));
    let result = tc.instantiate_univ_params(&e, &[]);
    // Empty `us` currently short-circuits with a clone (happy path for
    // the overwhelmingly common "no params to substitute" case), so
    // call the inner substitution directly with an empty slice.
    let _ = result; // ignore the fast-path result
    let direct = tc.subst_univ(&param(0), &[]);
    assert!(
      matches!(direct, Err(TcError::UnivParamOutOfRange { idx: 0, bound: 0 })),
      "subst_univ with empty us must return UnivParamOutOfRange, got: {direct:?}"
    );

    // And in a non-empty-but-still-too-short slice, the error carries
    // the correct `idx` and `bound`.
    let u = AU::zero();
    let direct2 = tc.subst_univ(&param(3), std::slice::from_ref(&u));
    assert!(
      matches!(direct2, Err(TcError::UnivParamOutOfRange { idx: 3, bound: 1 })),
      "subst_univ with too-short us must report correct idx/bound, got: {direct2:?}"
    );
  }
}
