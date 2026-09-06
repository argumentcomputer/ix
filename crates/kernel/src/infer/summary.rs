//! Conservative declaration summaries for proof-irrelevance eligibility.
//!
//! For a syntactic telescope `c : (x1 : A1) ... (xn : An) -> T`, the
//! classifying sort of T determines whether c, and each of its first n
//! partial applications, can be a proof: `imax a b` is zero iff b is zero.
//! We recognize T's sort ONLY from Sort nodes or syntactic types of its
//! constant/bound-variable head. No delta, reduction probes, fresh locals,
//! or argument validation occur here. Unknown means use ordinary inference.
//!
//! The substitution lemma justifies transferring a known nonzero sort to
//! well-typed arguments. This is NOT a typechecking shortcut: all arguments,
//! declaration types/bodies and universe scopes still undergo normal checks.

use super::*;
use crate::level::UnivData;

const MAX_SUMMARY_ARITY: usize = 64;
const MAX_LEVEL_VISITS: usize = 256;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ProofEligibility {
  Unknown,
  /// The result's type has sort Prop; still check BOTH proposition types
  /// with the existing proof-irrelevance procedure, never accept from here.
  ProofEligible,
  NonProof,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct DeclarationSummary {
  pub(crate) arity: usize,
  pub(crate) result: ProofEligibility,
}

const UNKNOWN: DeclarationSummary =
  DeclarationSummary { arity: 0, result: ProofEligibility::Unknown };

/// A bounded syntactic walk; deeper spines use ordinary inference.
fn head_and_arity<M: KernelMode>(
  mut e: &KExpr<M>,
) -> Option<(&KExpr<M>, usize)> {
  let mut arity = 0;
  while let ExprData::App(f, _, _) = e.data() {
    if arity == MAX_SUMMARY_ARITY {
      return None;
    }
    arity += 1;
    e = f;
  }
  Some((e, arity))
}

impl<M: KernelMode> TypeChecker<'_, M> {
  /// This predicate can only SKIP an inapplicable proof-irrelevance attempt.
  /// False includes unknown, malformed, overapplied, and propositional cases.
  pub(crate) fn known_non_proof(&mut self, e: &KExpr<M>) -> bool {
    let Some((head, arity)) = head_and_arity(e) else { return false };
    if !matches!(head.data(), ExprData::Const(..)) {
      return false;
    }
    let key = head.hash_key();
    let summary = if let Some(summary) = self.env.decl_summary_cache.get(&key) {
      self.env.perf.record_decl_summary_hit();
      *summary
    } else {
      self.env.perf.record_decl_summary_miss();
      // Dependency lookup/arity/substitution errors are not memoized as
      // negative facts. A later call with the dependency loaded can retry.
      let Ok(summary) = self.summarize_declaration(head) else { return false };
      self.env.decl_summary_cache.insert(key, summary);
      summary
    };
    let skip =
      arity <= summary.arity && summary.result == ProofEligibility::NonProof;
    if skip {
      self.env.perf.record_non_proof_skip();
    }
    skip
  }

  fn summarize_declaration(
    &mut self,
    head: &KExpr<M>,
  ) -> Result<DeclarationSummary, TcError<M>> {
    let ExprData::Const(id, us, _) = head.data() else { return Ok(UNKNOWN) };
    let c = self.get_const(id)?;
    if u64_to_usize::<M>(c.lvls())? != us.len() {
      return Err(TcError::UnivParamMismatch {
        expected: c.lvls(),
        got: us.len(),
      });
    }
    // Ordinary declaration checking enforces these. The summary must also
    // decline malformed hand-built/temporarily loaded declarations.
    if c.ty().lbr() != 0 || c.ty().has_fvars() {
      return Ok(UNKNOWN);
    }
    let mut domains: smallvec::SmallVec<[&KExpr<M>; 8]> =
      smallvec::SmallVec::new();
    let mut ty = c.ty();
    while let ExprData::All(_, _, dom, cod, _) = ty.data() {
      if domains.len() == MAX_SUMMARY_ARITY {
        return Ok(UNKNOWN);
      }
      domains.push(dom);
      ty = cod;
    }
    let Some(result) = self.summary_type_classification(ty, &domains, us)?
    else {
      return Ok(UNKNOWN);
    };
    Ok(DeclarationSummary { arity: domains.len(), result })
  }

  /// Infer only a syntactically evident sort of a telescope's terminal
  /// type. For a constant/application, its head type must expose exactly the
  /// required Pis followed by Sort. Bound-variable heads use their original
  /// domain; no lifting is necessary for the final universe-only result.
  fn summary_type_classification(
    &mut self,
    ty: &KExpr<M>,
    domains: &[&KExpr<M>],
    outer_us: &[KUniv<M>],
  ) -> Result<Option<ProofEligibility>, TcError<M>> {
    let mut visits = MAX_LEVEL_VISITS;
    if let ExprData::Sort(u, _) = ty.data() {
      // Sort u : Sort (u+1), never Prop. Still validate the universe
      // substitution within the same bounded walk before recording a fact.
      return Ok(
        classify_sort(u, &[outer_us], &mut visits)?
          .map(|_| ProofEligibility::NonProof),
      );
    }
    let Some((head, args)) = head_and_arity(ty) else { return Ok(None) };
    let (head_ty, levels) = match head.data() {
      ExprData::Var(i, _, _) => {
        let Some(pos) = usize::try_from(*i)
          .ok()
          .and_then(|i| i.checked_add(1))
          .and_then(|n| domains.len().checked_sub(n))
        else {
          return Ok(None);
        };
        (domains[pos].clone(), None)
      },
      ExprData::Const(id, us, _) => {
        let c = self.get_const(id)?;
        if u64_to_usize::<M>(c.lvls())? != us.len() {
          return Err(TcError::UnivParamMismatch {
            expected: c.lvls(),
            got: us.len(),
          });
        }
        if c.ty().lbr() != 0 || c.ty().has_fvars() {
          return Ok(None);
        }
        (c.ty().clone(), Some(us))
      },
      _ => return Ok(None),
    };
    let mut result = &head_ty;
    for _ in 0..args {
      let ExprData::All(_, _, _, cod, _) = result.data() else {
        return Ok(None);
      };
      result = cod;
    }
    let ExprData::Sort(u, _) = result.data() else { return Ok(None) };
    // Type-head universes are in this declaration's formal parameters.
    // Apply the inner substitution BEFORE the outer one, lazily, without
    // building levels or invoking unbounded universe-normalization helpers.
    match levels {
      Some(us) => classify_sort(u, &[us, outer_us], &mut visits),
      None => classify_sort(u, &[outer_us], &mut visits),
    }
  }
}

/// Interpret chained universe substitutions without constructing a level.
/// A parameter consumes ONE substitution layer, so an actual universe's
/// parameters cannot accidentally be captured by its own substitution.
/// Validate both branches, even when one determines nonzeroness, so errors
/// are not memoized as facts. None means the bounded analysis ran out of work.
/// A symbolic parameter with no substitution left is Unknown, NOT NonProof.
fn classify_sort<M: KernelMode>(
  u: &KUniv<M>,
  substitutions: &[&[KUniv<M>]],
  remaining: &mut usize,
) -> Result<Option<ProofEligibility>, TcError<M>> {
  use ProofEligibility::{NonProof, ProofEligible, Unknown};
  if *remaining == 0 {
    return Ok(None);
  }
  *remaining -= 1;
  let result = match u.data() {
    UnivData::Zero(_) => Some(ProofEligible),
    UnivData::Succ(inner, _) => {
      classify_sort(inner, substitutions, remaining)?.map(|_| NonProof)
    },
    UnivData::Param(i, _, _) => {
      let Some((us, rest)) = substitutions.split_first() else {
        return Ok(Some(Unknown));
      };
      let Some(actual) = usize::try_from(*i).ok().and_then(|i| us.get(i))
      else {
        return Err(TcError::UnivParamOutOfRange { idx: *i, bound: us.len() });
      };
      return classify_sort(actual, rest, remaining);
    },
    UnivData::IMax(a, b, _) | UnivData::Max(a, b, _) => {
      let Some(a) = classify_sort(a, substitutions, remaining)? else {
        return Ok(None);
      };
      let Some(b) = classify_sort(b, substitutions, remaining)? else {
        return Ok(None);
      };
      Some(if matches!(u.data(), UnivData::IMax(..)) {
        b
      } else {
        match (a, b) {
          (NonProof, _) | (_, NonProof) => NonProof,
          (ProofEligible, ProofEligible) => ProofEligible,
          _ => Unknown,
        }
      })
    },
  };
  Ok(result)
}

#[cfg(test)]
mod tests;
