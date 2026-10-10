//! Block-local auxiliary allocation. Every comparison below uses name
//! components, independently of cached digests. The source closure follows
//! actual declaration references and reached compiled groups only.

use std::collections::VecDeque;

use bignat::Nat;
use ix_common::env::{
  ConstantInfo, DataValue, Env, Expr, ExprData, Level, LevelData, Name,
  NameComponent, Syntax, SyntaxPreresolved,
};
use rustc_hash::FxHashSet;

use crate::compile::CompileState;
use crate::compile::validation::{AttemptError, Checkpoint};

fn prefix(root: &Name, name: &Name) -> bool {
  name.strip_prefix(root).is_some()
}

fn numeral_bound(names: &[Name]) -> Nat {
  let mut bound = Nat::from(0u64);
  for name in names {
    for component in name.components() {
      if let NameComponent::Num(n) = component {
        let next = Nat(n.0 + 1u32);
        if next > bound {
          bound = next;
        }
      }
    }
  }
  bound
}

fn family_free(forbidden: &[Name], root: &Name) -> bool {
  forbidden.iter().all(|name| !prefix(root, name))
}

pub(super) fn fresh_family(
  forbidden: &[Name],
  parent: &Name,
  label: String,
) -> Name {
  let candidate = Name::str(parent.clone(), label.clone());
  if family_free(forbidden, &candidate) {
    candidate
  } else {
    Name::str(Name::num(parent.clone(), numeral_bound(forbidden)), label)
  }
}

fn aux_suffix_families(aux: &Name) -> Vec<Name> {
  ["rec", "recOn", "casesOn", "below", "brecOn"]
    .into_iter()
    .map(|s| Name::str(aux.clone(), s.into()))
    .collect()
}

pub(super) fn fresh_ctor_family(
  forbidden: &[Name],
  aux: &Name,
  candidate: Name,
  index: usize,
  ctor_roots: &[Name],
) -> Name {
  let suffixes = aux_suffix_families(aux);
  let free = !prefix(&candidate, aux)
    && family_free(forbidden, &candidate)
    && suffixes
      .iter()
      .all(|root| !prefix(root, &candidate) && !prefix(&candidate, root))
    && ctor_roots
      .iter()
      .all(|root| !prefix(root, &candidate) && !prefix(&candidate, root));
  if free {
    candidate
  } else {
    let mut reserved = vec![aux.clone()];
    reserved.extend(suffixes);
    reserved.extend_from_slice(ctor_roots);
    reserved.extend_from_slice(forbidden);
    Name::str(
      Name::num(aux.clone(), numeral_bound(&reserved)),
      format!("_ctor_{index}"),
    )
  }
}

fn level_names(level: &Level, names: &mut Vec<Name>) {
  let mut pending = vec![level];
  while let Some(level) = pending.pop() {
    match level.as_data() {
      LevelData::Zero(_) => {},
      LevelData::Succ(u, _) => pending.push(u),
      LevelData::Max(u, v, _) | LevelData::Imax(u, v, _) => {
        pending.push(v);
        pending.push(u);
      },
      LevelData::Param(n, _) | LevelData::Mvar(n, _) => names.push(n.clone()),
    }
  }
}

fn syntax_names(syntax: &Syntax, names: &mut Vec<Name>) {
  let mut pending = vec![syntax];
  while let Some(syntax) = pending.pop() {
    match syntax {
      Syntax::Missing | Syntax::Atom(..) => {},
      Syntax::Node(_, kind, args) => {
        names.push(kind.clone());
        pending.extend(args.iter().rev());
      },
      Syntax::Ident(_, _, value, pres) => {
        names.push(value.clone());
        for pr in pres {
          match pr {
            SyntaxPreresolved::Namespace(n) | SyntaxPreresolved::Decl(n, _) => {
              names.push(n.clone())
            },
          }
        }
      },
    }
  }
}

/// All typed name fields are protected. Only constants and projection
/// heads become declaration references; metadata names are never followed.
fn expr_names_refs(
  expr: &Expr,
  names: &mut Vec<Name>,
  refs: &mut Vec<Name>,
  control: &Checkpoint,
) -> Result<(), AttemptError> {
  let mut pending = vec![expr];
  while let Some(expr) = pending.pop() {
    control.visit()?;
    match expr.as_data() {
      ExprData::Bvar(..) | ExprData::Lit(..) => {},
      ExprData::Fvar(n, _) | ExprData::Mvar(n, _) => names.push(n.clone()),
      ExprData::Sort(u, _) => level_names(u, names),
      ExprData::Const(n, us, _) => {
        names.push(n.clone());
        refs.push(n.clone());
        for u in us {
          level_names(u, names);
        }
      },
      ExprData::App(f, a, _) => {
        pending.push(a);
        pending.push(f);
      },
      ExprData::Lam(n, t, b, _, _) | ExprData::ForallE(n, t, b, _, _) => {
        names.push(n.clone());
        pending.push(b);
        pending.push(t);
      },
      ExprData::LetE(n, t, v, b, _, _) => {
        names.push(n.clone());
        pending.push(b);
        pending.push(v);
        pending.push(t);
      },
      ExprData::Proj(n, _, e, _) => {
        names.push(n.clone());
        refs.push(n.clone());
        pending.push(e);
      },
      ExprData::Mdata(md, e, _) => {
        for (key, value) in md {
          names.push(key.clone());
          match value {
            DataValue::OfName(n) => names.push(n.clone()),
            DataValue::OfSyntax(s) => syntax_names(s, names),
            _ => {},
          }
        }
        pending.push(e);
      },
    }
  }
  Ok(())
}

fn const_names_refs(
  ci: &ConstantInfo,
  names: &mut Vec<Name>,
  refs: &mut Vec<Name>,
  control: &Checkpoint,
) -> Result<(), AttemptError> {
  names.push(ci.get_name().clone());
  names.extend(ci.get_level_params().iter().cloned());
  expr_names_refs(ci.get_type(), names, refs, control)?;
  match ci {
    ConstantInfo::DefnInfo(v) => {
      names.extend(v.all.iter().cloned());
      refs.extend(v.all.iter().cloned());
      expr_names_refs(&v.value, names, refs, control)?;
    },
    ConstantInfo::ThmInfo(v) => {
      names.extend(v.all.iter().cloned());
      refs.extend(v.all.iter().cloned());
      expr_names_refs(&v.value, names, refs, control)?;
    },
    ConstantInfo::OpaqueInfo(v) => {
      names.extend(v.all.iter().cloned());
      refs.extend(v.all.iter().cloned());
      expr_names_refs(&v.value, names, refs, control)?;
    },
    ConstantInfo::InductInfo(v) => {
      names.extend(v.all.iter().chain(&v.ctors).cloned());
      refs.extend(v.all.iter().chain(&v.ctors).cloned());
    },
    ConstantInfo::CtorInfo(v) => {
      names.push(v.induct.clone());
      refs.push(v.induct.clone());
    },
    ConstantInfo::RecInfo(v) => {
      names.extend(v.all.iter().cloned());
      refs.extend(v.all.iter().cloned());
      for rule in &v.rules {
        names.push(rule.ctor.clone());
        refs.push(rule.ctor.clone());
        expr_names_refs(&rule.rhs, names, refs, control)?;
      }
    },
    _ => {},
  }
  Ok(())
}

/// Finite closure of the actual source map. `visited` uses that map's lookup
/// identity; every name stored for allocation is subsequently compared by
/// structural components, never by that lookup identity or a cached hash.
pub(super) fn source_names(
  env: &Env,
  members: &[Name],
  canon: Option<&CompileState>,
  control: &Checkpoint,
) -> Result<Vec<Name>, AttemptError> {
  let mut pending: VecDeque<Name> = members.iter().cloned().collect();
  let mut visited = FxHashSet::default();
  let mut names = Vec::new();
  while let Some(name) = pending.pop_front() {
    control.visit()?;
    names.push(name.clone());
    let Some(ci) = env.get(&name) else {
      continue;
    };
    if !visited.insert(name.clone()) {
      continue;
    }
    let mut refs = Vec::new();
    const_names_refs(&ci, &mut names, &mut refs, control)?;
    if matches!(&*ci, ConstantInfo::InductInfo(_))
      && let Some(classes) = canon.and_then(|stt| stt.blocks.get(&name))
    {
      refs.extend(classes.iter().flatten().cloned());
    }
    // FIFO versus DFS cannot affect membership or the numeric-component
    // bound used by allocation. Both follow every reached outgoing edge.
    pending.extend(refs);
  }
  Ok(names)
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::NameData;
  use std::sync::Arc;

  fn name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }

  #[test]
  fn preserves_free_candidates_and_separates_full_families() {
    let parent = Name::str(name("Root"), "_nested".into());
    let ordinary = fresh_family(&[], &parent, "List_1".into());
    assert_eq!(
      ordinary.components(),
      Name::str(parent.clone(), "List_1".into()).components()
    );
    for suffix in ["", "rec", "below", "brecOn"] {
      let collision = if suffix.is_empty() {
        ordinary.clone()
      } else {
        Name::str(ordinary.clone(), suffix.into())
      };
      let fresh = fresh_family(
        std::slice::from_ref(&collision),
        &parent,
        "List_1".into(),
      );
      assert!(!prefix(&fresh, &collision));
      assert_ne!(fresh.components(), ordinary.components());
    }
    let ctor = Name::str(ordinary.clone(), "cons".into());
    assert_eq!(
      fresh_ctor_family(&[], &ordinary, ctor.clone(), 0, &[]).components(),
      ctor.components()
    );
    let child = Name::str(ctor.clone(), "child".into());
    let fresh_child = fresh_ctor_family(
      &[],
      &ordinary,
      child.clone(),
      1,
      std::slice::from_ref(&ctor),
    );
    assert!(!prefix(&ctor, &fresh_child));
    assert!(!prefix(&fresh_child, &ctor));
    let fresh_parent = fresh_ctor_family(
      &[],
      &ordinary,
      ctor.clone(),
      1,
      std::slice::from_ref(&child),
    );
    assert!(!prefix(&child, &fresh_parent));
    assert!(!prefix(&fresh_parent, &child));
    let captured = Name::str(ordinary.clone(), "rec".into());

    let fresh = fresh_ctor_family(&[], &ordinary, captured.clone(), 0, &[]);
    assert!(!prefix(&fresh, &captured));
    assert!(!prefix(&captured, &fresh));
  }

  #[test]
  fn ignores_cached_components_and_uses_unbounded_numeric_names() {
    let parent = name("Root");
    let ordinary = Name::str(parent.clone(), "List_1".into());
    let rehashed_parent = Name(Arc::new(NameData::Str(
      Name::anon(),
      "Root".into(),
      blake3::hash(b"wrong parent hash"),
    )));
    let rehashed = Name::str(rehashed_parent, "List_1".into());
    let a = fresh_family(&[ordinary], &parent, "List_1".into());
    let b = fresh_family(&[rehashed], &parent, "List_1".into());
    assert_eq!(a.components(), b.components());
    let large = Nat(Nat::from(u64::MAX).0 + 1u32);
    let forbidden = Name::num(name("Unrelated"), large.clone());
    assert_eq!(numeral_bound(&[forbidden]), Nat(large.0 + 1u32));
  }
}
