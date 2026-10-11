//! Optional validator observations of generated auxiliary inputs.
//! Reference bindings are captured before compilation, so later promotion
//! cannot reinterpret a generated reference through a changed source name.

use dashmap::DashMap;
use ix_common::address::Address;
use ix_common::env::{
  ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Expr, ExprData,
  Name, OpaqueVal, TheoremVal,
};
use ixon::CompileError;
use ixon::constant::DefKind;
use rustc_hash::FxHashMap;

use crate::compile::aux_gen::source_identity::agrees;
use crate::graph::get_constant_info_references;
use crate::mutual::MutConst;

#[derive(Clone)]
pub(crate) struct CapturedAux {
  pub declaration: ConstantInfo,
  pub bindings: FxHashMap<Name, Address>,
}

#[derive(Clone)]
struct PublishedAux {
  input: CapturedAux,
  address: Address,
}

#[derive(Default)]
pub struct AuxInputCapture {
  declarations: DashMap<Name, PublishedAux>,
}

/// The actual source records passed to the auxiliary writer, including
/// constructors rather than only their containing inductive.
pub(crate) fn input_declarations(input: &MutConst) -> Vec<ConstantInfo> {
  match input {
    MutConst::Defn(definition) => {
      let cnst = ConstantVal {
        name: definition.name.clone(),
        level_params: definition.level_params.clone(),
        typ: definition.typ.clone(),
      };
      vec![match definition.kind {
        DefKind::Definition => ConstantInfo::DefnInfo(DefinitionVal {
          cnst,
          value: definition.value.clone(),
          hints: definition.hints,
          safety: definition.safety,
          all: definition.all.clone(),
        }),
        DefKind::Theorem => ConstantInfo::ThmInfo(TheoremVal {
          cnst,
          value: definition.value.clone(),
          all: definition.all.clone(),
        }),
        DefKind::Opaque => ConstantInfo::OpaqueInfo(OpaqueVal {
          cnst,
          value: definition.value.clone(),
          is_unsafe: definition.safety == DefinitionSafety::Unsafe,
          all: definition.all.clone(),
        }),
      }]
    },
    MutConst::Recr(recursor) => vec![ConstantInfo::RecInfo(recursor.clone())],
    MutConst::Indc(inductive) => {
      std::iter::once(ConstantInfo::InductInfo(inductive.ind.clone()))
        .chain(inductive.ctors.iter().cloned().map(ConstantInfo::CtorInfo))
        .collect()
    },
  }
}

/// Capture only external references. References within the current block
/// receive their published projection addresses after the writer finishes.
pub(crate) fn prepare_inputs(
  inputs: &[MutConst],
  own_names: &crate::mutual::MutCtx,
  resolve: impl Fn(&Name) -> Option<Address>,
) -> Result<Vec<CapturedAux>, String> {
  inputs
    .iter()
    .flat_map(input_declarations)
    .map(|declaration| {
      let mut bindings = FxHashMap::default();
      for name in get_constant_info_references(&declaration) {
        if own_names.contains_key(&name) {
          continue;
        }
        let address = resolve(&name).ok_or_else(|| {
          format!(
            "aux input capture: unresolved reference '{}' in '{}'",
            name.pretty(),
            declaration.get_name().pretty(),
          )
        })?;
        bindings.insert(name, address);
      }
      Ok(CapturedAux { declaration, bindings })
    })
    .collect()
}

impl AuxInputCapture {
  fn insert(&self, name: &Name, input: PublishedAux) -> Result<(), String> {
    match self.declarations.entry(name.clone()) {
      dashmap::mapref::entry::Entry::Occupied(entry) => {
        let old = entry.get();
        if old.address != input.address {
          return Err(format!(
            "aux capture address changed for '{}'",
            name.pretty()
          ));
        }
        check_declaration(
          &old.input.declaration,
          &input.input.declaration,
          &old.input.bindings,
          &input.input.bindings,
        )
        .map_err(|e| {
          format!("aux capture changed for '{}': {e}", name.pretty())
        })?;
      },
      dashmap::mapref::entry::Entry::Vacant(entry) => {
        entry.insert(input);
        super::block_txn::log_aux_capture(name);
      },
    }
    Ok(())
  }

  pub(crate) fn alias(
    &self,
    source: &Name,
    target: &Name,
  ) -> Result<(), String> {
    let input =
      self.declarations.get(target).map(|entry| entry.value().clone());
    let input = input.ok_or_else(|| {
      format!(
        "no captured auxiliary input for alias target '{}'",
        target.pretty()
      )
    })?;
    self.insert(source, input)
  }

  pub(crate) fn move_to_display(
    &self,
    source: &Name,
    target: &Name,
  ) -> Result<(), String> {
    self.alias(target, source)?;
    self.remove(source);
    Ok(())
  }

  pub(crate) fn remove(&self, name: &Name) {
    self.declarations.remove(name);
  }

  pub fn names(&self) -> Vec<Name> {
    self.declarations.iter().map(|entry| entry.key().clone()).collect()
  }

  /// Compare restored support with the writer input, retaining the captured
  /// meaning of references and positional universe parameters. A missing
  /// capture is an error, never a reason to omit a generated declaration.
  pub fn check(
    &self,
    name: &Name,
    address: &Address,
    recovered: &ConstantInfo,
    resolve: impl Fn(&Name) -> Option<Address>,
  ) -> Result<(), String> {
    let input = self.declarations.get(name).ok_or_else(|| {
      format!("no captured auxiliary input for '{}'", name.pretty())
    })?;
    if input.address != *address {
      return Err("auxiliary published address changed".into());
    }
    // Aliases share the target's metadata, including its declaration name.
    // Require the same published identity, not the same display spelling.
    if resolve(recovered.get_name()).as_ref() != Some(address) {
      return Err("auxiliary recovered under a different binding".into());
    }
    let mut actual_bindings = FxHashMap::default();
    for reference in get_constant_info_references(recovered) {
      let address = resolve(&reference).ok_or_else(|| {
        format!(
          "unresolved recovered auxiliary reference '{}'",
          reference.pretty(),
        )
      })?;
      actual_bindings.insert(reference, address);
    }
    check_declaration(
      &input.input.declaration,
      recovered,
      &input.input.bindings,
      &actual_bindings,
    )
  }
}

/// Complete internal bindings from the real publications, never from guessed
/// suffixes or the final source-name environment. Constructor publication does
/// not use the optional member-name rename map.
pub(crate) fn publish_inputs(
  stt: &super::CompileState,
  inputs: Vec<CapturedAux>,
  rename: impl Fn(&Name) -> Name,
) -> Result<(), CompileError> {
  let Some(capture) = &stt.aux_input_capture else { return Ok(()) };
  let finish = || -> Result<(), String> {
    let mut own_bindings = FxHashMap::default();
    let mut names = Vec::new();
    for input in &inputs {
      let name = input.declaration.get_name();
      let published = if matches!(input.declaration, ConstantInfo::CtorInfo(_))
      {
        name.clone()
      } else {
        rename(name)
      };
      let address = stt
        .env
        .lookup_name(&published)
        .ok_or_else(|| {
          format!(
            "aux input capture: '{}' was not published",
            published.pretty()
          )
        })?
        .addr;
      own_bindings.insert(name.clone(), address.clone());
      names.push((published, address));
    }
    for (mut input, (name, address)) in inputs.into_iter().zip(names) {
      for reference in get_constant_info_references(&input.declaration) {
        if let std::collections::hash_map::Entry::Vacant(entry) =
          input.bindings.entry(reference)
        {
          let address = own_bindings.get(entry.key()).ok_or_else(|| {
            format!(
              "aux input capture: missing internal binding '{}'",
              entry.key().pretty()
            )
          })?;
          entry.insert(address.clone());
        }
      }
      capture.insert(&name, PublishedAux { input, address })?;
    }
    Ok(())
  };
  finish().map_err(|reason| CompileError::InvalidMutualBlock { reason })
}

fn reference_expr(
  expr: &Expr,
  bindings: &FxHashMap<Name, Address>,
  memo: &mut FxHashMap<blake3::Hash, (Expr, Expr)>,
) -> Result<Expr, String> {
  if let Some((source, value)) = memo.get(expr.get_hash())
    && source == expr
  {
    return Ok(value.clone());
  }
  let reference = |name: &Name| -> Result<Name, String> {
    let address = bindings
      .get(name)
      .ok_or_else(|| format!("missing captured binding '{}'", name.pretty()))?;
    Ok(Name::str(
      Name::str(Name::anon(), "aux.capture.ref".into()),
      address.hex(),
    ))
  };
  let value = match expr.as_data() {
    ExprData::Const(name, levels, _) => {
      Expr::cnst(reference(name)?, levels.clone())
    },
    ExprData::Proj(name, index, value, _) => Expr::proj(
      reference(name)?,
      index.clone(),
      reference_expr(value, bindings, memo)?,
    ),
    ExprData::App(f, a, _) => Expr::app(
      reference_expr(f, bindings, memo)?,
      reference_expr(a, bindings, memo)?,
    ),
    ExprData::Lam(name, ty, body, info, _) => Expr::lam(
      name.clone(),
      reference_expr(ty, bindings, memo)?,
      reference_expr(body, bindings, memo)?,
      info.clone(),
    ),
    ExprData::ForallE(name, ty, body, info, _) => Expr::all(
      name.clone(),
      reference_expr(ty, bindings, memo)?,
      reference_expr(body, bindings, memo)?,
      info.clone(),
    ),
    ExprData::LetE(name, ty, value, body, non_dep, _) => Expr::letE(
      name.clone(),
      reference_expr(ty, bindings, memo)?,
      reference_expr(value, bindings, memo)?,
      reference_expr(body, bindings, memo)?,
      *non_dep,
    ),
    ExprData::Mdata(data, inner, _) => {
      Expr::mdata(data.clone(), reference_expr(inner, bindings, memo)?)
    },
    _ => expr.clone(),
  };
  memo.insert(*expr.get_hash(), (expr.clone(), value.clone()));
  Ok(value)
}

fn check_declaration(
  expected: &ConstantInfo,
  actual: &ConstantInfo,
  expected_bindings: &FxHashMap<Name, Address>,
  actual_bindings: &FxHashMap<Name, Address>,
) -> Result<(), String> {
  if std::mem::discriminant(expected) != std::mem::discriminant(actual) {
    return Err("auxiliary declaration kind changed".into());
  }
  if expected.get_level_params().len() != actual.get_level_params().len() {
    return Err("auxiliary universe arity changed".into());
  }
  let check_expr = |left: &Expr, right: &Expr| -> Result<(), String> {
    let left =
      reference_expr(left, expected_bindings, &mut FxHashMap::default())?;
    let right =
      reference_expr(right, actual_bindings, &mut FxHashMap::default())?;
    if agrees(
      expected.get_level_params(),
      actual.get_level_params(),
      &left,
      &right,
    ) {
      Ok(())
    } else {
      Err("auxiliary expression changed".into())
    }
  };
  let check_ref = |left: &Name, right: &Name| -> Result<(), String> {
    let a = expected_bindings
      .get(left)
      .ok_or_else(|| format!("missing captured binding '{}'", left.pretty()))?;
    let b = actual_bindings.get(right).ok_or_else(|| {
      format!("missing recovered binding '{}'", right.pretty())
    })?;
    if a == b {
      Ok(())
    } else {
      Err("auxiliary reference binding changed".into())
    }
  };
  check_expr(expected.get_type(), actual.get_type())
    .map_err(|e| format!("type: {e}"))?;
  match (expected.get_value(), actual.get_value()) {
    (Some(left), Some(right)) => {
      check_expr(left, right).map_err(|e| format!("value: {e}"))?
    },
    (None, None) => {},
    _ => return Err("auxiliary value presence changed".into()),
  }
  let header_ok = match (expected, actual) {
    (ConstantInfo::DefnInfo(a), ConstantInfo::DefnInfo(b)) => {
      a.safety == b.safety
    },
    (ConstantInfo::ThmInfo(_), ConstantInfo::ThmInfo(_)) => true,
    (ConstantInfo::OpaqueInfo(a), ConstantInfo::OpaqueInfo(b)) => {
      a.is_unsafe == b.is_unsafe
    },
    (ConstantInfo::InductInfo(a), ConstantInfo::InductInfo(b)) => {
      if a.ctors.len() != b.ctors.len() {
        return Err("auxiliary constructor count changed".into());
      }
      for (left, right) in a.ctors.iter().zip(&b.ctors) {
        check_ref(left, right)?;
      }
      a.num_params == b.num_params
        && a.num_indices == b.num_indices
        && a.is_unsafe == b.is_unsafe
        && a.num_nested == b.num_nested
        && a.is_rec == b.is_rec
        && a.is_reflexive == b.is_reflexive
    },
    (ConstantInfo::CtorInfo(a), ConstantInfo::CtorInfo(b)) => {
      check_ref(&a.induct, &b.induct)?;
      a.num_params == b.num_params
        && a.num_fields == b.num_fields
        && a.cidx == b.cidx
        && a.is_unsafe == b.is_unsafe
    },
    (ConstantInfo::RecInfo(a), ConstantInfo::RecInfo(b)) => {
      if a.rules.len() != b.rules.len() {
        return Err("auxiliary recursor rule count changed".into());
      }
      for (left, right) in a.rules.iter().zip(&b.rules) {
        check_ref(&left.ctor, &right.ctor)?;
        if left.n_fields != right.n_fields {
          return Err("auxiliary recursor rule fields changed".into());
        }
        check_expr(&left.rhs, &right.rhs).map_err(|e| format!("rule: {e}"))?;
      }
      a.num_params == b.num_params
        && a.num_indices == b.num_indices
        && a.num_motives == b.num_motives
        && a.num_minors == b.num_minors
        && a.k == b.k
        && a.is_unsafe == b.is_unsafe
    },
    _ => false,
  };
  if header_ok { Ok(()) } else { Err("auxiliary header changed".into()) }
}

#[cfg(test)]
mod tests;
