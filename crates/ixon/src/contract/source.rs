//! Version-3 semantic source frames shared by compiler and host adapters.
//!
//! These frames describe source binders. Optional Ixon metadata is not an
//! authority for contracts; Ixon consumers must read the scalar payload.

use crate::CompileError;
use crate::contract::{BinderContract, LetKind, ValueContract};
use crate::expr::Expr;
use bignat::Nat;
use ix_common::env::{DataValue, Expr as Source, ExprData, Name, NameData};
use std::sync::Arc;

fn error(desc: &str) -> CompileError {
  CompileError::UnsupportedExpr { desc: desc.into() }
}

fn root(name: &Name) -> bool {
  matches!(name.as_data(), NameData::Str(parent, text, _) if text == "contract" &&
    matches!(parent.as_data(), NameData::Str(parent, text, _) if text == "ix" &&
      matches!(parent.as_data(), NameData::Anonymous(_))))
}

pub fn reserved(mut name: &Name) -> bool {
  loop {
    if root(name) {
      return true;
    }
    match name.as_data() {
      NameData::Str(parent, ..) | NameData::Num(parent, ..) => name = parent,
      NameData::Anonymous(_) => return false,
    }
  }
}

pub fn has_metadata(data: &[(Name, DataValue)]) -> bool {
  data.iter().any(|(name, _)| reserved(name))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
  Lam,
  All,
  Let,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Contract {
  pub kind: Kind,
  pub binder: BinderContract,
  pub result: ValueContract,
  pub let_kind: LetKind,
}

impl Contract {
  pub fn is_default(self) -> bool {
    self.binder == BinderContract::default()
      && self.result == ValueContract::shared()
      && self.let_kind == LetKind::Value
  }

  pub fn kind_code(self) -> u64 {
    match self.kind {
      Kind::Lam => 0,
      Kind::All => 1,
      Kind::Let => 2,
    }
  }
  pub fn code(self) -> u8 {
    let low = self.binder.to_bits();
    match self.kind {
      Kind::Lam => low,
      Kind::All => low | (self.result.to_bits() << 4),
      Kind::Let => {
        low | if self.let_kind == LetKind::BorrowShared { 16 } else { 0 }
      },
    }
  }
  pub fn order_key(self) -> u64 {
    self.kind_code() * 64 + u64::from(self.code())
  }
  pub fn metadata(self) -> Vec<(Name, DataValue)> {
    let key =
      Name::str(Name::str(Name::anon(), "ix".into()), "contract".into());
    // Lean's KVMap.set appends a new field.
    vec![
      (key.clone(), DataValue::OfNat(Nat::from(3u64))),
      (
        Name::str(key.clone(), "kind".into()),
        DataValue::OfNat(Nat::from(self.kind_code())),
      ),
      (
        Name::str(key, "code".into()),
        DataValue::OfNat(Nat::from(u64::from(self.code()))),
      ),
    ]
  }
  pub fn attach(self, source: Source) -> Source {
    Source::mdata(self.metadata(), source)
  }
  pub fn lower(
    self,
    source: &Source,
    compiled: &Arc<Expr>,
  ) -> Result<Arc<Expr>, CompileError> {
    Ok(Arc::new(match (self.kind, source.as_data(), compiled.as_ref()) {
      (Kind::Lam, ExprData::Lam(..), Expr::Lam(_, typ, body)) => {
        Expr::Lam(self.binder, typ.clone(), body.clone())
      },
      (Kind::All, ExprData::ForallE(..), Expr::All(_, _, typ, body)) => {
        Expr::All(self.binder, self.result, typ.clone(), body.clone())
      },
      (Kind::Let, ExprData::LetE(..), Expr::Let(c, typ, value, body)) => {
        Expr::Let(
          crate::contract::LetContract {
            binder: self.binder,
            kind: self.let_kind,
            ..*c
          },
          typ.clone(),
          value.clone(),
          body.clone(),
        )
      },
      _ => {
        return Err(error(
          "semantic contract is not attached to its original binder",
        ));
      },
    }))
  }
}

pub fn decode(kind: u64, code: u64) -> Result<Contract, CompileError> {
  let kind = match kind {
    0 => Kind::Lam,
    1 => Kind::All,
    2 => Kind::Let,
    _ => return Err(error("invalid semantic contract kind")),
  };
  let limit = match kind {
    Kind::Lam => 16,
    Kind::All => 64,
    Kind::Let => 32,
  };
  if code >= limit {
    return Err(error("reserved semantic contract bits"));
  }
  let code = u8::try_from(code)
    .map_err(|_error| error("semantic contract code overflow"))?;
  let binder = BinderContract::from_bits(code % 16)
    .ok_or_else(|| error("invalid semantic binder contract"))?;
  let result = if kind == Kind::All {
    ValueContract::from_bits(code / 16)
      .ok_or_else(|| error("invalid semantic result contract"))?
  } else {
    ValueContract::shared()
  };
  let let_kind = if kind == Kind::Let && code >= 16 {
    LetKind::BorrowShared
  } else {
    LetKind::Value
  };
  if let_kind == LetKind::BorrowShared
    && binder.value != ValueContract::local_shared()
  {
    return Err(error("shared borrow requires a shared local view"));
  }
  Ok(Contract { kind, binder, result, let_kind })
}

pub fn read(data: &[(Name, DataValue)]) -> Result<Contract, CompileError> {
  if data.len() != 3 {
    return Err(error("malformed semantic contract frame"));
  }
  let (mut version, mut kind, mut code) = (None, None, None);
  for (name, value) in data {
    let DataValue::OfNat(value) = value else {
      return Err(error("semantic contract fields must be natural numbers"));
    };
    let value = value
      .to_u64()
      .ok_or_else(|| error("semantic contract field is too large"))?;
    let slot = if root(name) {
      &mut version
    } else {
      match name.as_data() {
        NameData::Str(parent, text, _) if root(parent) && text == "kind" => {
          &mut kind
        },
        NameData::Str(parent, text, _) if root(parent) && text == "code" => {
          &mut code
        },
        _ => return Err(error("unknown or duplicate semantic contract field")),
      }
    };
    if slot.replace(value).is_some() {
      return Err(error("unknown or duplicate semantic contract field"));
    }
  }
  if version != Some(3) {
    return Err(error("unsupported semantic contract version"));
  }
  decode(
    kind.ok_or_else(|| error("missing semantic contract kind"))?,
    code.ok_or_else(|| error("missing semantic contract code"))?,
  )
}

/// A source frame must be attached directly to its matching binder.
pub fn read_attached(
  data: &[(Name, DataValue)],
  node: &Source,
) -> Result<Contract, CompileError> {
  let contract = read(data)?;
  if !matches!(
    (contract.kind, node.as_data()),
    (Kind::Lam, ExprData::Lam(..))
      | (Kind::All, ExprData::ForallE(..))
      | (Kind::Let, ExprData::LetE(..))
  ) {
    return Err(error(
      "semantic contract is not attached to its original binder",
    ));
  }
  Ok(contract)
}

/// Validate a peeled direct-source metadata chain without treating unrelated
/// display layers as contracts. A semantic frame must be the innermost layer.
pub fn source_layers(
  node: &Source,
  layers: &[Vec<(Name, DataValue)>],
) -> Result<Option<Contract>, CompileError> {
  let mut contract = None;
  for (i, layer) in layers.iter().enumerate() {
    if has_metadata(layer) {
      if i + 1 != layers.len() {
        return Err(error(
          "semantic contract is not attached to its original binder",
        ));
      }
      contract = Some(read_attached(layer, node)?);
    }
  }
  Ok(contract)
}

/// Reconstruct source frames from authoritative kernel payloads. Existing
/// direct-source spelling is retained only when it agrees exactly; it never
/// overrides the payload. Optional Ixon metadata is refused before ingress.
pub fn egress_layers(
  actual: Option<Contract>,
  layers: &[Vec<(Name, DataValue)>],
) -> Result<Vec<Vec<(Name, DataValue)>>, CompileError> {
  if layers.is_empty() && actual.is_none_or(Contract::is_default) {
    return Ok(Vec::new());
  }
  if let Some(actual) = actual
    && decode(actual.kind_code(), u64::from(actual.code()))? != actual
  {
    return Err(error("noncanonical semantic contract payload"));
  }
  let mut supplied = false;
  for (i, layer) in layers.iter().enumerate() {
    if has_metadata(layer) {
      if i + 1 != layers.len() || Some(read(layer)?) != actual {
        return Err(error(
          "semantic contract metadata conflicts with kernel payload",
        ));
      }
      supplied = true;
    }
  }
  let mut out = layers.to_vec();
  if !supplied
    && let Some(actual) = actual
    && !actual.is_default()
  {
    out.push(actual.metadata());
  }
  Ok(out)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::expr::Uses;

  fn key(suffix: Option<&str>) -> Name {
    let root =
      Name::str(Name::str(Name::anon(), "ix".into()), "contract".into());
    suffix.map_or(root.clone(), |s| Name::str(root, s.into()))
  }

  #[test]
  fn version_three_spelling_and_independent_fields() {
    let contract = Contract {
      kind: Kind::All,
      binder: BinderContract {
        uses: Uses::Linear,
        value: ValueContract::local_unique(),
      },
      result: ValueContract::local_shared(),
      let_kind: LetKind::Value,
    };
    let expected = vec![
      (key(None), DataValue::OfNat(Nat::from(3u64))),
      (key(Some("kind")), DataValue::OfNat(Nat::from(1u64))),
      (key(Some("code")), DataValue::OfNat(Nat::from(57u64))),
    ];
    assert_eq!(contract.metadata(), expected);
    assert_eq!(read(&expected).unwrap(), contract);
    let reversed = expected.into_iter().rev().collect::<Vec<_>>();
    assert_eq!(read(&reversed).unwrap(), contract);
  }

  #[test]
  fn version_and_duplicate_errors_keep_the_existing_boundary() {
    let mut frame = vec![
      (key(None), DataValue::OfNat(Nat::from(2u64))),
      (key(Some("kind")), DataValue::OfNat(Nat::from(0u64))),
      (key(Some("code")), DataValue::OfNat(Nat::from(7u64))),
    ];
    let message = |result: Result<Contract, CompileError>| match result {
      Err(CompileError::UnsupportedExpr { desc }) => desc,
      other => panic!("unexpected protocol result: {other:?}"),
    };
    assert_eq!(message(read(&frame)), "unsupported semantic contract version");
    frame[0] = frame[1].clone();
    assert_eq!(
      message(read(&frame)),
      "unknown or duplicate semantic contract field"
    );
  }
}
