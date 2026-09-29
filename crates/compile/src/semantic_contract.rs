//! Semantic contract nodes carried through the source compiler.
//! Mirrors `Ix/SemanticContract.lean`; these frames are consumed into Ixon
//! binders and never serve as a resource-validity certificate.

use bignat::Nat;
use ix_common::env::{DataValue, Expr as Source, ExprData, Name, NameData};
use ixon::CompileError;
use ixon::contract::{BinderContract, LetKind, ValueContract};
use ixon::expr::Expr;
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
          ixon::contract::LetContract {
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

pub fn inspect(top: &Source) -> Result<bool, CompileError> {
  let mut seen = rustc_hash::FxHashSet::default();
  let mut stack = vec![top];
  let mut annotated = false;
  while let Some(expr) = stack.pop() {
    if !seen.insert(expr) {
      continue;
    }
    match expr.as_data() {
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::Lam(_, t, b, ..) | ExprData::ForallE(_, t, b, ..) => {
        stack.push(t);
        stack.push(b);
      },
      ExprData::LetE(_, t, v, b, ..) => {
        stack.push(t);
        stack.push(v);
        stack.push(b);
      },
      ExprData::Proj(_, _, v, _) => stack.push(v),
      ExprData::Mdata(data, inner, _) => {
        if has_metadata(data) {
          let c = read(data)?;
          if !matches!(
            (c.kind, inner.as_data()),
            (Kind::Lam, ExprData::Lam(..))
              | (Kind::All, ExprData::ForallE(..))
              | (Kind::Let, ExprData::LetE(..))
          ) {
            return Err(error(
              "semantic contract is not attached to its original binder",
            ));
          }
          annotated = true;
        }
        stack.push(inner);
      },
      _ => {},
    }
  }
  Ok(annotated)
}

pub fn inspect_constant(
  c: &ix_common::env::ConstantInfo,
) -> Result<bool, CompileError> {
  let mut annotated = inspect(c.get_type())?;
  if let Some(body) = c.get_value() {
    annotated |= inspect(body)?;
  }
  if let ix_common::env::ConstantInfo::RecInfo(r) = c {
    for rule in &r.rules {
      annotated |= inspect(&rule.rhs)?;
    }
  }
  if annotated
    && !matches!(
      c,
      ix_common::env::ConstantInfo::DefnInfo(_)
        | ix_common::env::ConstantInfo::ThmInfo(_)
        | ix_common::env::ConstantInfo::OpaqueInfo(_)
        | ix_common::env::ConstantInfo::AxiomInfo(_)
    )
  {
    return Err(error(
      "annotated inductive/constructor/recursor transformations are unsupported",
    ));
  }
  Ok(annotated)
}

pub fn of_ixon(expr: &Expr) -> Option<Contract> {
  let c = match expr {
    Expr::Lam(binder, ..) => Contract {
      kind: Kind::Lam,
      binder: *binder,
      result: ValueContract::shared(),
      let_kind: LetKind::Value,
    },
    Expr::All(binder, result, ..) => Contract {
      kind: Kind::All,
      binder: *binder,
      result: *result,
      let_kind: LetKind::Value,
    },
    Expr::Let(c, ..) => Contract {
      kind: Kind::Let,
      binder: c.binder,
      result: ValueContract::shared(),
      let_kind: c.kind,
    },
    _ => return None,
  };
  (c.binder != BinderContract::default()
    || c.result != ValueContract::shared()
    || c.let_kind != LetKind::Value)
    .then_some(c)
}

/// Context-free presence scan only; never used as resource-validity evidence.
pub fn contains_ixon(
  expr: &Arc<Expr>,
  sharing: &[Arc<Expr>],
) -> Result<bool, String> {
  let mut seen = rustc_hash::FxHashSet::default();
  let mut stack = vec![expr];
  while let Some(e) = stack.pop() {
    if !seen.insert(Arc::as_ptr(e)) {
      continue;
    }
    if of_ixon(e).is_some() {
      return Ok(true);
    }
    if let Expr::Share(index) = e.as_ref() {
      stack.push(
        sharing
          .get(
            usize::try_from(*index)
              .map_err(|_error| "semantic scan: sharing index overflow")?,
          )
          .ok_or("semantic scan: invalid sharing index")?,
      );
    } else {
      stack.extend(e.children());
    }
  }
  Ok(false)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::{BlockCache, CompileState, compare_expr, compile_expr};
  use crate::mutual::MutCtx;
  use ix_common::env::{BinderInfo, Level};
  #[test]
  fn strict_metadata_and_all_contract_codes() {
    for (kind, count) in [(0, 16), (1, 64), (2, 32)] {
      for code in 0..count {
        match decode(kind, code) {
          Ok(contract) => {
            assert_eq!(read(&contract.metadata()).unwrap(), contract);
            assert_eq!(u64::from(contract.code()), code);
          },
          Err(_) => assert!(kind == 2 && code >= 16 && (code % 16) / 4 != 3),
        }
      }
      assert!(decode(kind, count).is_err());
    }
    let data = decode(0, 1).unwrap().metadata();
    assert!(has_metadata(&data));
    assert!(read(&data[..2]).is_err());
    let mut duplicate = data.clone();
    duplicate[0] = duplicate[1].clone();
    assert!(read(&duplicate).is_err());
    let mut wrong = data;
    wrong[0].1 = DataValue::OfNat(Nat::from(2u64));
    assert!(read(&wrong).is_err());
  }

  #[test]
  fn lowering_cache_ordering_and_borrow_contracts() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let domain = Source::sort(Level::zero());
    let body = Source::bvar(Nat::from(0u64));
    let lambda = Source::lam(
      Name::anon(),
      domain.clone(),
      body.clone(),
      BinderInfo::Default,
    );
    let arrow = Source::all(
      Name::anon(),
      domain.clone(),
      domain.clone(),
      BinderInfo::Default,
    );
    let mut lambdas = vec![];
    for code in 0..16 {
      let contract = decode(0, code).unwrap();
      let source = contract.attach(lambda.clone());
      let output =
        compile_expr(&source, &[], &MutCtx::default(), &mut cache, &stt)
          .unwrap();
      assert_eq!(
        output,
        Expr::lam_contract(contract.binder, Expr::sort(0), Expr::var(0))
      );
      lambdas.push(source);
    }
    for code in 0..64 {
      let contract = decode(1, code).unwrap();
      let source = contract.attach(arrow.clone());
      let output =
        compile_expr(&source, &[], &MutCtx::default(), &mut cache, &stt)
          .unwrap();
      assert_eq!(
        output,
        Expr::all_contract(
          contract.binder,
          contract.result,
          Expr::sort(0),
          Expr::sort(0)
        )
      );
    }
    for (i, a) in lambdas.iter().enumerate() {
      for (j, b) in lambdas.iter().enumerate() {
        let order =
          compare_expr(a, b, &MutCtx::default(), &[], &[], &stt).unwrap();
        assert_eq!(order.ordering == std::cmp::Ordering::Equal, i == j);
      }
    }
    let plain = Source::letE(
      Name::anon(),
      domain.clone(),
      body.clone(),
      body.clone(),
      false,
    );
    let contract = decode(2, 30).unwrap();
    let borrowed = contract.attach(plain.clone());
    let expected = Expr::let_contract(
      ixon::contract::LetContract {
        non_dep: false,
        kind: LetKind::BorrowShared,
        binder: contract.binder,
      },
      Expr::sort(0),
      Expr::var(0),
      Expr::var(0),
    );
    for (source, expected) in [
      (&plain, Expr::let_(false, Expr::sort(0), Expr::var(0), Expr::var(0))),
      (&borrowed, expected),
      (&plain, Expr::let_(false, Expr::sort(0), Expr::var(0), Expr::var(0))),
    ] {
      assert_eq!(
        compile_expr(source, &[], &MutCtx::default(), &mut cache, &stt)
          .unwrap(),
        expected
      );
    }
    assert!(
      compile_expr(
        &contract.attach(domain.clone()),
        &[],
        &MutCtx::default(),
        &mut cache,
        &stt
      )
      .is_err()
    );
    let bad =
      Source::mdata(decode(0, 1).unwrap().metadata()[..1].to_vec(), domain);
    assert!(
      compile_expr(&bad, &[], &MutCtx::default(), &mut cache, &stt).is_err()
    );
  }
  #[test]
  fn committed_contracts_roundtrip_without_optional_metadata() {
    use crate::decompile::{
      BlockCache as DecompileCache, DecompileState, decompile_expr,
    };
    use ixon::metadata::{DataValue, ExprMeta, ExprMetaData};
    let stt = CompileState::new_empty();
    let mut terms = vec![];
    for bits in 0..16 {
      let c = BinderContract::from_bits(bits).unwrap();
      terms.push(Expr::lam_contract(c, Expr::sort(0), Expr::var(0)));
      for result in 0..4 {
        terms.push(Expr::all_contract(
          c,
          ValueContract::from_bits(result).unwrap(),
          Expr::sort(0),
          Expr::sort(0),
        ));
      }
      for non_dep in [false, true] {
        for kind in [LetKind::Value, LetKind::BorrowShared] {
          if kind == LetKind::BorrowShared
            && c.value != ValueContract::local_shared()
          {
            continue;
          }
          terms.push(Expr::let_contract(
            ixon::contract::LetContract { non_dep, kind, binder: c },
            Expr::sort(0),
            Expr::var(0),
            Expr::var(0),
          ));
        }
      }
    }
    for term in terms {
      let mut cache = DecompileCache {
        univ_table: vec![ixon::univ::Univ::zero()],
        ..Default::default()
      };
      let source = decompile_expr(
        &term,
        &ExprMeta::default(),
        u64::MAX,
        &[],
        &mut cache,
        &stt,
        &DecompileState::default(),
      )
      .unwrap();
      let result = compile_expr(
        &source,
        &[],
        &MutCtx::default(),
        &mut BlockCache::default(),
        &stt,
      )
      .unwrap();
      assert_eq!(result, term);
    }
    let nested = Expr::lam_contract(
      BinderContract {
        uses: ixon::expr::Uses::Affine,
        value: ValueContract::local_unique(),
      },
      Expr::sort(0),
      Expr::var(0),
    );
    let mut cache =
      DecompileCache { sharing: vec![nested], ..Default::default() };
    let mut arena = ExprMeta::default();
    let root = arena.alloc(ExprMetaData::CallSite {
      name: ix_common::address::Address::hash(b"unused"),
      entries: vec![],
      canon_meta: vec![],
      orig_head: None,
    });
    assert!(
      decompile_expr(
        &Expr::app(Expr::var(0), Expr::share(0)),
        &arena,
        root,
        &[],
        &mut cache,
        &stt,
        &DecompileState::default()
      )
      .is_err()
    );

    let key =
      Name::str(Name::str(Name::anon(), "ix".into()), "contract".into());
    let addr = ix_common::address::Address::from_blake3_hash(*key.get_hash());
    stt.env.store_name(addr.clone(), key);
    let leaf = arena.alloc(ExprMetaData::Leaf);
    let root = arena.alloc(ExprMetaData::Mdata {
      mdata: vec![vec![(addr, DataValue::OfBool(true))]],
      child: leaf,
    });
    assert!(
      decompile_expr(
        &Expr::var(0),
        &arena,
        root,
        &[],
        &mut DecompileCache::default(),
        &stt,
        &DecompileState::default()
      )
      .is_err()
    );
  }
}
