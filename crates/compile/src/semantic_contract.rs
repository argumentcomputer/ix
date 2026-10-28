//! Semantic contract nodes carried through the source compiler.
//! Mirrors `Ix/SemanticContract.lean`; these frames are consumed into Ixon
//! binders and never serve as a resource-validity certificate.

use ix_common::env::{Expr as Source, ExprData};
use ixon::CompileError;
use ixon::contract::{BinderContract, LetKind, ValueContract};
use ixon::expr::Expr;

pub use ixon::contract::source::{
  Contract, Kind, decode, has_metadata, read, reserved,
};

#[cfg(test)]
use bignat::Nat;
#[cfg(test)]
use ix_common::env::{DataValue, Name, NameData};
#[cfg(test)]
use std::sync::Arc;

fn error(desc: &str) -> CompileError {
  CompileError::UnsupportedExpr { desc: desc.into() }
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

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::{BlockCache, CompileState, compile_expr};
  use crate::mutual::MutCtx;
  use ix_common::env::{BinderInfo, Level};
  #[test]
  fn inspection_rejects_raw_hash_aliases_in_both_orders() {
    let domain = Source::sort(Level::zero());
    let lam = Source::lam(
      Name::anon(),
      domain.clone(),
      Source::bvar(0u64.into()),
      BinderInfo::Default,
    );
    let contract = decode(0, 1).unwrap();
    let data = contract.metadata();
    let frame = |md| {
      Source(Arc::new(ExprData::Mdata(
        md,
        lam.clone(),
        blake3::Hash::from([0; 32]),
      )))
    };
    let good = frame(data.clone());
    let mut nonnat = data.clone();
    nonnat[2].1 = DataValue::OfBool(true);
    let mut bits = data.clone();
    bits[2].1 = DataValue::OfNat(16u64.into());
    let mut unknown = data.clone();
    let NameData::Str(parent, _, hash) = data[2].0.as_data() else {
      panic!("code field has no name")
    };
    unknown[2].0 =
      Name(Arc::new(NameData::Str(parent.clone(), "unknown".into(), *hash)));
    for (md, message) in [
      (data[..2].to_vec(), "malformed semantic contract frame"),
      (
        decode(1, 1).unwrap().metadata(),
        "semantic contract is not attached to its original binder",
      ),
      (nonnat, "semantic contract fields must be natural numbers"),
      (bits, "reserved semantic contract bits"),
      (unknown, "unknown or duplicate semantic contract field"),
    ] {
      let bad = frame(md);
      assert_eq!(bad.get_hash(), good.get_hash());
      assert_ne!(bad, good); // Rust's existing derived Eq is already structural.
      for input in [
        bad.clone(),
        Source::app(bad.clone(), good.clone()),
        Source::app(good.clone(), bad),
      ] {
        assert!(
          matches!(inspect(&input), Err(CompileError::UnsupportedExpr { desc }) if desc == message)
        );
      }
    }
    let twin = frame(data);
    assert!(!Arc::ptr_eq(&good.0, &twin.0));
    assert!(good.same_raw(&twin));
    assert!(inspect(&Source::app(good.clone(), good.clone())).unwrap());
    assert!(inspect(&Source::app(good, twin)).unwrap());
    assert!(!inspect(&domain).unwrap());
  }

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
      let key = crate::compile::ExprKey(source.clone());
      assert_eq!(cache.exprs.get(&key).unwrap().expr, output);
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
      let key = crate::compile::ExprKey(source.clone());
      assert_eq!(cache.exprs.get(&key).unwrap().expr, output);
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

    let mut arena = ExprMeta::default();
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
