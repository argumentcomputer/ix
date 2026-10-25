//! Host conversion and reconstruction checks; resource validity is separate.

use crate::env::{InternTable, KEnv};
use crate::expr::{ExprData, FVarId, KExpr};
use crate::level::KUniv;
use crate::mode::{Anon, KernelMode, Meta};
use crate::subst::{
  abstract_fvars, instantiate_rev, lift, simul_subst, subst, subst_no_intern,
};
use crate::tc::TypeChecker;
use ix_common::env::{BinderInfo, Name};
use ixon::contract::{BinderContract, LetContract, LetKind, ValueContract};
use ixon::expr::Uses;

fn name<M: KernelMode>() -> M::MField<Name> {
  M::meta_field(Name::anon())
}
fn bi<M: KernelMode>() -> M::MField<BinderInfo> {
  M::meta_field(BinderInfo::Default)
}
fn input(code: u8) -> BinderContract {
  BinderContract::from_bits(code).unwrap()
}
fn sort<M: KernelMode>() -> KExpr<M> {
  KExpr::sort(KUniv::zero())
}
fn var<M: KernelMode>(i: u64) -> KExpr<M> {
  KExpr::var(i, name::<M>())
}
fn lam<M: KernelMode>(c: BinderContract, body: KExpr<M>) -> KExpr<M> {
  KExpr::lam_contract(name::<M>(), bi::<M>(), c, sort(), body)
}
fn all<M: KernelMode>(
  c: BinderContract,
  r: ValueContract,
  body: KExpr<M>,
) -> KExpr<M> {
  KExpr::all_contract(name::<M>(), bi::<M>(), c, r, sort(), body)
}

fn identity_and_conversion<M: KernelMode>() {
  let mut env = KEnv::<M>::new();
  let mut tc = TypeChecker::new(&mut env);
  let lambdas: Vec<_> =
    (0..16).map(|c| tc.intern(lam(input(c), var(0)))).collect();
  let pis: Vec<_> = (0..16)
    .map(|c| {
      (0..4)
        .map(|r| {
          tc.intern(all(input(c), ValueContract::from_bits(r).unwrap(), sort()))
        })
        .collect::<Vec<_>>()
    })
    .collect();
  for a in 0..16 {
    for b in 0..16 {
      assert_eq!(lambdas[a] == lambdas[b], a == b);
      assert_eq!(lambdas[a].addr() == lambdas[b].addr(), a == b);
      assert_eq!(tc.is_def_eq(&lambdas[a], &lambdas[b]).unwrap(), a == b);
      for r in 0..4 {
        assert_eq!(pis[a][0] == pis[b][r], a == b && r == 0);
        assert_eq!(pis[a][0].addr() == pis[b][r].addr(), a == b && r == 0);
        for (left, right) in
          [(&pis[a][0], &pis[b][r]), (&pis[b][r], &pis[a][0])]
        {
          assert_eq!(tc.is_def_eq(left, right).unwrap(), a == b);
        }
      }
    }
  }
  // Canonical reuse of a default constructor still meets the explicit payload.
  let default_lam =
    tc.intern(KExpr::lam(name::<M>(), bi::<M>(), sort(), var(0)));
  assert_eq!(default_lam.addr(), lambdas[7].addr());
  let default_pi =
    tc.intern(KExpr::all(name::<M>(), bi::<M>(), sort(), sort()));
  assert_eq!(default_pi.addr(), pis[7][1].addr());
  let mut lets = Vec::new();
  for non_dep in [false, true] {
    for kind in [LetKind::Value, LetKind::BorrowShared] {
      for c in 0..16 {
        lets.push(tc.intern(KExpr::let_contract(
          name::<M>(),
          LetContract { non_dep, kind, binder: input(c) },
          sort(),
          sort(),
          var(0),
        )));
      }
    }
  }
  // Structural identity covers every wire scalar, independently of whether
  // a separate resource check would admit a particular borrow contract.
  for (i, a) in lets.iter().enumerate() {
    for (j, b) in lets.iter().enumerate() {
      assert_eq!(a == b, i == j);
      assert_eq!(a.addr() == b.addr(), i == j);
    }
  }
}

#[test]
fn contract_identity_and_conversion_all_scalar_codes_both_modes() {
  identity_and_conversion::<Meta>();
  identity_and_conversion::<Anon>();
}

fn telescope<M: KernelMode>(
  contracts: &[BinderContract],
  lambda: bool,
  result: ValueContract,
) -> KExpr<M> {
  let mut out = if lambda { var(0) } else { sort() };
  for c in contracts.iter().rev() {
    out = if lambda { lam(*c, out) } else { all(*c, result, out) };
  }
  out
}

fn inference_and_batches<M: KernelMode>() {
  for n in [1, 2, 3, 4, 5] {
    let contracts: Vec<_> = (0..n).map(|i| input((i * 3 + 1) % 16)).collect();
    let value = telescope::<M>(&contracts, true, ValueContract::unique());
    let expected = telescope::<M>(&contracts, false, ValueContract::shared());
    let mut env = KEnv::<M>::new();
    let mut tc = TypeChecker::new(&mut env);
    assert_eq!(tc.infer(&value).unwrap(), expected);
    assert_eq!(tc.infer(&value).unwrap(), expected);
    assert!(tc.lctx.is_empty());
    for single in [false, true] {
      for lambda in [false, true] {
        for index in [0, usize::from(n - 1)] {
          let mut changed = contracts.clone();
          changed[index] = input(changed[index].to_bits() ^ 4);
          let mut env = KEnv::<M>::new();
          let mut tc = TypeChecker::new(&mut env);
          tc.in_binder_batch = single;
          let original =
            tc.intern(telescope(&contracts, lambda, ValueContract::shared()));
          let mismatch =
            tc.intern(telescope(&changed, lambda, ValueContract::unique()));
          assert!(!tc.is_def_eq(&original, &mismatch).unwrap());
          assert!(!tc.is_def_eq(&mismatch, &original).unwrap());
          if !lambda {
            let result_only =
              tc.intern(telescope(&contracts, false, ValueContract::unique()));
            assert!(tc.is_def_eq(&original, &result_only).unwrap());
          }
          assert!(tc.lctx.is_empty());
        }
      }
    }
  }
}

#[test]
fn inference_and_single_batched_conversion_preserve_input_contracts() {
  inference_and_batches::<Meta>();
  inference_and_batches::<Anon>();
}

fn eta<M: KernelMode>() {
  for r in 0..4 {
    for c in [5, 7, 13] {
      let mut env = KEnv::<M>::new();
      let mut tc = TypeChecker::new(&mut env);
      let ty = all(input(c), ValueContract::from_bits(r).unwrap(), sort());
      let (_, f, _) =
        tc.open_binder_with_fv(name::<M>(), bi::<M>(), ty, &var(0));
      let body = KExpr::app(f.clone(), var(0));
      let good = lam(input(c), body.clone());
      let bad = lam(input(c ^ 4), body);
      for (left, right) in [(&f, &good), (&good, &f)] {
        assert!(tc.is_def_eq(left, right).unwrap());
      }
      for (left, right) in [(&f, &bad), (&bad, &f)] {
        assert!(!tc.is_def_eq(left, right).unwrap());
      }
    }
  }
}

#[test]
fn eta_checks_input_and_ignores_result_both_directions() {
  eta::<Meta>();
  eta::<Anon>();
}

// An outer free variable occurs at every binder depth, forcing all rebuilders.
fn nested<M: KernelMode>(leaf: impl Fn(u64) -> KExpr<M>) -> KExpr<M> {
  KExpr::lam_contract(
    name::<M>(),
    bi::<M>(),
    input(5),
    leaf(0),
    KExpr::all_contract(
      name::<M>(),
      bi::<M>(),
      input(9),
      ValueContract::local_unique(),
      leaf(1),
      KExpr::let_contract(
        name::<M>(),
        LetContract::borrow(true, Uses::Affine),
        leaf(2),
        leaf(2),
        leaf(3),
      ),
    ),
  )
}

fn rebuilds<M: KernelMode>() {
  let mut intern = InternTable::<M>::new();
  let open = nested(var);
  let expected = nested(|_| sort());
  assert_eq!(subst(&mut intern, &open, &sort(), 0), expected);
  assert_eq!(subst_no_intern(&open, &sort(), 0), expected);
  assert_eq!(simul_subst(&mut intern, &open, &[sort()], 0), expected);
  assert_eq!(instantiate_rev(&mut intern, &open, &[sort()]), expected);
  assert_eq!(lift(&mut intern, &open, 2, 0), nested(|i| var(i + 2)));
  let id = FVarId(1234);
  let free = nested(|_| KExpr::fvar(id, name::<M>()));
  assert_eq!(abstract_fvars(&mut intern, &free, &[id]), open);
  let mut env = KEnv::<M>::new();
  let mut tc = TypeChecker::new(&mut env);
  let param = nested(|_| KExpr::sort(KUniv::param(0, name::<M>())));
  assert_eq!(
    tc.instantiate_univ_params(&param, &[KUniv::zero()]).unwrap(),
    expected
  );
  // The closure machine must read back an unapplied Lam/All with its payload.
  for lambda in [false, true] {
    let inner = if lambda {
      lam(input(5), var(1))
    } else {
      all(input(9), ValueContract::local_unique(), var(1))
    };
    let applied = KExpr::app(lam(input(7), inner), sort());
    let reduced = tc.whnf(&applied).unwrap();
    let expected = if lambda {
      lam(input(5), sort())
    } else {
      all(input(9), ValueContract::local_unique(), sort())
    };
    assert_eq!(reduced, expected);
  }
}

#[test]
fn substitutions_universes_and_closure_readback_preserve_contracts() {
  rebuilds::<Meta>();
  rebuilds::<Anon>();
}

fn locals<M: KernelMode>() {
  let mut env = KEnv::<M>::new();
  let mut tc = TypeChecker::new(&mut env);
  let (a, a_id) = tc.open_binder_contract(
    name::<M>(),
    bi::<M>(),
    input(9),
    ValueContract::local_unique(),
    sort(),
    &var(0),
  );
  let (x, x_id) = tc.open_binder_contract(
    name::<M>(),
    bi::<M>(),
    input(5),
    ValueContract::unique(),
    a.clone(),
    &var(0),
  );
  let contract = LetContract::borrow(true, Uses::Linear);
  let (body, y_id) = tc.open_let_contract(name::<M>(), contract, a, x, &var(0));
  let ids = [a_id, x_id, y_id];
  for lambda in [false, true] {
    let closed = if lambda {
      tc.lctx.mk_lambda(&mut tc.env.intern, &ids, &body)
    } else {
      tc.lctx.mk_pi(&mut tc.env.intern, &ids, &body)
    };
    assert!(!closed.has_fvars());
    let inner =
      KExpr::let_contract(name::<M>(), contract, var(1), var(0), var(0));
    let expected = if lambda {
      KExpr::lam_contract(
        name::<M>(),
        bi::<M>(),
        input(9),
        sort(),
        KExpr::lam_contract(name::<M>(), bi::<M>(), input(5), var(0), inner),
      )
    } else {
      KExpr::all_contract(
        name::<M>(),
        bi::<M>(),
        input(9),
        ValueContract::local_unique(),
        sort(),
        KExpr::all_contract(
          name::<M>(),
          bi::<M>(),
          input(5),
          ValueContract::unique(),
          var(0),
          inner,
        ),
      )
    };
    assert_eq!(closed, expected);
  }
  let plain = tc.intern(KExpr::let_contract(
    name::<M>(),
    LetContract::plain(true),
    sort(),
    sort(),
    var(0),
  ));
  let borrowed = tc.intern(KExpr::let_contract(
    name::<M>(),
    contract,
    sort(),
    sort(),
    var(0),
  ));
  assert_ne!(plain.addr(), borrowed.addr());
  assert_ne!(plain, borrowed);
  assert!(tc.is_def_eq(&plain, &borrowed).unwrap());
  assert!(
    matches!(borrowed.data(), ExprData::Let(_, _, _, _, c, _) if *c == contract)
  );
}

#[test]
fn local_open_close_preserves_dependent_domains_results_and_let_payload() {
  locals::<Meta>();
  locals::<Anon>();
}

#[test]
fn canonical_order_ignores_contracts_but_retains_let_non_dep() {
  use crate::canonical_check::{KMutCtx, compare_kexpr};
  use std::cmp::Ordering;
  let ctx = KMutCtx::default();
  for c in 0..16 {
    for r in 0..4 {
      let a = all::<Anon>(input(7), ValueContract::shared(), sort());
      let b =
        all::<Anon>(input(c), ValueContract::from_bits(r).unwrap(), sort());
      assert_eq!(
        compare_kexpr(&a, &b, &ctx).unwrap().ordering,
        Ordering::Equal
      );
      assert_eq!(
        compare_kexpr(
          &lam::<Anon>(input(7), var(0)),
          &lam::<Anon>(input(c), var(0)),
          &ctx
        )
        .unwrap()
        .ordering,
        Ordering::Equal
      );
    }
  }
  let make = |c| KExpr::<Anon>::let_contract((), c, sort(), sort(), var(0));
  let plain = make(LetContract::plain(false));
  let borrow = make(LetContract::borrow(false, Uses::Linear));
  assert_eq!(
    compare_kexpr(&plain, &borrow, &ctx).unwrap().ordering,
    Ordering::Equal
  );
  assert_ne!(
    compare_kexpr(&plain, &make(LetContract::plain(true)), &ctx)
      .unwrap()
      .ordering,
    Ordering::Equal
  );
}

#[test]
fn direct_source_ingress_preserves_frames_and_refuses_wrong_attachment() {
  use crate::ingress::lean_expr_to_zexpr_with_kenv;
  use ix_common::env::{Expr as Source, Level};
  use ixon::contract::source::{decode, egress_layers};
  let mut env = KEnv::<Meta>::new();
  let prop = Source::sort(Level::zero());
  let binder =
    Source::all(Name::anon(), prop.clone(), prop.clone(), BinderInfo::Default);
  for code in 0..64 {
    let contract = decode(1, code).unwrap();
    let framed = contract.attach(binder.clone());
    let kernel =
      lean_expr_to_zexpr_with_kenv(&framed, &[], &mut env, None, None).unwrap();
    assert_eq!(kernel.source_contract(), Some(contract));
    assert_eq!(
      egress_layers(kernel.source_contract(), kernel.mdata()).unwrap(),
      vec![contract.metadata()]
    );
    let warm =
      lean_expr_to_zexpr_with_kenv(&framed, &[], &mut env, None, None).unwrap();
    assert_eq!(warm.addr(), kernel.addr());
  }
  let frame = decode(1, 21).unwrap();
  for wrong in [prop, frame.attach(binder)] {
    let error = lean_expr_to_zexpr_with_kenv(
      &frame.attach(wrong),
      &[],
      &mut env,
      None,
      None,
    )
    .unwrap_err();
    assert!(error.contains("not attached to its original binder"), "{error}");
  }
}
