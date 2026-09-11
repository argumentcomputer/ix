/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.IxVM.Core

/-!
The C2 Aiur pilot uses the same occurrence annotations and explicit
block/member/constructor references as the semantic validator. Every recursive
operation has a decreasing, bounded fuel argument. Exhaustion aborts execution.
This module does not claim compiler or AIR reflection.
-/

namespace IxVM.Certified

def types := ⟦
  enum CLevelNode {
    Zero, Succ(CLevel), Max(CLevel, CLevel), IMax(CLevel, CLevel), Param(G)
  }
  type CLevel = &CLevelNode

  enum CWhen { Never, AllZero(List‹G›) }
  enum CRef { Member(Addr, G), Ctor(Addr, G, G) }
  enum CExprNode {
    Srt(CLevel), BVar(G), Const(CRef, List‹CLevel›),
    App(CExpr, CExpr), Lam(CWhen, CExpr, CExpr), Pi(CWhen, CExpr, CExpr)
  }
  type CExpr = &CExprNode

  enum CTypeNode {
    Srt, BVar, Const,
    App(CWhen, CExpr, CExpr, CType, CType),
    Lam(CLevel, CLevel, CExpr, CType, CType, CType),
    Pi(CLevel, CLevel, CType, CType),
    Conv(CExpr, CLevel, CType, CType, CConv)
  }
  type CType = &CTypeNode
  enum CConvNode {
    Refl, Symm(CConv), Trans(CExpr, CConv, CConv), App(CConv, CConv),
    Lam(CLevel, CType, CConv, CConv), Pi(CLevel, CType, CConv, CConv),
    Beta(CExpr, CType, CType), Eta(CExpr, CType),
    ProofIrrel(CExpr, CType, CType, CType), Delta, Srt
  }
  type CConv = &CConvNode

  enum CEntry { Mk(CRef, G, CExpr, Option‹CExpr›) }
  type CEnv = List‹CEntry›
  type CCtx = List‹CExpr›

  fn c_fuel(fuel: G) {
    match fuel { 0 => assert_eq!(0, 1); (), _ => (), }
  }
  fn c_nat(x: G) -> G {
    assert_eq!(u32_less_than(x, 65536), 1); x
  }
  fn c_add(a: G, b: G) -> G { c_nat(a + b) }
  fn c_eq(a: G, b: G) -> G { match a - b { 0 => 1, _ => 0, } }
  fn c_len‹T›(fuel: G, xs: List‹T›) -> G {
    c_fuel(fuel);
    match load(xs) {
      ListNode.Nil => 0,
      ListNode.Cons(_, tail) => c_add(1, c_len(fuel - 1, tail)),
    }
  }
  fn c_at‹T›(fuel: G, xs: List‹T›, i: G) -> T {
    c_fuel(fuel);
    let ListNode.Cons(x, tail) = load(xs);
    match i { 0 => x, _ => c_at(fuel - 1, tail, i - 1), }
  }
  fn c_ref_eq(a: CRef, b: CRef) -> G {
    match (a, b) {
      (CRef.Member(x, i), CRef.Member(y, j)) => address_eq(x, y) * c_eq(i, j),
      (CRef.Ctor(x, i, k), CRef.Ctor(y, j, l)) =>
        address_eq(x, y) * c_eq(i, j) * c_eq(k, l),
      _ => 0,
    }
  }
  fn c_nums_eq(fuel: G, xs: List‹G›, ys: List‹G›) -> G {
    c_fuel(fuel);
    match (load(xs), load(ys)) {
      (ListNode.Nil, ListNode.Nil) => 1,
      (ListNode.Cons(x, xt), ListNode.Cons(y, yt)) =>
        c_eq(x, y) * c_nums_eq(fuel - 1, xt, yt),
      _ => 0,
    }
  }
  fn c_when_eq(fuel: G, a: CWhen, b: CWhen) -> G {
    match (a, b) {
      (CWhen.Never, CWhen.Never) => 1,
      (CWhen.AllZero(xs), CWhen.AllZero(ys)) => c_nums_eq(fuel, xs, ys),
      _ => 0,
    }
  }
  fn c_nums_wf(fuel: G, n: G, xs: List‹G›) {
    c_fuel(fuel);
    match load(xs) {
      ListNode.Nil => (),
      ListNode.Cons(x, tail) =>
        assert_eq!(u32_less_than(x, n), 1);
        match load(tail) {
          ListNode.Nil => (),
          ListNode.Cons(y, _) => assert_eq!(u32_less_than(x, y), 1); (),
        };
        c_nums_wf(fuel - 1, n, tail),
    }
  }
  fn c_when_wf(fuel: G, n: G, p: CWhen) {
    match p { CWhen.Never => (), CWhen.AllZero(xs) => c_nums_wf(fuel, n, xs), }
  }
  fn c_insert(fuel: G, x: G, xs: List‹G›) -> List‹G› {
    c_fuel(fuel);
    match load(xs) {
      ListNode.Nil => store(ListNode.Cons(x, xs)),
      ListNode.Cons(y, tail) =>
        match u32_less_than(x, y) {
          1 => store(ListNode.Cons(x, xs)),
          0 => match x - y {
            0 => xs,
            _ => store(ListNode.Cons(y, c_insert(fuel - 1, x, tail))),
          },
        },
    }
  }
  fn c_union(fuel: G, xs: List‹G›, ys: List‹G›) -> List‹G› {
    c_fuel(fuel);
    match load(xs) {
      ListNode.Nil => ys,
      ListNode.Cons(x, tail) => c_insert(fuel - 1, x, c_union(fuel - 1, tail, ys)),
    }
  }
  fn c_intersect(fuel: G, a: CWhen, b: CWhen) -> CWhen {
    match (a, b) {
      (CWhen.AllZero(xs), CWhen.AllZero(ys)) => CWhen.AllZero(c_union(fuel, xs, ys)),
      _ => CWhen.Never,
    }
  }
⟧

end IxVM.Certified
