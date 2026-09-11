/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.IxVM.Certified.Types

namespace IxVM.Certified

def levels := ⟦
  fn c_level_wf(fuel: G, n: G, l: CLevel) {
    c_fuel(fuel);
    match load(l) {
      CLevelNode.Zero => (),
      CLevelNode.Param(i) => assert_eq!(u32_less_than(i, n), 1); (),
      CLevelNode.Succ(a) => c_level_wf(fuel - 1, n, a),
      CLevelNode.Max(a, b) =>
        c_level_wf(fuel - 1, n, a); c_level_wf(fuel - 1, n, b),
      CLevelNode.IMax(a, b) =>
        c_level_wf(fuel - 1, n, a); c_level_wf(fuel - 1, n, b),
    }
  }
  fn c_levels_wf(fuel: G, n: G, ls: List‹CLevel›) {
    c_fuel(fuel);
    match load(ls) {
      ListNode.Nil => (),
      ListNode.Cons(l, tail) =>
        c_level_wf(fuel - 1, n, l); c_levels_wf(fuel - 1, n, tail),
    }
  }
  fn c_level_eq(fuel: G, a: CLevel, b: CLevel) -> G {
    c_fuel(fuel);
    match (load(a), load(b)) {
      (CLevelNode.Zero, CLevelNode.Zero) => 1,
      (CLevelNode.Param(i), CLevelNode.Param(j)) => c_eq(i, j),
      (CLevelNode.Succ(x), CLevelNode.Succ(y)) => c_level_eq(fuel - 1, x, y),
      (CLevelNode.Max(a, b), CLevelNode.Max(c, d)) =>
        c_level_eq(fuel - 1, a, c) * c_level_eq(fuel - 1, b, d),
      (CLevelNode.IMax(a, b), CLevelNode.IMax(c, d)) =>
        c_level_eq(fuel - 1, a, c) * c_level_eq(fuel - 1, b, d),
      _ => 0,
    }
  }
  fn c_levels_eq(fuel: G, xs: List‹CLevel›, ys: List‹CLevel›) -> G {
    c_fuel(fuel);
    match (load(xs), load(ys)) {
      (ListNode.Nil, ListNode.Nil) => 1,
      (ListNode.Cons(x, xt), ListNode.Cons(y, yt)) =>
        c_level_eq(fuel - 1, x, y) * c_levels_eq(fuel - 1, xt, yt),
      _ => 0,
    }
  }
  fn c_zero_condition(fuel: G, l: CLevel) -> CWhen {
    c_fuel(fuel);
    match load(l) {
      CLevelNode.Zero => CWhen.AllZero(store(ListNode.Nil)),
      CLevelNode.Param(i) => CWhen.AllZero(store(ListNode.Cons(i, store(ListNode.Nil)))),
      CLevelNode.Succ(_) => CWhen.Never,
      CLevelNode.Max(a, b) =>
        c_intersect(fuel - 1, c_zero_condition(fuel - 1, a), c_zero_condition(fuel - 1, b)),
      CLevelNode.IMax(_, b) => c_zero_condition(fuel - 1, b),
    }
  }
  fn c_level_inst(fuel: G, ls: List‹CLevel›, l: CLevel) -> CLevel {
    c_fuel(fuel);
    match load(l) {
      CLevelNode.Zero => l,
      CLevelNode.Param(i) => c_at(fuel - 1, ls, i),
      CLevelNode.Succ(a) => store(CLevelNode.Succ(c_level_inst(fuel - 1, ls, a))),
      CLevelNode.Max(a, b) => store(CLevelNode.Max(
        c_level_inst(fuel - 1, ls, a), c_level_inst(fuel - 1, ls, b))),
      CLevelNode.IMax(a, b) => store(CLevelNode.IMax(
        c_level_inst(fuel - 1, ls, a), c_level_inst(fuel - 1, ls, b))),
    }
  }
  fn c_levels_inst(fuel: G, ls: List‹CLevel›, xs: List‹CLevel›) -> List‹CLevel› {
    c_fuel(fuel);
    match load(xs) {
      ListNode.Nil => xs,
      ListNode.Cons(x, tail) => store(ListNode.Cons(
        c_level_inst(fuel - 1, ls, x), c_levels_inst(fuel - 1, ls, tail))),
    }
  }
  fn c_nums_inst(fuel: G, ls: List‹CLevel›, xs: List‹G›) -> CWhen {
    c_fuel(fuel);
    match load(xs) {
      ListNode.Nil => CWhen.AllZero(store(ListNode.Nil)),
      ListNode.Cons(x, tail) => c_intersect(fuel - 1,
        c_zero_condition(fuel - 1, c_at(fuel - 1, ls, x)),
        c_nums_inst(fuel - 1, ls, tail)),
    }
  }
  fn c_when_inst(fuel: G, ls: List‹CLevel›, p: CWhen) -> CWhen {
    match p {
      CWhen.Never => CWhen.Never,
      CWhen.AllZero(xs) => c_nums_inst(fuel, ls, xs),
    }
  }
  fn c_level_max(fuel: G, a: CLevel, b: CLevel) -> CLevel {
    match (load(a), load(b)) {
      (CLevelNode.Zero, _) => b,
      (_, CLevelNode.Zero) => a,
      _ => match c_level_eq(fuel, a, b) {
        1 => a, 0 => store(CLevelNode.Max(a, b)),
      },
    }
  }
  fn c_level_imax(fuel: G, a: CLevel, b: CLevel) -> CLevel {
    match (load(a), load(b)) {
      (_, CLevelNode.Zero) => b,
      (_, CLevelNode.Succ(_)) => c_level_max(fuel, a, b),
      (CLevelNode.Zero, _) => b,
      _ => match c_level_eq(fuel, a, b) {
        1 => a, 0 => store(CLevelNode.IMax(a, b)),
      },
    }
  }
  fn c_level_normalize(fuel: G, l: CLevel) -> CLevel {
    c_fuel(fuel);
    match load(l) {
      CLevelNode.Zero => l,
      CLevelNode.Param(_) => l,
      CLevelNode.Succ(a) => store(CLevelNode.Succ(c_level_normalize(fuel - 1, a))),
      CLevelNode.Max(a, b) => c_level_max(fuel - 1,
        c_level_normalize(fuel - 1, a), c_level_normalize(fuel - 1, b)),
      CLevelNode.IMax(a, b) => c_level_imax(fuel - 1,
        c_level_normalize(fuel - 1, a), c_level_normalize(fuel - 1, b)),
    }
  }
⟧

end IxVM.Certified
