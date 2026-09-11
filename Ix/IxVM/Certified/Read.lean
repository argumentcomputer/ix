/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.IxVM.Certified.Checker

/-!
Bounded private-witness transport for the C2 pilot. Scalars are field words
with an enforced `< 65536` domain, addresses are range-checked bytes, and
every recursive decoder decreases fuel. The entrypoint checks exact packet
consumption. This is a certificate transport, not the Ixon wire codec.
-/

namespace IxVM.Certified

def read := ⟦
  enum CSource {
    Axiom(G, CExpr, G), Defn(G, G, CExpr, CExpr, G),
    Induct(G, G, G, CExpr, G, G),
    Recr(G, G, G, G, G, CExpr, G, G, G), Unsupported
  }
  fn c_read_nat(idx: G) -> (G, G) {
    let [x] = io_read(17, idx, 1);
    (c_nat(x), c_add(idx, 1))
  }
  fn c_make_address(raw: [G; 32]) -> Addr {
    let (b0, b1) = u8_range_check(raw[0], raw[1]);
    let (b2, b3) = u8_range_check(raw[2], raw[3]);
    let (b4, b5) = u8_range_check(raw[4], raw[5]);
    let (b6, b7) = u8_range_check(raw[6], raw[7]);
    let (b8, b9) = u8_range_check(raw[8], raw[9]);
    let (b10, b11) = u8_range_check(raw[10], raw[11]);
    let (b12, b13) = u8_range_check(raw[12], raw[13]);
    let (b14, b15) = u8_range_check(raw[14], raw[15]);
    let (b16, b17) = u8_range_check(raw[16], raw[17]);
    let (b18, b19) = u8_range_check(raw[18], raw[19]);
    let (b20, b21) = u8_range_check(raw[20], raw[21]);
    let (b22, b23) = u8_range_check(raw[22], raw[23]);
    let (b24, b25) = u8_range_check(raw[24], raw[25]);
    let (b26, b27) = u8_range_check(raw[26], raw[27]);
    let (b28, b29) = u8_range_check(raw[28], raw[29]);
    let (b30, b31) = u8_range_check(raw[30], raw[31]);
    store([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31])
  }
  fn c_read_address(idx: G) -> (Addr, G) {
    let raw: [G; 32] = io_read(17, idx, 32);
    (c_make_address(raw), c_add(idx, 32))
  }
  fn c_read_ref(idx: G) -> (CRef, G) {
    let (tag, idx) = c_read_nat(idx);
    let (addr, idx) = c_read_address(idx);
    let (member, idx) = c_read_nat(idx);
    match tag {
      0 => (CRef.Member(addr, member), idx),
      1 => let (ctor, idx) = c_read_nat(idx); (CRef.Ctor(addr, member, ctor), idx),
    }
  }
  fn c_read_nums(fuel: G, count: G, idx: G) -> (List‹G›, G) {
    c_fuel(fuel);
    match count {
      0 => (store(ListNode.Nil), idx),
      _ =>
        let (x, idx) = c_read_nat(idx);
        let (xs, idx) = c_read_nums(fuel - 1, count - 1, idx);
        (store(ListNode.Cons(x, xs)), idx),
    }
  }
  fn c_read_when(fuel: G, idx: G) -> (CWhen, G) {
    let (tag, idx) = c_read_nat(idx);
    match tag {
      0 => (CWhen.Never, idx),
      1 =>
        let (count, idx) = c_read_nat(idx);
        let (xs, idx) = c_read_nums(fuel, count, idx);
        (CWhen.AllZero(xs), idx),
    }
  }
  fn c_read_level(fuel: G, idx: G) -> (CLevel, G) {
    c_fuel(fuel);
    let (tag, idx) = c_read_nat(idx);
    match tag {
      0 => (store(CLevelNode.Zero), idx),
      1 => let (l, idx) = c_read_level(fuel - 1, idx); (store(CLevelNode.Succ(l)), idx),
      2 =>
        let (a, idx) = c_read_level(fuel - 1, idx);
        let (b, idx) = c_read_level(fuel - 1, idx); (store(CLevelNode.Max(a, b)), idx),
      3 =>
        let (a, idx) = c_read_level(fuel - 1, idx);
        let (b, idx) = c_read_level(fuel - 1, idx); (store(CLevelNode.IMax(a, b)), idx),
      4 => let (i, idx) = c_read_nat(idx); (store(CLevelNode.Param(i)), idx),
    }
  }
  fn c_read_levels(fuel: G, count: G, idx: G) -> (List‹CLevel›, G) {
    c_fuel(fuel);
    match count {
      0 => (store(ListNode.Nil), idx),
      _ =>
        let (l, idx) = c_read_level(fuel - 1, idx);
        let (ls, idx) = c_read_levels(fuel - 1, count - 1, idx);
        (store(ListNode.Cons(l, ls)), idx),
    }
  }
  fn c_read_expr(fuel: G, idx: G) -> (CExpr, G) {
    c_fuel(fuel);
    let (tag, idx) = c_read_nat(idx);
    match tag {
      0 => let (l, idx) = c_read_level(fuel - 1, idx); (store(CExprNode.Srt(l)), idx),
      1 => let (i, idx) = c_read_nat(idx); (store(CExprNode.BVar(i)), idx),
      2 =>
        let (r, idx) = c_read_ref(idx);
        let (count, idx) = c_read_nat(idx);
        let (ls, idx) = c_read_levels(fuel - 1, count, idx);
        (store(CExprNode.Const(r, ls)), idx),
      3 =>
        let (f, idx) = c_read_expr(fuel - 1, idx);
        let (a, idx) = c_read_expr(fuel - 1, idx); (store(CExprNode.App(f, a)), idx),
      4 =>
        let (p, idx) = c_read_when(fuel - 1, idx);
        let (a, idx) = c_read_expr(fuel - 1, idx);
        let (b, idx) = c_read_expr(fuel - 1, idx); (store(CExprNode.Lam(p, a, b)), idx),
      5 =>
        let (p, idx) = c_read_when(fuel - 1, idx);
        let (a, idx) = c_read_expr(fuel - 1, idx);
        let (b, idx) = c_read_expr(fuel - 1, idx); (store(CExprNode.Pi(p, a, b)), idx),
    }
  }
  fn c_read_type(fuel: G, idx: G) -> (CType, G) {
    c_fuel(fuel);
    let (tag, idx) = c_read_nat(idx);
    match tag {
      0 => (store(CTypeNode.Srt), idx),
      1 => (store(CTypeNode.BVar), idx),
      2 => (store(CTypeNode.Const), idx),
      3 =>
        let (p, idx) = c_read_when(fuel - 1, idx);
        let (d, idx) = c_read_expr(fuel - 1, idx);
        let (b, idx) = c_read_expr(fuel - 1, idx);
        let (wf, idx) = c_read_type(fuel - 1, idx);
        let (wa, idx) = c_read_type(fuel - 1, idx);
        (store(CTypeNode.App(p, d, b, wf, wa)), idx),
      4 =>
        let (ld, idx) = c_read_level(fuel - 1, idx);
        let (lb, idx) = c_read_level(fuel - 1, idx);
        let (b, idx) = c_read_expr(fuel - 1, idx);
        let (wd, idx) = c_read_type(fuel - 1, idx);
        let (wb, idx) = c_read_type(fuel - 1, idx);
        let (wt, idx) = c_read_type(fuel - 1, idx);
        (store(CTypeNode.Lam(ld, lb, b, wd, wb, wt)), idx),
      5 =>
        let (ld, idx) = c_read_level(fuel - 1, idx);
        let (lb, idx) = c_read_level(fuel - 1, idx);
        let (wd, idx) = c_read_type(fuel - 1, idx);
        let (wb, idx) = c_read_type(fuel - 1, idx);
        (store(CTypeNode.Pi(ld, lb, wd, wb)), idx),
      6 =>
        let (b, idx) = c_read_expr(fuel - 1, idx);
        let (la, idx) = c_read_level(fuel - 1, idx);
        let (we, idx) = c_read_type(fuel - 1, idx);
        let (wa, idx) = c_read_type(fuel - 1, idx);
        let (wc, idx) = c_read_conv(fuel - 1, idx);
        (store(CTypeNode.Conv(b, la, we, wa, wc)), idx),
    }
  }
  fn c_read_conv(fuel: G, idx: G) -> (CConv, G) {
    c_fuel(fuel);
    let (tag, idx) = c_read_nat(idx);
    match tag {
      0 => (store(CConvNode.Refl), idx),
      1 => let (w, idx) = c_read_conv(fuel - 1, idx); (store(CConvNode.Symm(w)), idx),
      2 =>
        let (c, idx) = c_read_expr(fuel - 1, idx);
        let (wl, idx) = c_read_conv(fuel - 1, idx);
        let (wr, idx) = c_read_conv(fuel - 1, idx); (store(CConvNode.Trans(c, wl, wr)), idx),
      3 =>
        let (wf, idx) = c_read_conv(fuel - 1, idx);
        let (wa, idx) = c_read_conv(fuel - 1, idx); (store(CConvNode.App(wf, wa)), idx),
      4 =>
        let (ld, idx) = c_read_level(fuel - 1, idx);
        let (wd, idx) = c_read_type(fuel - 1, idx);
        let (wa, idx) = c_read_conv(fuel - 1, idx);
        let (wb, idx) = c_read_conv(fuel - 1, idx); (store(CConvNode.Lam(ld, wd, wa, wb)), idx),
      5 =>
        let (ld, idx) = c_read_level(fuel - 1, idx);
        let (wd, idx) = c_read_type(fuel - 1, idx);
        let (wa, idx) = c_read_conv(fuel - 1, idx);
        let (wb, idx) = c_read_conv(fuel - 1, idx); (store(CConvNode.Pi(ld, wd, wa, wb)), idx),
      6 =>
        let (t, idx) = c_read_expr(fuel - 1, idx);
        let (wl, idx) = c_read_type(fuel - 1, idx);
        let (wa, idx) = c_read_type(fuel - 1, idx); (store(CConvNode.Beta(t, wl, wa)), idx),
      7 =>
        let (b, idx) = c_read_expr(fuel - 1, idx);
        let (wf, idx) = c_read_type(fuel - 1, idx); (store(CConvNode.Eta(b, wf)), idx),
      8 =>
        let (a, idx) = c_read_expr(fuel - 1, idx);
        let (wt, idx) = c_read_type(fuel - 1, idx);
        let (wa, idx) = c_read_type(fuel - 1, idx);
        let (wb, idx) = c_read_type(fuel - 1, idx); (store(CConvNode.ProofIrrel(a, wt, wa, wb)), idx),
      9 => (store(CConvNode.Delta), idx),
      10 => (store(CConvNode.Srt), idx),
    }
  }
  fn c_read_source(idx: G) -> (CSource, G) {
    let (tag, idx) = c_read_nat(idx);
    match tag {
      0 =>
        let (n, idx) = c_read_nat(idx);
        let (typ, idx) = c_read_expr(192, idx);
        let (unsafe_flag, idx) = c_read_nat(idx); (CSource.Axiom(n, typ, unsafe_flag), idx),
      1 =>
        let (n, idx) = c_read_nat(idx);
        let (kind, idx) = c_read_nat(idx);
        let (typ, idx) = c_read_expr(192, idx);
        let (body, idx) = c_read_expr(192, idx);
        let (safety, idx) = c_read_nat(idx); (CSource.Defn(n, kind, typ, body, safety), idx),
      2 =>
        let (n, idx) = c_read_nat(idx);
        let (params, idx) = c_read_nat(idx);
        let (indices, idx) = c_read_nat(idx);
        let (typ, idx) = c_read_expr(192, idx);
        let (ctors, idx) = c_read_nat(idx);
        let (unsafe_flag, idx) = c_read_nat(idx); (CSource.Induct(n, params, indices, typ, ctors, unsafe_flag), idx),
      3 =>
        let (n, idx) = c_read_nat(idx);
        let (params, idx) = c_read_nat(idx);
        let (indices, idx) = c_read_nat(idx);
        let (motives, idx) = c_read_nat(idx);
        let (minors, idx) = c_read_nat(idx);
        let (typ, idx) = c_read_expr(192, idx);
        let (rules, idx) = c_read_nat(idx);
        let (k, idx) = c_read_nat(idx);
        let (unsafe_flag, idx) = c_read_nat(idx);
        (CSource.Recr(n, params, indices, motives, minors, typ, rules, k, unsafe_flag), idx),
      4 => (CSource.Unsupported, idx),
    }
  }
⟧

end IxVM.Certified
