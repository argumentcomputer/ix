/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.IxVM.Certified.Read
import Ix.Aiur.Compiler

/-!
Complete C2 certificate-checking execution, initialized from the pinned empty
type and eliminator and an empty context. This pilot consumes host-decoded
source declarations alongside certificates. Its packet is not authenticated
Ixon; C6 byte binding and C8 success reflection remain open.
-/

namespace IxVM.Certified

def accept := ⟦
  fn c_false_elim_type(fref: CRef) -> CExpr {
    let false_type = store(CExprNode.Const(fref, store(ListNode.Nil)));
    let p = CWhen.AllZero(store(ListNode.Cons(0, store(ListNode.Nil))));
    let motive = store(CExprNode.Pi(CWhen.Never, false_type,
      store(CExprNode.Srt(store(CLevelNode.Param(0))))));
    let result = store(CExprNode.App(store(CExprNode.BVar(1)), store(CExprNode.BVar(0))));
    store(CExprNode.Pi(p, motive, store(CExprNode.Pi(p, false_type, result))))
  }
  fn c_initialize(fref: CRef, eref: CRef, idx: G) -> (CEnv, G) {
    assert_eq!(c_ref_eq(fref, eref), 0);
    let prop = store(CExprNode.Srt(store(CLevelNode.Zero)));
    let (fsrc, idx) = c_read_source(idx);
    let CSource.Induct(0, 0, 0, ftyp, 0, 0) = fsrc;
    assert_eq!(c_expr_eq(192, 0, ftyp, prop), 1);
    let (esrc, idx) = c_read_source(idx);
    let CSource.Recr(1, 0, 0, 1, 0, etyp, 0, 0, 0) = esrc;
    let elim_type = c_false_elim_type(fref);
    assert_eq!(c_expr_eq(192, 0, etyp, elim_type), 1);
    let env = store(ListNode.Cons(CEntry.Mk(fref, 0, prop, Option.None),
      store(ListNode.Cons(CEntry.Mk(eref, 1, elim_type, Option.None), store(ListNode.Nil)))));
    (env, idx)
  }
  fn c_admit(env: CEnv, idx: G) -> (CEnv, G) {
    let (ref, idx) = c_read_ref(idx);
    let (source, idx) = c_read_source(idx);
    let CSource.Defn(n, kind, source_type, source_body, 0) = source;
    assert_eq!(u32_less_than(kind, 3), 1);
    let (typ, idx) = c_read_expr(192, idx);
    let (body, idx) = c_read_expr(192, idx);
    let (level, idx) = c_read_level(192, idx);
    let (wt, idx) = c_read_type(192, idx);
    let (wb, idx) = c_read_type(192, idx);
    assert_eq!(c_expr_eq(192, 0, source_type, typ), 1);
    assert_eq!(c_expr_eq(192, 0, source_body, body), 1);
    let Option.None = c_lookup(192, env, ref);
    c_scope(192, n, 0, typ); c_scope(192, n, 0, body);
    c_references(192, env, typ); c_references(192, env, body);
    let empty = store(ListNode.Nil);
    c_type(192, n, env, empty, typ, store(CExprNode.Srt(level)), wt);
    c_type(192, n, env, empty, body, typ, wb);
    (store(ListNode.Cons(CEntry.Mk(ref, n, typ, Option.Some(body)), env)), idx)
  }
  fn c_admit_many(fuel: G, count: G, env: CEnv, idx: G) -> (CEnv, G) {
    c_fuel(fuel);
    match count {
      0 => (env, idx),
      _ =>
        let (env, idx) = c_admit(env, idx);
        c_admit_many(fuel - 1, count - 1, env, idx),
    }
  }
  pub fn c_accept(faddr: [G; 32], fmember: G, eaddr: [G; 32], emember: G) -> G {
    let fref = CRef.Member(c_make_address(faddr), c_nat(fmember));
    let eref = CRef.Member(c_make_address(eaddr), c_nat(emember));
    let (start, len) = io_get_info(17, [0]);
    let start = c_nat(start);
    let len = c_nat(len);
    let limit = c_add(start, len);
    let (version, idx) = c_read_nat(start);
    assert_eq!(version, 1);
    let (env, idx) = c_initialize(fref, eref, idx);
    let (count, idx) = c_read_nat(idx);
    let (env, idx) = c_admit_many(192, count, env, idx);
    let (n, idx) = c_read_nat(idx);
    let (source_proof, idx) = c_read_expr(192, idx);
    let (source_prop, idx) = c_read_expr(192, idx);
    let (proof, idx) = c_read_expr(192, idx);
    let (prop, idx) = c_read_expr(192, idx);
    let (wp, idx) = c_read_type(192, idx);
    let (wt, idx) = c_read_type(192, idx);
    assert_eq!(idx, limit);
    assert_eq!(c_expr_eq(192, 0, source_proof, proof), 1);
    assert_eq!(c_expr_eq(192, 0, source_prop, prop), 1);
    c_references(192, env, proof); c_references(192, env, prop);
    let empty = store(ListNode.Nil);
    c_type(192, n, env, empty, prop, store(CExprNode.Srt(store(CLevelNode.Zero))), wt);
    c_type(192, n, env, empty, proof, prop, wp);
    1
  }
⟧

def toplevel : Except Aiur.Global Aiur.Source.Toplevel := do
  let vm ← IxVM.core.merge types
  let vm ← vm.merge levels
  let vm ← vm.merge expr
  let vm ← vm.merge checker
  let vm ← vm.merge read
  let vm ← vm.merge accept
  return vm.prune [`c_accept]

def compiled : Except String Aiur.CompiledToplevel := do
  let vm ← toplevel.mapError toString
  vm.compile

end IxVM.Certified
