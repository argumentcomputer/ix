import Aiur.Modules.Function

/-! # IxVM module `KernelNatPrim`

Native reduction of `Nat`, `String`, `BitVec` and related primitives.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelNatPrim where

def mk_bool := aiur_fn⟦
  fn mk_bool(rc: KernelRoles::RoleCtx, g: Field) -> KernelTypes::KExpr {
      match g {
        0 => {  (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_bool_false()), (&(Lists::Node::Nil))))) } ,
        _ => {  (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_bool_true()), (&(Lists::Node::Nil))))) } ,
      }
    }
⟧










def utf8_validate := aiur_fn⟦
  fn utf8_validate(bs: Bytes::Stream) -> () {
      match (*(bs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(b0, rest) => {
          match utf8_decode_one(b0, rest) {
            (_, remaining) => {  utf8_validate(remaining) } ,
          } } ,
      }
    }
⟧



def utf8_cont := aiur_fn⟦
  fn utf8_cont(b: UInt8::U8) -> Field {
      match UInt8::less_than(b, UInt8::BYTE_128) {
        0 => {
          match UInt8::less_than(b, UInt8::BYTE_192) {
            1 => {  UInt8::to_field(b) - 128 } ,
          } } ,
      }
    }
⟧

def utf8_decode_one := aiur_fn⟦
  fn utf8_decode_one(b0: UInt8::U8, rest: Bytes::Stream) -> (Field, Bytes::Stream) {
      match UInt8::less_than(b0, UInt8::BYTE_128) {
        1 => {  (UInt8::to_field(b0), rest) } ,
        _ => {

          match UInt8::less_than(b0, UInt8::BYTE_194) {
            0 => {
              match UInt8::less_than(b0, UInt8::BYTE_224) {
                1 => {
                  match (*(rest)) {
                    Lists::Node::Cons(b1, r1) => {

                      let cp = (UInt8::to_field(b0) - 192) * 64 + utf8_cont(b1);
                      (cp, r1) } ,
                  } } ,
                _ => {
                  match UInt8::less_than(b0, UInt8::BYTE_240) {
                    1 => {
                      match (*(rest)) {
                        Lists::Node::Cons(b1, r1) => {
                          match (*(r1)) {
                            Lists::Node::Cons(b2, r2) => {
                              let cp = (UInt8::to_field(b0) - 224) * 4096
                                     + utf8_cont(b1) * 64
                                     + utf8_cont(b2);

                              match UInt32::less_than_fields(cp, 2048) {
                                0 => {

                                  match UInt32::less_than_fields(cp, 55296) {
                                    1 => {  (cp, r2) } ,
                                    0 => {
                                      match UInt32::less_than_fields(cp, 57344) {
                                        0 => {  (cp, r2) } ,
                                      } } ,
                                  } } ,
                              } } ,
                          } } ,
                      } } ,
                    _ => {
                      match (*(rest)) {
                        Lists::Node::Cons(b1, r1) => {
                          match (*(r1)) {
                            Lists::Node::Cons(b2, r2) => {
                              match (*(r2)) {
                                Lists::Node::Cons(b3, r3) => {
                                  let cp = (UInt8::to_field(b0) - 240) * 262144
                                         + utf8_cont(b1) * 4096
                                         + utf8_cont(b2) * 64
                                         + utf8_cont(b3);

                                  match UInt32::less_than_fields(cp, 65536) {
                                    0 => {

                                      match UInt32::less_than_fields(cp, 1114112) {
                                        1 => {  (cp, r3) } ,
                                      } } ,
                                  } } ,
                              } } ,
                          } } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def str_lit_to_ctor := aiur_fn⟦
  fn str_lit_to_ctor(rc: KernelRoles::RoleCtx, bs: Bytes::Stream) -> KernelTypes::KExpr {
      let zero_lvl = (&(KernelTypes::KLevelNode::Zero));
      let ulvls = (&(Lists::Node::Cons(zero_lvl, (&(Lists::Node::Nil)))));
      let nil_const = (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_list_nil()), ulvls)));
      let cons_const = (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_list_cons()), ulvls)));
      let char_const =
        (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_char()), (&(Lists::Node::Nil)))));
      let con_const =
        (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_char_of_nat()), (&(Lists::Node::Nil)))));
      let str_const =
        (&(KernelTypes::KExprNode::Const(KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_string_of_list()), (&(Lists::Node::Nil)))));
      let nil_app = (&(KernelTypes::KExprNode::App(nil_const, char_const)));
      let cons_partial = (&(KernelTypes::KExprNode::App(cons_const, char_const)));
      let list_expr = build_char_list(bs, nil_app, cons_partial, con_const);
      (&(KernelTypes::KExprNode::App(str_const, list_expr)))
    }
⟧

def build_char_list := aiur_fn⟦
  fn build_char_list(bs: Bytes::Stream, nil_app: KernelTypes::KExpr,
                           cons_partial: KernelTypes::KExpr, con_const: KernelTypes::KExpr) -> KernelTypes::KExpr {
      match (*(bs)) {
        Lists::Node::Nil => {  nil_app } ,
        Lists::Node::Cons(b0, rest) => {
          match utf8_decode_one(b0, rest) {
            (cp, remaining) => {
              let cp_limbs = klimbs_from_g(cp);
              let cp_lit = (&(KernelTypes::KExprNode::Lit(KernelTypes::KLiteral::Nat(cp_limbs))));
              let char_val = (&(KernelTypes::KExprNode::App(con_const, cp_lit)));
              let with_head = (&(KernelTypes::KExprNode::App(cons_partial, char_val)));
              let tail = build_char_list(remaining, nil_app, cons_partial, con_const);
              (&(KernelTypes::KExprNode::App(with_head, tail))) } ,
          } } ,
      }
    }
⟧

def str_lit_delta_step := aiur_fn⟦
  fn str_lit_delta_step(rc: KernelRoles::RoleCtx, expanded: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(expanded)) {
        KernelTypes::KExprNode::App(f, list_arg) => {
          match (*(f)) {
            KernelTypes::KExprNode::Const(caddr, _) => {
              let ci = (*(Ingress::get_ci(caddr)));
              match ci {
                KernelTypes::KConstantInfo::Defn(_, _, value, _, _) => {
                  let body = KernelLevels::expr_inst_levels(value, (&(Lists::Node::Nil)));
                  match (*(body)) {
                    KernelTypes::KExprNode::Lam(_, lam_body, bl) => {
                      match KernelLevels::level_is_not_zero(bl) {
                        1 => {  KernelWhnf::whnf_nd(rc, KernelSubst::expr_inst1(lam_body, list_arg, 0), types) } ,
                        _ => {  KernelWhnf::whnf_nd(rc, (&(KernelTypes::KExprNode::App(body, list_arg))), types) } ,
                      } } ,
                    _ => {  KernelWhnf::whnf_nd(rc, (&(KernelTypes::KExprNode::App(body, list_arg))), types) } ,
                  } } ,
                _ => {  expanded } ,
              } } ,
            _ => {  expanded } ,
          } } ,
        _ => {  expanded } ,
      }
    }
⟧

def str_lit_to_ctor_app_or_self := aiur_fn⟦
  fn str_lit_to_ctor_app_or_self(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Lit(lit) => {
          match lit {
            KernelTypes::KLiteral::Str(bs) => {  str_lit_delta_step(rc, str_lit_to_ctor(rc, bs), types) } ,
            _ => {  e } ,
          } } ,
        _ => {  e } ,
      }
    }
⟧

def split_u32 := aiur_fn⟦
  fn split_u32(x: Field) -> (Field, Field, Field, Field) {
      match KernelKlimbs::divmod_256(x, 0) {
        (b0, q1) => {
          match KernelKlimbs::divmod_256(q1, 0) {
            (b1, q2) => {
              match KernelKlimbs::divmod_256(q2, 0) {
                (b2, q3) => {
                  match KernelKlimbs::divmod_256(q3, 0) {
                    (b3, _) => {  (b0, b1, b2, b3) } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def klimbs_from_g := aiur_fn⟦
  fn klimbs_from_g(x: Field) -> KernelTypes::KLimbs {
      match split_u32(x) {
        (rb0, rb1, rb2, rb3) => {
          let b0 = UInt8::from_field(rb0);
          let b1 = UInt8::from_field(rb1);
          let b2 = UInt8::from_field(rb2);
          let b3 = UInt8::from_field(rb3);

          constrain_eq!(x, UInt8::to_field(b0) + 256 * UInt8::to_field(b1)
                     + 65536 * UInt8::to_field(b2) + 16777216 * UInt8::to_field(b3),
            "u32 byte split does not recompose to the original value");

          KernelKlimbs::klimbs_normalize((&(Lists::Node::Cons(
            [b0, b1, b2, b3, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], (&(Lists::Node::Nil)))))) } ,
      }
    }
⟧








  -- A `Nat` reading (`rawNatLit?`, through `Red.natSucc`): a literal, or `Nat.zero` and
  -- `Nat.succ` at an empty level list.

def lvls_empty := aiur_fn⟦
  inline fn lvls_empty(lvls: Lists::List<KernelTypes::KLevel>) -> Field {
      match (*(lvls)) {
        Lists::Node::Nil => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

def try_extract_nat := aiur_fn⟦
  fn try_extract_nat(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr) -> (Field, KernelTypes::KLimbs) {
      match (*(e)) {
        KernelTypes::KExprNode::Lit(lit) => {
          match lit {
            KernelTypes::KLiteral::Nat(limbs) => {  (1, limbs) } ,
            _ => {  (0, (&(Lists::Node::Nil))) } ,
          } } ,
        KernelTypes::KExprNode::Const(caddr, clvls) => {
          match KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_nat_zero()) * lvls_empty(clvls) {
            1 => {  (1, (&(Lists::Node::Nil))) } ,
            _ => {  (0, (&(Lists::Node::Nil))) } ,
          } } ,
        KernelTypes::KExprNode::App(f, a) => {  try_extract_nat_app(rc, f, a) } ,
        _ => {  (0, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

def try_extract_nat_app := aiur_fn⟦
  fn try_extract_nat_app(rc: KernelRoles::RoleCtx, f: KernelTypes::KExpr, a: KernelTypes::KExpr) -> (Field, KernelTypes::KLimbs) {
      match (*(f)) {
        KernelTypes::KExprNode::Const(caddr, clvls) => {
          match KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_nat_succ()) * lvls_empty(clvls) {
            1 => {
              match try_extract_nat(rc, a) {
                (1, pred_limbs) => {  (1, KernelKlimbs::klimbs_succ(pred_limbs)) } ,
                _ => {  (0, (&(Lists::Node::Nil))) } ,
              } } ,
            _ => {  (0, (&(Lists::Node::Nil))) } ,
          } } ,
        _ => {  (0, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

def mk_nat_lit := aiur_fn⟦
  fn mk_nat_lit(n: KernelTypes::KLimbs) -> KernelTypes::KExpr {
      (&(KernelTypes::KExprNode::Lit(KernelTypes::KLiteral::Nat(n))))
    }
⟧










def np_apply_spine := aiur_fn⟦
  fn np_apply_spine(head: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(spine)) {
        Lists::Node::Nil => {  head } ,
        Lists::Node::Cons(a, rest) => {
          np_apply_spine((&(KernelTypes::KExprNode::App(head, a))), rest) } ,
      }
    }
⟧

def try_nat_binop_addr := aiur_fn⟦
  fn try_nat_binop_addr(rc: KernelRoles::RoleCtx, op: Field, a: KernelTypes::KLimbs, b: KernelTypes::KLimbs) -> (Field, KernelTypes::KExpr) {
      match op {
        3 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_add(a, b)))) } ,
        4 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_sub(a, b)))) } ,
        5 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_mul(a, b)))) } ,
        6 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_div(a, b)))) } ,
        7 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_mod(a, b)))) } ,
        8 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_gcd(a, b)))) } ,
        -- IxC's cap (N4 removed): `Nat.pow` is computed only for an exponent up to 2^24.
        9 => {
          let cap = (&(Lists::Node::Cons([UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], (&(Lists::Node::Nil)))));
          match KernelKlimbs::klimbs_le(b, cap) {
            1 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_pow(a, b)))) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
        10 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_land(a, b)))) } ,
        11 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_lor(a, b)))) } ,
        12 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_xor_op(a, b)))) } ,
        13 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_shl(a, b)))) } ,
        14 => {  (1, mk_nat_lit(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_shr(a, b)))) } ,
        15 => {  (1, mk_bool(rc, KernelLevels::klimbs_eq(a, b))) } ,
        16 => {  (1, mk_bool(rc, KernelKlimbs::klimbs_le(a, b))) } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def try_match_nat_add := aiur_fn⟦
  fn try_match_nat_add(rc: KernelRoles::RoleCtx, head: KernelTypes::KExpr, args: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr, KernelTypes::KLimbs) {
      match (*(head)) {
        KernelTypes::KExprNode::Const(caddr, _) => {
          match KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_nat_add()) {
            0 => {  (0, head, (&(Lists::Node::Nil))) } ,
            _ => {
              match Lists::length(args) - 2 {
                0 => {
                  let lhs = Lists::lookup(args, 0);
                  let rhs = Lists::lookup(args, 1);
                  match (*(rhs)) {
                    KernelTypes::KExprNode::Lit(lit) => {
                      match lit {
                        KernelTypes::KLiteral::Nat(limbs) => {  (1, lhs, limbs) } ,
                        _ => {  (0, head, (&(Lists::Node::Nil))) } ,
                      } } ,
                    _ => {  (0, head, (&(Lists::Node::Nil))) } ,
                  } } ,
                _ => {  (0, head, (&(Lists::Node::Nil))) } ,
              } } ,
          } } ,
        _ => {  (0, head, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

def build_succ_offset := aiur_fn⟦
  fn build_succ_offset(rc: KernelRoles::RoleCtx, base: KernelTypes::KExpr, lit: KernelTypes::KLimbs) -> KernelTypes::KExpr {
      let one = (&(Lists::Node::Cons([UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0],
                                    (&(Lists::Node::Nil)))));
      let pred_lit_norm = KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_sub(lit, one));
      let succ_const = (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_nat_succ()), (&(Lists::Node::Nil)))));
      match KernelKlimbs::klimbs_is_zero(pred_lit_norm) {
        1 => {  (&(KernelTypes::KExprNode::App(succ_const, base))) } ,
        _ => {
          let add_const = (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_nat_add()), (&(Lists::Node::Nil)))));
          let pred_lit_expr = (&(KernelTypes::KExprNode::Lit(KernelTypes::KLiteral::Nat(pred_lit_norm))));
          let pred = (&(KernelTypes::KExprNode::App(
            (&(KernelTypes::KExprNode::App(add_const, base))),
            pred_lit_expr)));
          (&(KernelTypes::KExprNode::App(succ_const, pred))) } ,
      }
    }
⟧

def cleanup_nat_offset_major := aiur_fn⟦
  fn cleanup_nat_offset_major(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Lit(_) => {  e } ,
        _ => {
          match KernelTypes::collect_spine(e) {
            (head, args) => {
              match (*(head)) {
                KernelTypes::KExprNode::Const(_, _) => {
                  match try_match_nat_add(rc, head, args) {
                    (1, base, lit) => {
                      let lit_norm = KernelKlimbs::klimbs_normalize(lit);
                      match KernelKlimbs::klimbs_is_zero(lit_norm) {
                        1 => {  e } ,
                        _ => {  build_succ_offset(rc, base, lit_norm) } ,
                      } } ,
                    _ => {  e } ,
                  } } ,
                _ => {  e } ,
              } } ,
          } } ,
      }
    }
⟧

def mk_nat_offset_stuck := aiur_fn⟦
  fn mk_nat_offset_stuck(rc: KernelRoles::RoleCtx, base_w: KernelTypes::KExpr, n: KernelTypes::KLimbs,
                                post: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match KernelKlimbs::klimbs_is_zero(n) {
        1 => {  (1, np_apply_spine(base_w, post)) } ,
        _ => {
          let add_const = (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_nat_add()), (&(Lists::Node::Nil)))));
          let off = (&(KernelTypes::KExprNode::App(
            (&(KernelTypes::KExprNode::App(add_const, base_w))),
            mk_nat_lit(n))));
          (1, np_apply_spine(off, post)) } ,
      }
    }
⟧



def try_nat_dispatch := aiur_fn⟦
  inline fn try_nat_dispatch(rc: KernelRoles::RoleCtx, head_addr: Bytes::AddressRef, op: Field, spine: Lists::List<KernelTypes::KExpr>,
                            types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let spine_len = Lists::length(spine);
      match op {
        1 => {
          match UInt32::less_than_fields(spine_len, 1) {
            1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
            _ => {
              let a0 = Lists::lookup(spine, 0);
              match try_extract_nat(rc, a0) {
                (1, na) => {
                  let post = Lists::drop(spine, 1);
                  (1, np_apply_spine(mk_nat_lit(KernelKlimbs::klimbs_succ(na)), post)) } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
          } } ,
        -- `Nat.pred` (A4) is not a native: it reduces by its definition.
        2 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        _ => {  try_nat_binop_dispatch(rc, head_addr, op, spine, spine_len) } ,
      }
    }
⟧

def try_nat_binop_dispatch := aiur_fn⟦
  fn try_nat_binop_dispatch(rc: KernelRoles::RoleCtx, head_addr: Bytes::AddressRef, op: Field, spine: Lists::List<KernelTypes::KExpr>,
                                   spine_len: Field) -> (Field, KernelTypes::KExpr) {
      match UInt32::less_than_fields(spine_len, 2) {
        1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        _ => {
          let a0 = Lists::lookup(spine, 0);
          let a1 = Lists::lookup(spine, 1);
          match try_extract_nat(rc, a0) {
            (1, na) => {
              match try_extract_nat(rc, a1) {
                (1, nb) => {
                  match try_nat_binop_addr(rc, op, na, nb) {
                    (1, result) => {
                      let post = Lists::drop(spine, 2);
                      (1, np_apply_spine(result, post)) } ,
                    _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                  } } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
            _ => {

              match try_extract_nat(rc, a1) {
                (1, nb) => {
                  try_nat_offset_dispatch(rc, head_addr, op, a0, nb, spine) } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
          } } ,
      }
    }
⟧

def try_nat_offset_dispatch := aiur_fn⟦
  fn try_nat_offset_dispatch(rc: KernelRoles::RoleCtx, head_addr: Bytes::AddressRef, op: Field, a0_w: KernelTypes::KExpr, nb: KernelTypes::KLimbs,
                                    spine: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let post = Lists::drop(spine, 2);

      match op {
        3 => {
          match mk_nat_offset_stuck(rc, a0_w, nb, post) {
            (1, stuck) => {  (2, stuck) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
        6 | 7 => {
          let ge_two = (1 - KernelKlimbs::klimbs_is_zero(nb))
            * (1 - KernelKlimbs::klimbs_is_zero(KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_dec(nb))));
          match ge_two {
            0 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
            _ => {  (2, mk_nat_binop_stuck(head_addr, a0_w, nb, post)) } ,
          } } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def mk_nat_binop_stuck := aiur_fn⟦
  fn mk_nat_binop_stuck(op_addr: Bytes::AddressRef, base_w: KernelTypes::KExpr, n: KernelTypes::KLimbs,
                               post: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let op_const = (&(KernelTypes::KExprNode::Const(op_addr, (&(Lists::Node::Nil)))));
      let stuck = (&(KernelTypes::KExprNode::App(
        (&(KernelTypes::KExprNode::App(op_const, base_w))),
        mk_nat_lit(n))));
      np_apply_spine(stuck, post)
    }
⟧

end

end IxVM
