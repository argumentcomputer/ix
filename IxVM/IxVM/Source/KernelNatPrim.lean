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

def try_extract_nat_or_whnf := aiur_fn⟦
  fn try_extract_nat_or_whnf(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr,
                             types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KLimbs) {
      match try_extract_nat(rc, e) {
        (1, n) => {  (1, n) } ,
        _ => {  try_extract_nat(rc, KernelWhnf::whnf(rc, e, types)) } ,
      }
    }
⟧

  -- Extract a signed integer literal `Int.ofNat n` (`sign = 0`, `mag = n`) or
  -- `Int.negSucc n` (`sign = 1`, `mag = n + 1`) at an empty level list,
  -- normalizing the inner `Nat` argument lazily when not already a literal.

def try_extract_int_prim := aiur_fn⟦
  fn try_extract_int_prim(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr,
                          types: Lists::List<KernelTypes::KExpr>) -> (Field, Field, KernelTypes::KLimbs) {
      match (*(e)) {
        KernelTypes::KExprNode::App(f, a) => {
          match (*(f)) {
            KernelTypes::KExprNode::Const(caddr, clvls) => {
              match lvls_empty(clvls) {
                1 => {
                  match KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_int_of_nat()) {
                    1 => {
                      match try_extract_nat_or_whnf(rc, a, types) {
                        (1, n) => {  (1, 0, KernelKlimbs::klimbs_normalize(n)) } ,
                        _ => {  (0, 0, (&(Lists::Node::Nil))) } ,
                      } } ,
                    _ => {
                      match KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_int_neg_succ()) {
                        1 => {
                          match try_extract_nat_or_whnf(rc, a, types) {
                            (1, n) => {  (1, 1, KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_succ(n))) } ,
                            _ => {  (0, 0, (&(Lists::Node::Nil))) } ,
                          } } ,
                        _ => {  (0, 0, (&(Lists::Node::Nil))) } ,
                      } } ,
                  } } ,
                _ => {  (0, 0, (&(Lists::Node::Nil))) } ,
              } } ,
            _ => {  (0, 0, (&(Lists::Node::Nil))) } ,
          } } ,
        _ => {  (0, 0, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

def mk_int_prim := aiur_fn⟦
  fn mk_int_prim(rc: KernelRoles::RoleCtx, sign: Field, magnitude: KernelTypes::KLimbs) -> KernelTypes::KExpr {
      let mag = KernelKlimbs::klimbs_normalize(magnitude);
      let neg = sign * (1 - KernelKlimbs::klimbs_is_zero(mag));
      let caddr = match neg {
        0 => {  KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_int_of_nat()) } ,
        _ => {  KernelRoles::role_used_implicitly(rc, KernelRoleSpec::role_int_neg_succ()) } ,
      };
      let arg = match neg {
        0 => {  mag } ,
        _ => {  KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_dec(mag)) } ,
      };
      (&(KernelTypes::KExprNode::App((&(KernelTypes::KExprNode::Const(caddr, (&(Lists::Node::Nil))))), mk_nat_lit(arg))))
    }
⟧

def int_add_prim := aiur_fn⟦
  fn int_add_prim(rc: KernelRoles::RoleCtx, sa: Field, a: KernelTypes::KLimbs, sb: Field, b: KernelTypes::KLimbs) -> KernelTypes::KExpr {
      match sa - sb {
        0 => {  mk_int_prim(rc, sa, KernelKlimbs::klimbs_add(a, b)) } ,
        _ => {
          match KernelKlimbs::klimbs_le(a, b) {
            1 => {  mk_int_prim(rc, sb, KernelKlimbs::klimbs_sub(b, a)) } ,
            _ => {  mk_int_prim(rc, sa, KernelKlimbs::klimbs_sub(a, b)) } ,
          } } ,
      }
    }
⟧

def int_emod_prim := aiur_fn⟦
  fn int_emod_prim(rc: KernelRoles::RoleCtx, sa: Field, a: KernelTypes::KLimbs, b: KernelTypes::KLimbs) -> KernelTypes::KExpr {
      match KernelKlimbs::klimbs_is_zero(b) {
        1 => {  mk_int_prim(rc, sa, a) } ,
        _ => {
          let r0 = KernelKlimbs::klimbs_mod(a, b);
          match sa * (1 - KernelKlimbs::klimbs_is_zero(r0)) {
            1 => {  mk_int_prim(rc, 0, KernelKlimbs::klimbs_sub(b, r0)) } ,
            _ => {  mk_int_prim(rc, 0, r0) } ,
          } } ,
      }
    }
⟧

def int_ediv_prim := aiur_fn⟦
  fn int_ediv_prim(rc: KernelRoles::RoleCtx, sa: Field, a: KernelTypes::KLimbs, sb: Field, b: KernelTypes::KLimbs) -> KernelTypes::KExpr {
      match KernelKlimbs::klimbs_is_zero(b) {
        1 => {  mk_int_prim(rc, 0, (&(Lists::Node::Nil))) } ,
        _ => {
          let q0 = KernelKlimbs::klimbs_div(a, b);
          let r0 = KernelKlimbs::klimbs_mod(a, b);
          let q = match sa * (1 - KernelKlimbs::klimbs_is_zero(r0)) {
            1 => {  KernelKlimbs::klimbs_succ(q0) } ,
            _ => {  q0 } ,
          };
          mk_int_prim(rc, (sa + sb - 2 * sa * sb) * (1 - KernelKlimbs::klimbs_is_zero(q)), q) } ,
      }
    }
⟧

def int_bmod_prim := aiur_fn⟦
  fn int_bmod_prim(rc: KernelRoles::RoleCtx, sa: Field, a: KernelTypes::KLimbs, m: KernelTypes::KLimbs) -> KernelTypes::KExpr {
      match KernelKlimbs::klimbs_is_zero(m) {
        1 => {  mk_int_prim(rc, sa, a) } ,
        _ => {
          let r0 = KernelKlimbs::klimbs_mod(a, m);
          let r = match sa * (1 - KernelKlimbs::klimbs_is_zero(r0)) {
            1 => {  KernelKlimbs::klimbs_sub(m, r0) } ,
            _ => {  r0 } ,
          };
          let two = (&(Lists::Node::Cons([UInt8::BYTE_2, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], (&(Lists::Node::Nil)))));
          let half = KernelKlimbs::klimbs_div(KernelKlimbs::klimbs_succ(m), two);
          match KernelKlimbs::klimbs_le(half, r) {
            1 => {  mk_int_prim(rc, 1, KernelKlimbs::klimbs_sub(m, r)) } ,
            _ => {  mk_int_prim(rc, 0, r) } ,
          } } ,
      }
    }
⟧

def int_bdiv_prim := aiur_fn⟦
  fn int_bdiv_prim(rc: KernelRoles::RoleCtx, sa: Field, a: KernelTypes::KLimbs, m: KernelTypes::KLimbs) -> KernelTypes::KExpr {
      match KernelKlimbs::klimbs_is_zero(m) {
        1 => {  mk_int_prim(rc, 0, (&(Lists::Node::Nil))) } ,
        _ => {
          let r0 = KernelKlimbs::klimbs_mod(a, m);
          let r = match sa * (1 - KernelKlimbs::klimbs_is_zero(r0)) {
            1 => {  KernelKlimbs::klimbs_sub(m, r0) } ,
            _ => {  r0 } ,
          };
          let q0 = KernelKlimbs::klimbs_div(a, m);
          let qmag = match sa * (1 - KernelKlimbs::klimbs_is_zero(r0)) {
            1 => {  KernelKlimbs::klimbs_succ(q0) } ,
            _ => {  q0 } ,
          };
          let qsign = sa * (1 - KernelKlimbs::klimbs_is_zero(qmag));
          let two = (&(Lists::Node::Cons([UInt8::BYTE_2, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], (&(Lists::Node::Nil)))));
          let half = KernelKlimbs::klimbs_div(KernelKlimbs::klimbs_succ(m), two);
          match KernelKlimbs::klimbs_le(half, r) {
            0 => {  mk_int_prim(rc, qsign, qmag) } ,
            _ => {  int_add_prim(rc, qsign, qmag, 0,
              (&(Lists::Node::Cons([UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], (&(Lists::Node::Nil)))))) } ,
          } } ,
      }
    }
⟧

def try_int_unop_dispatch := aiur_fn⟦
  fn try_int_unop_dispatch(rc: KernelRoles::RoleCtx, op: Field, a0: KernelTypes::KExpr,
                           post: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>)
                           -> (Field, KernelTypes::KExpr) {
      let w0 = KernelWhnf::whnf(rc, a0, types);
      match try_extract_int_prim(rc, w0, types) {
        (1, s, a) => {
          let v = match op {
            2 => {  mk_nat_lit(a) } ,
            _ => {  mk_int_prim(rc, (1 - s) * (1 - KernelKlimbs::klimbs_is_zero(a)), a) } ,
          };
          (1, np_apply_spine(v, post)) } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def try_int_nat_arg_prim := aiur_fn⟦
  fn try_int_nat_arg_prim(rc: KernelRoles::RoleCtx, op: Field, sa: Field,
                          a: KernelTypes::KLimbs, b: KernelTypes::KLimbs) -> (Field, KernelTypes::KExpr) {
      match op {
        3 => {  (1, int_bmod_prim(rc, sa, a, b)) } ,
        4 => {  (1, int_bdiv_prim(rc, sa, a, b)) } ,
        5 => {
          let cap = (&(Lists::Node::Cons([UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], (&(Lists::Node::Nil)))));
          match KernelKlimbs::klimbs_le(b, cap) {
            1 => {
              let two = (&(Lists::Node::Cons([UInt8::BYTE_2, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], (&(Lists::Node::Nil)))));
              let odd = 1 - KernelKlimbs::klimbs_is_zero(KernelKlimbs::klimbs_mod(b, two));
              (1, mk_int_prim(rc, sa * odd, KernelKlimbs::klimbs_pow(a, b))) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def try_int_int_arg_prim := aiur_fn⟦
  fn try_int_int_arg_prim(rc: KernelRoles::RoleCtx, op: Field, sa: Field, a: KernelTypes::KLimbs,
                          sb: Field, b: KernelTypes::KLimbs) -> (Field, KernelTypes::KExpr) {
      match op {
        6 => {  (1, int_add_prim(rc, sa, a, sb, b)) } ,
        7 => {  (1, int_add_prim(rc, sa, a, (1 - sb) * (1 - KernelKlimbs::klimbs_is_zero(b)), b)) } ,
        8 => {  (1, mk_int_prim(rc, (sa + sb - 2 * sa * sb)
          * (1 - KernelKlimbs::klimbs_is_zero(a)) * (1 - KernelKlimbs::klimbs_is_zero(b)),
          KernelKlimbs::klimbs_mul(a, b))) } ,
        9 => {  (1, int_emod_prim(rc, sa, a, b)) } ,
        10 => {  (1, int_ediv_prim(rc, sa, a, sb, b)) } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def try_int_binop_second := aiur_fn⟦
  fn try_int_binop_second(rc: KernelRoles::RoleCtx, op: Field, a1: KernelTypes::KExpr,
                          post: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>,
                          sa: Field, a: KernelTypes::KLimbs) -> (Field, KernelTypes::KExpr) {
      let w1 = KernelWhnf::whnf(rc, a1, types);
      let is_nat_arg = Fields::is_zero(op - 3) + Fields::is_zero(op - 4) + Fields::is_zero(op - 5);
      match is_nat_arg {
        0 => {
          match try_extract_int_prim(rc, w1, types) {
            (1, sb, b) => {
              match try_int_int_arg_prim(rc, op, sa, a, sb, b) {
                (1, v) => {  (1, np_apply_spine(v, post)) } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
        _ => {
          match try_extract_nat(rc, w1) {
            (1, b) => {
              match try_int_nat_arg_prim(rc, op, sa, a, KernelKlimbs::klimbs_normalize(b)) {
                (1, v) => {  (1, np_apply_spine(v, post)) } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
      }
    }
⟧

def try_int_prim_dispatch := aiur_fn⟦
  fn try_int_prim_dispatch(rc: KernelRoles::RoleCtx, op: Field, spine: Lists::List<KernelTypes::KExpr>,
                           types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match (*(spine)) {
        Lists::Node::Nil => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        Lists::Node::Cons(a0, rest0) => {
          let is_unop = Fields::is_zero(op - 1) + Fields::is_zero(op - 2);
          match is_unop {
            0 => {
              match (*(rest0)) {
                Lists::Node::Nil => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                Lists::Node::Cons(a1, post) => {
                  let w0 = KernelWhnf::whnf(rc, a0, types);
                  match try_extract_int_prim(rc, w0, types) {
                    (1, sa, a) => {  try_int_binop_second(rc, op, a1, post, types, sa, a) } ,
                    _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                  } } ,
              } } ,
            _ => {  try_int_unop_dispatch(rc, op, a0, rest0, types) } ,
          } } ,
      }
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
