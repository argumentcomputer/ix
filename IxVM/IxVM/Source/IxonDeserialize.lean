import Aiur.Modules.Function

/-! # IxVM module `IxonDeserialize`

Ixon deserialization.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module IxonDeserialize where

def read_byte := aiur_fn⟦
  fn read_byte(stream: Bytes::Stream) -> (UInt8::U8, Bytes::Stream) {
      let Lists::Node::Cons(byte, rest) = (*(stream));
      (byte, rest)
    }
⟧

def get_u64_le := aiur_fn⟦
  fn get_u64_le(stream: Bytes::Stream, num_bytes: Field) -> (UInt64::U64, Bytes::Stream) {
      match num_bytes {
        0 => {  ([UInt8::BYTE_0; 8], stream) } ,
        _ => {
          let Lists::Node::Cons(byte, s) = (*(stream));
          let (rest_bytes, s2) = get_u64_le(s, num_bytes - 1);
          let [r0, r1, r2, r3, r4, r5, r6, _] = rest_bytes;
          ([byte, r0, r1, r2, r3, r4, r5, r6], s2) } ,
      }
    }
⟧

def get_tagn4 := aiur_fn⟦
  fn get_tagn4(stream: Bytes::Stream) -> ((Field, UInt64::U64), Bytes::Stream) {
      let Lists::Node::Cons(byte, s) = (*(stream));
      let [b0, b1, b2, b3, b4, b5, b6, b7] = UInt8::bit_decomposition(byte);
      let flag = b4 + 2 * b5 + 4 * b6 + 8 * b7;
      let low = b0 + 2 * b1 + 4 * b2;
      match b3 {
        0 => {  ((flag, [UInt8::from_field(low), UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), s) } ,
        1 => {
          let (value, rest) = get_tagn_tail(low, 4, s);
          ((flag, value), rest) } ,
      }
    }
⟧

def get_tagn2 := aiur_fn⟦
  fn get_tagn2(stream: Bytes::Stream) -> ((Field, UInt64::U64), Bytes::Stream) {
      let Lists::Node::Cons(byte, s) = (*(stream));
      let [b0, b1, b2, b3, b4, b5, b6, b7] = UInt8::bit_decomposition(byte);
      let flag = b6 + 2 * b7;
      let low = b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4;
      match b5 {
        0 => {  ((flag, [UInt8::from_field(low), UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]), s) } ,
        1 => {
          let (value, rest) = get_tagn_tail(low, 16, s);
          ((flag, value), rest) } ,
      }
    }
⟧

def get_tagn0 := aiur_fn⟦
  fn get_tagn0(stream: Bytes::Stream) -> (UInt64::U64, Bytes::Stream) {
      let Lists::Node::Cons(byte, s) = (*(stream));
      match UInt8::less_than(byte, UInt8::BYTE_128) {
        1 => {  ([byte, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], s) } ,
        0 => {  get_tagn_tail(UInt8::to_field(byte) - 128, 64, s) } ,
      }
    }
⟧

def get_tagn_tail := aiur_fn⟦
  fn get_tagn_tail(q: Field, h: Field, stream: Bytes::Stream) -> (UInt64::U64, Bytes::Stream) {
      match UInt8::raw_lt(q, h) {

        1 => {
          let Lists::Node::Cons(lo, s) = (*(stream));
          let (v0, carry) = UInt8::raw_add(UInt8::to_field(lo), 2 * h);
          ([v0, UInt8::from_field(q + UInt8::to_field(carry)), UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0], s) } ,
        0 => {  get_tagn_wide(q - h, h, stream) } ,
      }
    }
⟧

def get_tagn_wide := aiur_fn⟦
  fn get_tagn_wide(c: Field, h: Field, stream: Bytes::Stream) -> (UInt64::U64, Bytes::Stream) {
      let r0 = UInt8::from_field(2 * h);
      let r1 = UInt8::from_field(h);
      match c {
        0 => {
          let (x, s) = get_u64_le(stream, 2);
          let (value, _) = UInt64::add(x, [r0, r1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]);
          (value, s) } ,
        1 => {
          let (x, s) = get_u64_le(stream, 3);
          let (value, _) = UInt64::add(x, [r0, r1, UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]);
          (value, s) } ,
        2 => {
          let (x, s) = get_u64_le(stream, 4);
          let (value, _) = UInt64::add(x, [r0, r1, UInt8::BYTE_1, UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]);
          (value, s) } ,
        3 => {
          let (x, s) = get_u64_le(stream, 8);
          let (value, carry) = UInt64::add(x, [r0, r1, UInt8::BYTE_1, UInt8::BYTE_1, UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0]);
          assert_eq!(UInt8::to_field(carry), 0, "TagN value exceeds UInt64");
          (value, s) } ,
      }
    }
⟧

def get_u64_list := aiur_fn⟦
  fn get_u64_list(stream: Bytes::Stream, count: UInt64::U64) -> (Lists::List<UInt64::U64>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (val, s) = get_tagn0(stream);
          let (rest, s2) = get_u64_list(s, UInt64::saturating_pred(count));
          ((&(Lists::Node::Cons(val, rest))), s2) } ,
      }
    }
⟧

def get_app_telescope := aiur_fn⟦
  fn get_app_telescope(func: &Ixon::Expr, stream: Bytes::Stream, count: UInt64::U64) -> (&Ixon::Expr, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  (func, stream) } ,
        0 => {
          let (arg, s) = get_expr(stream);
          get_app_telescope((&(Ixon::Expr::App(func, arg))), s, UInt64::saturating_pred(count)) } ,
      }
    }
⟧

def value_contract_from_bits := aiur_fn⟦
  fn value_contract_from_bits(owned_bit: Field, locality_bit: Field) -> Ixon::ValueContract {
      let owned = match owned_bit { 0 => {  Ixon::Owned::Unique } , 1 => {  Ixon::Owned::Shared } , };
      let locality = match locality_bit { 0 => {  Ixon::Locality::Unrestricted } , 1 => {  Ixon::Locality::Local } , };
      Ixon::ValueContract::Mk(owned, locality)
    }
⟧

def binder_contract_from_bits := aiur_fn⟦
  fn binder_contract_from_bits(b0: Field, b1: Field, b2: Field, b3: Field) -> Ixon::BinderContract {
      let uses = match b0 + 2 * b1 { 0 => {  Ixon::Uses::Erased } , 1 => {  Ixon::Uses::Linear } , 2 => {  Ixon::Uses::Affine } , 3 => {  Ixon::Uses::Many } , };
      Ixon::BinderContract::Mk(uses, value_contract_from_bits(b2, b3))
    }
⟧

def get_lam_mode := aiur_fn⟦
  fn get_lam_mode(stream: Bytes::Stream) -> (Ixon::BinderContract, Bytes::Stream) {
      let (mode, s) = read_byte(stream);
      let [b0, b1, b2, b3, b4, b5, b6, b7] = UInt8::bit_decomposition(mode);
      assert_eq!(b4 + b5 + b6 + b7, 0, "reserved binder contract bits");
      (binder_contract_from_bits(b0, b1, b2, b3), s)
    }
⟧

def get_all_mode := aiur_fn⟦
  fn get_all_mode(stream: Bytes::Stream) -> ((Ixon::BinderContract, Ixon::ValueContract), Bytes::Stream) {
      let (mode, s) = read_byte(stream);
      let [b0, b1, b2, b3, b4, b5, b6, b7] = UInt8::bit_decomposition(mode);
      assert_eq!(b6 + b7, 0, "reserved forall contract bits");
      ((binder_contract_from_bits(b0, b1, b2, b3), value_contract_from_bits(b4, b5)), s)
    }
⟧

def get_lam_telescope := aiur_fn⟦
  fn get_lam_telescope(stream: Bytes::Stream, count: UInt64::U64) -> (&Ixon::Expr, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {
          let (body, s) = get_expr(stream);
          match (*(body)) {
            Ixon::Expr::Lam(_, _, _) => {
              assert_eq!(0, 1, "non-canonical lambda telescope");
              (body, s) } ,
            _ => {  (body, s) } ,
          } } ,
        0 => {
          let (contract, s) = get_lam_mode(stream);
          let (ty, s2) = get_expr(s);
          let (inner, s3) = get_lam_telescope(s2, UInt64::saturating_pred(count));
          ((&(Ixon::Expr::Lam(contract, ty, inner))), s3) } ,
      }
    }
⟧

def get_all_telescope := aiur_fn⟦
  fn get_all_telescope(stream: Bytes::Stream, count: UInt64::U64) -> (&Ixon::Expr, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {
          let (body, s) = get_expr(stream);
          match (*(body)) {
            Ixon::Expr::All(_, _, _, _) => {
              assert_eq!(0, 1, "non-canonical forall telescope");
              (body, s) } ,
            _ => {  (body, s) } ,
          } } ,
        0 => {
          let (mode, s) = get_all_mode(stream);
          let (input, result) = mode;
          let (ty, s2) = get_expr(s);
          let (inner, s3) = get_all_telescope(s2, UInt64::saturating_pred(count));
          ((&(Ixon::Expr::All(input, result, ty, inner))), s3) } ,
      }
    }
⟧

def get_expr := aiur_fn⟦
  fn get_expr(stream: Bytes::Stream) -> (&Ixon::Expr, Bytes::Stream) {
      let (tag, s) = get_tagn4(stream);
      let (flag, size) = tag;
      match flag {

        0 => {  ((&(Ixon::Expr::Srt(size))), s) } ,

        1 => {  ((&(Ixon::Expr::Var(size))), s) } ,

        2 => {
          let (ref_idx, s2) = get_tagn0(s);
          let (univ_list, s3) = get_u64_list(s2, size);
          ((&(Ixon::Expr::Ref(ref_idx, univ_list))), s3) } ,

        3 => {
          let (rec_idx, s2) = get_tagn0(s);
          let (univ_list, s3) = get_u64_list(s2, size);
          ((&(Ixon::Expr::Rec(rec_idx, univ_list))), s3) } ,

        4 => {
          let (type_ref_idx, s2) = get_tagn0(s);
          let (val, s3) = get_expr(s2);
          ((&(Ixon::Expr::Prj(type_ref_idx, size, val))), s3) } ,

        5 => {  ((&(Ixon::Expr::Str(size))), s) } ,

        6 => {  ((&(Ixon::Expr::Nat(size))), s) } ,

        7 => {
          assert_eq!(UInt64::is_zero(size), 0, "App with zero arguments");
          let (func, s2) = get_expr(s);

          match (*(func)) {
            Ixon::Expr::App(_, _) => {
              assert_eq!(0, 1, "non-canonical application telescope");
              get_app_telescope(func, s2, size) } ,
            _ => {  get_app_telescope(func, s2, size) } ,
          } } ,

        8 => {
          assert_eq!(UInt64::is_zero(size), 0, "Lam with zero binders");
          get_lam_telescope(s, size) } ,

        9 => {
          assert_eq!(UInt64::is_zero(size), 0, "All with zero binders");
          get_all_telescope(s, size) } ,

        10 => {  get_expr_let(s, size) } ,

        11 => {  ((&(Ixon::Expr::Share(size))), s) } ,
      }
    }
⟧

def get_expr_let := aiur_fn⟦
  fn get_expr_let(s: Bytes::Stream, size: UInt64::U64) -> (&Ixon::Expr, Bytes::Stream) {
      let [head, b1, b2, b3, b4, b5, b6, b7] = size;
      assert_eq!(UInt8::to_field(b1) + UInt8::to_field(b2) + UInt8::to_field(b3) + UInt8::to_field(b4) +
        UInt8::to_field(b5) + UInt8::to_field(b6) + UInt8::to_field(b7), 0, "oversized let flags");
      assert_eq!(UInt8::less_than(head, UInt8::BYTE_4), 1, "reserved let flags");
      let bits = UInt8::bit_decomposition(head);
      let kind = match bits[1] { 0 => {  Ixon::LetKind::Value } , 1 => {  Ixon::LetKind::BorrowShared } , };
      let (contract, s1) = get_lam_mode(s);
      let (ty, s2) = get_expr(s1);
      let (value, s3) = get_expr(s2);
      let (body, rest) = get_expr(s3);
      ((&(Ixon::Expr::Let(Ixon::LetContract::Mk(bits[0], kind, contract), ty, value, body))), rest)
    }
⟧

def build_succ_chain := aiur_fn⟦
  fn build_succ_chain(base: Ixon::Univ, count: UInt64::U64) -> Ixon::Univ {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  base } ,
        0 => {
          let inner = build_succ_chain(base, UInt64::saturating_pred(count));
          Ixon::Univ::Succ((&(inner))) } ,
      }
    }
⟧

def get_univ := aiur_fn⟦
  fn get_univ(stream: Bytes::Stream) -> (Ixon::Univ, Bytes::Stream) {
      let (tag, s) = get_tagn2(stream);
      let (flag, size) = tag;
      match flag {

        0 => {
          let is_zero = UInt64::is_zero(size);
          match is_zero {
            1 => {  (Ixon::Univ::Zero, s) } ,
            0 => {
              let (base, s2) = get_univ(s);
              (build_succ_chain(base, size), s2) } ,
          } } ,

        1 => {
          let (a, s2) = get_univ(s);
          let (b, s3) = get_univ(s2);
          (Ixon::Univ::Max((&(a)), (&(b))), s3) } ,

        2 => {
          let (a, s2) = get_univ(s);
          let (b, s3) = get_univ(s2);
          (Ixon::Univ::IMax((&(a)), (&(b))), s3) } ,

        3 => {  (Ixon::Univ::Var(size), s) } ,
      }
    }
⟧

def get_address := aiur_fn⟦
  fn get_address(stream: Bytes::Stream) -> (Bytes::AddressRef, Bytes::Stream) {
      let Lists::Node::Cons(b0, s) = (*(stream));
      let Lists::Node::Cons(b1, s) = (*(s));
      let Lists::Node::Cons(b2, s) = (*(s));
      let Lists::Node::Cons(b3, s) = (*(s));
      let Lists::Node::Cons(b4, s) = (*(s));
      let Lists::Node::Cons(b5, s) = (*(s));
      let Lists::Node::Cons(b6, s) = (*(s));
      let Lists::Node::Cons(b7, s) = (*(s));
      let Lists::Node::Cons(b8, s) = (*(s));
      let Lists::Node::Cons(b9, s) = (*(s));
      let Lists::Node::Cons(b10, s) = (*(s));
      let Lists::Node::Cons(b11, s) = (*(s));
      let Lists::Node::Cons(b12, s) = (*(s));
      let Lists::Node::Cons(b13, s) = (*(s));
      let Lists::Node::Cons(b14, s) = (*(s));
      let Lists::Node::Cons(b15, s) = (*(s));
      let Lists::Node::Cons(b16, s) = (*(s));
      let Lists::Node::Cons(b17, s) = (*(s));
      let Lists::Node::Cons(b18, s) = (*(s));
      let Lists::Node::Cons(b19, s) = (*(s));
      let Lists::Node::Cons(b20, s) = (*(s));
      let Lists::Node::Cons(b21, s) = (*(s));
      let Lists::Node::Cons(b22, s) = (*(s));
      let Lists::Node::Cons(b23, s) = (*(s));
      let Lists::Node::Cons(b24, s) = (*(s));
      let Lists::Node::Cons(b25, s) = (*(s));
      let Lists::Node::Cons(b26, s) = (*(s));
      let Lists::Node::Cons(b27, s) = (*(s));
      let Lists::Node::Cons(b28, s) = (*(s));
      let Lists::Node::Cons(b29, s) = (*(s));
      let Lists::Node::Cons(b30, s) = (*(s));
      let Lists::Node::Cons(b31, s) = (*(s));
      ((&([b0, b1, b2,
        b3, b4, b5,
        b6, b7, b8,
        b9, b10, b11,
        b12, b13, b14,
        b15, b16, b17,
        b18, b19, b20,
        b21, b22, b23,
        b24, b25, b26,
        b27, b28, b29,
        b30, b31])), s)
    }
⟧

def get_expr_list := aiur_fn⟦
  fn get_expr_list(stream: Bytes::Stream, count: UInt64::U64) -> (Lists::List<&Ixon::Expr>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (expr, s) = get_expr(stream);
          let (rest, s2) = get_expr_list(s, UInt64::saturating_pred(count));
          ((&(Lists::Node::Cons(expr, rest))), s2) } ,
      }
    }
⟧

def get_univ_list := aiur_fn⟦
  fn get_univ_list(stream: Bytes::Stream, count: UInt64::U64) -> (Lists::List<&Ixon::Univ>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (u, s) = get_univ(stream);
          let (rest, s2) = get_univ_list(s, UInt64::saturating_pred(count));
          ((&(Lists::Node::Cons((&(u)), rest))), s2) } ,
      }
    }
⟧

def get_address_list := aiur_fn⟦
  fn get_address_list(stream: Bytes::Stream, count: UInt64::U64) -> (Lists::List<Bytes::AddressRef>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (addr, s) = get_address(stream);
          let (rest, s2) = get_address_list(s, UInt64::saturating_pred(count));
          ((&(Lists::Node::Cons(addr, rest))), s2) } ,
      }
    }
⟧

def get_sharing := aiur_fn⟦
  inline fn get_sharing(stream: Bytes::Stream) -> (Lists::List<&Ixon::Expr>, Bytes::Stream) {
      let (len, s) = get_tagn0(stream);
      get_expr_list(s, len)
    }
⟧

def get_refs := aiur_fn⟦
  inline fn get_refs(stream: Bytes::Stream) -> (Lists::List<Bytes::AddressRef>, Bytes::Stream) {
      let (len, s) = get_tagn0(stream);
      get_address_list(s, len)
    }
⟧

def get_univs := aiur_fn⟦
  inline fn get_univs(stream: Bytes::Stream) -> (Lists::List<&Ixon::Univ>, Bytes::Stream) {
      let (len, s) = get_tagn0(stream);
      get_univ_list(s, len)
    }
⟧

def unpack_def_kind_safety := aiur_fn⟦
  fn unpack_def_kind_safety(byte: UInt8::U8) -> (Ixon::DefKind, Ixon::DefinitionSafety) {
      match UInt8::to_field(byte) {
        0 => {  (Ixon::DefKind::Definition, Ixon::DefinitionSafety::Unsafe) } ,
        1 => {  (Ixon::DefKind::Definition, Ixon::DefinitionSafety::Safe) } ,
        2 => {  (Ixon::DefKind::Definition, Ixon::DefinitionSafety::Partial) } ,
        4 => {  (Ixon::DefKind::Opaque, Ixon::DefinitionSafety::Unsafe) } ,
        5 => {  (Ixon::DefKind::Opaque, Ixon::DefinitionSafety::Safe) } ,
        6 => {  (Ixon::DefKind::Opaque, Ixon::DefinitionSafety::Partial) } ,
        8 => {  (Ixon::DefKind::Theorem, Ixon::DefinitionSafety::Unsafe) } ,
        9 => {  (Ixon::DefKind::Theorem, Ixon::DefinitionSafety::Safe) } ,
        10 => {  (Ixon::DefKind::Theorem, Ixon::DefinitionSafety::Partial) } ,
      }
    }
⟧

def get_definition := aiur_fn⟦
  fn get_definition(stream: Bytes::Stream) -> (Ixon::Definition, Bytes::Stream) {
      let (packed, s) = read_byte(stream);
      let (kind, safety) = unpack_def_kind_safety(packed);
      let (lvls, s2) = get_tagn0(s);
      let (typ, s3) = get_expr(s2);
      let (value, s4) = get_expr(s3);
      (Ixon::Definition::Mk(kind, safety, lvls, typ, value), s4)
    }
⟧

def get_recursor_rule := aiur_fn⟦
  inline fn get_recursor_rule(stream: Bytes::Stream) -> (Ixon::RecursorRule, Bytes::Stream) {
      let (fields, s) = get_tagn0(stream);
      let (rhs, s2) = get_expr(s);
      (Ixon::RecursorRule::Mk(fields, rhs), s2)
    }
⟧

def get_recursor_rule_list := aiur_fn⟦
  fn get_recursor_rule_list(stream: Bytes::Stream, count: UInt64::U64) -> (Lists::List<Ixon::RecursorRule>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (rule, s) = get_recursor_rule(stream);
          let (rest, s2) = get_recursor_rule_list(s, UInt64::saturating_pred(count));
          ((&(Lists::Node::Cons(rule, rest))), s2) } ,
      }
    }
⟧

def get_recursor := aiur_fn⟦
  fn get_recursor(stream: Bytes::Stream) -> (Ixon::Recursor, Bytes::Stream) {
      let (bools_byte, s) = read_byte(stream);
      assert_eq!(UInt8::less_than(bools_byte, UInt8::BYTE_4), 1, "invalid recursor flags");
      let bits = UInt8::bit_decomposition(bools_byte);
      let k = bits[0];
      let is_unsafe = bits[1];
      let (lvls, s2) = get_tagn0(s);
      let (params, s3) = get_tagn0(s2);
      let (indices, s4) = get_tagn0(s3);
      let (motives, s5) = get_tagn0(s4);
      let (minors, s6) = get_tagn0(s5);
      let (typ, s7) = get_expr(s6);
      let (rules_len, s8) = get_tagn0(s7);
      let (rules, s9) = get_recursor_rule_list(s8, rules_len);
      (Ixon::Recursor::Mk(k, is_unsafe, lvls, params, indices, motives, minors, typ, rules), s9)
    }
⟧

def assert_wire_bool := aiur_fn⟦
  fn assert_wire_bool(b: UInt8::U8) -> () {
      assert_eq!(UInt8::less_than(b, UInt8::BYTE_2), 1, "Bool byte is not 0 or 1");
      ()
    }
⟧

def get_axiom := aiur_fn⟦
  fn get_axiom(stream: Bytes::Stream) -> (Ixon::Axiom, Bytes::Stream) {
      let (is_unsafe, s) = read_byte(stream);
      assert_wire_bool(is_unsafe);
      let (lvls, s2) = get_tagn0(s);
      let (typ, s3) = get_expr(s2);
      (Ixon::Axiom::Mk(UInt8::to_field(is_unsafe), lvls, typ), s3)
    }
⟧

def get_quot_kind := aiur_fn⟦
  fn get_quot_kind(byte: UInt8::U8) -> Ixon::QuotKind {
      match UInt8::to_field(byte) {
        0 => {  Ixon::QuotKind::Typ } ,
        1 => {  Ixon::QuotKind::Ctor } ,
        2 => {  Ixon::QuotKind::Lift } ,
        3 => {  Ixon::QuotKind::Ind } ,
      }
    }
⟧

def get_quotient := aiur_fn⟦
  fn get_quotient(stream: Bytes::Stream) -> (Ixon::Quotient, Bytes::Stream) {
      let (kind_byte, s) = read_byte(stream);
      let kind = get_quot_kind(kind_byte);
      let (lvls, s2) = get_tagn0(s);
      let (typ, s3) = get_expr(s2);
      (Ixon::Quotient::Mk(kind, lvls, typ), s3)
    }
⟧

def get_constructor := aiur_fn⟦
  fn get_constructor(stream: Bytes::Stream) -> (Ixon::Constructor, Bytes::Stream) {
      let (is_unsafe, s) = read_byte(stream);
      assert_wire_bool(is_unsafe);
      let (lvls, s2) = get_tagn0(s);
      let (cidx, s3) = get_tagn0(s2);
      let (params, s4) = get_tagn0(s3);
      let (fields, s5) = get_tagn0(s4);
      let (typ, s6) = get_expr(s5);
      (Ixon::Constructor::Mk(UInt8::to_field(is_unsafe), lvls, cidx, params, fields, typ), s6)
    }
⟧

def get_constructor_list := aiur_fn⟦
  fn get_constructor_list(stream: Bytes::Stream, count: UInt64::U64) -> (Lists::List<Ixon::Constructor>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (ctor, s) = get_constructor(stream);
          let (rest, s2) = get_constructor_list(s, UInt64::saturating_pred(count));
          ((&(Lists::Node::Cons(ctor, rest))), s2) } ,
      }
    }
⟧

def get_inductive := aiur_fn⟦
  fn get_inductive(stream: Bytes::Stream) -> (Ixon::Inductive, Bytes::Stream) {
      let (bools_byte, s) = read_byte(stream);
      assert_wire_bool(bools_byte);
      let bits = UInt8::bit_decomposition(bools_byte);
      let is_unsafe = bits[0];
      let (lvls, s2) = get_tagn0(s);
      let (params, s3) = get_tagn0(s2);
      let (indices, s4) = get_tagn0(s3);
      let (typ, s5) = get_expr(s4);
      let (ctors_len, s6) = get_tagn0(s5);
      let (ctors, s7) = get_constructor_list(s6, ctors_len);
      (Ixon::Inductive::Mk(is_unsafe, lvls, params, indices, typ, ctors), s7)
    }
⟧

def get_inductive_proj := aiur_fn⟦
  fn get_inductive_proj(stream: Bytes::Stream) -> (Ixon::InductiveProj, Bytes::Stream) {
      let (idx, s) = get_tagn0(stream);
      let (block, s2) = get_address(s);
      (Ixon::InductiveProj::Mk(idx, block), s2)
    }
⟧

def get_constructor_proj := aiur_fn⟦
  fn get_constructor_proj(stream: Bytes::Stream) -> (Ixon::ConstructorProj, Bytes::Stream) {
      let (idx, s) = get_tagn0(stream);
      let (cidx, s2) = get_tagn0(s);
      let (block, s3) = get_address(s2);
      (Ixon::ConstructorProj::Mk(idx, cidx, block), s3)
    }
⟧

def get_recursor_proj := aiur_fn⟦
  fn get_recursor_proj(stream: Bytes::Stream) -> (Ixon::RecursorProj, Bytes::Stream) {
      let (idx, s) = get_tagn0(stream);
      let (block, s2) = get_address(s);
      (Ixon::RecursorProj::Mk(idx, block), s2)
    }
⟧

def get_definition_proj := aiur_fn⟦
  fn get_definition_proj(stream: Bytes::Stream) -> (Ixon::DefinitionProj, Bytes::Stream) {
      let (idx, s) = get_tagn0(stream);
      let (block, s2) = get_address(s);
      (Ixon::DefinitionProj::Mk(idx, block), s2)
    }
⟧

def get_mut_const := aiur_fn⟦
  fn get_mut_const(stream: Bytes::Stream) -> (Ixon::MutConst, Bytes::Stream) {
      let (tag, s) = read_byte(stream);
      match UInt8::to_field(tag) {
        0 => {
          let (defn, s2) = get_definition(s);
          (Ixon::MutConst::Defn(defn), s2) } ,
        1 => {
          let (indc, s2) = get_inductive(s);
          (Ixon::MutConst::Indc(indc), s2) } ,
        2 => {
          let (recr, s2) = get_recursor(s);
          (Ixon::MutConst::Recr(recr), s2) } ,
      }
    }
⟧

def get_mut_const_list := aiur_fn⟦
  fn get_mut_const_list(stream: Bytes::Stream, count: UInt64::U64) -> (Lists::List<Ixon::MutConst>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (mc, s) = get_mut_const(stream);
          let (rest, s2) = get_mut_const_list(s, UInt64::saturating_pred(count));
          ((&(Lists::Node::Cons(mc, rest))), s2) } ,
      }
    }
⟧

def get_constant_info_by_variant := aiur_fn⟦
  fn get_constant_info_by_variant(variant: Field, stream: Bytes::Stream) -> (Ixon::ConstantInfo, Bytes::Stream) {
      match variant {
        0 => {
          let (defn, s) = get_definition(stream);
          (Ixon::ConstantInfo::Defn(defn), s) } ,
        1 => {
          let (recr, s) = get_recursor(stream);
          (Ixon::ConstantInfo::Recr(recr), s) } ,
        2 => {
          let (axim, s) = get_axiom(stream);
          (Ixon::ConstantInfo::Axio(axim), s) } ,
        3 => {
          let (quot, s) = get_quotient(stream);
          (Ixon::ConstantInfo::Quot(quot), s) } ,
        4 => {
          let (prj, s) = get_constructor_proj(stream);
          (Ixon::ConstantInfo::CPrj(prj), s) } ,
        5 => {
          let (prj, s) = get_recursor_proj(stream);
          (Ixon::ConstantInfo::RPrj(prj), s) } ,
        6 => {
          let (prj, s) = get_inductive_proj(stream);
          (Ixon::ConstantInfo::IPrj(prj), s) } ,
        7 => {
          let (prj, s) = get_definition_proj(stream);
          (Ixon::ConstantInfo::DPrj(prj), s) } ,
      }
    }
⟧

def get_constant_info := aiur_fn⟦
  inline fn get_constant_info(flag: Field, size: UInt64::U64, stream: Bytes::Stream) -> (Ixon::ConstantInfo, Bytes::Stream) {
      match flag {

        12 => {
          let (mutuals, s) = get_mut_const_list(stream, size);
          (Ixon::ConstantInfo::Muts(mutuals), s) } ,

        13 => {
          let [_, sz1, sz2, sz3, sz4, sz5, sz6, sz7] = size;
          assert_eq!(((((((UInt8::to_field(sz1) + UInt8::to_field(sz2)) + UInt8::to_field(sz3))
                        + UInt8::to_field(sz4)) + UInt8::to_field(sz5)) + UInt8::to_field(sz6))
                        + UInt8::to_field(sz7)), 0,
            "constant info: TagN size exceeds a single byte");
          get_constant_info_by_variant(UInt8::to_field(size[0]), stream) } ,
      }
    }
⟧

  -- The binder-data section, the last field of a record:
  --
  --   section := nblocks:TagN0 block[nblocks]
  --   block   := ekind:u8 eidx:TagN0 variant:TagN0 nnodes:TagN0 node[nnodes]
  --   node    := 0x00 | 0x01 | 0x02 k:TagN0 p[k]:TagN0 | 0x03 v:TagN0 | 0x04
  --
  -- It is read in canonical form: `ekind` 0 (a root) or 1 (a sharing entry); a root block at
  -- variant 0; no empty block; blocks strictly ascending by `(ekind, eidx, variant)`; node tags
  -- 0 to 4; an `ifAllZero` parameter list (tag 2) nonempty, strictly ascending and below the
  -- record's level count (`max_lvls`, the largest of its members'); a projection's section
  -- empty. The undecided node (tag 4) is read; a conversion that reaches it rejects. Indices,
  -- variants, parameters and level counts are compared as fields by `UInt32::less_than_fields`,
  -- which refuses a value of 2^32 or more where it compares one.

def mut_const_lvls := aiur_fn⟦
  fn mut_const_lvls(m: Ixon::MutConst) -> Field {
      match m {
        Ixon::MutConst::Defn(d) => {
          let Ixon::Definition::Mk(_, _, lvls, _, _) = d;
          UInt64::to_field(lvls) } ,
        Ixon::MutConst::Indc(i) => {
          let Ixon::Inductive::Mk(_, lvls, _, _, _, _) = i;
          UInt64::to_field(lvls) } ,
        Ixon::MutConst::Recr(r) => {
          let Ixon::Recursor::Mk(_, _, lvls, _, _, _, _, _, _) = r;
          UInt64::to_field(lvls) } ,
      }
    }
⟧

def muts_max_lvls := aiur_fn⟦
  fn muts_max_lvls(members: Lists::List<Ixon::MutConst>, acc: Field) -> Field {
      match (*(members)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(m, rest) => {
          let lvls = mut_const_lvls(m);
          match UInt32::less_than_fields(acc, lvls) {
            1 => {  muts_max_lvls(rest, lvls) } ,
            0 => {  muts_max_lvls(rest, acc) } ,
          } } ,
      }
    }
⟧

def max_lvls := aiur_fn⟦
  fn max_lvls(info: Ixon::ConstantInfo) -> Field {
      match info {
        Ixon::ConstantInfo::Defn(d) => {
          let Ixon::Definition::Mk(_, _, lvls, _, _) = d;
          UInt64::to_field(lvls) } ,
        Ixon::ConstantInfo::Recr(r) => {
          let Ixon::Recursor::Mk(_, _, lvls, _, _, _, _, _, _) = r;
          UInt64::to_field(lvls) } ,
        Ixon::ConstantInfo::Axio(a) => {
          let Ixon::Axiom::Mk(_, lvls, _) = a;
          UInt64::to_field(lvls) } ,
        Ixon::ConstantInfo::Quot(q) => {
          let Ixon::Quotient::Mk(_, lvls, _) = q;
          UInt64::to_field(lvls) } ,
        Ixon::ConstantInfo::Muts(members) => {  muts_max_lvls(members, 0) } ,
        _ => {  0 } ,
      }
    }
⟧

def assert_params_canonical := aiur_fn⟦
  fn assert_params_canonical(params: Lists::List<UInt64::U64>, lvls: Field) -> () {
      match (*(params)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(p, rest) => {
          let pf = UInt64::to_field(p);
          assert_eq!(UInt32::less_than_fields(pf, lvls), 1,
            "binder data: a parameter is not below the level count");
          match (*(rest)) {
            Lists::Node::Nil => {  () } ,
            Lists::Node::Cons(q, _) => {
              assert_eq!(UInt32::less_than_fields(pf, UInt64::to_field(q)), 1,
                "binder data: parameters are not strictly ascending");
              assert_params_canonical(rest, lvls) } ,
          } } ,
      }
    }
⟧

def get_binder_node := aiur_fn⟦
  fn get_binder_node(stream: Bytes::Stream, lvls: Field) -> (Ixon::BinderNode, Bytes::Stream) {
      let (tag, s) = read_byte(stream);
      match UInt8::to_field(tag) {
        0 => {  (Ixon::BinderNode::Never, s) } ,
        1 => {  (Ixon::BinderNode::Zero, s) } ,
        2 => {
          let (count, s2) = get_tagn0(s);
          assert_eq!(UInt64::is_zero(count), 0, "binder data: an empty parameter list");
          let (params, s3) = get_u64_list(s2, count);
          assert_params_canonical(params, lvls);
          (Ixon::BinderNode::IfAllZero(params), s3) } ,
        3 => {
          let (variant, s2) = get_tagn0(s);
          (Ixon::BinderNode::Share(variant), s2) } ,
        4 => {  (Ixon::BinderNode::Undecided, s) } ,
      }
    }
⟧

def get_binder_node_list := aiur_fn⟦
  fn get_binder_node_list(stream: Bytes::Stream, count: UInt64::U64, lvls: Field)
      -> (Lists::List<Ixon::BinderNode>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (node, s) = get_binder_node(stream, lvls);
          let (rest, s2) = get_binder_node_list(s, UInt64::saturating_pred(count), lvls);
          ((&(Lists::Node::Cons(node, rest))), s2) } ,
      }
    }
⟧

def get_binder_block := aiur_fn⟦
  fn get_binder_block(stream: Bytes::Stream, lvls: Field) -> (Ixon::BinderBlock, Bytes::Stream) {
      let (ekind, s) = read_byte(stream);
      assert_wire_bool(ekind);
      let shared = UInt8::to_field(ekind);
      let (eidx, s2) = get_tagn0(s);
      let (variant, s3) = get_tagn0(s2);
      assert_eq!((1 - shared) * (1 - UInt64::is_zero(variant)), 0,
        "binder data: a root block at a variant other than 0");
      let (count, s4) = get_tagn0(s3);
      assert_eq!(UInt64::is_zero(count), 0, "binder data: an empty block");
      let (nodes, s5) = get_binder_node_list(s4, count, lvls);
      (Ixon::BinderBlock::Mk(shared, eidx, variant, nodes), s5)
    }
⟧

def get_binder_block_list := aiur_fn⟦
  fn get_binder_block_list(stream: Bytes::Stream, count: UInt64::U64, lvls: Field)
      -> (Lists::List<Ixon::BinderBlock>, Bytes::Stream) {
      let is_zero = UInt64::is_zero(count);
      match is_zero {
        1 => {  ((&(Lists::Node::Nil)), stream) } ,
        0 => {
          let (block, s) = get_binder_block(stream, lvls);
          let (rest, s2) = get_binder_block_list(s, UInt64::saturating_pred(count), lvls);
          ((&(Lists::Node::Cons(block, rest))), s2) } ,
      }
    }
⟧

  -- The strict `(ekind, eidx, variant)` order of blocks (a root before a sharing entry).

def binder_block_lt := aiur_fn⟦
  fn binder_block_lt(a: Ixon::BinderBlock, b: Ixon::BinderBlock) -> Field {
      let Ixon::BinderBlock::Mk(ea, ia, va, _) = a;
      let Ixon::BinderBlock::Mk(eb, ib, vb, _) = b;
      match ea - eb {
        0 => {
          let i = UInt64::to_field(ia);
          let j = UInt64::to_field(ib);
          match i - j {
            0 => {  UInt32::less_than_fields(UInt64::to_field(va), UInt64::to_field(vb)) } ,
            _ => {  UInt32::less_than_fields(i, j) } ,
          } } ,
        _ => {  eb } ,
      }
    }
⟧

def assert_blocks_ascending := aiur_fn⟦
  fn assert_blocks_ascending(blocks: Lists::List<Ixon::BinderBlock>) -> () {
      match (*(blocks)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(a, rest) => {
          match (*(rest)) {
            Lists::Node::Nil => {  () } ,
            Lists::Node::Cons(b, _) => {
              assert_eq!(binder_block_lt(a, b), 1, "binder data: blocks are not strictly ascending");
              assert_blocks_ascending(rest) } ,
          } } ,
      }
    }
⟧

def get_binders := aiur_fn⟦
  fn get_binders(stream: Bytes::Stream, lvls: Field) -> (Lists::List<Ixon::BinderBlock>, Bytes::Stream) {
      let (len, s) = get_tagn0(stream);
      let (blocks, s2) = get_binder_block_list(s, len, lvls);
      assert_blocks_ascending(blocks);
      (blocks, s2)
    }
⟧

def assert_prj_empty_tables := aiur_fn⟦
  fn assert_prj_empty_tables(
    info: Ixon::ConstantInfo,
    sharing: Lists::List<&Ixon::Expr>,
    refs: Lists::List<Bytes::AddressRef>,
    univs: Lists::List<&Ixon::Univ>,
    binders: Lists::List<Ixon::BinderBlock>
  ) -> () {
      match info {
        Ixon::ConstantInfo::DPrj(_) => {
          let Lists::Node::Nil = (*(sharing));
          let Lists::Node::Nil = (*(refs));
          let Lists::Node::Nil = (*(univs));
          let Lists::Node::Nil = (*(binders));
          () } ,
        Ixon::ConstantInfo::IPrj(_) => {
          let Lists::Node::Nil = (*(sharing));
          let Lists::Node::Nil = (*(refs));
          let Lists::Node::Nil = (*(univs));
          let Lists::Node::Nil = (*(binders));
          () } ,
        Ixon::ConstantInfo::CPrj(_) => {
          let Lists::Node::Nil = (*(sharing));
          let Lists::Node::Nil = (*(refs));
          let Lists::Node::Nil = (*(univs));
          let Lists::Node::Nil = (*(binders));
          () } ,
        Ixon::ConstantInfo::RPrj(_) => {
          let Lists::Node::Nil = (*(sharing));
          let Lists::Node::Nil = (*(refs));
          let Lists::Node::Nil = (*(univs));
          let Lists::Node::Nil = (*(binders));
          () } ,
        _ => {  () } ,
      }
    }
⟧

def get_constant := aiur_fn⟦
  fn get_constant(stream: Bytes::Stream) -> (Ixon::Constant, Bytes::Stream) {
      let (tag, s) = get_tagn4(stream);
      let (flag, size) = tag;
      let (info, s2) = get_constant_info(flag, size, s);
      let (sharing, s3) = get_sharing(s2);
      let (refs, s4) = get_refs(s3);
      let (univs, s5) = get_univs(s4);
      let (binders, s6) = get_binders(s5, max_lvls(info));
      assert_prj_empty_tables(info, sharing, refs, univs, binders);
      (Ixon::Constant::Mk(info, sharing, refs, univs, binders), s6)
    }
⟧

end

end IxVM
