module
public import Ix.Aiur.Meta

public section

namespace IxVM

def ixonSerialize := ⟦
  fn put_expr(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      -- Srt: TagN4(0x0, univ_idx)
      Expr.Srt(univ_idx) => put_tagn4(0x0, univ_idx, rest),

      -- Var: TagN4(0x1, idx)
      Expr.Var(idx) => put_tagn4(0x1, idx, rest),

      -- Ref: TagN4(0x2, len) + TagN0(ref_idx) + univ_list
      Expr.Ref(ref_idx, univ_list) =>
        let len = list_length_u64(univ_list);
        put_tagn4(0x2, len, put_tagn0(ref_idx, put_u64_list(univ_list, rest))),

      -- Rec: TagN4(0x3, len) + TagN0(rec_idx) + univ_list
      Expr.Rec(rec_idx, univ_list) =>
        let len = list_length_u64(univ_list);
        put_tagn4(0x3, len, put_tagn0(rec_idx, put_u64_list(univ_list, rest))),

      -- Prj: TagN4(0x4, field_idx) + TagN0(type_ref_idx) + put_expr(val)
      Expr.Prj(type_ref_idx, field_idx, &val) =>
        put_tagn4(0x4, field_idx, put_tagn0(type_ref_idx, put_expr(val, rest))),

      -- Str: TagN4(0x5, ref_idx)
      Expr.Str(ref_idx) => put_tagn4(0x5, ref_idx, rest),

      -- Nat: TagN4(0x6, ref_idx)
      Expr.Nat(ref_idx) => put_tagn4(0x6, ref_idx, rest),

      -- App: TagN4(0x7, count) + telescope
      Expr.App(_, _) =>
        let count = app_telescope_count(expr);
        put_tagn4(0x7, count, put_app_telescope(expr, rest)),

      -- Lam: TagN4(0x8, count) + telescope
      Expr.Lam(_, _, _) =>
        let count = lam_telescope_count(expr);
        put_tagn4(0x8, count, put_lam_telescope(expr, rest)),

      -- All: TagN4(0x9, count) + telescope
      Expr.All(_, _, _, _) =>
        let count = all_telescope_count(expr);
        put_tagn4(0x9, count, put_all_telescope(expr, rest)),

      -- Let: flags in the TagN4 value, then the binder byte and three children.
      Expr.Let(LetContract.Mk(non_dep, kind, contract), &ty, &val, &body) =>
        let kind_bit = match kind { LetKind.Value => 0, LetKind.BorrowShared => 1, };
        let flags = [u8_from_field_unsafe(non_dep + 2 * kind_bit), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        put_tagn4(0xA, flags, put_lam_mode(contract,
          put_expr(ty, put_expr(val, put_expr(body, rest))))),

      -- Share: TagN4(0xB, idx)
      Expr.Share(idx) => put_tagn4(0xB, idx, rest),
    }
  }

  fn put_u64_le(bs: U64, num_bytes: G, rest: ByteStream) -> ByteStream {
    match num_bytes {
      0 => rest,
      _ =>
        let [b1, b2, b3, b4, b5, b6, b7, b8] = bs;
        let rest_shifted = [b2, b3, b4, b5, b6, b7, b8, 0u8];
        store(ListNode.Cons(b1, put_u64_le(rest_shifted, num_bytes - 1, rest))),
    }
  }

  -- ============================================================================
  -- TagN integers (`Ixon.putTagN`; layout in IxonDeserialize.lean)
  -- ============================================================================

  -- Rung 1 (value < R1 = 2h) is the header byte alone; every larger value
  -- goes through `put_tagn_tail`. `base` is the flag in the header's high
  -- bits. The values written here are range-checked bytes (decoded fields,
  -- list lengths), so the sum of the high seven is zero only when each is.

  -- TagN, f = 4.
  fn put_tagn4(flag: G, v: U64, rest: ByteStream) -> ByteStream {
    let [v0, v1, v2, v3, v4, v5, v6, v7] = v;
    match to_field(v1) + to_field(v2) + to_field(v3) + to_field(v4)
        + to_field(v5) + to_field(v6) + to_field(v7) {
      0 =>
        match u8_less_than(v0, 8u8) {
          1 => store(ListNode.Cons(u8_from_field_unsafe(16 * flag + to_field(v0)), rest)),
          0 => put_tagn_tail(16 * flag, 4, v, rest),
        },
      _ => put_tagn_tail(16 * flag, 4, v, rest),
    }
  }

  -- TagN, f = 2.
  fn put_tagn2(flag: G, v: U64, rest: ByteStream) -> ByteStream {
    let [v0, v1, v2, v3, v4, v5, v6, v7] = v;
    match to_field(v1) + to_field(v2) + to_field(v3) + to_field(v4)
        + to_field(v5) + to_field(v6) + to_field(v7) {
      0 =>
        match u8_less_than(v0, 32u8) {
          1 => store(ListNode.Cons(u8_from_field_unsafe(64 * flag + to_field(v0)), rest)),
          0 => put_tagn_tail(64 * flag, 16, v, rest),
        },
      _ => put_tagn_tail(64 * flag, 16, v, rest),
    }
  }

  -- TagN, f = 0.
  fn put_tagn0(v: U64, rest: ByteStream) -> ByteStream {
    let [v0, v1, v2, v3, v4, v5, v6, v7] = v;
    match to_field(v1) + to_field(v2) + to_field(v3) + to_field(v4)
        + to_field(v5) + to_field(v6) + to_field(v7) {
      0 =>
        match u8_less_than(v0, 128u8) {
          1 => store(ListNode.Cons(v0, rest)),
          0 => put_tagn_tail(0, 64, v, rest),
        },
      _ => put_tagn_tail(0, 64, v, rest),
    }
  }

  -- Rungs 2 to 6 of `v >= R1 = 2h`. Subtracting R2 = [2h, h] is adding its
  -- two's complement; the carry is set exactly when v >= R2.
  fn put_tagn_tail(base: G, h: G, v: U64, rest: ByteStream) -> ByteStream {
    let (d, at_least_r2) = u64_add(v, [u8_from_field_unsafe(256 - 2 * h),
      u8_from_field_unsafe(255 - h), 255u8, 255u8, 255u8, 255u8, 255u8, 255u8]);
    match to_field(at_least_r2) {
      -- Rung 2: v - R1 = 256 hi + lo with hi < h, and v < R2 < 2^16.
      0 =>
        let (lo, no_borrow) = u8_add(v[0], u8_from_field_unsafe(256 - 2 * h));
        let hi = to_field(v[1]) + to_field(no_borrow) - 1;
        store(ListNode.Cons(u8_from_field_unsafe(base + 2 * h + hi),
          store(ListNode.Cons(lo, rest)))),
      1 => put_tagn_wide(base + 3 * h, 0, d, rest),
    }
  }

  -- Rungs 3 to 6: `d = v - R(c + 2)`. Code c (0, 1, 2) holds d below 2^16,
  -- 2^24, 2^32 in 2, 3, 4 bytes; otherwise d moves to the next rung, whose
  -- start is 2^16, 2^24, 2^32 further. Code 3 holds the rest in 8 bytes.
  fn put_tagn_wide(header: G, c: G, d: U64, rest: ByteStream) -> ByteStream {
    let [_, _, d2, d3, d4, d5, d6, d7] = d;
    match c {
      0 =>
        match to_field(d2) + to_field(d3) + to_field(d4) + to_field(d5)
            + to_field(d6) + to_field(d7) {
          0 => store(ListNode.Cons(u8_from_field_unsafe(header), put_u64_le(d, 2, rest))),
          _ =>
            let (next, _) = u64_add(d, [0u8, 0u8, 255u8, 255u8, 255u8, 255u8, 255u8, 255u8]);
            put_tagn_wide(header, 1, next, rest),
        },
      1 =>
        match to_field(d3) + to_field(d4) + to_field(d5) + to_field(d6) + to_field(d7) {
          0 => store(ListNode.Cons(u8_from_field_unsafe(header + 1), put_u64_le(d, 3, rest))),
          _ =>
            let (next, _) = u64_add(d, [0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8, 255u8]);
            put_tagn_wide(header, 2, next, rest),
        },
      2 =>
        match to_field(d4) + to_field(d5) + to_field(d6) + to_field(d7) {
          0 => store(ListNode.Cons(u8_from_field_unsafe(header + 2), put_u64_le(d, 4, rest))),
          _ =>
            let (next, _) = u64_add(d, [0u8, 0u8, 0u8, 0u8, 255u8, 255u8, 255u8, 255u8]);
            put_tagn_wide(header, 3, next, rest),
        },
      3 => store(ListNode.Cons(u8_from_field_unsafe(header + 3), put_u64_le(d, 8, rest))),
    }
  }

  -- Serialize field list (each element as TagN0)
  fn put_u64_list(list: List‹U64›, rest: ByteStream) -> ByteStream {
    match load(list) {
      ListNode.Nil => rest,
      ListNode.Cons(idx, rest_list) =>
        put_tagn0(idx, put_u64_list(rest_list, rest)),
    }
  }

  -- Two-bit value contract: ownership and locality.
  fn value_contract_code(value: ValueContract) -> G {
    let ValueContract.Mk(owned, locality) = value;
    let o = match owned { Owned.Unique => 0, Owned.Shared => 1, };
    let l = match locality { Locality.Unrestricted => 0, Locality.Local => 1, };
    o + 2 * l
  }

  -- Four-bit binder contract: usage and value contract.
  fn binder_contract_code(contract: BinderContract) -> G {
    let BinderContract.Mk(uses, value) = contract;
    let u = match uses { Uses.Erased => 0, Uses.Linear => 1, Uses.Affine => 2, Uses.Many => 3, };
    u + 4 * value_contract_code(value)
  }

  fn put_lam_mode(contract: BinderContract, rest: ByteStream) -> ByteStream {
    store(ListNode.Cons(u8_from_field_unsafe(binder_contract_code(contract)), rest))
  }

  -- Four input bits and two result bits.
  fn put_all_mode(contract: BinderContract, result: ValueContract, rest: ByteStream) -> ByteStream {
    let code = binder_contract_code(contract) + 16 * value_contract_code(result);
    store(ListNode.Cons(u8_from_field_unsafe(code), rest))
  }

  -- Count nested App expressions
  fn app_telescope_count(expr: Expr) -> U64 {
    match expr {
      Expr.App(&func, _) => relaxed_u64_succ(app_telescope_count(func)),
      _ => [0u8; 8],
    }
  }

  -- Count nested Lam expressions
  fn lam_telescope_count(expr: Expr) -> U64 {
    match expr {
      Expr.Lam(_, _, &body) => relaxed_u64_succ(lam_telescope_count(body)),
      _ => [0u8; 8],
    }
  }

  -- Count nested All expressions
  fn all_telescope_count(expr: Expr) -> U64 {
    match expr {
      Expr.All(_, _, _, &body) => relaxed_u64_succ(all_telescope_count(body)),
      _ => [0u8; 8],
    }
  }

  -- Serialize App telescope body (function, then all args in order)
  fn put_app_telescope(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      Expr.App(&func, &arg) =>
        put_app_telescope(func, put_expr(arg, rest)),
      _ => put_expr(expr, rest),
    }
  }

  -- Serialize Lam telescope body (contract/type pairs, then body)
  fn put_lam_telescope(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      Expr.Lam(contract, &ty, &body) =>
        put_lam_mode(contract, put_expr(ty, put_lam_telescope(body, rest))),
      _ => put_expr(expr, rest),
    }
  }

  -- Serialize All telescope body (input/result contracts and types, then body)
  fn put_all_telescope(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      Expr.All(input, result, &ty, &body) =>
        put_all_mode(input, result, put_expr(ty, put_all_telescope(body, rest))),
      _ => put_expr(expr, rest),
    }
  }

  -- Write a 32-byte address
  fn put_address(a: Addr, rest: ByteStream) -> ByteStream {
    let arr = load(a);
    let list31 = store(ListNode.Cons(arr[31], rest));
    let list30 = store(ListNode.Cons(arr[30], list31));
    let list29 = store(ListNode.Cons(arr[29], list30));
    let list28 = store(ListNode.Cons(arr[28], list29));
    let list27 = store(ListNode.Cons(arr[27], list28));
    let list26 = store(ListNode.Cons(arr[26], list27));
    let list25 = store(ListNode.Cons(arr[25], list26));
    let list24 = store(ListNode.Cons(arr[24], list25));
    let list23 = store(ListNode.Cons(arr[23], list24));
    let list22 = store(ListNode.Cons(arr[22], list23));
    let list21 = store(ListNode.Cons(arr[21], list22));
    let list20 = store(ListNode.Cons(arr[20], list21));
    let list19 = store(ListNode.Cons(arr[19], list20));
    let list18 = store(ListNode.Cons(arr[18], list19));
    let list17 = store(ListNode.Cons(arr[17], list18));
    let list16 = store(ListNode.Cons(arr[16], list17));
    let list15 = store(ListNode.Cons(arr[15], list16));
    let list14 = store(ListNode.Cons(arr[14], list15));
    let list13 = store(ListNode.Cons(arr[13], list14));
    let list12 = store(ListNode.Cons(arr[12], list13));
    let list11 = store(ListNode.Cons(arr[11], list12));
    let list10 = store(ListNode.Cons(arr[10], list11));
    let list9 = store(ListNode.Cons(arr[9], list10));
    let list8 = store(ListNode.Cons(arr[8], list9));
    let list7 = store(ListNode.Cons(arr[7], list8));
    let list6 = store(ListNode.Cons(arr[6], list7));
    let list5 = store(ListNode.Cons(arr[5], list6));
    let list4 = store(ListNode.Cons(arr[4], list5));
    let list3 = store(ListNode.Cons(arr[3], list4));
    let list2 = store(ListNode.Cons(arr[2], list3));
    let list1 = store(ListNode.Cons(arr[1], list2));
    store(ListNode.Cons(arr[0], list1))
  }

  -- Pack DefKind (2 bits) and DefinitionSafety (2 bits) into a single byte
  fn pack_def_kind_safety(kind: DefKind, safety: DefinitionSafety) -> G {
    match (kind, safety) {
      (DefKind.Definition, DefinitionSafety.Unsafe) => 0,
      (DefKind.Definition, DefinitionSafety.Safe) => 1,
      (DefKind.Definition, DefinitionSafety.Partial) => 2,
      (DefKind.Opaque, DefinitionSafety.Unsafe) => 4,
      (DefKind.Opaque, DefinitionSafety.Safe) => 5,
      (DefKind.Opaque, DefinitionSafety.Partial) => 6,
      (DefKind.Theorem, DefinitionSafety.Unsafe) => 8,
      (DefKind.Theorem, DefinitionSafety.Safe) => 9,
      (DefKind.Theorem, DefinitionSafety.Partial) => 10,
    }
  }

  -- ============================================================================
  -- Universe serialization
  -- ============================================================================

  -- Count nested Succ universes for telescope compression
  fn univ_succ_count(u: Univ) -> U64 {
    match u {
      Univ.Succ(&inner) => relaxed_u64_succ(univ_succ_count(inner)),
      _ => [0u8; 8],
    }
  }

  -- Get the base (non-Succ) universe
  fn univ_succ_base(u: Univ) -> Univ {
    match u {
      Univ.Succ(&inner) => univ_succ_base(inner),
      _ => u,
    }
  }

  fn put_univ(u: Univ, rest: ByteStream) -> ByteStream {
    match u {
      Univ.Zero =>
        -- TagN2(FLAG_ZERO_SUCC=0, size=0)
        store(ListNode.Cons(0u8, rest)),

      Univ.Succ(_) =>
        -- Count nested Succs for telescope compression
        let count = univ_succ_count(u);
        -- Find the base (non-Succ) universe
        let base = univ_succ_base(u);
        -- TagN2(FLAG_ZERO_SUCC=0, size=count) + base
        put_tagn2(0, count, put_univ(base, rest)),

      Univ.Max(&a, &b) =>
        -- TagN2(FLAG_MAX=1, size=0)
        put_tagn2(1, [0u8; 8], put_univ(a, put_univ(b, rest))),

      Univ.IMax(&a, &b) =>
        -- TagN2(FLAG_IMAX=2, size=0)
        put_tagn2(2, [0u8; 8], put_univ(a, put_univ(b, rest))),

      Univ.Var(idx) =>
        -- TagN2(FLAG_VAR=3, size=idx)
        put_tagn2(3, idx, rest),
    }
  }

  -- ============================================================================
  -- List serialization
  -- ============================================================================

  fn put_expr_list(list: List‹&Expr›, rest: ByteStream) -> ByteStream {
    match load(list) {
      ListNode.Nil => rest,
      ListNode.Cons(&expr, rest_list) =>
        put_expr(expr, put_expr_list(rest_list, rest)),
    }
  }

  fn put_univ_list(list: List‹&Univ›, rest: ByteStream) -> ByteStream {
    match load(list) {
      ListNode.Nil => rest,
      ListNode.Cons(&u, rest_list) =>
        put_univ(u, put_univ_list(rest_list, rest)),
    }
  }

  fn put_address_list(list: List‹Addr›, rest: ByteStream) -> ByteStream {
    match load(list) {
      ListNode.Nil => rest,
      ListNode.Cons(addr, rest_list) =>
        put_address(addr, put_address_list(rest_list, rest)),
    }
  }

  -- ============================================================================
  -- Constant serialization
  -- ============================================================================

  fn put_quot_kind(kind: QuotKind, rest: ByteStream) -> ByteStream {
    match kind {
      QuotKind.Typ => store(ListNode.Cons(0u8, rest)),
      QuotKind.Ctor => store(ListNode.Cons(1u8, rest)),
      QuotKind.Lift => store(ListNode.Cons(2u8, rest)),
      QuotKind.Ind => store(ListNode.Cons(3u8, rest)),
    }
  }

  fn put_definition(defn: Definition, rest: ByteStream) -> ByteStream {
    match defn {
      Definition.Mk(kind, safety, lvls, &typ, &value) =>
        let packed = pack_def_kind_safety(kind, safety);
        store(ListNode.Cons(u8_from_field_unsafe(packed), put_tagn0(lvls, put_expr(typ, put_expr(value, rest))))),
    }
  }

  fn put_recursor_rule(rule: RecursorRule, rest: ByteStream) -> ByteStream {
    match rule {
      RecursorRule.Mk(fields, &rhs) =>
        put_tagn0(fields, put_expr(rhs, rest)),
    }
  }

  fn put_recursor_rule_list(list: List‹RecursorRule›, rest: ByteStream) -> ByteStream {
    match load(list) {
      ListNode.Nil => rest,
      ListNode.Cons(rule, rest_list) =>
        put_recursor_rule(rule, put_recursor_rule_list(rest_list, rest)),
    }
  }

  fn put_recursor(recr: Recursor, rest: ByteStream) -> ByteStream {
    match recr {
      Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, &typ, rules) =>
        let bools = k + 2 * is_unsafe;
        let rules_len = list_length_u64(rules);
        store(ListNode.Cons(u8_from_field_unsafe(bools),
          put_tagn0(lvls,
            put_tagn0(params,
              put_tagn0(indices,
                put_tagn0(motives,
                  put_tagn0(minors,
                    put_expr(typ,
                      put_tagn0(rules_len,
                        put_recursor_rule_list(rules, rest)))))))))),
    }
  }

  fn put_axiom(axim: Axiom, rest: ByteStream) -> ByteStream {
    match axim {
      Axiom.Mk(is_unsafe, lvls, &typ) =>
        store(ListNode.Cons(u8_from_field_unsafe(is_unsafe), put_tagn0(lvls, put_expr(typ, rest)))),
    }
  }

  fn put_quotient(quot: Quotient, rest: ByteStream) -> ByteStream {
    match quot {
      Quotient.Mk(kind, lvls, &typ) =>
        put_quot_kind(kind, put_tagn0(lvls, put_expr(typ, rest))),
    }
  }

  fn put_constructor(ctor: Constructor, rest: ByteStream) -> ByteStream {
    match ctor {
      Constructor.Mk(is_unsafe, lvls, cidx, params, fields, &typ) =>
        store(ListNode.Cons(u8_from_field_unsafe(is_unsafe),
          put_tagn0(lvls,
            put_tagn0(cidx,
              put_tagn0(params,
                put_tagn0(fields,
                  put_expr(typ, rest))))))),
    }
  }

  fn put_constructor_list(list: List‹Constructor›, rest: ByteStream) -> ByteStream {
    match load(list) {
      ListNode.Nil => rest,
      ListNode.Cons(ctor, rest_list) =>
        put_constructor(ctor, put_constructor_list(rest_list, rest)),
    }
  }

  fn put_inductive(indc: Inductive, rest: ByteStream) -> ByteStream {
    match indc {
      Inductive.Mk(is_unsafe, lvls, params, indices, &typ, ctors) =>
        let ctors_len = list_length_u64(ctors);
        store(ListNode.Cons(u8_from_field_unsafe(is_unsafe),
          put_tagn0(lvls,
            put_tagn0(params,
              put_tagn0(indices,
                put_expr(typ,
                  put_tagn0(ctors_len,
                    put_constructor_list(ctors, rest)))))))),
    }
  }

  fn put_inductive_proj(prj: InductiveProj, rest: ByteStream) -> ByteStream {
    match prj {
      InductiveProj.Mk(idx, block) =>
        put_tagn0(idx, put_address(block, rest)),
    }
  }

  fn put_constructor_proj(prj: ConstructorProj, rest: ByteStream) -> ByteStream {
    match prj {
      ConstructorProj.Mk(idx, cidx, block) =>
        put_tagn0(idx, put_tagn0(cidx, put_address(block, rest))),
    }
  }

  fn put_recursor_proj(prj: RecursorProj, rest: ByteStream) -> ByteStream {
    match prj {
      RecursorProj.Mk(idx, block) =>
        put_tagn0(idx, put_address(block, rest)),
    }
  }

  fn put_definition_proj(prj: DefinitionProj, rest: ByteStream) -> ByteStream {
    match prj {
      DefinitionProj.Mk(idx, block) =>
        put_tagn0(idx, put_address(block, rest)),
    }
  }

  fn put_mut_const(mc: MutConst, rest: ByteStream) -> ByteStream {
    match mc {
      MutConst.Defn(defn) =>
        store(ListNode.Cons(0u8, put_definition(defn, rest))),
      MutConst.Indc(indc) =>
        store(ListNode.Cons(1u8, put_inductive(indc, rest))),
      MutConst.Recr(recr) =>
        store(ListNode.Cons(2u8, put_recursor(recr, rest))),
    }
  }

  fn put_mut_const_list(list: List‹MutConst›, rest: ByteStream) -> ByteStream {
    match load(list) {
      ListNode.Nil => rest,
      ListNode.Cons(mc, rest_list) =>
        put_mut_const(mc, put_mut_const_list(rest_list, rest)),
    }
  }

  fn put_constant_info(info: ConstantInfo, rest: ByteStream) -> ByteStream {
    match info {
      ConstantInfo.Defn(defn) => put_definition(defn, rest),
      ConstantInfo.Recr(recr) => put_recursor(recr, rest),
      ConstantInfo.Axio(axim) => put_axiom(axim, rest),
      ConstantInfo.Quot(quot) => put_quotient(quot, rest),
      ConstantInfo.CPrj(prj) => put_constructor_proj(prj, rest),
      ConstantInfo.RPrj(prj) => put_recursor_proj(prj, rest),
      ConstantInfo.IPrj(prj) => put_inductive_proj(prj, rest),
      ConstantInfo.DPrj(prj) => put_definition_proj(prj, rest),
    }
  }

  fn put_sharing(list: List‹&Expr›, rest: ByteStream) -> ByteStream {
    let len = list_length_u64(list);
    put_tagn0(len, put_expr_list(list, rest))
  }

  fn put_refs(list: List‹Addr›, rest: ByteStream) -> ByteStream {
    let len = list_length_u64(list);
    put_tagn0(len, put_address_list(list, rest))
  }

  fn put_univs(list: List‹&Univ›, rest: ByteStream) -> ByteStream {
    let len = list_length_u64(list);
    put_tagn0(len, put_univ_list(list, rest))
  }

  fn put_constant(cnst: Constant, rest: ByteStream) -> ByteStream {
    match cnst {
      Constant.Mk(info, sharing, refs, univs) =>
        let up_to_sharing = put_sharing(sharing, put_refs(refs, put_univs(univs, rest)));
        match info {
          ConstantInfo.Muts(mutuals) =>
            -- Use FLAG_MUTS (0xC) with the entry count as the TagN value
            let count = list_length_u64(mutuals);
            put_tagn4(0xC, count, put_mut_const_list(mutuals, up_to_sharing)),
          -- Use FLAG (0xD) with the variant as the TagN value
          ConstantInfo.Defn(_) =>
            put_tagn4(0xD, [0u8; 8], put_constant_info(info, up_to_sharing)),
          ConstantInfo.Recr(_) =>
            put_tagn4(0xD, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], put_constant_info(info, up_to_sharing)),
          ConstantInfo.Axio(_) =>
            put_tagn4(0xD, [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], put_constant_info(info, up_to_sharing)),
          ConstantInfo.Quot(_) =>
            put_tagn4(0xD, [3u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], put_constant_info(info, up_to_sharing)),
          ConstantInfo.CPrj(_) =>
            put_tagn4(0xD, [4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], put_constant_info(info, up_to_sharing)),
          ConstantInfo.RPrj(_) =>
            put_tagn4(0xD, [5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], put_constant_info(info, up_to_sharing)),
          ConstantInfo.IPrj(_) =>
            put_tagn4(0xD, [6u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], put_constant_info(info, up_to_sharing)),
          ConstantInfo.DPrj(_) =>
            put_tagn4(0xD, [7u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], put_constant_info(info, up_to_sharing)),
        },
    }
  }
⟧

end IxVM

end
