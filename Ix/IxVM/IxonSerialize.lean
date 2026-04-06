module
public import Ix.Aiur.Meta

public section

namespace IxVM

def ixonSerialize := ⟦
  fn put_expr(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      -- Srt: Tag4(0x0, univ_idx)
      Expr.Srt(univ_idx) => put_tag4(0x0, univ_idx, rest),

      -- Var: Tag4(0x1, idx)
      Expr.Var(idx) => put_tag4(0x1, idx, rest),

      -- Ref: Tag4(0x2, len) + Tag0(ref_idx) + univ_list
      Expr.Ref(ref_idx, &univ_list) =>
        let len = list_length_u64(univ_list);
        put_tag4(0x2, len, put_tag0(ref_idx, put_u64_list(univ_list, rest))),

      -- Rec: Tag4(0x3, len) + Tag0(rec_idx) + univ_list
      Expr.Rec(rec_idx, &univ_list) =>
        let len = list_length_u64(univ_list);
        put_tag4(0x3, len, put_tag0(rec_idx, put_u64_list(univ_list, rest))),

      -- Prj: Tag4(0x4, field_idx) + Tag0(type_ref_idx) + put_expr(val)
      Expr.Prj(type_ref_idx, field_idx, &val) =>
        put_tag4(0x4, field_idx, put_tag0(type_ref_idx, put_expr(val, rest))),

      -- Str: Tag4(0x5, ref_idx)
      Expr.Str(ref_idx) => put_tag4(0x5, ref_idx, rest),

      -- Nat: Tag4(0x6, ref_idx)
      Expr.Nat(ref_idx) => put_tag4(0x6, ref_idx, rest),

      -- App: Tag4(0x7, count) + telescope
      Expr.App(_, _) =>
        let count = app_telescope_count(expr);
        put_tag4(0x7, count, put_app_telescope(expr, rest)),

      -- Lam: Tag4(0x8, count) + telescope
      Expr.Lam(_, _) =>
        let count = lam_telescope_count(expr);
        put_tag4(0x8, count, put_lam_telescope(expr, rest)),

      -- All: Tag4(0x9, count) + telescope
      Expr.All(_, _) =>
        let count = all_telescope_count(expr);
        put_tag4(0x9, count, put_all_telescope(expr, rest)),

      -- Let: Tag4(0xA, non_dep) + put_expr(ty) + put_expr(val) + put_expr(body)
      -- non_dep: 0 for dependent, 1 for non-dependent
      Expr.Let(non_dep, &ty, &val, &body) =>
        put_tag4(0xA, non_dep, put_expr(ty, put_expr(val, put_expr(body, rest)))),

      -- Share: Tag4(0xB, idx)
      Expr.Share(idx) => put_tag4(0xB, idx, rest),
    }
  }

  fn put_u64_le(bs: [G; 8], num_bytes: G, rest: ByteStream) -> ByteStream {
    match num_bytes {
      0 => rest,
      _ =>
        let [b1, b2, b3, b4, b5, b6, b7, b8] = bs;
        let rest_shifted = [b2, b3, b4, b5, b6, b7, b8, 0];
        List.Cons(b1, store(put_u64_le(rest_shifted, num_bytes - 1, rest))),
    }
  }

  fn put_tag0(bs: [G; 8], rest: ByteStream) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 128);
    match (byte_count, small) {
      (1, 1) => List.Cons(bs[0], store(rest)),
      _ =>
        let head = 128 + (byte_count - 1);
        List.Cons(head, store(put_u64_le(bs, byte_count, rest))),
    }
  }

  -- Tag2: 2-bit flag, variable size
  -- Format: [flag:2][large:1][size:5] or [flag:2][large:1][size_bytes...]
  fn put_tag2(flag: G, size: [G; 8], rest: ByteStream) -> ByteStream {
    let byte_count = u64_byte_count(size);
    let small = u8_less_than(size[0], 32);
    match (byte_count, small) {
      (1, 1) =>
        -- Single byte: flag in bits 6-7, size in bits 0-4
        let head = flag * 64 + size[0];
        List.Cons(head, store(rest)),
      _ =>
        -- Multi-byte: flag in bits 6-7, large=1 in bit 5, size_bytes-1 in bits 0-4
        let head = flag * 64 + 32 + (byte_count - 1);
        List.Cons(head, store(put_u64_le(size, byte_count, rest))),
    }
  }

  fn put_tag4(flag: G, bs: [G; 8], rest: ByteStream) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 8);
    match (byte_count, small) {
      (1, 1) =>
        let head = flag * 16 + bs[0];
        List.Cons(head, store(rest)),
      _ =>
        let head = flag * 16 + 8 + (byte_count - 1);
        List.Cons(head, store(put_u64_le(bs, byte_count, rest))),
    }
  }

  -- Serialize field list (each element as Tag0)
  fn put_u64_list(list: List‹U64›, rest: ByteStream) -> ByteStream {
    match list {
      List.Nil => rest,
      List.Cons(idx, rest_list) =>
        put_tag0(idx, put_u64_list(load(rest_list), rest)),
    }
  }

  -- Count nested App expressions
  fn app_telescope_count(expr: Expr) -> [G; 8] {
    match expr {
      Expr.App(&func, _) => relaxed_u64_succ(app_telescope_count(func)),
      _ => [0; 8],
    }
  }

  -- Count nested Lam expressions
  fn lam_telescope_count(expr: Expr) -> [G; 8] {
    match expr {
      Expr.Lam(_, &body) => relaxed_u64_succ(lam_telescope_count(body)),
      _ => [0; 8],
    }
  }

  -- Count nested All expressions
  fn all_telescope_count(expr: Expr) -> [G; 8] {
    match expr {
      Expr.All(_, &body) => relaxed_u64_succ(all_telescope_count(body)),
      _ => [0; 8],
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

  -- Serialize Lam telescope body (all types, then body)
  fn put_lam_telescope(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      Expr.Lam(&ty, &body) =>
        put_expr(ty, put_lam_telescope(body, rest)),
      _ => put_expr(expr, rest),
    }
  }

  -- Serialize All telescope body (all types, then body)
  fn put_all_telescope(expr: Expr, rest: ByteStream) -> ByteStream {
    match expr {
      Expr.All(&ty, &body) =>
        put_expr(ty, put_all_telescope(body, rest)),
      _ => put_expr(expr, rest),
    }
  }

  -- Write a 32-byte address
  fn put_address(a: [G; 32], rest: ByteStream) -> ByteStream {
    let list31 = List.Cons(a[31], store(rest));
    let list30 = List.Cons(a[30], store(list31));
    let list29 = List.Cons(a[29], store(list30));
    let list28 = List.Cons(a[28], store(list29));
    let list27 = List.Cons(a[27], store(list28));
    let list26 = List.Cons(a[26], store(list27));
    let list25 = List.Cons(a[25], store(list26));
    let list24 = List.Cons(a[24], store(list25));
    let list23 = List.Cons(a[23], store(list24));
    let list22 = List.Cons(a[22], store(list23));
    let list21 = List.Cons(a[21], store(list22));
    let list20 = List.Cons(a[20], store(list21));
    let list19 = List.Cons(a[19], store(list20));
    let list18 = List.Cons(a[18], store(list19));
    let list17 = List.Cons(a[17], store(list18));
    let list16 = List.Cons(a[16], store(list17));
    let list15 = List.Cons(a[15], store(list16));
    let list14 = List.Cons(a[14], store(list15));
    let list13 = List.Cons(a[13], store(list14));
    let list12 = List.Cons(a[12], store(list13));
    let list11 = List.Cons(a[11], store(list12));
    let list10 = List.Cons(a[10], store(list11));
    let list9 = List.Cons(a[9], store(list10));
    let list8 = List.Cons(a[8], store(list9));
    let list7 = List.Cons(a[7], store(list8));
    let list6 = List.Cons(a[6], store(list7));
    let list5 = List.Cons(a[5], store(list6));
    let list4 = List.Cons(a[4], store(list5));
    let list3 = List.Cons(a[3], store(list4));
    let list2 = List.Cons(a[2], store(list3));
    let list1 = List.Cons(a[1], store(list2));
    List.Cons(a[0], store(list1))
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
  fn univ_succ_count(u: Univ) -> [G; 8] {
    match u {
      Univ.Succ(&inner) => relaxed_u64_succ(univ_succ_count(inner)),
      _ => [0; 8],
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
        -- Tag2(FLAG_ZERO_SUCC=0, size=0)
        List.Cons(0, store(rest)),

      Univ.Succ(_) =>
        -- Count nested Succs for telescope compression
        let count = univ_succ_count(u);
        -- Find the base (non-Succ) universe
        let base = univ_succ_base(u);
        -- Tag2(FLAG_ZERO_SUCC=0, size=count) + base
        put_tag2(0, count, put_univ(base, rest)),

      Univ.Max(&a, &b) =>
        -- Tag2(FLAG_MAX=1, size=0)
        put_tag2(1, [0; 8], put_univ(a, put_univ(b, rest))),

      Univ.IMax(&a, &b) =>
        -- Tag2(FLAG_IMAX=2, size=0)
        put_tag2(2, [0; 8], put_univ(a, put_univ(b, rest))),

      Univ.Var(idx) =>
        -- Tag2(FLAG_VAR=3, size=idx)
        put_tag2(3, idx, rest),
    }
  }

  -- ============================================================================
  -- List serialization
  -- ============================================================================

  fn put_expr_list(list: List‹&Expr›, rest: ByteStream) -> ByteStream {
    match list {
      List.Nil => rest,
      List.Cons(&expr, &rest_list) =>
        put_expr(expr, put_expr_list(rest_list, rest)),
    }
  }

  fn put_univ_list(list: List‹&Univ›, rest: ByteStream) -> ByteStream {
    match list {
      List.Nil => rest,
      List.Cons(&u, &rest_list) =>
        put_univ(u, put_univ_list(rest_list, rest)),
    }
  }

  fn put_address_list(list: List‹[G; 32]›, rest: ByteStream) -> ByteStream {
    match list {
      List.Nil => rest,
      List.Cons(addr, &rest_list) =>
        put_address(addr, put_address_list(rest_list, rest)),
    }
  }

  -- ============================================================================
  -- Constant serialization
  -- ============================================================================

  fn put_quot_kind(kind: QuotKind, rest: ByteStream) -> ByteStream {
    match kind {
      QuotKind.Typ => List.Cons(0, store(rest)),
      QuotKind.Ctor => List.Cons(1, store(rest)),
      QuotKind.Lift => List.Cons(2, store(rest)),
      QuotKind.Ind => List.Cons(3, store(rest)),
    }
  }

  fn put_definition(defn: Definition, rest: ByteStream) -> ByteStream {
    match defn {
      Definition.Mk(kind, safety, lvls, &typ, &value) =>
        let packed = pack_def_kind_safety(kind, safety);
        List.Cons(packed, store(put_tag0(lvls, put_expr(typ, put_expr(value, rest))))),
    }
  }

  fn put_recursor_rule(rule: RecursorRule, rest: ByteStream) -> ByteStream {
    match rule {
      RecursorRule.Mk(fields, &rhs) =>
        put_tag0(fields, put_expr(rhs, rest)),
    }
  }

  fn put_recursor_rule_list(list: List‹RecursorRule›, rest: ByteStream) -> ByteStream {
    match list {
      List.Nil => rest,
      List.Cons(rule, &rest_list) =>
        put_recursor_rule(rule, put_recursor_rule_list(rest_list, rest)),
    }
  }

  fn put_recursor(recr: Recursor, rest: ByteStream) -> ByteStream {
    match recr {
      Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, &typ, &rules) =>
        let bools = k + 2 * is_unsafe;
        let rules_len = list_length_u64(rules);
        List.Cons(bools, store(
          put_tag0(lvls,
            put_tag0(params,
              put_tag0(indices,
                put_tag0(motives,
                  put_tag0(minors,
                    put_expr(typ,
                      put_tag0(rules_len,
                        put_recursor_rule_list(rules, rest)))))))))),
    }
  }

  fn put_axiom(axim: Axiom, rest: ByteStream) -> ByteStream {
    match axim {
      Axiom.Mk(is_unsafe, lvls, &typ) =>
        List.Cons(is_unsafe, store(put_tag0(lvls, put_expr(typ, rest)))),
    }
  }

  fn put_quotient(quot: Quotient, rest: ByteStream) -> ByteStream {
    match quot {
      Quotient.Mk(kind, lvls, &typ) =>
        put_quot_kind(kind, put_tag0(lvls, put_expr(typ, rest))),
    }
  }

  fn put_constructor(ctor: Constructor, rest: ByteStream) -> ByteStream {
    match ctor {
      Constructor.Mk(is_unsafe, lvls, cidx, params, fields, &typ) =>
        List.Cons(is_unsafe, store(
          put_tag0(lvls,
            put_tag0(cidx,
              put_tag0(params,
                put_tag0(fields,
                  put_expr(typ, rest))))))),
    }
  }

  fn put_constructor_list(list: List‹Constructor›, rest: ByteStream) -> ByteStream {
    match list {
      List.Nil => rest,
      List.Cons(ctor, &rest_list) =>
        put_constructor(ctor, put_constructor_list(rest_list, rest)),
    }
  }

  fn put_inductive(indc: Inductive, rest: ByteStream) -> ByteStream {
    match indc {
      Inductive.Mk(recr, refl, is_unsafe, lvls, params, indices, nested, &typ, &ctors) =>
        let bools = recr + 2 * refl + 4 * is_unsafe;
        let ctors_len = list_length_u64(ctors);
        List.Cons(bools, store(
          put_tag0(lvls,
            put_tag0(params,
              put_tag0(indices,
                put_tag0(nested,
                  put_expr(typ,
                    put_tag0(ctors_len,
                      put_constructor_list(ctors, rest))))))))),
    }
  }

  fn put_inductive_proj(prj: InductiveProj, rest: ByteStream) -> ByteStream {
    match prj {
      InductiveProj.Mk(idx, block) =>
        put_tag0(idx, put_address(block, rest)),
    }
  }

  fn put_constructor_proj(prj: ConstructorProj, rest: ByteStream) -> ByteStream {
    match prj {
      ConstructorProj.Mk(idx, cidx, block) =>
        put_tag0(idx, put_tag0(cidx, put_address(block, rest))),
    }
  }

  fn put_recursor_proj(prj: RecursorProj, rest: ByteStream) -> ByteStream {
    match prj {
      RecursorProj.Mk(idx, block) =>
        put_tag0(idx, put_address(block, rest)),
    }
  }

  fn put_definition_proj(prj: DefinitionProj, rest: ByteStream) -> ByteStream {
    match prj {
      DefinitionProj.Mk(idx, block) =>
        put_tag0(idx, put_address(block, rest)),
    }
  }

  fn put_mut_const(mc: MutConst, rest: ByteStream) -> ByteStream {
    match mc {
      MutConst.Defn(defn) =>
        List.Cons(0, store(put_definition(defn, rest))),
      MutConst.Indc(indc) =>
        List.Cons(1, store(put_inductive(indc, rest))),
      MutConst.Recr(recr) =>
        List.Cons(2, store(put_recursor(recr, rest))),
    }
  }

  fn put_mut_const_list(list: List‹MutConst›, rest: ByteStream) -> ByteStream {
    match list {
      List.Nil => rest,
      List.Cons(mc, &rest_list) =>
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
    put_tag0(len, put_expr_list(list, rest))
  }

  fn put_refs(list: List‹[G; 32]›, rest: ByteStream) -> ByteStream {
    let len = list_length_u64(list);
    put_tag0(len, put_address_list(list, rest))
  }

  fn put_univs(list: List‹&Univ›, rest: ByteStream) -> ByteStream {
    let len = list_length_u64(list);
    put_tag0(len, put_univ_list(list, rest))
  }

  fn put_constant(cnst: Constant, rest: ByteStream) -> ByteStream {
    match cnst {
      Constant.Mk(info, &sharing, &refs, &univs) =>
        let up_to_sharing = put_sharing(sharing, put_refs(refs, put_univs(univs, rest)));
        match info {
          ConstantInfo.Muts(&mutuals) =>
            -- Use FLAG_MUTS (0xC) with entry count in size field
            let count = list_length_u64(mutuals);
            put_tag4(0xC, count, put_mut_const_list(mutuals, up_to_sharing)),
          -- Use FLAG (0xD) with variant in size field
          ConstantInfo.Defn(_) =>
            put_tag4(0xD, [0; 8], put_constant_info(info, up_to_sharing)),
          ConstantInfo.Recr(_) =>
            put_tag4(0xD, [1, 0, 0, 0, 0, 0, 0, 0], put_constant_info(info, up_to_sharing)),
          ConstantInfo.Axio(_) =>
            put_tag4(0xD, [2, 0, 0, 0, 0, 0, 0, 0], put_constant_info(info, up_to_sharing)),
          ConstantInfo.Quot(_) =>
            put_tag4(0xD, [3, 0, 0, 0, 0, 0, 0, 0], put_constant_info(info, up_to_sharing)),
          ConstantInfo.CPrj(_) =>
            put_tag4(0xD, [4, 0, 0, 0, 0, 0, 0, 0], put_constant_info(info, up_to_sharing)),
          ConstantInfo.RPrj(_) =>
            put_tag4(0xD, [5, 0, 0, 0, 0, 0, 0, 0], put_constant_info(info, up_to_sharing)),
          ConstantInfo.IPrj(_) =>
            put_tag4(0xD, [6, 0, 0, 0, 0, 0, 0, 0], put_constant_info(info, up_to_sharing)),
          ConstantInfo.DPrj(_) =>
            put_tag4(0xD, [7, 0, 0, 0, 0, 0, 0, 0], put_constant_info(info, up_to_sharing)),
        },
    }
  }
⟧

end IxVM

end
