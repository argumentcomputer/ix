import Ix.Aiur.Meta

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
        let len = u64_list_length(univ_list);
        put_tag4(0x2, len, put_tag0(ref_idx, put_u64_list(univ_list, rest))),

      -- Rec: Tag4(0x3, len) + Tag0(rec_idx) + univ_list
      Expr.Rec(rec_idx, &univ_list) =>
        let len = u64_list_length(univ_list);
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
        ByteStream.Cons(b1, store(put_u64_le(rest_shifted, num_bytes - 1, rest))),
    }
  }

  fn put_tag0(bs: [G; 8], rest: ByteStream) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 128);
    match (byte_count, small) {
      (1, 1) => ByteStream.Cons(bs[0], store(rest)),
      _ =>
        let head = 128 + (byte_count - 1);
        ByteStream.Cons(head, store(put_u64_le(bs, byte_count, rest))),
    }
  }

  fn put_tag4(flag: G, bs: [G; 8], rest: ByteStream) -> ByteStream {
    let byte_count = u64_byte_count(bs);
    let small = u8_less_than(bs[0], 8);
    match (byte_count, small) {
      (1, 1) =>
        let head = flag * 16 + bs[0];
        ByteStream.Cons(head, store(rest)),
      _ =>
        let head = flag * 16 + 8 + (byte_count - 1);
        ByteStream.Cons(head, store(put_u64_le(bs, byte_count, rest))),
    }
  }

  -- Serialize field list (each element as Tag0)
  fn put_u64_list(list: U64List, rest: ByteStream) -> ByteStream {
    match list {
      U64List.Nil => rest,
      U64List.Cons(idx, rest_list) =>
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
    let list31 = ByteStream.Cons(a[31], store(rest));
    let list30 = ByteStream.Cons(a[30], store(list31));
    let list29 = ByteStream.Cons(a[29], store(list30));
    let list28 = ByteStream.Cons(a[28], store(list29));
    let list27 = ByteStream.Cons(a[27], store(list28));
    let list26 = ByteStream.Cons(a[26], store(list27));
    let list25 = ByteStream.Cons(a[25], store(list26));
    let list24 = ByteStream.Cons(a[24], store(list25));
    let list23 = ByteStream.Cons(a[23], store(list24));
    let list22 = ByteStream.Cons(a[22], store(list23));
    let list21 = ByteStream.Cons(a[21], store(list22));
    let list20 = ByteStream.Cons(a[20], store(list21));
    let list19 = ByteStream.Cons(a[19], store(list20));
    let list18 = ByteStream.Cons(a[18], store(list19));
    let list17 = ByteStream.Cons(a[17], store(list18));
    let list16 = ByteStream.Cons(a[16], store(list17));
    let list15 = ByteStream.Cons(a[15], store(list16));
    let list14 = ByteStream.Cons(a[14], store(list15));
    let list13 = ByteStream.Cons(a[13], store(list14));
    let list12 = ByteStream.Cons(a[12], store(list13));
    let list11 = ByteStream.Cons(a[11], store(list12));
    let list10 = ByteStream.Cons(a[10], store(list11));
    let list9 = ByteStream.Cons(a[9], store(list10));
    let list8 = ByteStream.Cons(a[8], store(list9));
    let list7 = ByteStream.Cons(a[7], store(list8));
    let list6 = ByteStream.Cons(a[6], store(list7));
    let list5 = ByteStream.Cons(a[5], store(list6));
    let list4 = ByteStream.Cons(a[4], store(list5));
    let list3 = ByteStream.Cons(a[3], store(list4));
    let list2 = ByteStream.Cons(a[2], store(list3));
    let list1 = ByteStream.Cons(a[1], store(list2));
    ByteStream.Cons(a[0], store(list1))
  }

  -- Pack DefKind (2 bits) and DefinitionSafety (2 bits) into a single byte
  fn pack_def_kind_safety(kind: DefKind, safety: DefinitionSafety) -> G {
    let kind_bits = match kind {
      DefKind.Definition => 0,
      DefKind.Opaque => 1,
      DefKind.Theorem => 2,
    };
    let safety_bits = match safety {
      DefinitionSafety.Unsafe => 0,
      DefinitionSafety.Safe => 1,
      DefinitionSafety.Partial => 2,
    };
    kind_bits * 4 + safety_bits
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
        ByteStream.Cons(0, store(rest)),

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

  -- Tag2: 2-bit flag, variable size
  -- Format: [flag:2][large:1][size:5] or [flag:2][large:1][size_bytes...]
  fn put_tag2(flag: G, size: [G; 8], rest: ByteStream) -> ByteStream {
    let byte_count = u64_byte_count(size);
    let small = u8_less_than(size[0], 32);
    match (byte_count, small) {
      (1, 1) =>
        -- Single byte: flag in bits 6-7, size in bits 0-4
        let head = flag * 64 + size[0];
        ByteStream.Cons(head, store(rest)),
      _ =>
        -- Multi-byte: flag in bits 6-7, large=1 in bit 5, size_bytes-1 in bits 0-4
        let head = flag * 64 + 32 + (byte_count - 1);
        ByteStream.Cons(head, store(put_u64_le(size, byte_count, rest))),
    }
  }

  -- ============================================================================
  -- List serialization
  -- ============================================================================

  fn put_expr_list(list: ExprList, rest: ByteStream) -> ByteStream {
    match list {
      ExprList.Nil => rest,
      ExprList.Cons(&expr, &rest_list) =>
        put_expr(expr, put_expr_list(rest_list, rest)),
    }
  }

  fn put_univ_list(list: UnivList, rest: ByteStream) -> ByteStream {
    match list {
      UnivList.Nil => rest,
      UnivList.Cons(&u, &rest_list) =>
        put_univ(u, put_univ_list(rest_list, rest)),
    }
  }

  fn put_address_list(list: AddressList, rest: ByteStream) -> ByteStream {
    match list {
      AddressList.Nil => rest,
      AddressList.Cons(addr, &rest_list) =>
        put_address(addr, put_address_list(rest_list, rest)),
    }
  }

  fn expr_list_length(list: ExprList) -> [G; 8] {
    match list {
      ExprList.Nil => [0; 8],
      ExprList.Cons(_, &rest) => relaxed_u64_succ(expr_list_length(rest)),
    }
  }

  fn univ_list_length(list: UnivList) -> [G; 8] {
    match list {
      UnivList.Nil => [0; 8],
      UnivList.Cons(_, &rest) => relaxed_u64_succ(univ_list_length(rest)),
    }
  }

  fn address_list_length(list: AddressList) -> [G; 8] {
    match list {
      AddressList.Nil => [0; 8],
      AddressList.Cons(_, &rest) => relaxed_u64_succ(address_list_length(rest)),
    }
  }

  fn recursor_rule_list_length(list: RecursorRuleList) -> [G; 8] {
    match list {
      RecursorRuleList.Nil => [0; 8],
      RecursorRuleList.Cons(_, &rest) => relaxed_u64_succ(recursor_rule_list_length(rest)),
    }
  }

  fn constructor_list_length(list: ConstructorList) -> [G; 8] {
    match list {
      ConstructorList.Nil => [0; 8],
      ConstructorList.Cons(_, &rest) => relaxed_u64_succ(constructor_list_length(rest)),
    }
  }

  fn mut_const_list_length(list: MutConstList) -> [G; 8] {
    match list {
      MutConstList.Nil => [0; 8],
      MutConstList.Cons(_, &rest) => relaxed_u64_succ(mut_const_list_length(rest)),
    }
  }

  -- ============================================================================
  -- Constant serialization
  -- ============================================================================

  fn put_quot_kind(kind: QuotKind, rest: ByteStream) -> ByteStream {
    let tag = match kind {
      QuotKind.Typ => 0,
      QuotKind.Ctor => 1,
      QuotKind.Lift => 2,
      QuotKind.Ind => 3,
    };
    ByteStream.Cons(tag, store(rest))
  }

  fn put_definition(defn: Definition, rest: ByteStream) -> ByteStream {
    match defn {
      Definition.Mk(kind, safety, lvls, &typ, &value) =>
        let packed = pack_def_kind_safety(kind, safety);
        ByteStream.Cons(packed, store(put_tag0(lvls, put_expr(typ, put_expr(value, rest))))),
    }
  }

  fn put_recursor_rule(rule: RecursorRule, rest: ByteStream) -> ByteStream {
    match rule {
      RecursorRule.Mk(fields, &rhs) =>
        put_tag0(fields, put_expr(rhs, rest)),
    }
  }

  fn put_recursor_rule_list(list: RecursorRuleList, rest: ByteStream) -> ByteStream {
    match list {
      RecursorRuleList.Nil => rest,
      RecursorRuleList.Cons(rule, &rest_list) =>
        put_recursor_rule(rule, put_recursor_rule_list(rest_list, rest)),
    }
  }

  fn put_recursor(recr: Recursor, rest: ByteStream) -> ByteStream {
    match recr {
      Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, &typ, &rules) =>
        let bools = k + 2 * is_unsafe;
        let rules_len = recursor_rule_list_length(rules);
        ByteStream.Cons(bools, store(
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
        ByteStream.Cons(is_unsafe, store(put_tag0(lvls, put_expr(typ, rest)))),
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
        ByteStream.Cons(is_unsafe, store(
          put_tag0(lvls,
            put_tag0(cidx,
              put_tag0(params,
                put_tag0(fields,
                  put_expr(typ, rest))))))),
    }
  }

  fn put_constructor_list(list: ConstructorList, rest: ByteStream) -> ByteStream {
    match list {
      ConstructorList.Nil => rest,
      ConstructorList.Cons(ctor, &rest_list) =>
        put_constructor(ctor, put_constructor_list(rest_list, rest)),
    }
  }

  fn put_inductive(indc: Inductive, rest: ByteStream) -> ByteStream {
    match indc {
      Inductive.Mk(recr, refl, is_unsafe, lvls, params, indices, nested, &typ, &ctors) =>
        let bools = recr + 2 * refl + 4 * is_unsafe;
        let ctors_len = constructor_list_length(ctors);
        ByteStream.Cons(bools, store(
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
        ByteStream.Cons(0, store(put_definition(defn, rest))),
      MutConst.Indc(indc) =>
        ByteStream.Cons(1, store(put_inductive(indc, rest))),
      MutConst.Recr(recr) =>
        ByteStream.Cons(2, store(put_recursor(recr, rest))),
    }
  }

  fn put_mut_const_list(list: MutConstList, rest: ByteStream) -> ByteStream {
    match list {
      MutConstList.Nil => rest,
      MutConstList.Cons(mc, &rest_list) =>
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
      -- Muts is never called here - handled separately in put_constant
      ConstantInfo.Muts(_) => rest,
    }
  }

  fn constant_info_variant(info: ConstantInfo) -> [G; 8] {
    match info {
      ConstantInfo.Defn(_) => [0; 8],  -- CONST_DEFN
      ConstantInfo.Recr(_) => [1; 8],  -- CONST_RECR
      ConstantInfo.Axio(_) => [2; 8],  -- CONST_AXIO
      ConstantInfo.Quot(_) => [3; 8],  -- CONST_QUOT
      ConstantInfo.CPrj(_) => [4; 8],  -- CONST_CPRJ
      ConstantInfo.RPrj(_) => [5; 8],  -- CONST_RPRJ
      ConstantInfo.IPrj(_) => [6; 8],  -- CONST_IPRJ
      ConstantInfo.DPrj(_) => [7; 8],  -- CONST_DPRJ
      ConstantInfo.Muts(_) => [0; 8],  -- Not used (handled separately)
    }
  }

  fn put_sharing(list: ExprList, rest: ByteStream) -> ByteStream {
    let len = expr_list_length(list);
    put_tag0(len, put_expr_list(list, rest))
  }

  fn put_refs(list: AddressList, rest: ByteStream) -> ByteStream {
    let len = address_list_length(list);
    put_tag0(len, put_address_list(list, rest))
  }

  fn put_univs(list: UnivList, rest: ByteStream) -> ByteStream {
    let len = univ_list_length(list);
    put_tag0(len, put_univ_list(list, rest))
  }

  fn put_constant(cnst: Constant, rest: ByteStream) -> ByteStream {
    match cnst {
      Constant.Mk(info, &sharing, &refs, &univs) =>
        match info {
          ConstantInfo.Muts(&mutuals) =>
            -- Use FLAG_MUTS (0xC) with entry count in size field
            let count = mut_const_list_length(mutuals);
            put_tag4(0xC, count,
              put_mut_const_list(mutuals,
                put_sharing(sharing,
                  put_refs(refs,
                    put_univs(univs, rest))))),
          _ =>
            -- Use FLAG (0xD) with variant in size field
            let variant = constant_info_variant(info);
            put_tag4(0xD, variant,
              put_constant_info(info,
                put_sharing(sharing,
                  put_refs(refs,
                    put_univs(univs, rest))))),
        },
    }
  }
⟧

end IxVM
