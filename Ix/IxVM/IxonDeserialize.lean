module
public import Ix.Aiur.Meta

public section

namespace IxVM

def ixonDeserialize := ⟦
  -- ============================================================================
  -- Byte reading primitives
  -- ============================================================================

  fn read_byte(stream: ByteStream) -> (G, ByteStream) {
    match stream {
      ByteStream.Cons(byte, &rest) => (byte, rest),
      ByteStream.Nil => (0, ByteStream.Nil),
    }
  }

  -- Read num_bytes little-endian bytes into a u64
  fn get_u64_le(stream: ByteStream, num_bytes: G) -> ([G; 8], ByteStream) {
    match num_bytes {
      0 => ([0; 8], stream),
      _ =>
        let (byte, s) = read_byte(stream);
        let (rest_bytes, s2) = get_u64_le(s, num_bytes - 1);
        let [r0, r1, r2, r3, r4, r5, r6, _] = rest_bytes;
        ([byte, r0, r1, r2, r3, r4, r5, r6], s2),
    }
  }

  -- ============================================================================
  -- Tag parsing
  -- ============================================================================

  -- Tag0: [large:1][size:7]
  fn get_tag0(stream: ByteStream) -> ([G; 8], ByteStream) {
    let (byte, s) = read_byte(stream);
    let bits = u8_bit_decomposition(byte);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bits;
    let small_size = b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5 + 64 * b6;
    match b7 {
      0 =>
        ([small_size, 0, 0, 0, 0, 0, 0, 0], s),
      _ =>
        let num_bytes = small_size + 1;
        get_u64_le(s, num_bytes),
    }
  }

  -- Tag2: [flag:2][large:1][size:5]
  fn get_tag2(stream: ByteStream) -> ((G, [G; 8]), ByteStream) {
    let (byte, s) = read_byte(stream);
    let bits = u8_bit_decomposition(byte);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bits;
    let flag = b6 + 2 * b7;
    let small_size = b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4;
    match b5 {
      0 =>
        ((flag, [small_size, 0, 0, 0, 0, 0, 0, 0]), s),
      _ =>
        let num_bytes = small_size + 1;
        let (size, s2) = get_u64_le(s, num_bytes);
        ((flag, size), s2),
    }
  }

  -- Tag4: [flag:4][large:1][size:3]
  fn get_tag4(stream: ByteStream) -> ((G, [G; 8]), ByteStream) {
    let (byte, s) = read_byte(stream);
    let bits = u8_bit_decomposition(byte);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bits;
    let flag = b4 + 2 * b5 + 4 * b6 + 8 * b7;
    let small_size = b0 + 2 * b1 + 4 * b2;
    match b3 {
      0 =>
        ((flag, [small_size, 0, 0, 0, 0, 0, 0, 0]), s),
      _ =>
        let num_bytes = small_size + 1;
        let (size, s2) = get_u64_le(s, num_bytes);
        ((flag, size), s2),
    }
  }

  -- ============================================================================
  -- U64 list deserialization
  -- ============================================================================

  fn get_u64_list(stream: ByteStream, count: [G; 8]) -> (U64List, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (U64List.Nil, stream),
      _ =>
        let (val, s) = get_tag0(stream);
        let (rest, s2) = get_u64_list(s, relaxed_u64_pred(count));
        (U64List.Cons(val, store(rest)), s2),
    }
  }

  -- ============================================================================
  -- Expression deserialization
  -- ============================================================================

  -- App telescope: read count args, wrapping func in App nodes
  fn get_app_telescope(func: Expr, stream: ByteStream, count: [G; 8]) -> (Expr, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (func, stream),
      _ =>
        let (arg, s) = get_expr(stream);
        let app = Expr.App(store(func), store(arg));
        get_app_telescope(app, s, relaxed_u64_pred(count)),
    }
  }

  -- Lam telescope: read count types then body, wrap as nested Lams
  fn get_lam_telescope(stream: ByteStream, count: [G; 8]) -> (Expr, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 =>
        -- No more types, read the body
        get_expr(stream),
      _ =>
        -- Read one type, recurse for remaining types + body
        let (ty, s) = get_expr(stream);
        let (inner, s2) = get_lam_telescope(s, relaxed_u64_pred(count));
        (Expr.Lam(store(ty), store(inner)), s2),
    }
  }

  -- All telescope: read count types then body, wrap as nested Alls
  fn get_all_telescope(stream: ByteStream, count: [G; 8]) -> (Expr, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 =>
        -- No more types, read the body
        get_expr(stream),
      _ =>
        -- Read one type, recurse for remaining types + body
        let (ty, s) = get_expr(stream);
        let (inner, s2) = get_all_telescope(s, relaxed_u64_pred(count));
        (Expr.All(store(ty), store(inner)), s2),
    }
  }

  fn get_expr(stream: ByteStream) -> (Expr, ByteStream) {
    let (tag, s) = get_tag4(stream);
    let (flag, size) = tag;
    match flag {
      -- Srt: Tag4(0x0, univ_idx)
      0 => (Expr.Srt(size), s),

      -- Var: Tag4(0x1, idx)
      1 => (Expr.Var(size), s),

      -- Ref: Tag4(0x2, len) + Tag0(ref_idx) + univ_list
      2 =>
        let (ref_idx, s2) = get_tag0(s);
        let (univ_list, s3) = get_u64_list(s2, size);
        (Expr.Ref(ref_idx, store(univ_list)), s3),

      -- Rec: Tag4(0x3, len) + Tag0(rec_idx) + univ_list
      3 =>
        let (rec_idx, s2) = get_tag0(s);
        let (univ_list, s3) = get_u64_list(s2, size);
        (Expr.Rec(rec_idx, store(univ_list)), s3),

      -- Prj: Tag4(0x4, field_idx) + Tag0(type_ref_idx) + expr(val)
      4 =>
        let (type_ref_idx, s2) = get_tag0(s);
        let (val, s3) = get_expr(s2);
        (Expr.Prj(type_ref_idx, size, store(val)), s3),

      -- Str: Tag4(0x5, ref_idx)
      5 => (Expr.Str(size), s),

      -- Nat: Tag4(0x6, ref_idx)
      6 => (Expr.Nat(size), s),

      -- App: Tag4(0x7, count) + func + args...
      7 =>
        let (func, s2) = get_expr(s);
        get_app_telescope(func, s2, size),

      -- Lam: Tag4(0x8, count) + types... + body
      8 => get_lam_telescope(s, size),

      -- All: Tag4(0x9, count) + types... + body
      9 => get_all_telescope(s, size),

      -- Let: Tag4(0xA, non_dep) + expr(ty) + expr(val) + expr(body)
      10 =>
        let (ty, s2) = get_expr(s);
        let (val, s3) = get_expr(s2);
        let (body, s4) = get_expr(s3);
        (Expr.Let(size, store(ty), store(val), store(body)), s4),

      -- Share: Tag4(0xB, idx)
      _ => (Expr.Share(size), s),
    }
  }

  -- ============================================================================
  -- Universe deserialization
  -- ============================================================================

  -- Build a chain of Succ constructors around a base universe
  fn build_succ_chain(base: Univ, count: [G; 8]) -> Univ {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => base,
      _ =>
        let inner = build_succ_chain(base, relaxed_u64_pred(count));
        Univ.Succ(store(inner)),
    }
  }

  fn get_univ(stream: ByteStream) -> (Univ, ByteStream) {
    let (tag, s) = get_tag2(stream);
    let (flag, size) = tag;
    match flag {
      -- Zero/Succ: Tag2(0, count)
      0 =>
        let is_zero = u64_is_zero(size);
        match is_zero {
          1 => (Univ.Zero, s),
          _ =>
            let (base, s2) = get_univ(s);
            (build_succ_chain(base, size), s2),
        },

      -- Max: Tag2(1, 0) + univ(a) + univ(b)
      1 =>
        let (a, s2) = get_univ(s);
        let (b, s3) = get_univ(s2);
        (Univ.Max(store(a), store(b)), s3),

      -- IMax: Tag2(2, 0) + univ(a) + univ(b)
      2 =>
        let (a, s2) = get_univ(s);
        let (b, s3) = get_univ(s2);
        (Univ.IMax(store(a), store(b)), s3),

      -- Var: Tag2(3, idx)
      _ => (Univ.Var(size), s),
    }
  }

  -- ============================================================================
  -- Address deserialization (32 bytes)
  -- ============================================================================

  fn get_address(stream: ByteStream) -> ([G; 32], ByteStream) {
    let (b0, s) = read_byte(stream);
    let (b1, s) = read_byte(s);
    let (b2, s) = read_byte(s);
    let (b3, s) = read_byte(s);
    let (b4, s) = read_byte(s);
    let (b5, s) = read_byte(s);
    let (b6, s) = read_byte(s);
    let (b7, s) = read_byte(s);
    let (b8, s) = read_byte(s);
    let (b9, s) = read_byte(s);
    let (b10, s) = read_byte(s);
    let (b11, s) = read_byte(s);
    let (b12, s) = read_byte(s);
    let (b13, s) = read_byte(s);
    let (b14, s) = read_byte(s);
    let (b15, s) = read_byte(s);
    let (b16, s) = read_byte(s);
    let (b17, s) = read_byte(s);
    let (b18, s) = read_byte(s);
    let (b19, s) = read_byte(s);
    let (b20, s) = read_byte(s);
    let (b21, s) = read_byte(s);
    let (b22, s) = read_byte(s);
    let (b23, s) = read_byte(s);
    let (b24, s) = read_byte(s);
    let (b25, s) = read_byte(s);
    let (b26, s) = read_byte(s);
    let (b27, s) = read_byte(s);
    let (b28, s) = read_byte(s);
    let (b29, s) = read_byte(s);
    let (b30, s) = read_byte(s);
    let (b31, s) = read_byte(s);
    ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], s)
  }

  -- ============================================================================
  -- List deserialization
  -- ============================================================================

  fn get_expr_list(stream: ByteStream, count: [G; 8]) -> (ExprList, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (ExprList.Nil, stream),
      _ =>
        let (expr, s) = get_expr(stream);
        let (rest, s2) = get_expr_list(s, relaxed_u64_pred(count));
        (ExprList.Cons(store(expr), store(rest)), s2),
    }
  }

  fn get_univ_list(stream: ByteStream, count: [G; 8]) -> (UnivList, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (UnivList.Nil, stream),
      _ =>
        let (u, s) = get_univ(stream);
        let (rest, s2) = get_univ_list(s, relaxed_u64_pred(count));
        (UnivList.Cons(store(u), store(rest)), s2),
    }
  }

  fn get_address_list(stream: ByteStream, count: [G; 8]) -> (AddressList, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (AddressList.Nil, stream),
      _ =>
        let (addr, s) = get_address(stream);
        let (rest, s2) = get_address_list(s, relaxed_u64_pred(count));
        (AddressList.Cons(addr, store(rest)), s2),
    }
  }

  -- ============================================================================
  -- Sharing, refs, univs table deserialization
  -- ============================================================================

  fn get_sharing(stream: ByteStream) -> (ExprList, ByteStream) {
    let (len, s) = get_tag0(stream);
    get_expr_list(s, len)
  }

  fn get_refs(stream: ByteStream) -> (AddressList, ByteStream) {
    let (len, s) = get_tag0(stream);
    get_address_list(s, len)
  }

  fn get_univs(stream: ByteStream) -> (UnivList, ByteStream) {
    let (len, s) = get_tag0(stream);
    get_univ_list(s, len)
  }

  -- ============================================================================
  -- Constant structure deserialization
  -- ============================================================================

  -- Unpack DefKind and DefinitionSafety from packed byte
  -- Encoding: kind * 4 + safety
  -- kind: Definition=0, Opaque=1, Theorem=2
  -- safety: Unsafe=0, Safe=1, Partial=2
  fn unpack_def_kind_safety(byte: G) -> (DefKind, DefinitionSafety) {
    match byte {
      0 => (DefKind.Definition, DefinitionSafety.Unsafe),
      1 => (DefKind.Definition, DefinitionSafety.Safe),
      2 => (DefKind.Definition, DefinitionSafety.Partial),
      4 => (DefKind.Opaque, DefinitionSafety.Unsafe),
      5 => (DefKind.Opaque, DefinitionSafety.Safe),
      6 => (DefKind.Opaque, DefinitionSafety.Partial),
      8 => (DefKind.Theorem, DefinitionSafety.Unsafe),
      9 => (DefKind.Theorem, DefinitionSafety.Safe),
      _ => (DefKind.Theorem, DefinitionSafety.Partial),
    }
  }

  -- Definition: byte(packed_kind_safety) + Tag0(lvls) + expr(typ) + expr(value)
  fn get_definition(stream: ByteStream) -> (Definition, ByteStream) {
    let (packed, s) = read_byte(stream);
    let (kind, safety) = unpack_def_kind_safety(packed);
    let (lvls, s2) = get_tag0(s);
    let (typ, s3) = get_expr(s2);
    let (value, s4) = get_expr(s3);
    (Definition.Mk(kind, safety, lvls, store(typ), store(value)), s4)
  }

  -- RecursorRule: Tag0(fields) + expr(rhs)
  fn get_recursor_rule(stream: ByteStream) -> (RecursorRule, ByteStream) {
    let (fields, s) = get_tag0(stream);
    let (rhs, s2) = get_expr(s);
    (RecursorRule.Mk(fields, store(rhs)), s2)
  }

  fn get_recursor_rule_list(stream: ByteStream, count: [G; 8]) -> (RecursorRuleList, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (RecursorRuleList.Nil, stream),
      _ =>
        let (rule, s) = get_recursor_rule(stream);
        let (rest, s2) = get_recursor_rule_list(s, relaxed_u64_pred(count));
        (RecursorRuleList.Cons(rule, store(rest)), s2),
    }
  }

  -- Recursor: byte(bools) + Tag0(lvls) + Tag0(params) + Tag0(indices) +
  --           Tag0(motives) + Tag0(minors) + expr(typ) + Tag0(rules_len) + rules...
  fn get_recursor(stream: ByteStream) -> (Recursor, ByteStream) {
    let (bools_byte, s) = read_byte(stream);
    let bits = u8_bit_decomposition(bools_byte);
    let k = bits[0];
    let is_unsafe = bits[1];
    let (lvls, s2) = get_tag0(s);
    let (params, s3) = get_tag0(s2);
    let (indices, s4) = get_tag0(s3);
    let (motives, s5) = get_tag0(s4);
    let (minors, s6) = get_tag0(s5);
    let (typ, s7) = get_expr(s6);
    let (rules_len, s8) = get_tag0(s7);
    let (rules, s9) = get_recursor_rule_list(s8, rules_len);
    (Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, store(typ), store(rules)), s9)
  }

  -- Axiom: byte(is_unsafe) + Tag0(lvls) + expr(typ)
  fn get_axiom(stream: ByteStream) -> (Axiom, ByteStream) {
    let (is_unsafe, s) = read_byte(stream);
    let (lvls, s2) = get_tag0(s);
    let (typ, s3) = get_expr(s2);
    (Axiom.Mk(is_unsafe, lvls, store(typ)), s3)
  }

  -- QuotKind: byte(0=Typ, 1=Ctor, 2=Lift, 3=Ind)
  fn get_quot_kind(byte: G) -> QuotKind {
    match byte {
      0 => QuotKind.Typ,
      1 => QuotKind.Ctor,
      2 => QuotKind.Lift,
      _ => QuotKind.Ind,
    }
  }

  -- Quotient: byte(kind) + Tag0(lvls) + expr(typ)
  fn get_quotient(stream: ByteStream) -> (Quotient, ByteStream) {
    let (kind_byte, s) = read_byte(stream);
    let kind = get_quot_kind(kind_byte);
    let (lvls, s2) = get_tag0(s);
    let (typ, s3) = get_expr(s2);
    (Quotient.Mk(kind, lvls, store(typ)), s3)
  }

  -- Constructor: byte(is_unsafe) + Tag0(lvls) + Tag0(cidx) + Tag0(params) +
  --              Tag0(fields) + expr(typ)
  fn get_constructor(stream: ByteStream) -> (Constructor, ByteStream) {
    let (is_unsafe, s) = read_byte(stream);
    let (lvls, s2) = get_tag0(s);
    let (cidx, s3) = get_tag0(s2);
    let (params, s4) = get_tag0(s3);
    let (fields, s5) = get_tag0(s4);
    let (typ, s6) = get_expr(s5);
    (Constructor.Mk(is_unsafe, lvls, cidx, params, fields, store(typ)), s6)
  }

  fn get_constructor_list(stream: ByteStream, count: [G; 8]) -> (ConstructorList, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (ConstructorList.Nil, stream),
      _ =>
        let (ctor, s) = get_constructor(stream);
        let (rest, s2) = get_constructor_list(s, relaxed_u64_pred(count));
        (ConstructorList.Cons(ctor, store(rest)), s2),
    }
  }

  -- Inductive: byte(bools) + Tag0(lvls) + Tag0(params) + Tag0(indices) +
  --            Tag0(nested) + expr(typ) + Tag0(ctors_len) + ctors...
  fn get_inductive(stream: ByteStream) -> (Inductive, ByteStream) {
    let (bools_byte, s) = read_byte(stream);
    let bits = u8_bit_decomposition(bools_byte);
    let recr = bits[0];
    let refl = bits[1];
    let is_unsafe = bits[2];
    let (lvls, s2) = get_tag0(s);
    let (params, s3) = get_tag0(s2);
    let (indices, s4) = get_tag0(s3);
    let (nested, s5) = get_tag0(s4);
    let (typ, s6) = get_expr(s5);
    let (ctors_len, s7) = get_tag0(s6);
    let (ctors, s8) = get_constructor_list(s7, ctors_len);
    (Inductive.Mk(recr, refl, is_unsafe, lvls, params, indices, nested, store(typ), store(ctors)), s8)
  }

  -- ============================================================================
  -- Projection deserialization
  -- ============================================================================

  -- InductiveProj: Tag0(idx) + address(block)
  fn get_inductive_proj(stream: ByteStream) -> (InductiveProj, ByteStream) {
    let (idx, s) = get_tag0(stream);
    let (block, s2) = get_address(s);
    (InductiveProj.Mk(idx, block), s2)
  }

  -- ConstructorProj: Tag0(idx) + Tag0(cidx) + address(block)
  fn get_constructor_proj(stream: ByteStream) -> (ConstructorProj, ByteStream) {
    let (idx, s) = get_tag0(stream);
    let (cidx, s2) = get_tag0(s);
    let (block, s3) = get_address(s2);
    (ConstructorProj.Mk(idx, cidx, block), s3)
  }

  -- RecursorProj: Tag0(idx) + address(block)
  fn get_recursor_proj(stream: ByteStream) -> (RecursorProj, ByteStream) {
    let (idx, s) = get_tag0(stream);
    let (block, s2) = get_address(s);
    (RecursorProj.Mk(idx, block), s2)
  }

  -- DefinitionProj: Tag0(idx) + address(block)
  fn get_definition_proj(stream: ByteStream) -> (DefinitionProj, ByteStream) {
    let (idx, s) = get_tag0(stream);
    let (block, s2) = get_address(s);
    (DefinitionProj.Mk(idx, block), s2)
  }

  -- ============================================================================
  -- Mutual constant deserialization
  -- ============================================================================

  -- MutConst: byte(tag) + payload
  fn get_mut_const(stream: ByteStream) -> (MutConst, ByteStream) {
    let (tag, s) = read_byte(stream);
    match tag {
      0 =>
        let (defn, s2) = get_definition(s);
        (MutConst.Defn(defn), s2),
      1 =>
        let (indc, s2) = get_inductive(s);
        (MutConst.Indc(indc), s2),
      _ =>
        let (recr, s2) = get_recursor(s);
        (MutConst.Recr(recr), s2),
    }
  }

  fn get_mut_const_list(stream: ByteStream, count: [G; 8]) -> (MutConstList, ByteStream) {
    let is_zero = u64_is_zero(count);
    match is_zero {
      1 => (MutConstList.Nil, stream),
      _ =>
        let (mc, s) = get_mut_const(stream);
        let (rest, s2) = get_mut_const_list(s, relaxed_u64_pred(count));
        (MutConstList.Cons(mc, store(rest)), s2),
    }
  }

  -- ============================================================================
  -- Constant info deserialization
  -- ============================================================================

  -- Dispatch on variant number (0-7) to deserialize the appropriate ConstantInfo
  fn get_constant_info_by_variant(variant: G, stream: ByteStream) -> (ConstantInfo, ByteStream) {
    match variant {
      0 =>
        let (defn, s) = get_definition(stream);
        (ConstantInfo.Defn(defn), s),
      1 =>
        let (recr, s) = get_recursor(stream);
        (ConstantInfo.Recr(recr), s),
      2 =>
        let (axim, s) = get_axiom(stream);
        (ConstantInfo.Axio(axim), s),
      3 =>
        let (quot, s) = get_quotient(stream);
        (ConstantInfo.Quot(quot), s),
      4 =>
        let (prj, s) = get_constructor_proj(stream);
        (ConstantInfo.CPrj(prj), s),
      5 =>
        let (prj, s) = get_recursor_proj(stream);
        (ConstantInfo.RPrj(prj), s),
      6 =>
        let (prj, s) = get_inductive_proj(stream);
        (ConstantInfo.IPrj(prj), s),
      _ =>
        let (prj, s) = get_definition_proj(stream);
        (ConstantInfo.DPrj(prj), s),
    }
  }

  -- Parse ConstantInfo from flag (0xC for Muts, 0xD for non-Muts) and size
  fn get_constant_info(flag: G, size: [G; 8], stream: ByteStream) -> (ConstantInfo, ByteStream) {
    match flag {
      -- Muts: flag=0xC, size is the entry count
      12 =>
        let (mutuals, s) = get_mut_const_list(stream, size);
        (ConstantInfo.Muts(store(mutuals)), s),
      -- Non-Muts: flag=0xD, size[0] is the variant number
      _ =>
        get_constant_info_by_variant(size[0], stream),
    }
  }

  -- ============================================================================
  -- Top-level constant deserialization
  -- ============================================================================

  fn get_constant(stream: ByteStream) -> (Constant, ByteStream) {
    let (tag, s) = get_tag4(stream);
    let (flag, size) = tag;
    let (info, s2) = get_constant_info(flag, size, s);
    let (sharing, s3) = get_sharing(s2);
    let (refs, s4) = get_refs(s3);
    let (univs, s5) = get_univs(s4);
    (Constant.Mk(info, store(sharing), store(refs), store(univs)), s5)
  }
⟧

end IxVM

end
