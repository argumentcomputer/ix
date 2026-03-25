module
public import Ix.Aiur.Meta

public section

namespace IxVM

def convert := ⟦

  -- ============================================================================
  -- Conversion input types
  --
  -- A raw Ixon Constant is not self-contained: converting it requires
  -- auxiliary data the prover must supply (ref-to-index mappings, decoded
  -- literal values, reducibility hints, etc.).
  --
  -- ConvertCtx bundles the expression-conversion context.
  -- ConvertKind selects what to convert plus kind-specific auxiliary data.
  -- ConvertInput pairs the two; ConvertInputList is what convert_all consumes.
  -- ============================================================================

  -- Expression conversion context
  -- (sharing, ref_idxs, recur_idxs, lit_blobs, univs)
  --
  -- sharing:    the constant's sharing array (for Expr.Share expansion)
  -- ref_idxs:   maps ref array index -> kernel constant list index
  -- recur_idxs: maps recur index -> kernel constant list index
  -- lit_blobs:  maps blob ref index -> raw blob ByteStream
  -- univs:      the constant's universe array
  enum ConvertCtx {
    Mk(&ExprList, &KGList, &KGList, &ByteStreamList, &UnivList)
  }

  -- What to convert, with kind-specific auxiliary data
  enum ConvertKind {
    CKDefn(Definition, KHints),
    CKAxio(Axiom),
    CKQuot(Quotient),
    CKRecr(Recursor, &KGList),
    CKIndc(Inductive, &KGList),
    CKCtor(Constructor, G)
  }

  -- A fully resolved input ready for conversion
  enum ConvertInput {
    Mk(ConvertCtx, ConvertKind)
  }

  enum ConvertInputList {
    Cons(&ConvertInput, &ConvertInputList),
    Nil
  }

  -- ============================================================================
  -- Ixon list lookups
  -- ============================================================================

  fn g_list_lookup(list: KGList, idx: G) -> G {
    match list {
      KGList.Cons(v, &rest) =>
        match idx {
          0 => v,
          _ => g_list_lookup(rest, idx - 1),
        },
    }
  }

  fn expr_list_lookup(list: ExprList, idx: [G; 8]) -> Expr {
    match list {
      ExprList.Cons(&e, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => e,
          0 => expr_list_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  fn univ_list_lookup(list: UnivList, idx: [G; 8]) -> Univ {
    match list {
      UnivList.Cons(&u, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => u,
          0 => univ_list_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  fn blob_list_lookup(list: ByteStreamList, idx: [G; 8]) -> ByteStream {
    match list {
      ByteStreamList.Nil => ByteStream.Nil,
      ByteStreamList.Cons(bs, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => bs,
          0 => blob_list_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  fn mut_const_list_lookup(list: MutConstList, idx: [G; 8]) -> MutConst {
    match list {
      MutConstList.Cons(mc, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => mc,
          0 => mut_const_list_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  fn constructor_list_lookup(list: ConstructorList, idx: [G; 8]) -> Constructor {
    match list {
      ConstructorList.Cons(c, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => c,
          0 => constructor_list_lookup(rest, relaxed_u64_pred(idx)),
        },
    }
  }

  -- ============================================================================
  -- Universe conversion: Ixon Univ -> KLevel
  -- ============================================================================

  fn convert_univ(u: Univ) -> KLevel {
    match u {
      Univ.Zero => KLevel.Zero,
      Univ.Succ(&inner) => KLevel.Succ(store(convert_univ(inner))),
      Univ.Max(&a, &b) => KLevel.Max(store(convert_univ(a)), store(convert_univ(b))),
      Univ.IMax(&a, &b) => KLevel.IMax(store(convert_univ(a)), store(convert_univ(b))),
      Univ.Var(idx) => KLevel.Param(flatten_u64(idx)),
    }
  }

  -- Resolve a list of universe indices to a KLevelList
  fn convert_univ_idxs(idxs: U64List, univs: UnivList) -> KLevelList {
    match idxs {
      U64List.Nil => KLevelList.Nil,
      U64List.Cons(idx, &rest) =>
        let u = univ_list_lookup(univs, idx);
        KLevelList.Cons(store(convert_univ(u)), store(convert_univ_idxs(rest, univs))),
    }
  }

  -- ============================================================================
  -- Expression conversion: Ixon Expr -> KExpr
  -- ============================================================================

  -- Convert a LE byte stream to KLimbs (list of U64, little-endian bignum).
  -- Reads 8 bytes per limb, zero-padding the last limb if needed.
  -- Strips trailing zero limbs for canonical form.
  fn bytes_to_limbs(bytes: ByteStream) -> KLimbs {
    let limb = bytes_to_u64_limb(bytes, [0; 8], 0);
    let rest_bytes = skip_bytes(bytes, 8);
    match limb {
      -- If this limb is zero and there are no more bytes, return Nil
      _ =>
        match rest_bytes {
          ByteStream.Nil =>
            let is_zero = u64_is_zero(limb);
            match is_zero {
              1 => KLimbs.Nil,
              0 => KLimbs.Cons(limb, store(KLimbs.Nil)),
            },
          _ =>
            let rest_limbs = bytes_to_limbs(rest_bytes);
            KLimbs.Cons(limb, store(rest_limbs)),
        },
    }
  }

  -- Read up to 8 bytes into a U64 (LE), zero-padding.
  fn bytes_to_u64_limb(bytes: ByteStream, acc: [G; 8], pos: G) -> [G; 8] {
    match pos {
      8 => acc,
      _ =>
        match bytes {
          ByteStream.Nil => acc,
          ByteStream.Cons(byte, &rest) =>
            let [v0, v1, v2, v3, v4, v5, v6, v7] = acc;
            match pos {
              0 => bytes_to_u64_limb(rest, [byte, v1, v2, v3, v4, v5, v6, v7], 1),
              1 => bytes_to_u64_limb(rest, [v0, byte, v2, v3, v4, v5, v6, v7], 2),
              2 => bytes_to_u64_limb(rest, [v0, v1, byte, v3, v4, v5, v6, v7], 3),
              3 => bytes_to_u64_limb(rest, [v0, v1, v2, byte, v4, v5, v6, v7], 4),
              4 => bytes_to_u64_limb(rest, [v0, v1, v2, v3, byte, v5, v6, v7], 5),
              5 => bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, byte, v6, v7], 6),
              6 => bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, v5, byte, v7], 7),
              _ => bytes_to_u64_limb(rest, [v0, v1, v2, v3, v4, v5, v6, byte], 8),
            },
        },
    }
  }

  -- Skip n bytes from a ByteStream
  fn skip_bytes(bytes: ByteStream, n: G) -> ByteStream {
    match n {
      0 => bytes,
      _ =>
        match bytes {
          ByteStream.Nil => ByteStream.Nil,
          ByteStream.Cons(_, &rest) => skip_bytes(rest, n - 1),
        },
    }
  }

  fn convert_expr(
    e: Expr,
    sharing: ExprList,
    ref_idxs: KGList,
    recur_idxs: KGList,
    lit_blobs: ByteStreamList,
    univs: UnivList
  ) -> KExpr {
    match e {
      Expr.Srt(univ_idx) =>
        let u = univ_list_lookup(univs, univ_idx);
        KExpr.Srt(store(convert_univ(u))),

      Expr.Var(idx) =>
        KExpr.BVar(flatten_u64(idx)),

      Expr.Ref(ref_idx, &univ_idxs) =>
        let const_idx = g_list_lookup(ref_idxs, flatten_u64(ref_idx));
        let levels = convert_univ_idxs(univ_idxs, univs);
        KExpr.Const(const_idx, store(levels)),

      Expr.Rec(rec_idx, &univ_idxs) =>
        let const_idx = g_list_lookup(recur_idxs, flatten_u64(rec_idx));
        let levels = convert_univ_idxs(univ_idxs, univs);
        KExpr.Const(const_idx, store(levels)),

      Expr.Prj(type_ref_idx, field_idx, &inner) =>
        let type_idx = g_list_lookup(ref_idxs, flatten_u64(type_ref_idx));
        KExpr.Proj(
          type_idx,
          flatten_u64(field_idx),
          store(convert_expr(inner, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.Str(blob_ref_idx) =>
        let bs = blob_list_lookup(lit_blobs, blob_ref_idx);
        KExpr.Lit(KLiteral.Str(bs)),

      Expr.Nat(blob_ref_idx) =>
        let bs = blob_list_lookup(lit_blobs, blob_ref_idx);
        let limbs = bytes_to_limbs(bs);
        KExpr.Lit(KLiteral.Nat(store(limbs))),

      Expr.App(&f, &a) =>
        KExpr.App(
          store(convert_expr(f, sharing, ref_idxs, recur_idxs, lit_blobs, univs)),
          store(convert_expr(a, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.Lam(&ty, &body) =>
        KExpr.Lam(
          store(convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_blobs, univs)),
          store(convert_expr(body, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.All(&ty, &body) =>
        KExpr.Forall(
          store(convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_blobs, univs)),
          store(convert_expr(body, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.Let(_, &ty, &val, &body) =>
        KExpr.Let(
          store(convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_blobs, univs)),
          store(convert_expr(val, sharing, ref_idxs, recur_idxs, lit_blobs, univs)),
          store(convert_expr(body, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.Share(idx) =>
        let shared = expr_list_lookup(sharing, idx);
        convert_expr(shared, sharing, ref_idxs, recur_idxs, lit_blobs, univs),
    }
  }

  fn ctx_convert_expr(e: Expr, ctx: ConvertCtx) -> KExpr {
    match ctx {
      ConvertCtx.Mk(&sharing, &ref_idxs, &recur_idxs, &lit_blobs, &univs) =>
        convert_expr(e, sharing, ref_idxs, recur_idxs, lit_blobs, univs),
    }
  }

  -- ============================================================================
  -- Enum conversions
  -- ============================================================================

  fn convert_safety(s: DefinitionSafety) -> KSafety {
    match s {
      DefinitionSafety.Unsafe => KSafety.Unsafe,
      DefinitionSafety.Safe => KSafety.Safe,
      DefinitionSafety.Partial => KSafety.Partial,
    }
  }

  fn convert_quot_kind(k: QuotKind) -> KQuotKind {
    match k {
      QuotKind.Typ => KQuotKind.Typ,
      QuotKind.Ctor => KQuotKind.Ctor,
      QuotKind.Lift => KQuotKind.Lift,
      QuotKind.Ind => KQuotKind.Ind,
    }
  }

  -- ============================================================================
  -- Recursor rule conversion
  -- ============================================================================

  -- Convert Ixon RecursorRuleList to KRecRuleList.
  -- rule_ctor_idxs provides the kernel constant index for each rule's constructor.
  fn convert_rules(
    rules: RecursorRuleList,
    rule_ctor_idxs: KGList,
    ctx: ConvertCtx
  ) -> KRecRuleList {
    match rules {
      RecursorRuleList.Nil => KRecRuleList.Nil,
      RecursorRuleList.Cons(rule, &rest_rules) =>
        match rule {
          RecursorRule.Mk(nfields, &rhs) =>
            match rule_ctor_idxs {
              KGList.Cons(ctor_idx, &rest_ctor_idxs) =>
                let krhs = ctx_convert_expr(rhs, ctx);
                let krule = KRecRule.Mk(ctor_idx, flatten_u64(nfields), store(krhs));
                KRecRuleList.Cons(
                  store(krule),
                  store(convert_rules(rest_rules, rest_ctor_idxs, ctx))),
            },
        },
    }
  }

  -- ============================================================================
  -- Per-kind conversion
  -- ============================================================================

  fn convert_definition(d: Definition, ctx: ConvertCtx, hints: KHints) -> KConstantInfo {
    match d {
      Definition.Mk(kind, safety, lvls, &typ, &value) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        let kval = ctx_convert_expr(value, ctx);
        match kind {
          DefKind.Definition =>
            KConstantInfo.Defn(flatten_u64(lvls), store(ktyp), store(kval), hints, convert_safety(safety)),
          DefKind.Opaque =>
            match safety {
              DefinitionSafety.Unsafe =>
                KConstantInfo.Opaque(flatten_u64(lvls), store(ktyp), store(kval), 1),
              _ =>
                KConstantInfo.Opaque(flatten_u64(lvls), store(ktyp), store(kval), 0),
            },
          DefKind.Theorem =>
            KConstantInfo.Thm(flatten_u64(lvls), store(ktyp), store(kval)),
        },
    }
  }

  fn convert_axiom(a: Axiom, ctx: ConvertCtx) -> KConstantInfo {
    match a {
      Axiom.Mk(is_unsafe, lvls, &typ) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        KConstantInfo.Axiom(flatten_u64(lvls), store(ktyp), is_unsafe),
    }
  }

  fn convert_quotient(q: Quotient, ctx: ConvertCtx) -> KConstantInfo {
    match q {
      Quotient.Mk(kind, lvls, &typ) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        KConstantInfo.Quot(flatten_u64(lvls), store(ktyp), convert_quot_kind(kind)),
    }
  }

  fn convert_recursor(r: Recursor, ctx: ConvertCtx, rule_ctor_idxs: KGList) -> KConstantInfo {
    match r {
      Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, &typ, &rules) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        let krules = convert_rules(rules, rule_ctor_idxs, ctx);
        KConstantInfo.Rec(
          flatten_u64(lvls), store(ktyp), flatten_u64(params), flatten_u64(indices),
          flatten_u64(motives), flatten_u64(minors),
          store(krules), k, is_unsafe),
    }
  }

  fn convert_inductive(ind: Inductive, ctx: ConvertCtx, ctor_idxs: KGList) -> KConstantInfo {
    match ind {
      Inductive.Mk(is_rec, is_refl, is_unsafe, lvls, params, indices, _, &typ, _) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        KConstantInfo.Induct(
          flatten_u64(lvls), store(ktyp), flatten_u64(params), flatten_u64(indices),
          store(ctor_idxs), is_rec, is_refl, is_unsafe),
    }
  }

  fn convert_constructor(c: Constructor, ctx: ConvertCtx, induct_idx: G) -> KConstantInfo {
    match c {
      Constructor.Mk(is_unsafe, lvls, cidx, params, fields, &typ) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        KConstantInfo.Ctor(
          flatten_u64(lvls), store(ktyp), induct_idx, flatten_u64(cidx),
          flatten_u64(params), flatten_u64(fields), is_unsafe),
    }
  }

  -- ============================================================================
  -- Top-level conversion
  -- ============================================================================

  -- Convert a single resolved input to a KConstantInfo
  fn convert_one(input: ConvertInput) -> KConstantInfo {
    match input {
      ConvertInput.Mk(ctx, kind) =>
        match kind {
          ConvertKind.CKDefn(d, hints) => convert_definition(d, ctx, hints),
          ConvertKind.CKAxio(a) => convert_axiom(a, ctx),
          ConvertKind.CKQuot(q) => convert_quotient(q, ctx),
          ConvertKind.CKRecr(r, &rule_ctor_idxs) => convert_recursor(r, ctx, rule_ctor_idxs),
          ConvertKind.CKIndc(ind, &ctor_idxs) => convert_inductive(ind, ctx, ctor_idxs),
          ConvertKind.CKCtor(c, induct_idx) => convert_constructor(c, ctx, induct_idx),
        },
    }
  }

  -- Convert a list of resolved inputs to a KConstList
  fn convert_all(inputs: ConvertInputList) -> KConstList {
    match inputs {
      ConvertInputList.Nil => KConstList.Nil,
      ConvertInputList.Cons(&input, &rest) =>
        let ci = convert_one(input);
        KConstList.Cons(store(ci), store(convert_all(rest))),
    }
  }
⟧

end IxVM

end
