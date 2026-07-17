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
  -- ConvertInput pairs the two; List‹&ConvertInput› is what convert_all consumes.
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
    Mk(List‹&Expr›, List‹G›, List‹G›, List‹ByteStream›, List‹&Univ›)
  }

  -- What to convert, with kind-specific auxiliary data
  enum ConvertKind {
    -- CKDefn carries Definition + reducibility hint G (packed:
    -- 0=Opaque, 1+h=Regular(h), 0xFFFFFFFF=Abbrev). See KernelTypes.
    CKDefn(Definition, G),
    CKAxio(Axiom),
    CKQuot(Quotient),
    CKRecr(Recursor, List‹G›, Addr),
    CKIndc(Inductive, List‹G›, Addr),
    CKCtor(Constructor, G)
  }

  -- A fully resolved input ready for conversion
  enum ConvertInput {
    Mk(ConvertCtx, ConvertKind)
  }


  -- ============================================================================
  -- Universe conversion: Ixon Univ -> KLevel
  -- ============================================================================

  -- Take `&Univ` (pointer) to shrink the per-row input width — Univ is a
  -- 5-variant enum, by-value passing taxes every row with the widest
  -- arm's columns. Mirror the `reference_aiur_pass_pointer_not_value`
  -- pattern already used for `convert_expr(e: &Expr)`.
  #[group=cold3] fn convert_univ(u: &Univ) -> KLevel {
    match load(u) {
      Univ.Zero => store(KLevelNode.Zero),
      Univ.Succ(inner) => store(KLevelNode.Succ(convert_univ(inner))),
      Univ.Max(a, b) => store(KLevelNode.Max(convert_univ(a), convert_univ(b))),
      Univ.IMax(a, b) => store(KLevelNode.IMax(convert_univ(a), convert_univ(b))),
      Univ.Var(idx) => store(KLevelNode.Param(flatten_u64(idx))),
    }
  }

  -- Resolve a list of universe indices to a List‹KLevel›
  #[group=cold4] fn convert_univ_idxs(idxs: List‹U64›, univs: List‹&Univ›) -> List‹KLevel› {
    match load(idxs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(idx, rest) =>
        -- universe indices are small; walk with a field index (cheap per-step
        -- field sub) instead of `list_lookup_u64`'s per-step U64 predecessor.
        let u_ref = list_lookup(univs, flatten_u64(idx));
        store(ListNode.Cons(convert_univ(u_ref), convert_univ_idxs(rest, univs))),
    }
  }

  -- ============================================================================
  -- Expression conversion: Ixon Expr -> KExpr
  -- ============================================================================

  -- Convert a LE byte stream to KLimbs (list of U64, little-endian bignum).
  -- Reads 8 bytes per limb, zero-padding the last limb if needed.
  -- Strips trailing zero limbs for canonical form.
  #[group=cold4] fn bytes_to_limbs(bytes: ByteStream) -> KLimbs {
    let limb = bytes_to_u64_limb(bytes, [0u8; 8], 0);
    let rest_bytes = skip_bytes(bytes, 8);
    match limb {
      -- If this limb is zero and there are no more bytes, return Nil
      _ =>
        match load(rest_bytes) {
          ListNode.Nil =>
            let is_zero = u64_is_zero(limb);
            match is_zero {
              1 => store(ListNode.Nil),
              0 => store(ListNode.Cons(limb, store(ListNode.Nil))),
            },
          _ =>
            let rest_limbs = bytes_to_limbs(rest_bytes);
            store(ListNode.Cons(limb, rest_limbs)),
        },
    }
  }

  -- Read up to 8 bytes into a U64 (LE), zero-padding.
  #[group=cold5] fn bytes_to_u64_limb(bytes: ByteStream, acc: U64, pos: G) -> U64 {
    match pos {
      8 => acc,
      _ =>
        match load(bytes) {
          ListNode.Nil => acc,
          ListNode.Cons(byte, rest) =>
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
  #[group=cold2] fn skip_bytes(bytes: ByteStream, n: G) -> ByteStream {
    match n {
      0 => bytes,
      _ =>
        match load(bytes) {
          ListNode.Nil => store(ListNode.Nil),
          ListNode.Cons(_, rest) => skip_bytes(rest, n - 1),
        },
    }
  }

  fn convert_expr(
    e: &Expr,
    sharing: List‹&Expr›,
    ref_idxs: List‹G›,
    recur_idxs: List‹G›,
    lit_blobs: List‹ByteStream›,
    univs: List‹&Univ›
  ) -> KExpr {
    match load(e) {
      Expr.Srt(univ_idx) =>
        -- field-indexed walk (see `convert_univ_idxs`): avoids the per-step
        -- U64 predecessor of `list_lookup_u64` on this hot universe lookup.
        let u_ref = list_lookup(univs, flatten_u64(univ_idx));
        store(KExprNode.Srt(convert_univ(u_ref))),

      Expr.Var(idx) =>
        store(KExprNode.BVar(flatten_u64(idx))),

      Expr.Ref(ref_idx, univ_idxs) =>
        let const_idx = list_lookup(ref_idxs, flatten_u64(ref_idx));
        let levels = convert_univ_idxs(univ_idxs, univs);
        store(KExprNode.Const(const_idx, levels)),

      Expr.Rec(rec_idx, univ_idxs) =>
        let const_idx = list_lookup(recur_idxs, flatten_u64(rec_idx));
        let levels = convert_univ_idxs(univ_idxs, univs);
        store(KExprNode.Const(const_idx, levels)),

      Expr.Prj(type_ref_idx, field_idx, inner) =>
        let type_idx = list_lookup(ref_idxs, flatten_u64(type_ref_idx));
        store(KExprNode.Proj(
          type_idx,
          flatten_u64(field_idx),
          convert_expr(inner, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.Str(blob_ref_idx) =>
        let bs = list_lookup_u64(lit_blobs, blob_ref_idx);
        store(KExprNode.Lit(KLiteral.Str(bs))),

      Expr.Nat(blob_ref_idx) =>
        let bs = list_lookup_u64(lit_blobs, blob_ref_idx);
        let limbs = bytes_to_limbs(bs);
        store(KExprNode.Lit(KLiteral.Nat(limbs))),

      Expr.App(f, a) =>
        store(KExprNode.App(
          convert_expr(f, sharing, ref_idxs, recur_idxs, lit_blobs, univs),
          convert_expr(a, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.Lam(ty, body) =>
        store(KExprNode.Lam(
          convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_blobs, univs),
          convert_expr(body, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.All(ty, body) =>
        store(KExprNode.Forall(
          convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_blobs, univs),
          convert_expr(body, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.Let(_, ty, val, body) =>
        store(KExprNode.Let(
          convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_blobs, univs),
          convert_expr(val, sharing, ref_idxs, recur_idxs, lit_blobs, univs),
          convert_expr(body, sharing, ref_idxs, recur_idxs, lit_blobs, univs))),

      Expr.Share(idx) =>
        let ListNode.Cons(e, _) = load(list_drop(sharing, flatten_u64(idx)));
        convert_expr(e, sharing, ref_idxs, recur_idxs, lit_blobs, univs),
    }
  }

  -- ============================================================================
  -- Recursor rule conversion
  -- ============================================================================

  -- Convert Ixon List‹RecursorRule› to List‹KRecRule›.
  -- rule_ctor_idxs provides the kernel constant index for each rule's constructor.
  #[group=cold4] fn convert_rules(
    rules: List‹RecursorRule›,
    rule_ctor_idxs: List‹G›,
    ctx: ConvertCtx
  ) -> List‹KRecRule› {
    match load(rules) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(rule, rest_rules) =>
        match rule {
          RecursorRule.Mk(nfields, rhs) =>
            match load(rule_ctor_idxs) {
              ListNode.Cons(ctor_idx, rest_ctor_idxs) =>
                match ctx {
                  ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs) =>
                    let krhs = convert_expr(rhs, sharing, ref_idxs, recur_idxs, lit_blobs, univs);
                    let krule = KRecRule.Mk(ctor_idx, flatten_u64(nfields), krhs);
                    store(ListNode.Cons(
                      krule,
                      convert_rules(rest_rules, rest_ctor_idxs, ctx))),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Per-kind conversion
  -- ============================================================================

  #[group=cold4] fn convert_definition(d: Definition, ctx: ConvertCtx, hint: G) -> KConstantInfo {
    match ctx {
      ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs) =>
        match d {
          Definition.Mk(kind, safety, lvls, typ, value) =>
            let ktyp = convert_expr(typ, sharing, ref_idxs, recur_idxs, lit_blobs, univs);
            let kval = convert_expr(value, sharing, ref_idxs, recur_idxs, lit_blobs, univs);
            match kind {
              DefKind.Definition =>
                KConstantInfo.Defn(flatten_u64(lvls), ktyp, kval, safety, hint),
              DefKind.Opaque =>
                match safety {
                  DefinitionSafety.Unsafe =>
                    KConstantInfo.Opaque(flatten_u64(lvls), ktyp, kval, 1),
                  _ =>
                    KConstantInfo.Opaque(flatten_u64(lvls), ktyp, kval, 0),
                },
              DefKind.Theorem =>
                KConstantInfo.Thm(flatten_u64(lvls), ktyp, kval),
            },
        },
    }
  }

  #[group=cold3] fn convert_axiom(a: Axiom, ctx: ConvertCtx) -> KConstantInfo {
    match ctx {
      ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs) =>
        match a {
          Axiom.Mk(is_unsafe, lvls, typ) =>
            let ktyp = convert_expr(typ, sharing, ref_idxs, recur_idxs, lit_blobs, univs);
            KConstantInfo.Axiom(flatten_u64(lvls), ktyp, is_unsafe),
        },
    }
  }

  #[group=cold3] fn convert_quotient(q: Quotient, ctx: ConvertCtx) -> KConstantInfo {
    match ctx {
      ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs) =>
        match q {
          Quotient.Mk(kind, lvls, typ) =>
            let ktyp = convert_expr(typ, sharing, ref_idxs, recur_idxs, lit_blobs, univs);
            KConstantInfo.Quot(flatten_u64(lvls), ktyp, kind),
        },
    }
  }

  #[group=cold6] fn convert_recursor(r: Recursor, ctx: ConvertCtx, rule_ctor_idxs: List‹G›,
                      block_addr: Addr) -> KConstantInfo {
    match ctx {
      ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs) =>
        match r {
          Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, typ, rules) =>
            let ktyp = convert_expr(typ, sharing, ref_idxs, recur_idxs, lit_blobs, univs);
            let krules = convert_rules(rules, rule_ctor_idxs, ctx);
            KConstantInfo.Rec(
              flatten_u64(lvls), ktyp, flatten_u64(params), flatten_u64(indices),
              flatten_u64(motives), flatten_u64(minors),
              krules, k, is_unsafe, block_addr),
        },
    }
  }

  #[group=cold5] fn convert_inductive(ind: Inductive, ctx: ConvertCtx, ctor_idxs: List‹G›,
                       block_addr: Addr) -> KConstantInfo {
    match ctx {
      ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs) =>
        match ind {
          Inductive.Mk(is_unsafe, lvls, params, indices, typ, _) =>
            let ktyp = convert_expr(typ, sharing, ref_idxs, recur_idxs, lit_blobs, univs);
            KConstantInfo.Induct(
              flatten_u64(lvls), ktyp, flatten_u64(params), flatten_u64(indices),
              ctor_idxs, is_unsafe, block_addr),
        },
    }
  }

  #[group=cold5] fn convert_constructor(c: Constructor, ctx: ConvertCtx, induct_idx: G) -> KConstantInfo {
    match ctx {
      ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs) =>
        match c {
          Constructor.Mk(is_unsafe, lvls, cidx, params, fields, typ) =>
            let ktyp = convert_expr(typ, sharing, ref_idxs, recur_idxs, lit_blobs, univs);
            KConstantInfo.Ctor(
              flatten_u64(lvls), ktyp, induct_idx, flatten_u64(cidx),
              flatten_u64(params), flatten_u64(fields), is_unsafe),
        },
    }
  }

  -- ============================================================================
  -- Top-level conversion
  -- ============================================================================

  -- Convert a single resolved input to a KConstantInfo. Takes &ConvertInput
  -- (pointer) so the per-row input width is one G column, not the full
  -- ConvertInput union width.
  #[group=cold6] fn convert_one(input: &ConvertInput) -> KConstantInfo {
    match load(input) {
      ConvertInput.Mk(ctx, kind) =>
        match kind {
          ConvertKind.CKDefn(d, hint) => convert_definition(d, ctx, hint),
          ConvertKind.CKAxio(a) => convert_axiom(a, ctx),
          ConvertKind.CKQuot(q) => convert_quotient(q, ctx),
          ConvertKind.CKRecr(r, rule_ctor_idxs, block_addr) =>
            convert_recursor(r, ctx, rule_ctor_idxs, block_addr),
          ConvertKind.CKIndc(ind, ctor_idxs, block_addr) => convert_inductive(ind, ctx, ctor_idxs, block_addr),
          ConvertKind.CKCtor(c, induct_idx) => convert_constructor(c, ctx, induct_idx),
        },
    }
  }

  -- Convert a list of resolved inputs to a List‹&KConstantInfo›
  #[group=cold4] fn convert_all(inputs: List‹&ConvertInput›) -> List‹&KConstantInfo› {
    match load(inputs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(input, rest) =>
        let ci = convert_one(input);
        store(ListNode.Cons(store(ci), convert_all(rest))),
    }
  }
⟧

end IxVM

end
