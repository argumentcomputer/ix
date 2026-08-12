module
public import Ix.Aiur.Meta

public section

namespace IxVM

def convert := ⟦
  -- ============================================================================
  -- Convert — addr-first Ixon → KExpr / KConstantInfo
  --
  -- Ixon encodes references as indices into a constant's own side tables
  -- (`refs`, recursor tables, literal blobs). Conversion resolves each
  -- index to the address it names, so nothing downstream carries an
  -- index or needs a table to interpret it:
  --
  -- - Expr.Ref(ref_idx, univs)  → Const(refs[ref_idx], levels)
  -- - Expr.Prj(type_idx, ...)   → Proj(refs[type_idx], ...)
  -- - Expr.Str/Nat(blob_idx)    → Lit(load_verified_blob(refs[blob_idx]))
  -- - Expr.Rec(rec_idx, univs)  → Const(recur_addrs[rec_idx], levels),
  --                                where recur_addrs holds one
  --                                projection wrapper addr per member of
  --                                the enclosing Muts block (built by
  --                                build_recur_addrs at get_ci entry).
  --
  -- `refs` is the Constant.refs list (List<Addr>) taken straight from
  -- Ixon. Addresses arriving here are already alpha-collapsed by the
  -- Lean→Ixon compile, so equal terms have equal addrs and the kernel
  -- never re-canonicalizes.
  -- ============================================================================

  -- Byte→limbs conversion for Nat literals.
  fn bytes_to_u64_limb(bytes: ByteStream, acc: U64, pos: G) -> U64 {
    match pos {
      8 => acc,
      _ =>
        match bytes {
          List.Nil => acc,
          List.Cons(__cell1) => let (byte, rest) = load(__cell1);
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

  fn skip_bytes(bytes: ByteStream, n: G) -> ByteStream {
    match n {
      0 => bytes,
      _ =>
        match bytes {
          List.Nil => List.Nil,
          List.Cons(__cell2) => let (_, rest) = load(__cell2); skip_bytes(rest, n - 1),
        },
    }
  }

  -- Convert a LE byte stream to KLimbs (list of U64, little-endian bignum).
  -- Reads 8 bytes per limb, zero-padding the last limb if needed.
  -- Strips trailing zero limbs for canonical form.
  fn bytes_to_limbs(bytes: ByteStream) -> KLimbs {
    let limb = bytes_to_u64_limb(bytes, [0u8; 8], 0);
    let rest_bytes = skip_bytes(bytes, 8);
    let rest_limbs = match rest_bytes {
      List.Nil => List.Nil,
      _ => bytes_to_limbs(rest_bytes),
    };
    match rest_limbs {
      List.Nil =>
        match u64_is_zero(limb) {
          1 => List.Nil,
          0 => List.Cons(store((limb, List.Nil))),
        },
      _ => List.Cons(store((limb, rest_limbs))),
    }
  }

  -- Universe conversion.
  fn convert_univ(u: &Univ) -> KLevel {
    match load(u) {
      Univ.Zero => store(KLevelNode.Zero),
      Univ.Succ(inner) => store(KLevelNode.Succ(convert_univ(inner))),
      Univ.Max(a, b) => store(KLevelNode.Max(convert_univ(a), convert_univ(b))),
      Univ.IMax(a, b) => store(KLevelNode.IMax(convert_univ(a), convert_univ(b))),
      Univ.Var(idx) => store(KLevelNode.Param(flatten_u64(idx))),
    }
  }

  fn convert_univ_idxs(idxs: List‹U64›, univs: List‹&Univ›) -> List‹KLevel› {
    match idxs {
      List.Nil => List.Nil,
      List.Cons(__cell3) => let (idx, rest) = load(__cell3);
        let u_ref = list_lookup(univs, flatten_u64(idx));
        List.Cons(store((convert_univ(u_ref), convert_univ_idxs(rest, univs)))),
    }
  }

  -- ============================================================================
  -- Expression conversion
  --
  -- Params:
  --   e:       the Ixon Expr node.
  --   sharing: Constant.sharing (for Expr.Share).
  --   refs:    Constant.refs — direct List<Addr>. Ref/Prj/Str/Nat all
  --            index into this. Under Ixon semantics, entries at Ref/Prj
  --            positions are const addrs; entries at Str/Nat positions
  --            are blob addrs.
  --   univs:   Constant.univs.
  --
  -- Recur handling deferred to  — asserts unreachable for /.
  -- ============================================================================
  fn convert_expr(
    e: &Expr,
    sharing: List‹&Expr›,
    refs: List‹Addr›,
    recur_addrs: List‹Addr›,
    univs: List‹&Univ›
  ) -> KExpr {
    match load(e) {
      Expr.Srt(univ_idx) =>
        let u_ref = list_lookup(univs, flatten_u64(univ_idx));
        store(KExprNode.Srt(convert_univ(u_ref))),

      Expr.Var(idx) =>
        store(KExprNode.BVar(flatten_u64(idx))),

      Expr.Ref(ref_idx, univ_idxs) =>
        let ref_addr = list_lookup(refs, flatten_u64(ref_idx));
        let levels = convert_univ_idxs(univ_idxs, univs);
        store(KExprNode.Const(ref_addr, levels)),

      Expr.Rec(rec_idx, univ_idxs) =>
        -- Rec resolves to a member of the enclosing Muts block.
        -- `recur_addrs` = projection wrapper addr per member,
        -- precomputed by build_recur_addrs at get_ci entry.
        let ref_addr = list_lookup(recur_addrs, flatten_u64(rec_idx));
        let levels = convert_univ_idxs(univ_idxs, univs);
        store(KExprNode.Const(ref_addr, levels)),

      Expr.Prj(type_ref_idx, field_idx, inner) =>
        let type_addr = list_lookup(refs, flatten_u64(type_ref_idx));
        store(KExprNode.Proj(
          type_addr,
          flatten_u64(field_idx),
          convert_expr(inner, sharing, refs, recur_addrs, univs))),

      Expr.Str(blob_ref_idx) =>
        let blob_addr = list_lookup(refs, flatten_u64(blob_ref_idx));
        let bs = load_verified_blob(blob_addr);
        -- The bytes are hash-bound to `blob_addr`, but nothing else on
        -- this path inspects them: `k_infer_lit` types a `KLiteral.Str`
        -- as `String` outright. Validate here, mirroring the reference
        -- kernels' `String::from_utf8` at ingress, or a literal that is
        -- never decoded typechecks as a `String` with no Lean
        -- counterpart.
        utf8_validate(bs);
        store(KExprNode.Lit(KLiteral.Str(bs))),

      Expr.Nat(blob_ref_idx) =>
        let blob_addr = list_lookup(refs, flatten_u64(blob_ref_idx));
        let bs = load_verified_blob(blob_addr);
        let limbs = bytes_to_limbs(bs);
        store(KExprNode.Lit(KLiteral.Nat(limbs))),

      Expr.App(f, a) =>
        store(KExprNode.App(
          convert_expr(f, sharing, refs, recur_addrs, univs),
          convert_expr(a, sharing, refs, recur_addrs, univs))),

      Expr.Lam(ty, body) =>
        store(KExprNode.Lam(
          convert_expr(ty, sharing, refs, recur_addrs, univs),
          convert_expr(body, sharing, refs, recur_addrs, univs))),

      Expr.All(ty, body) =>
        store(KExprNode.Forall(
          convert_expr(ty, sharing, refs, recur_addrs, univs),
          convert_expr(body, sharing, refs, recur_addrs, univs))),

      Expr.Let(_, ty, val, body) =>
        store(KExprNode.Let(
          convert_expr(ty, sharing, refs, recur_addrs, univs),
          convert_expr(val, sharing, refs, recur_addrs, univs),
          convert_expr(body, sharing, refs, recur_addrs, univs))),

      Expr.Share(idx) =>
        let List.Cons(__lcell1001) = list_drop(sharing, flatten_u64(idx)); let (e, _) = load(__lcell1001);
        convert_expr(e, sharing, refs, recur_addrs, univs),
    }
  }

  -- ============================================================================
  -- Constant conversion — one KConstantInfo per Ixon Constant.
  --
  -- / scope: Defn, Axiom, Quot only. Muts/IPrj/CPrj/RPrj/DPrj
  -- (inductive/recursor/projection) added here.2.
  -- ============================================================================
  fn convert_definition(d: Definition, sharing: List‹&Expr›,
                            refs: List‹Addr›, recur_addrs: List‹Addr›,
                            univs: List‹&Univ›, hint: G) -> KConstantInfo {
    match d {
      Definition.Mk(kind, safety, lvls, typ, value) =>
        let ktyp = convert_expr(typ, sharing, refs, recur_addrs, univs);
        let kval = convert_expr(value, sharing, refs, recur_addrs, univs);
        let nlvls = flatten_u64(lvls);
        match kind {
          DefKind.Definition =>
            KConstantInfo.Defn(nlvls, ktyp, kval, safety, hint),
          DefKind.Opaque =>
            let is_unsafe = match safety { DefinitionSafety.Unsafe => 1, _ => 0, };
            KConstantInfo.Opaque(nlvls, ktyp, kval, is_unsafe),
          DefKind.Theorem =>
            KConstantInfo.Thm(nlvls, ktyp, kval),
        },
    }
  }

  fn convert_axiom(a: Axiom, sharing: List‹&Expr›,
                       refs: List‹Addr›, recur_addrs: List‹Addr›,
                       univs: List‹&Univ›) -> KConstantInfo {
    match a {
      Axiom.Mk(is_unsafe, lvls, typ) =>
        let ktyp = convert_expr(typ, sharing, refs, recur_addrs, univs);
        KConstantInfo.Axiom(flatten_u64(lvls), ktyp, is_unsafe),
    }
  }

  fn convert_quotient(q: Quotient, sharing: List‹&Expr›,
                          refs: List‹Addr›, recur_addrs: List‹Addr›,
                          univs: List‹&Univ›) -> KConstantInfo {
    match q {
      Quotient.Mk(kind, lvls, typ) =>
        let ktyp = convert_expr(typ, sharing, refs, recur_addrs, univs);
        KConstantInfo.Quot(flatten_u64(lvls), ktyp, kind),
    }
  }

  -- Count ctors in Inductive.ctors list.
  fn count_ctors(cs: List‹Constructor›) -> G {
    match cs {
      List.Nil => 0,
      List.Cons(__cell4) => let (_, rest) = load(__cell4); count_ctors(rest) + 1,
    }
  }

  -- Look up Constructor at cidx in Inductive.ctors.
  fn ctor_at(cs: List‹Constructor›, cidx: G) -> Constructor {
    match cs {
      List.Cons(__cell5) => let (c, rest) = load(__cell5);
        match cidx {
          0 => c,
          _ => ctor_at(rest, cidx - 1),
        },
    }
  }

  fn convert_inductive(ind: Inductive, block_addr: Addr, ind_idx: G,
                           sharing: List‹&Expr›, refs: List‹Addr›,
                           recur_addrs: List‹Addr›,
                           univs: List‹&Univ›) -> KConstantInfo {
    match ind {
      Inductive.Mk(is_unsafe, lvls, params, indices, typ, ctors) =>
        let ktyp = convert_expr(typ, sharing, refs, recur_addrs, univs);
        KConstantInfo.Induct(
          flatten_u64(lvls), ktyp,
          flatten_u64(params), flatten_u64(indices),
          count_ctors(ctors), is_unsafe,
          block_addr, ind_idx),
    }
  }

  fn convert_constructor(c: Constructor, block_addr: Addr, ind_idx: G,
                             sharing: List‹&Expr›, refs: List‹Addr›,
                             recur_addrs: List‹Addr›,
                             univs: List‹&Univ›) -> KConstantInfo {
    match c {
      Constructor.Mk(is_unsafe, lvls, cidx, params, fields, typ) =>
        let ktyp = convert_expr(typ, sharing, refs, recur_addrs, univs);
        KConstantInfo.Ctor(
          flatten_u64(lvls), ktyp,
          block_addr, ind_idx, flatten_u64(cidx),
          flatten_u64(params), flatten_u64(fields), is_unsafe),
    }
  }

  fn convert_rec_rules(rs: List‹RecursorRule›, sharing: List‹&Expr›,
                           refs: List‹Addr›, recur_addrs: List‹Addr›,
                           univs: List‹&Univ›, cidx: G) -> List‹KRecRule› {
    match rs {
      List.Nil =>
        List.Nil,
      List.Cons(__cell6) => let (r, rest) = load(__cell6);
        match r {
          RecursorRule.Mk(fields, rhs) =>
            let krhs = convert_expr(rhs, sharing, refs, recur_addrs, univs);
            List.Cons(store((
              KRecRule.Mk(cidx, flatten_u64(fields), krhs),
              convert_rec_rules(rest, sharing, refs, recur_addrs, univs, cidx + 1)))),
        },
    }
  }

  fn convert_recursor(r: Recursor, block_addr: Addr, rec_idx: G,
                          sharing: List‹&Expr›, refs: List‹Addr›,
                          recur_addrs: List‹Addr›,
                          univs: List‹&Univ›) -> KConstantInfo {
    match r {
      Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, typ, rules) =>
        let ktyp = convert_expr(typ, sharing, refs, recur_addrs, univs);
        let krules = convert_rec_rules(rules, sharing, refs, recur_addrs, univs, 0);
        KConstantInfo.Rec(
          flatten_u64(lvls), ktyp,
          flatten_u64(params), flatten_u64(indices),
          flatten_u64(motives), flatten_u64(minors),
          krules, k, is_unsafe,
          block_addr, rec_idx),
    }
  }
⟧

end IxVM

end
