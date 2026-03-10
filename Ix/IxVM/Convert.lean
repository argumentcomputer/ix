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
  -- (sharing, ref_idxs, recur_idxs, lit_vals, univs)
  --
  -- sharing:    the constant's sharing array (for Expr.Share expansion)
  -- ref_idxs:   maps ref array index -> kernel constant list index
  -- recur_idxs: maps recur index -> kernel constant list index
  -- lit_vals:   maps blob ref index -> decoded literal value
  -- univs:      the constant's universe array
  enum ConvertCtx {
    Mk(&ExprList, &U64List, &U64List, &U64List, &UnivList)
  }

  -- What to convert, with kind-specific auxiliary data
  enum ConvertKind {
    CKDefn(Definition, KHints),
    CKAxio(Axiom),
    CKQuot(Quotient),
    CKRecr(Recursor, &KU64List),
    CKIndc(Inductive, &KU64List),
    CKCtor(Constructor, [G; 8])
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

  fn u64_list_lookup(list: U64List, idx: [G; 8]) -> [G; 8] {
    match list {
      U64List.Cons(v, &rest) =>
        let z = u64_is_zero(idx);
        match z {
          1 => v,
          0 => u64_list_lookup(rest, relaxed_u64_pred(idx)),
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
      Univ.Zero => KLevel.LZero,
      Univ.Succ(&inner) => KLevel.LSucc(store(convert_univ(inner))),
      Univ.Max(&a, &b) => KLevel.LMax(store(convert_univ(a)), store(convert_univ(b))),
      Univ.IMax(&a, &b) => KLevel.LIMax(store(convert_univ(a)), store(convert_univ(b))),
      Univ.Var(idx) => KLevel.LParam(idx),
    }
  }

  -- Resolve a list of universe indices to a KLevelList
  fn convert_univ_idxs(idxs: U64List, univs: UnivList) -> KLevelList {
    match idxs {
      U64List.Nil => KLevelList.LLNil,
      U64List.Cons(idx, &rest) =>
        let u = univ_list_lookup(univs, idx);
        KLevelList.LLCons(store(convert_univ(u)), store(convert_univ_idxs(rest, univs))),
    }
  }

  -- ============================================================================
  -- Expression conversion: Ixon Expr -> KExpr
  -- ============================================================================

  fn convert_expr(
    e: Expr,
    sharing: ExprList,
    ref_idxs: U64List,
    recur_idxs: U64List,
    lit_vals: U64List,
    univs: UnivList
  ) -> KExpr {
    match e {
      Expr.Srt(univ_idx) =>
        let u = univ_list_lookup(univs, univ_idx);
        KExpr.ESort(store(convert_univ(u))),

      Expr.Var(idx) =>
        KExpr.EBVar(idx),

      Expr.Ref(ref_idx, &univ_idxs) =>
        let const_idx = u64_list_lookup(ref_idxs, ref_idx);
        let levels = convert_univ_idxs(univ_idxs, univs);
        KExpr.EConst(const_idx, store(levels)),

      Expr.Rec(rec_idx, &univ_idxs) =>
        let const_idx = u64_list_lookup(recur_idxs, rec_idx);
        let levels = convert_univ_idxs(univ_idxs, univs);
        KExpr.EConst(const_idx, store(levels)),

      Expr.Prj(type_ref_idx, field_idx, &inner) =>
        let type_idx = u64_list_lookup(ref_idxs, type_ref_idx);
        KExpr.EProj(
          type_idx,
          field_idx,
          store(convert_expr(inner, sharing, ref_idxs, recur_idxs, lit_vals, univs))),

      Expr.Str(blob_ref_idx) =>
        let val = u64_list_lookup(lit_vals, blob_ref_idx);
        KExpr.ELit(KLiteral.LitStr(val)),

      Expr.Nat(blob_ref_idx) =>
        let val = u64_list_lookup(lit_vals, blob_ref_idx);
        KExpr.ELit(KLiteral.LitNat(val)),

      Expr.App(&f, &a) =>
        KExpr.EApp(
          store(convert_expr(f, sharing, ref_idxs, recur_idxs, lit_vals, univs)),
          store(convert_expr(a, sharing, ref_idxs, recur_idxs, lit_vals, univs))),

      Expr.Lam(&ty, &body) =>
        KExpr.ELam(
          store(convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_vals, univs)),
          store(convert_expr(body, sharing, ref_idxs, recur_idxs, lit_vals, univs))),

      Expr.All(&ty, &body) =>
        KExpr.EForallE(
          store(convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_vals, univs)),
          store(convert_expr(body, sharing, ref_idxs, recur_idxs, lit_vals, univs))),

      Expr.Let(_, &ty, &val, &body) =>
        KExpr.ELetE(
          store(convert_expr(ty, sharing, ref_idxs, recur_idxs, lit_vals, univs)),
          store(convert_expr(val, sharing, ref_idxs, recur_idxs, lit_vals, univs)),
          store(convert_expr(body, sharing, ref_idxs, recur_idxs, lit_vals, univs))),

      Expr.Share(idx) =>
        let shared = expr_list_lookup(sharing, idx);
        convert_expr(shared, sharing, ref_idxs, recur_idxs, lit_vals, univs),
    }
  }

  -- Shorthand: convert an expression using a ConvertCtx
  fn ctx_convert_expr(e: Expr, ctx: ConvertCtx) -> KExpr {
    match ctx {
      ConvertCtx.Mk(&sharing, &ref_idxs, &recur_idxs, &lit_vals, &univs) =>
        convert_expr(e, sharing, ref_idxs, recur_idxs, lit_vals, univs),
    }
  }

  -- ============================================================================
  -- Enum conversions
  -- ============================================================================

  fn convert_safety(s: DefinitionSafety) -> KSafety {
    match s {
      DefinitionSafety.Unsafe => KSafety.SUnsafe,
      DefinitionSafety.Safe => KSafety.SSafe,
      DefinitionSafety.Partial => KSafety.SPartial,
    }
  }

  fn convert_quot_kind(k: QuotKind) -> KQuotKind {
    match k {
      QuotKind.Typ => KQuotKind.QType,
      QuotKind.Ctor => KQuotKind.QCtor,
      QuotKind.Lift => KQuotKind.QLift,
      QuotKind.Ind => KQuotKind.QInd,
    }
  }

  -- ============================================================================
  -- Recursor rule conversion
  -- ============================================================================

  -- Convert Ixon RecursorRuleList to KRecRuleList.
  -- rule_ctor_idxs provides the kernel constant index for each rule's constructor.
  fn convert_rules(
    rules: RecursorRuleList,
    rule_ctor_idxs: KU64List,
    ctx: ConvertCtx
  ) -> KRecRuleList {
    match rules {
      RecursorRuleList.Nil => KRecRuleList.RRNil,
      RecursorRuleList.Cons(rule, &rest_rules) =>
        match rule {
          RecursorRule.Mk(nfields, &rhs) =>
            match rule_ctor_idxs {
              KU64List.KUCons(ctor_idx, &rest_ctor_idxs) =>
                let krhs = ctx_convert_expr(rhs, ctx);
                let krule = KRecRule.RRMk(ctor_idx, nfields, store(krhs));
                KRecRuleList.RRCons(
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
            KConstantInfo.CIDefn(lvls, store(ktyp), store(kval), hints, convert_safety(safety)),
          DefKind.Opaque =>
            match safety {
              DefinitionSafety.Unsafe =>
                KConstantInfo.CIOpaque(lvls, store(ktyp), store(kval), 1),
              _ =>
                KConstantInfo.CIOpaque(lvls, store(ktyp), store(kval), 0),
            },
          DefKind.Theorem =>
            KConstantInfo.CIThm(lvls, store(ktyp), store(kval)),
        },
    }
  }

  fn convert_axiom(a: Axiom, ctx: ConvertCtx) -> KConstantInfo {
    match a {
      Axiom.Mk(is_unsafe, lvls, &typ) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        KConstantInfo.CIAxiom(lvls, store(ktyp), is_unsafe),
    }
  }

  fn convert_quotient(q: Quotient, ctx: ConvertCtx) -> KConstantInfo {
    match q {
      Quotient.Mk(kind, lvls, &typ) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        KConstantInfo.CIQuot(lvls, store(ktyp), convert_quot_kind(kind)),
    }
  }

  fn convert_recursor(r: Recursor, ctx: ConvertCtx, rule_ctor_idxs: KU64List) -> KConstantInfo {
    match r {
      Recursor.Mk(k, is_unsafe, lvls, params, indices, motives, minors, &typ, &rules) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        let krules = convert_rules(rules, rule_ctor_idxs, ctx);
        KConstantInfo.CIRec(
          lvls, store(ktyp), params, indices, motives, minors,
          store(krules), k, is_unsafe),
    }
  }

  fn convert_inductive(ind: Inductive, ctx: ConvertCtx, ctor_idxs: KU64List) -> KConstantInfo {
    match ind {
      Inductive.Mk(is_rec, is_refl, is_unsafe, lvls, params, indices, _, &typ, _) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        KConstantInfo.CIInduct(
          lvls, store(ktyp), params, indices,
          store(ctor_idxs), is_rec, is_refl, is_unsafe),
    }
  }

  fn convert_constructor(c: Constructor, ctx: ConvertCtx, induct_idx: [G; 8]) -> KConstantInfo {
    match c {
      Constructor.Mk(is_unsafe, lvls, cidx, params, fields, &typ) =>
        let ktyp = ctx_convert_expr(typ, ctx);
        KConstantInfo.CICtor(
          lvls, store(ktyp), induct_idx, cidx, params, fields, is_unsafe),
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
      ConvertInputList.Nil => KConstList.CLNil,
      ConvertInputList.Cons(&input, &rest) =>
        let ci = convert_one(input);
        KConstList.CLCons(store(ci), store(convert_all(rest))),
    }
  }
⟧

end IxVM

end
