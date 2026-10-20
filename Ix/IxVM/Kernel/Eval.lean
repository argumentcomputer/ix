module
public import Ix.Aiur.Meta
public import Ix.IxVM.Kernel.Whnf

public section

namespace IxVM

/-- Recursive WHNF normalization in erased Lean semantics. Unlike def-eq,
evaluation never reduces the expected output or uses proof irrelevance to
accept a different result. Constants left opaque by WHNF remain opaque. -/
def eval := ⟦
  fn eval_nf(e: KExpr, types: List‹KExpr›) -> KExpr {
    let w = whnf(e, types);
    match load(w) {
      KExprNode.Lam(t, b) =>
        let nt = eval_nf(t, types);
        store(KExprNode.Lam(nt, eval_nf(b, store(ListNode.Cons(t, types))))),
      KExprNode.Forall(t, b) =>
        let nt = eval_nf(t, types);
        store(KExprNode.Forall(nt, eval_nf(b, store(ListNode.Cons(t, types))))),
      _ => eval_nf_spine(w, types),
    }
  }

  -- WHNF has already reduced the entire application. Preserve its head and
  -- normalize arguments, rather than delta-unfolding an isolated primitive
  -- head (which would destroy the compact stuck Nat forms used by WHNF).
  fn eval_nf_spine(e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.App(f, a) =>
        store(KExprNode.App(eval_nf_spine(f, types), eval_nf(a, types))),
      KExprNode.Proj(addr, i, e) =>
        store(KExprNode.Proj(addr, i, eval_nf(e, types))),
      _ => e,
    }
  }

  -- Structural validation of ExprObj's tables BEFORE conversion: dead
  -- entries must not hide a cycle, Rec, or an invalid table index.
  fn eval_obj_index(i: U64, bound: G) {
    assert_eq!(u32_less_than(flatten_u64(i), bound), 1,
      "ExprObj: table index out of bounds");
    ()
  }

  fn eval_obj_levels(us: List‹U64›, bound: G) {
    match load(us) {
      ListNode.Nil => (),
      ListNode.Cons(u, rest) =>
        eval_obj_index(u, bound);
        eval_obj_levels(rest, bound),
    }
  }

  fn eval_obj_expr(e: &Expr, shares: List‹G›, nr: G, nu: G) -> G {
    match load(e) {
      Expr.Srt(i) => eval_obj_index(i, nu); 0,
      Expr.Var(i) =>
        let n = flatten_u64(i);
        -- Keep loose-variable bounds within the kernel's u32 index domain.
        assert_eq!(u32_less_than(n, 0xffffffff), 1, "ExprObj: variable index too large");
        n + 1,
      Expr.Ref(i, us) =>
        eval_obj_index(i, nr);
        eval_obj_levels(us, nu);
        0,
      Expr.Rec(_, _) =>
        assert_eq!(0, 1, "ExprObj: block-local Rec is forbidden");
        0,
      Expr.Prj(i, _, inner) =>
        eval_obj_index(i, nr);
        eval_obj_expr(inner, shares, nr, nu),
      Expr.Str(i) => eval_obj_index(i, nr); 0,
      Expr.Nat(i) => eval_obj_index(i, nr); 0,
      Expr.App(f, a) =>
        lbr_max(eval_obj_expr(f, shares, nr, nu), eval_obj_expr(a, shares, nr, nu)),
      Expr.Lam(_, t, b) =>
        lbr_max(eval_obj_expr(t, shares, nr, nu), lbr_dec(eval_obj_expr(b, shares, nr, nu))),
      Expr.All(_, _, t, b) =>
        lbr_max(eval_obj_expr(t, shares, nr, nu), lbr_dec(eval_obj_expr(b, shares, nr, nu))),
      Expr.Let(_, t, v, b) =>
        lbr_max(lbr_max(eval_obj_expr(t, shares, nr, nu), eval_obj_expr(v, shares, nr, nu)),
          lbr_dec(eval_obj_expr(b, shares, nr, nu))),
      Expr.Share(i) =>
        eval_obj_index(i, list_length(shares));
        list_lookup(shares, flatten_u64(i)),
    }
  }

  fn eval_obj_sharing(es: List‹&Expr›, bounds: List‹G›, nr: G, nu: G) -> List‹G› {
    match load(es) {
      ListNode.Nil => bounds,
      ListNode.Cons(e, rest) =>
        let bound = eval_obj_expr(e, bounds, nr, nu);
        eval_obj_sharing(rest, list_snoc(bounds, bound), nr, nu),
    }
  }

  fn eval_obj_univs(us: List‹&Univ›, bound: G) {
    match load(us) {
      ListNode.Nil => (),
      ListNode.Cons(u, rest) =>
        validate_univ_params_seen(convert_univ(u), bound);
        eval_obj_univs(rest, bound),
    }
  }

  -- Channel 6 contains hash-bound ExprObj bytes (blob transport on the host).
  fn eval_output(addr: Addr, nlvls: G) -> KExpr {
    let raw = load(addr);
    let (idx, len) = io_get_info(6, raw);
    let bytes = read_finite_byte_stream(6, idx, len);
    verify_bytes_against(bytes, raw);
    let (obj, rest) = get_expr_obj(bytes);
    assert_eq!(load(rest), ListNode.Nil, "ExprObj: trailing bytes");
    let ExprObj.Mk(lvls, root, sharing, refs, univs) = obj;
    assert_eq!(flatten_u64(lvls), nlvls, "Eval: universe parameter count mismatch");
    eval_obj_univs(univs, nlvls);
    let nr = list_length(refs);
    let nu = list_length(univs);
    let bounds = eval_obj_sharing(sharing, store(ListNode.Nil), nr, nu);
    assert_eq!(eval_obj_expr(root, bounds, nr, nu), 0, "ExprObj: free term variable");
    convert_expr(root, sharing, refs, store(ListNode.Nil), univs)
  }

  fn eval_body(input: Addr) -> (G, KExpr) {
    let ci = load(get_ci(input));
    assert_eq!(is_unsafe_ci(ci), 0, "Eval: unsafe or partial input");
    match ci {
      KConstantInfo.Defn(n, _, value, _, _) => (n, value),
      KConstantInfo.Thm(n, _, value) => (n, value),
      KConstantInfo.Opaque(n, _, value, _) => (n, value),
    }
  }

  fn run_eval(input: Addr, output: Addr, asm: Option‹Addr›) {
    -- The subject must be checked even if a malicious assumption tree lists
    -- it. Assumptions waive dependency checks, never the subject check.
    run_check(input);
    match asm {
      Option.None => run_check_transitive(input),
      Option.Some(r) =>
        let asm_set = addr_set_build(load_assumption_tree(r), RBTreeMap.Nil);
        assert_eq!(addr_set_member(input, asm_set), 0, "Eval: input is an assumption");
        env_walk(input, RBTreeMap.Nil, asm_set, 0),
    };
    let (nlvls, body) = eval_body(input);
    let result = eval_nf(body, store(ListNode.Nil));
    let expected = eval_output(output, nlvls);
    -- Hash-consed KExpr pointers identify structural terms after table
    -- resolution and contract erasure. No output typechecking or def-eq.
    assert_eq!(result, expected, "Eval: result does not match output");
    ()
  }
⟧

end IxVM

end
