module
public import Ix.Aiur.Meta
public import Ix.IxVM.Kernel.Whnf

public section

namespace IxVM

/-- Recursive normalization using the kernel's existing WHNF rules. Output
definitions use ordinary constant transport and retain the input's type. -/
def eval := ⟦
  fn eval_nf(rc: RoleCtx, e: KExpr, types: List‹KExpr›) -> KExpr {
    let w = whnf(rc, e, types);
    match load(w) {
      KExprNode.Lam(t, b) =>
        let nt = eval_nf(rc, t, types);
        store(KExprNode.Lam(nt, eval_nf(rc, b, store(ListNode.Cons(t, types))))),
      KExprNode.Forall(t, b) =>
        let nt = eval_nf(rc, t, types);
        store(KExprNode.Forall(nt, eval_nf(rc, b, store(ListNode.Cons(t, types))))),
      _ => eval_nf_spine(rc, w, types),
    }
  }

  -- Preserve the head WHNF selected for the whole application. Unfolding
  -- an isolated primitive head would destroy compact stuck Nat forms.
  fn eval_nf_spine(rc: RoleCtx, e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.App(f, a) =>
        store(KExprNode.App(eval_nf_spine(rc, f, types), eval_nf(rc, a, types))),
      KExprNode.Proj(addr, i, e) =>
        store(KExprNode.Proj(addr, i, eval_nf(rc, e, types))),
      _ => e,
    }
  }

  fn eval_body(input: Addr) -> (G, KExpr, KExpr) {
    let ci = load(get_ci(input));
    assert_eq!(is_unsafe_ci(ci), 0, "Eval: unsafe or partial input");
    match ci {
      KConstantInfo.Defn(n, ty, value, _, _) => (n, ty, value),
      KConstantInfo.Thm(n, ty, value) => (n, ty, value),
      KConstantInfo.Opaque(n, ty, value, _) => (n, ty, value),
    }
  }

  fn eval_output(output: Addr, nlvls: G, input_type: KExpr) -> KExpr {
    let Constant.Mk(info, sharing, refs, univs) = load_verified_constant(output);
    let ConstantInfo.Defn(defn) = info;
    let Definition.Mk(kind, safety, lvls, ty, value) = defn;
    assert_eq!(kind, DefKind.Definition, "Eval: output must be a definition");
    assert_eq!(safety, DefinitionSafety.Safe, "Eval: unsafe or partial output");
    assert_eq!(flatten_u64(lvls), nlvls, "Eval: universe parameter count mismatch");
    let no_recur = store(ListNode.Nil);
    let output_type = convert_expr(ty, sharing, refs, no_recur, univs);
    assert_eq!(output_type, input_type, "Eval: output type does not match input");
    convert_expr(value, sharing, refs, no_recur, univs)
  }

  fn run_eval(rc: RoleCtx, input: Addr, output: Addr, asm: Option‹Addr›) {
    -- Assumptions waive dependency checks, never the subject check.
    run_check(rc, input);
    match asm {
      Option.None => run_check_transitive(rc, input),
      Option.Some(r) =>
        let asm_set = addr_set_build(load_assumption_tree(r), RBTreeMap.Nil);
        assert_eq!(addr_set_member(input, asm_set), 0, "Eval: input is an assumption");
        env_walk(rc, input, RBTreeMap.Nil, asm_set, 0),
    };
    let (nlvls, ty, body) = eval_body(input);
    let expected = eval_output(output, nlvls, ty);
    let result = eval_nf(rc, body, store(ListNode.Nil));
    -- Hash-consed pointers compare decoded, erased terms structurally.
    -- Neither the proposed result nor its type is normalized here. Output
    -- typing follows from the checked input and type-preserving reduction.
    assert_eq!(result, expected, "Eval: result does not match output");
    ()
  }
⟧

end IxVM

end
