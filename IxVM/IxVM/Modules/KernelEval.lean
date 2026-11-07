import Aiur.Modules.Frontend

/-! # IxVM module `KernelEval`

Evaluation claims (`run_eval`).

Formal Aiur source, written as Lean syntax (`aiur⟦ … ⟧`). `IxVM.source`
(`IxVM/IxVM/Program.lean`) composes the modules. -/

namespace IxVM.Source

def kernelEval : Aiur.Modules.Program Nat := aiur⟦
module KernelEval {
  fn eval_nf(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let w = KernelWhnf::whnf(rc, e, types);
      match (*(w)) {
        KernelTypes::KExprNode::Lam(t, b) => {
          let nt = eval_nf(rc, t, types);
          (&(KernelTypes::KExprNode::Lam(nt, eval_nf(rc, b, (&(Lists::Node::Cons(t, types))))))) } ,
        KernelTypes::KExprNode::Forall(t, b) => {
          let nt = eval_nf(rc, t, types);
          (&(KernelTypes::KExprNode::Forall(nt, eval_nf(rc, b, (&(Lists::Node::Cons(t, types))))))) } ,
        _ => {  eval_nf_spine(rc, w, types) } ,
      }
    }

  fn eval_nf_spine(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::App(f, a) => {
          (&(KernelTypes::KExprNode::App(eval_nf_spine(rc, f, types), eval_nf(rc, a, types)))) } ,
        KernelTypes::KExprNode::Proj(addr, i, e) => {
          (&(KernelTypes::KExprNode::Proj(addr, i, eval_nf(rc, e, types)))) } ,
        _ => {  e } ,
      }
    }

  fn eval_body(input: Bytes::AddressRef) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      let ci = (*(Ingress::get_ci(input)));
      assert_eq!(KernelCheck::is_unsafe_ci(ci), 0, "Eval: unsafe or partial input");
      match ci {
        KernelTypes::KConstantInfo::Defn(n, ty, value, _, _) => {  (n, ty, value) } ,
        KernelTypes::KConstantInfo::Thm(n, ty, value) => {  (n, ty, value) } ,
        KernelTypes::KConstantInfo::Opaque(n, ty, value, _) => {  (n, ty, value) } ,
      }
    }

  fn eval_output(output: Bytes::AddressRef, nlvls: Field, input_type: KernelTypes::KExpr) -> KernelTypes::KExpr {
      let Ixon::Constant::Mk(info, sharing, refs, univs) = Ingress::load_verified_constant(output);
      let Ixon::ConstantInfo::Defn(defn) = info;
      let Ixon::Definition::Mk(kind, safety, lvls, ty, value) = defn;
      assert_eq!(kind, Ixon::DefKind::Definition, "Eval: output must be a definition");
      assert_eq!(safety, Ixon::DefinitionSafety::Safe, "Eval: unsafe or partial output");
      assert_eq!(UInt64::to_field(lvls), nlvls, "Eval: universe parameter count mismatch");
      let no_recur = (&(Lists::Node::Nil));
      let output_type = Convert::convert_expr(ty, sharing, refs, no_recur, univs);
      assert_eq!(KernelCheck::kexpr_struct_eq(output_type, input_type), 1, "Eval: output type does not match input");
      Convert::convert_expr(value, sharing, refs, no_recur, univs)
    }

  fn run_eval(rc: KernelRoles::RoleCtx, input: Bytes::AddressRef, output: Bytes::AddressRef, asm: Options::Option<Bytes::AddressRef>) -> () {

      KernelClaim::run_check(rc, input);
      match asm {
        Options::Option::None => {  KernelClaim::run_check_transitive(rc, input) } ,
        Options::Option::Some(r) => {
          let asm_set = KernelClaim::addr_set_build(KernelClaim::load_assumption_tree(r), RBTreeMap::RBTreeMap::Nil);
          assert_eq!(KernelClaim::addr_set_member(input, asm_set), 0, "Eval: input is an assumption");
          KernelClaim::env_walk(rc, input, RBTreeMap::RBTreeMap::Nil, asm_set, 0) } ,
      };
      let (nlvls, ty, body) = eval_body(input);
      let expected = eval_output(output, nlvls, ty);
      let result = eval_nf(rc, body, (&(Lists::Node::Nil)));

      assert_eq!(KernelCheck::kexpr_struct_eq(result, expected), 1, "Eval: result does not match output");
      ()
    }
}
⟧

end IxVM.Source
