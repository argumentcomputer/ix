import Aiur.Modules.Function

/-! # IxVM module `KernelEval`

Evaluation claims (`run_eval`).

An `eval` claim checks its input as a `check` claim checks its target, then
compares the output's value with the input's normal form (`eval_nf`)
structurally, and its type with the input's. It then checks the output
declaration as a `check` claim would, under the claim's role context and
assumptions (`check_output`), so that the claim states that the output is
accepted without appealing to subject reduction: with an assumed dependency,
the input's normal form can be ill-typed.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelEval where

def eval_nf := aiur_fn⟦
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
⟧

def eval_nf_spine := aiur_fn⟦
  fn eval_nf_spine(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::App(f, a) => {
          (&(KernelTypes::KExprNode::App(eval_nf_spine(rc, f, types), eval_nf(rc, a, types)))) } ,
        KernelTypes::KExprNode::Proj(addr, i, e) => {
          (&(KernelTypes::KExprNode::Proj(addr, i, eval_nf(rc, e, types)))) } ,
        _ => {  e } ,
      }
    }
⟧

def eval_body := aiur_fn⟦
  fn eval_body(input: Bytes::AddressRef) -> (Field, KernelTypes::KExpr, KernelTypes::KExpr) {
      let ci = (*(Ingress::get_ci(input)));
      assert_eq!(KernelCheck::is_unsafe_ci(ci), 0, "Eval: unsafe or partial input");
      match ci {
        KernelTypes::KConstantInfo::Defn(n, ty, value, _, _) => {  (n, ty, value) } ,
        KernelTypes::KConstantInfo::Thm(n, ty, value) => {  (n, ty, value) } ,
        KernelTypes::KConstantInfo::Opaque(n, ty, value, _) => {  (n, ty, value) } ,
      }
    }
⟧

def eval_output := aiur_fn⟦
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
⟧

def run_eval := aiur_fn⟦
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
      check_output(rc, output, asm)
    }
⟧

def check_output := aiur_fn⟦
  fn check_output(rc: KernelRoles::RoleCtx, output: Bytes::AddressRef, asm: Options::Option<Bytes::AddressRef>) -> () {
      match asm {
        Options::Option::None => {  KernelClaim::run_check_transitive(rc, output) } ,
        Options::Option::Some(r) => {
          let asm_set = KernelClaim::addr_set_build(KernelClaim::load_assumption_tree(r), RBTreeMap::RBTreeMap::Nil);
          assert_eq!(KernelClaim::addr_set_member(output, asm_set), 0, "Eval: output is an assumption");
          KernelClaim::env_walk(rc, output, RBTreeMap::RBTreeMap::Nil, asm_set, 0) } ,
      }
    }
⟧

end

end IxVM
