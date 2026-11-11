import Aiur.Modules.Function

/-! # IxVM module `KernelCheck`

Declaration checking: scoping, universe parameters, inductives, constructors and recursors.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelCheck where

def is_unsafe_ci := aiur_fn⟦
  fn is_unsafe_ci(ci: KernelTypes::KConstantInfo) -> Field {
      match ci {
        KernelTypes::KConstantInfo::Axiom(_, _, u) => {  u } ,
        KernelTypes::KConstantInfo::Defn(_, _, _, s, _) => {
          match s {
            Ixon::DefinitionSafety::Safe => {  0 } ,
            _ => {  1 } ,
          } } ,
        KernelTypes::KConstantInfo::Thm(_, _, _) => {  0 } ,
        KernelTypes::KConstantInfo::Opaque(_, _, _, u) => {  u } ,
        KernelTypes::KConstantInfo::Quot(_, _, _) => {  0 } ,
        KernelTypes::KConstantInfo::Induct(_, _, _, _, _, u, _, _) => {  u } ,
        KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, _, _, u) => {  u } ,
        KernelTypes::KConstantInfo::Rec(_, _, _, _, _, _, _, _, u, _, _) => {  u } ,
      }
    }
⟧

def safe_refs_only := aiur_fn⟦
  fn safe_refs_only(e: KernelTypes::KExpr) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(_) => {  1 } ,
        KernelTypes::KExprNode::Srt(_) => {  1 } ,
        KernelTypes::KExprNode::Const(caddr, _) => {
          let ci = (*(Ingress::get_ci(caddr)));
          1 - is_unsafe_ci(ci) } ,
        KernelTypes::KExprNode::App(f, a) => {
          safe_refs_only(f) * safe_refs_only(a) } ,
        KernelTypes::KExprNode::Lam(t, b, _) => {
          safe_refs_only(t) * safe_refs_only(b) } ,
        KernelTypes::KExprNode::Forall(t, b, _) => {
          safe_refs_only(t) * safe_refs_only(b) } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          safe_refs_only(t) * safe_refs_only(v) * safe_refs_only(b) } ,
        KernelTypes::KExprNode::Lit(_) => {  1 } ,
        KernelTypes::KExprNode::Proj(_, _, e1) => {  safe_refs_only(e1) } ,
      }
    }
⟧

def assert_safety := aiur_fn⟦
  fn assert_safety(self_unsafe: Field, e: KernelTypes::KExpr) -> () {
      match self_unsafe {
        1 => {  () } ,
        _ => {
          assert_eq!(safe_refs_only(e), 1,
            "safe constant references an unsafe constant");
          () } ,
      }
    }
⟧

def validate_univ_params_seen := aiur_fn⟦
  fn validate_univ_params_seen(u: KernelTypes::KLevel, bound: Field) -> () {
      match (*(u)) {
        KernelTypes::KLevelNode::Zero => {  () } ,
        KernelTypes::KLevelNode::Succ(inner) => {  validate_univ_params_seen(inner, bound) } ,
        KernelTypes::KLevelNode::Max(a, b) => {
          validate_univ_params_seen(a, bound);
          validate_univ_params_seen(b, bound) } ,
        KernelTypes::KLevelNode::IMax(a, b) => {
          validate_univ_params_seen(a, bound);
          validate_univ_params_seen(b, bound) } ,
        KernelTypes::KLevelNode::Param(i) => {
          assert_eq!(UInt32::less_than_fields(i, bound), 1,
            "universe param index out of range");
          () } ,
      }
    }
⟧

def validate_univ_params_list := aiur_fn⟦
  fn validate_univ_params_list(lvls: Lists::List<KernelTypes::KLevel>, bound: Field) -> () {
      match (*(lvls)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(u, rest) => {
          validate_univ_params_seen(u, bound);
          validate_univ_params_list(rest, bound) } ,
      }
    }
⟧

def validate_expr_well_scoped := aiur_fn⟦
  fn validate_expr_well_scoped(e: KernelTypes::KExpr, depth: Field, bound: Field) -> () {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(i) => {
          assert_eq!(UInt32::less_than_fields(i, depth), 1,
            "loose bound variable: BVar index exceeds binder depth");
          () } ,
        KernelTypes::KExprNode::Srt(l) => {  validate_univ_params_seen(l, bound) } ,
        KernelTypes::KExprNode::Const(addr, lvls) => {
          let ci = (*(Ingress::get_ci(addr)));
          let expected = KernelInfer::const_num_lvls(ci);
          assert_eq!(Lists::length(lvls), expected,
            "Const applied to wrong number of universe levels");
          validate_univ_params_list(lvls, bound) } ,
        KernelTypes::KExprNode::App(f, a) => {
          validate_expr_well_scoped(f, depth, bound);
          validate_expr_well_scoped(a, depth, bound) } ,
        KernelTypes::KExprNode::Lam(t, b, l) => {
          validate_univ_params_seen(l, bound);
          validate_expr_well_scoped(t, depth, bound);
          validate_expr_well_scoped(b, depth + 1, bound) } ,
        KernelTypes::KExprNode::Forall(t, b, l) => {
          validate_univ_params_seen(l, bound);
          validate_expr_well_scoped(t, depth, bound);
          validate_expr_well_scoped(b, depth + 1, bound) } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          validate_expr_well_scoped(t, depth, bound);
          validate_expr_well_scoped(v, depth, bound);
          validate_expr_well_scoped(b, depth + 1, bound) } ,
        KernelTypes::KExprNode::Lit(_) => {  () } ,
        KernelTypes::KExprNode::Proj(_, _, e1) => {
          validate_expr_well_scoped(e1, depth, bound) } ,
      }
    }
⟧

def check_quot := aiur_fn⟦
  fn check_quot(rc: KernelRoles::RoleCtx, self_addr: Bytes::AddressRef, kind: Ixon::QuotKind) -> () {
      let r = match kind {
        Ixon::QuotKind::Typ => {  KernelRoleSpec::role_quot() } ,
        Ixon::QuotKind::Ctor => {  KernelRoleSpec::role_quot_mk() } ,
        Ixon::QuotKind::Lift => {  KernelRoleSpec::role_quot_lift() } ,
        Ixon::QuotKind::Ind => {  KernelRoleSpec::role_quot_ind() } ,
      };
      assert_eq!(KernelRoles::role_is(rc, self_addr, r), 1,
        "a quotient constant is not the binding's quotient role of its kind");
      ()
    }
⟧

def peel_n_foralls := aiur_fn⟦
  fn peel_n_foralls(e: KernelTypes::KExpr, n: Field) -> KernelTypes::KExpr {
      match n {
        0 => {  e } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::Forall(_, body, _) => {  peel_n_foralls(body, n - 1) } ,
          } } ,
      }
    }
⟧

def assert_lvls_are_params := aiur_fn⟦
  fn assert_lvls_are_params(lvls: Lists::List<KernelTypes::KLevel>, count: Field, idx: Field) -> () {
      match count {
        0 => {
          assert_eq!(Lists::length(lvls), 0,
            "more universe levels than the inductive declares");
          () } ,
        _ => {
          match (*(lvls)) {
            Lists::Node::Cons(l, rest) => {
              match (*(l)) {
                KernelTypes::KLevelNode::Param(i) => {
                  assert_eq!(i, idx,
                    "ctor return type: universe level is not Param(i) in order");
                  assert_lvls_are_params(rest, count - 1, idx + 1);
                  () } ,
              } } ,
          } } ,
      }
    }
⟧

def assert_first_args_are_param_bvars := aiur_fn⟦
  fn assert_first_args_are_param_bvars(args: Lists::List<KernelTypes::KExpr>,
                                              n_params: Field, n_fields: Field, i: Field) -> () {
      match n_params - i {
        0 => {  () } ,
        _ => {
          match (*(args)) {
            Lists::Node::Cons(arg, rest) => {
              match (*(arg)) {
                KernelTypes::KExprNode::BVar(j) => {
                  assert_eq!(j, ((n_fields + n_params) - 1) - i,
                    "ctor return type: param arg is not the expected param BVar");
                  assert_first_args_are_param_bvars(rest, n_params, n_fields, i + 1);
                  () } ,
              } } ,
          } } ,
      }
    }
⟧

def assert_return_head_is_parent := aiur_fn⟦
  fn assert_return_head_is_parent(caddr: Bytes::AddressRef, block_addr: Bytes::AddressRef,
                                         ind_idx: Field) -> () {
      let ci = (*(Ingress::get_ci(caddr)));
      match ci {
        KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, ba, ii) => {
          assert_eq!(Bytes::address_eq(ba, block_addr), 1,
            "ctor return head belongs to a different block");
          assert_eq!(ii, ind_idx,
            "ctor return head is a different member of the block");
          () } ,
      }
    }
⟧

def check_ctor_return_type := aiur_fn⟦
  fn check_ctor_return_type(ctor_ty: KernelTypes::KExpr, n_params: Field,
                                   n_indices: Field, n_fields: Field,
                                   ind_num_lvls: Field, block_addr: Bytes::AddressRef,
                                   ind_idx: Field) -> () {
      let body = peel_n_foralls(ctor_ty, n_params + n_fields);
      match KernelTypes::collect_spine(body) {
        (head, args) => {
          match (*(head)) {
            KernelTypes::KExprNode::Const(head_addr, lvls) => {
              assert_return_head_is_parent(head_addr, block_addr, ind_idx);
              assert_lvls_are_params(lvls, ind_num_lvls, 0);
              assert_eq!(Lists::length(args), n_params + n_indices,
                "ctor return type: wrong number of spine arguments");
              assert_first_args_are_param_bvars(args, n_params, n_fields, 0);

              let idx_args = Lists::drop(args, n_params);
              let block_addrs = (&(Lists::Node::Cons(block_addr,
                                                     (&(Lists::Node::Nil)))));
              assert_eq!(list_any_mentions_block(idx_args, block_addrs), 0,
                "ctor return type: reflexive occurrence in an index argument");
              () } ,
          } } ,
      }
    }
⟧

def check_param_agreement_go := aiur_fn⟦
  fn check_param_agreement_go(rc: KernelRoles::RoleCtx, ta: KernelTypes::KExpr, tb: KernelTypes::KExpr, n: Field,
                                     types: Lists::List<KernelTypes::KExpr>) -> () {
      match n {
        0 => {  () } ,
        _ => {
          match (*(ta)) {
            KernelTypes::KExprNode::Forall(da, ba, _) => {
              match (*(tb)) {
                KernelTypes::KExprNode::Forall(db, bb, _) => {
                  let eq = KernelDefEq::k_is_def_eq(rc, da, db, types);
                  assert_eq!(eq, 1,
                    "ctor parameter type disagrees with the inductive's");
                  let inner = (&(Lists::Node::Cons(da, types)));
                  check_param_agreement_go(rc, ba, bb, n - 1, inner) } ,
              } } ,
          } } ,
      }
    }
⟧

def check_param_agreement := aiur_fn⟦
  fn check_param_agreement(rc: KernelRoles::RoleCtx, ta: KernelTypes::KExpr, tb: KernelTypes::KExpr, n: Field) -> () {
      check_param_agreement_go(rc, ta, tb, n, (&(Lists::Node::Nil)))
    }
⟧

def get_result_sort_level := aiur_fn⟦
  fn get_result_sort_level(rc: KernelRoles::RoleCtx, ind_ty: KernelTypes::KExpr, n: Field,
                                  types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KLevel {
      let w = KernelWhnf::whnf(rc, ind_ty, types);
      match n {
        0 => {
          match (*(w)) {
            KernelTypes::KExprNode::Srt(l) => {  l } ,
          } } ,
        _ => {
          match (*(w)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              get_result_sort_level(rc, body, n - 1,
                (&(Lists::Node::Cons(dom, types)))) } ,
          } } ,
      }
    }
⟧

def check_field_universes_inner := aiur_fn⟦
  fn check_field_universes_inner(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, ind_level: KernelTypes::KLevel,
                                        types: Lists::List<KernelTypes::KExpr>) -> () {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          let dom_level = KernelInfer::k_ensure_sort(rc, dom, types);
          assert_eq!(KernelLevels::level_leq(dom_level, ind_level), 1,
            "ctor field lives in a universe above the inductive's");
          check_field_universes_inner(rc, body, ind_level,
            (&(Lists::Node::Cons(dom, types)))) } ,
        _ => {  () } ,
      }
    }
⟧

def check_field_universes_skip_params := aiur_fn⟦
  fn check_field_universes_skip_params(rc: KernelRoles::RoleCtx, ctor_ty: KernelTypes::KExpr, n_params: Field,
                                              ind_level: KernelTypes::KLevel,
                                              types: Lists::List<KernelTypes::KExpr>) -> () {
      match n_params {
        0 => {  check_field_universes_inner(rc, ctor_ty, ind_level, types) } ,
        _ => {
          match (*(ctor_ty)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              check_field_universes_skip_params(rc, body, n_params - 1,
                ind_level, (&(Lists::Node::Cons(dom, types)))) } ,
          } } ,
      }
    }
⟧

def check_field_universes := aiur_fn⟦
  fn check_field_universes(rc: KernelRoles::RoleCtx, ctor_ty: KernelTypes::KExpr, n_params: Field,
                                   ind_level: KernelTypes::KLevel) -> () {
      match (*(ind_level)) {
        KernelTypes::KLevelNode::Zero => {  () } ,
        _ => {  check_field_universes_skip_params(rc, ctor_ty, n_params,
                                                    ind_level, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

def ctor_parent_ind_ci := aiur_fn⟦
  inline fn ctor_parent_ind_ci(block_addr: Bytes::AddressRef, ind_idx: Field)
                                -> &KernelTypes::KConstantInfo {
      Ingress::get_ci_iprj(block_addr, ind_idx)
    }
⟧

def addr_list_contains := aiur_fn⟦
  fn addr_list_contains(xs: Lists::List<Bytes::AddressRef>, target: Bytes::AddressRef) -> Field {
      match (*(xs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(a, rest) => {
          match Bytes::address_eq(a, target) {
            1 => {  1 } ,
            _ => {  addr_list_contains(rest, target) } ,
          } } ,
      }
    }
⟧

def caddr_is_peer := aiur_fn⟦
  fn caddr_is_peer(caddr: Bytes::AddressRef, block_addrs: Lists::List<Bytes::AddressRef>) -> Field {
      let ci = (*(Ingress::get_ci(caddr)));
      match ci {
        KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, ba, _) => {
          addr_list_contains(block_addrs, ba) } ,
        _ => {  0 } ,
      }
    }
⟧

def expr_mentions_block := aiur_fn⟦
  fn expr_mentions_block(e: KernelTypes::KExpr, block_addrs: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::BVar(_) => {  0 } ,
        KernelTypes::KExprNode::Srt(_) => {  0 } ,
        KernelTypes::KExprNode::Const(caddr, _) => {  caddr_is_peer(caddr, block_addrs) } ,
        KernelTypes::KExprNode::App(f, a) => {
          match expr_mentions_block(f, block_addrs) {
            1 => {  1 } ,
            _ => {  expr_mentions_block(a, block_addrs) } ,
          } } ,
        KernelTypes::KExprNode::Lam(t, b, _) => {
          match expr_mentions_block(t, block_addrs) {
            1 => {  1 } ,
            _ => {  expr_mentions_block(b, block_addrs) } ,
          } } ,
        KernelTypes::KExprNode::Forall(t, b, _) => {
          match expr_mentions_block(t, block_addrs) {
            1 => {  1 } ,
            _ => {  expr_mentions_block(b, block_addrs) } ,
          } } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          match expr_mentions_block(t, block_addrs) {
            1 => {  1 } ,
            _ => {
              match expr_mentions_block(v, block_addrs) {
                1 => {  1 } ,
                _ => {  expr_mentions_block(b, block_addrs) } ,
              } } ,
          } } ,
        KernelTypes::KExprNode::Lit(_) => {  0 } ,
        KernelTypes::KExprNode::Proj(_, _, e1) => {  expr_mentions_block(e1, block_addrs) } ,
      }
    }
⟧

def list_any_mentions_block := aiur_fn⟦
  fn list_any_mentions_block(es: Lists::List<KernelTypes::KExpr>,
                                    block_addrs: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(es)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(e, rest) => {
          match expr_mentions_block(e, block_addrs) {
            1 => {  1 } ,
            _ => {  list_any_mentions_block(rest, block_addrs) } ,
          } } ,
      }
    }
⟧

def peel_n_foralls_with_types := aiur_fn⟦
  fn peel_n_foralls_with_types(e: KernelTypes::KExpr, n: Field,
                                      types: Lists::List<KernelTypes::KExpr>) -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match n {
        0 => {  (e, types) } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              let t2 = (&(Lists::Node::Cons(dom, types)));
              peel_n_foralls_with_types(body, n - 1, t2) } ,
            _ => {  (e, types) } ,
          } } ,
      }
    }
⟧

def assert_occ_param_bvars := aiur_fn⟦
  fn assert_occ_param_bvars(args: Lists::List<KernelTypes::KExpr>, n_params: Field, depth: Field,
                                   i: Field) -> () {
      match n_params - i {
        0 => {  () } ,
        _ => {
          match (*(args)) {
            Lists::Node::Cons(arg, rest) => {
              match (*(arg)) {
                KernelTypes::KExprNode::BVar(j) => {
                  assert_eq!(j, (depth - 1) - i,
                    "recursive occurrence: parameter arg is not the parameter binder");
                  assert_occ_param_bvars(rest, n_params, depth, i + 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def check_valid_ind_app := aiur_fn⟦
  fn check_valid_ind_app(caddr: Bytes::AddressRef, us: Lists::List<KernelTypes::KLevel>,
                                args: Lists::List<KernelTypes::KExpr>, block_addrs: Lists::List<Bytes::AddressRef>,
                                depth: Field) -> () {
      let ci = (*(Ingress::get_ci(caddr)));
      match ci {
        KernelTypes::KConstantInfo::Induct(occ_nlvls, _, occ_params, occ_indices,
                              _, _, _, _) => {
          assert_lvls_are_params(us, occ_nlvls, 0);
          assert_eq!(Lists::length(args), occ_params + occ_indices,
            "recursive occurrence is not fully applied");
          assert_occ_param_bvars(args, occ_params, depth, 0);
          assert_eq!(list_any_mentions_block(Lists::drop(args, occ_params),
                                                  block_addrs), 0,
            "recursive occurrence: index argument mentions the block");
          () } ,
      }
    }
⟧

def check_positivity_aug := aiur_fn⟦
  fn check_positivity_aug(rc: KernelRoles::RoleCtx, dom: KernelTypes::KExpr, block_addrs: Lists::List<Bytes::AddressRef>,
                                 types: Lists::List<KernelTypes::KExpr>, check_params: Field) -> () {
      match expr_mentions_block(dom, block_addrs) {
        0 => {  () } ,
        _ => {
          let dom_w = KernelWhnf::whnf(rc, dom, types);
          -- Lean tests positivity after whnf: a field whose occurrences whnf
          -- erases (`Tagged T`, `Tagged _ := Nat`) is an ordinary field
          match expr_mentions_block(dom_w, block_addrs) {
            0 => {  () } ,
            _ => {
              match (*(dom_w)) {
                KernelTypes::KExprNode::Forall(idom, ibody, _) => {
                  assert_eq!(expr_mentions_block(idom, block_addrs), 0,
                    "strict positivity: block occurs left of an arrow");
                  let t2 = (&(Lists::Node::Cons(idom, types)));
                  check_positivity_aug(rc, ibody, block_addrs, t2, check_params) } ,
                _ => {
                  match KernelTypes::collect_spine(dom_w) {
                    (head, args) => {
                      match (*(head)) {
                        KernelTypes::KExprNode::Const(caddr, us) => {
                          match caddr_is_peer(caddr, block_addrs) {
                            1 => {
                              match check_params {
                                1 => {
                                  check_valid_ind_app(caddr, us, args,
                                    block_addrs, Lists::length(types)) } ,
                                _ => {  () } ,
                              } } ,
                            _ => {
                              -- D7: a nested occurrence is the modeled route's
                              -- (`KernelModeled::block_is_modeled`); one that only
                              -- whnf exposes is refused here, as Lean refuses it.
                              assert_eq!(0, 1,
                                "strict positivity: nested occurrence on the native route");
                              () } ,
                          } } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def check_positivity_fields := aiur_fn⟦
  fn check_positivity_fields(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, block_addrs: Lists::List<Bytes::AddressRef>,
                                    types: Lists::List<KernelTypes::KExpr>, check_params: Field) -> () {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          check_positivity_aug(rc, dom, block_addrs, types, check_params);
          let t2 = (&(Lists::Node::Cons(dom, types)));
          check_positivity_fields(rc, body, block_addrs, t2, check_params) } ,
        _ => {  () } ,
      }
    }
⟧

def check_positivity := aiur_fn⟦
  fn check_positivity(rc: KernelRoles::RoleCtx, ctor_ty: KernelTypes::KExpr, n_params: Field,
                            block_addr: Bytes::AddressRef, types: Lists::List<KernelTypes::KExpr>) -> () {
      let block_addrs = (&(Lists::Node::Cons(block_addr, (&(Lists::Node::Nil)))));
      match peel_n_foralls_with_types(ctor_ty, n_params, types) {
        (body, types_after) => {
          check_positivity_fields(rc, body, block_addrs, types_after, 1) } ,
      }
    }
⟧

def check_inductive_shape := aiur_fn⟦
  fn check_inductive_shape(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, n_params: Field, n_indices: Field,
                                  num_ctors: Field, num_lvls: Field,
                                  block_addr: Bytes::AddressRef, ind_idx: Field,
                                  is_unsafe: Field) -> () {
      let ind_level = get_result_sort_level(rc, ty, n_params + n_indices,
                                                 (&(Lists::Node::Nil)));
      check_inductive_shape_ctors(rc, ty, n_params, n_indices, num_ctors,
                                       num_lvls, block_addr, ind_idx,
                                       ind_level, is_unsafe, 0)
    }
⟧

def check_inductive_shape_ctors := aiur_fn⟦
  fn check_inductive_shape_ctors(rc: KernelRoles::RoleCtx, ind_ty: KernelTypes::KExpr, n_params: Field,
                                        n_indices: Field, num_ctors: Field,
                                        num_lvls: Field, block_addr: Bytes::AddressRef,
                                        ind_idx: Field, ind_level: KernelTypes::KLevel,
                                        is_unsafe: Field, cidx: Field) -> () {
      match num_ctors - cidx {
        0 => {  () } ,
        _ => {
          let ctor_ci = (*(Ingress::get_ci_cprj(block_addr, ind_idx, cidx)));
          match ctor_ci {
            KernelTypes::KConstantInfo::Ctor(c_nlvls, cty, c_block, c_ind_idx, c_cidx,
                                c_np, c_nf, c_unsafe) => {

              assert_eq!(Bytes::address_eq(c_block, block_addr), 1,
                "ctor belongs to a different block than its inductive");
              assert_eq!(c_ind_idx, ind_idx,
                "ctor points at a different member of the block");
              assert_eq!(c_cidx, cidx,
                "ctor's stored index differs from its position");
              assert_eq!(c_nlvls, num_lvls,
                "ctor universe count differs from the inductive's");
              assert_eq!(c_np, n_params,
                "ctor parameter count differs from the inductive's");
              assert_eq!(c_unsafe, is_unsafe,
                "ctor safety differs from the inductive's");
              validate_expr_well_scoped(cty, 0, num_lvls);
              KernelInfer::k_ensure_sort(rc, cty, (&(Lists::Node::Nil)));
              assert_safety(is_unsafe, cty);
              check_param_agreement(rc, ind_ty, cty, n_params);
              check_ctor_return_type(cty, c_np, n_indices, c_nf, num_lvls,
                                          block_addr, ind_idx);
              check_field_universes(rc, cty, c_np, ind_level);

              match is_unsafe {
                0 => {  check_positivity(rc, cty, c_np, block_addr,
                                           (&(Lists::Node::Nil))) } ,
                _ => {  () } ,
              };
              check_inductive_shape_ctors(rc, ind_ty, n_params, n_indices,
                                               num_ctors, num_lvls,
                                               block_addr, ind_idx,
                                               ind_level, is_unsafe,
                                               cidx + 1) } ,
          } } ,
      }
    }
⟧

  -- The declared shape of a modeled type's constructors (`checkIndShape`,
  -- `indParamsOk`): their records, counts and return types. Their parameter
  -- domains, field universes and positivity are the model's to justify.

def check_modeled_ctors := aiur_fn⟦
  fn check_modeled_ctors(rc: KernelRoles::RoleCtx, n_params: Field, n_indices: Field, num_ctors: Field,
                         num_lvls: Field, block_addr: Bytes::AddressRef, ind_idx: Field,
                         is_unsafe: Field, cidx: Field) -> () {
      match num_ctors - cidx {
        0 => {  () } ,
        _ => {
          let ctor_ci = (*(Ingress::get_ci_cprj(block_addr, ind_idx, cidx)));
          match ctor_ci {
            KernelTypes::KConstantInfo::Ctor(c_nlvls, cty, c_block, c_ind_idx, c_cidx,
                                c_np, c_nf, c_unsafe) => {
              assert_eq!(Bytes::address_eq(c_block, block_addr), 1,
                "ctor belongs to a different block than its inductive");
              assert_eq!(c_ind_idx, ind_idx,
                "ctor points at a different member of the block");
              assert_eq!(c_cidx, cidx,
                "ctor's stored index differs from its position");
              assert_eq!(c_nlvls, num_lvls,
                "ctor universe count differs from the inductive's");
              assert_eq!(c_np, n_params,
                "ctor parameter count differs from the inductive's");
              assert_eq!(c_unsafe, is_unsafe,
                "ctor safety differs from the inductive's");
              validate_expr_well_scoped(cty, 0, num_lvls);
              KernelInfer::k_ensure_sort(rc, cty, (&(Lists::Node::Nil)));
              assert_safety(is_unsafe, cty);
              check_ctor_return_type(cty, c_np, n_indices, c_nf, num_lvls,
                                          block_addr, ind_idx);
              check_modeled_ctors(rc, n_params, n_indices, num_ctors, num_lvls,
                                  block_addr, ind_idx, is_unsafe, cidx + 1) } ,
          } } ,
      }
    }
⟧

def check_parent_inductive_shape := aiur_fn⟦
  fn check_parent_inductive_shape(rc: KernelRoles::RoleCtx, ind_ci: KernelTypes::KConstantInfo) -> () {
      match ind_ci {
        KernelTypes::KConstantInfo::Induct(nlvls, ty, n_params, n_indices, num_ctors,
                              is_unsafe, block_addr, ind_idx) => {
          check_inductive_shape(rc, ty, n_params, n_indices, num_ctors,
                                     nlvls, block_addr, ind_idx, is_unsafe) } ,
        _ => {  () } ,
      }
    }
⟧

def check_block_peer_param_agreement := aiur_fn⟦
  fn check_block_peer_param_agreement(rc: KernelRoles::RoleCtx, ind_ci: KernelTypes::KConstantInfo, addr: Bytes::AddressRef) -> () {
      match ind_ci {
        KernelTypes::KConstantInfo::Induct(_, self_ty, self_np, self_ni, _, _,
                               block_addr, self_ind_idx) => {
          match Bytes::address_eq(block_addr, addr) {
            1 => {  () } ,
            _ => {
              let block_c = Ingress::load_verified_constant(block_addr);
              match block_c {
                Ixon::Constant::Mk(info, _, _, _) => {
                  match info {
                    Ixon::ConstantInfo::Muts(members) => {
                      peer_agree_walk(rc, members, self_ty, self_np, self_ni,
                                           self_ind_idx, 0, block_addr) } ,
                    _ => {  () } ,
                  } } ,
              } } ,
          } } ,
        _ => {  () } ,
      }
    }
⟧

def peer_agree_walk := aiur_fn⟦
  fn peer_agree_walk(rc: KernelRoles::RoleCtx, members: Lists::List<Ixon::MutConst>, self_ty: KernelTypes::KExpr,
                            self_np: Field, self_ni: Field,
                            self_ind_idx: Field, pos: Field, block_addr: Bytes::AddressRef) -> () {
      match (*(members)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(_) => {
              let is_self = Fields::is_zero(pos - self_ind_idx);
              match is_self {
                1 => {
                  peer_agree_walk(rc, rest, self_ty, self_np, self_ni,
                                       self_ind_idx, pos + 1, block_addr) } ,
                _ => {
                  let peer_ci = (*(Ingress::get_ci_iprj(block_addr, pos)));
                  match peer_ci {
                    KernelTypes::KConstantInfo::Induct(_, peer_ty, peer_np, peer_ni,
                                           _, _, _, _) => {
                      assert_eq!(peer_np, self_np,
                        "mutual block peers disagree on parameter count");
                      check_param_agreement(rc, self_ty, peer_ty, self_np);
                      let self_lvl = get_result_sort_level(rc, self_ty,
                        self_np + self_ni, (&(Lists::Node::Nil)));
                      let peer_lvl = get_result_sort_level(rc, peer_ty,
                        peer_np + peer_ni, (&(Lists::Node::Nil)));
                      assert_eq!(KernelLevels::level_equal(self_lvl, peer_lvl), 1,
                        "mutual block peers land in different universes");
                      peer_agree_walk(rc, rest, self_ty, self_np, self_ni,
                                           self_ind_idx, pos + 1, block_addr) } ,
                    _ => {
                      peer_agree_walk(rc, rest, self_ty, self_np, self_ni,
                                           self_ind_idx, pos + 1, block_addr) } ,
                  } } ,
              } } ,
            _ => {
              peer_agree_walk(rc, rest, self_ty, self_np, self_ni,
                                   self_ind_idx, pos + 1, block_addr) } ,
          } } ,
      }
    }
⟧

def is_large_eliminator := aiur_fn⟦
  fn is_large_eliminator(rc: KernelRoles::RoleCtx, result_level: KernelTypes::KLevel, num_ctors: Field,
                                single_ctor_opt: (Field, KernelTypes::KConstantInfo),
                                is_solo: Field) -> Field {
      match KernelLevels::level_is_not_zero(result_level) {
        1 => {  1 } ,
        _ => {

          match is_solo {
            0 => {  0 } ,
            _ => {
              match num_ctors {
                0 => {  1 } ,
                1 => {
                  match single_ctor_opt {
                    (present, ctor_ci) => {
                      match present {
                        0 => {  0 } ,
                        _ => {
                          match ctor_ci {
                            KernelTypes::KConstantInfo::Ctor(_, ctor_ty, _, _, _, n_params,
                                                  n_fields, _) => {
                              match n_fields {
                                0 => {  1 } ,
                                _ => {  check_large_prop_ctor(rc, ctor_ty, n_params,
                                                                n_fields,
                                                                (&(Lists::Node::Nil))) } ,
                              } } ,
                            _ => {  0 } ,
                          } } ,
                      } } ,
                  } } ,
                _ => {  0 } ,
              } } ,
          } } ,
      }
    }
⟧

def check_large_prop_ctor := aiur_fn⟦
  fn check_large_prop_ctor(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, n_params: Field, n_fields: Field,
                                  types: Lists::List<KernelTypes::KExpr>) -> Field {
      match n_params {
        0 => {
          check_large_walk_fields(rc, ty, n_fields, 0, types,
                                       (&(Lists::Node::Nil))) } ,
        _ => {
          match (*(ty)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              let inner = (&(Lists::Node::Cons(dom, types)));
              check_large_prop_ctor(rc, body, n_params - 1, n_fields, inner) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def check_large_walk_fields := aiur_fn⟦
  fn check_large_walk_fields(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, n_fields: Field, field_idx: Field,
                                    types: Lists::List<KernelTypes::KExpr>,
                                    data_bvars: Lists::List<Field>) -> Field {
      match n_fields - field_idx {
        0 => {
          match KernelTypes::collect_spine(ty) {
            (_, args) => {  all_bvars_in_args(data_bvars, args) } ,
          } } ,
        _ => {
          match (*(ty)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              let lvl = KernelInfer::k_ensure_sort(rc, dom, types);
              let is_data = 1 - KernelLevels::level_equal(lvl, (&(KernelTypes::KLevelNode::Zero)));

              let bvar_idx = (n_fields - 1) - field_idx;
              let new_bvars = match is_data {
                0 => {  data_bvars } ,
                _ => {  (&(Lists::Node::Cons(bvar_idx, data_bvars))) } ,
              };
              let inner = (&(Lists::Node::Cons(dom, types)));
              check_large_walk_fields(rc, body, n_fields, field_idx + 1,
                                            inner, new_bvars) } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def all_bvars_in_args := aiur_fn⟦
  fn all_bvars_in_args(bvars: Lists::List<Field>, args: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(bvars)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(b, rest) => {
          match args_contain_bvar(args, b) {
            0 => {  0 } ,
            _ => {  all_bvars_in_args(rest, args) } ,
          } } ,
      }
    }
⟧

def args_contain_bvar := aiur_fn⟦
  fn args_contain_bvar(args: Lists::List<KernelTypes::KExpr>, target: Field) -> Field {
      match (*(args)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(a, rest) => {
          match (*(a)) {
            KernelTypes::KExprNode::BVar(i) => {
              match i - target {
                0 => {  1 } ,
                _ => {  args_contain_bvar(rest, target) } ,
              } } ,
            _ => {  args_contain_bvar(rest, target) } ,
          } } ,
      }
    }
⟧

def compute_k_target := aiur_fn⟦
  fn compute_k_target(rc: KernelRoles::RoleCtx, ind_ci: KernelTypes::KConstantInfo, ind_addr: Bytes::AddressRef) -> Field {
      match ind_ci {
        KernelTypes::KConstantInfo::Induct(_, ind_ty, n_params, n_indices, num_ctors,
                               _, block_addr, ind_idx) => {
          let is_solo = ind_is_solo(block_addr, ind_addr);
          match is_solo {
            0 => {  0 } ,
            _ => {
              let result_level = get_result_sort_level(rc, ind_ty,
                n_params + n_indices, (&(Lists::Node::Nil)));
              match KernelLevels::level_equal(result_level, (&(KernelTypes::KLevelNode::Zero))) {
                0 => {  0 } ,
                _ => {
                  match num_ctors {
                    1 => {
                      let ctor_ci = (*(Ingress::get_ci_cprj(block_addr,
                        ind_idx, 0)));
                      match ctor_ci {
                        KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, _, n_fields, _) => {
                          Fields::is_zero(n_fields) } ,
                        _ => {  0 } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
              } } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def ind_is_solo := aiur_fn⟦
  fn ind_is_solo(block_addr: Bytes::AddressRef, ind_addr: Bytes::AddressRef) -> Field {
      match Bytes::address_eq(block_addr, ind_addr) {
        1 => {  1 } ,
        _ => {
          let block_c = Ingress::load_verified_constant(block_addr);
          match block_c {
            Ixon::Constant::Mk(info, _, _, _) => {
              match info {
                Ixon::ConstantInfo::Muts(members) => {  muts_indc_count_is_one(members, 0) } ,
                _ => {  0 } ,
              } } ,
          } } ,
      }
    }
⟧

def is_muts_block := aiur_fn⟦
  fn is_muts_block(addr: Bytes::AddressRef) -> Field {
      let block_c = Ingress::load_verified_constant(addr);
      match block_c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(_) => {  1 } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def muts_indc_count_is_one := aiur_fn⟦
  fn muts_indc_count_is_one(members: Lists::List<Ixon::MutConst>, count: Field) -> Field {
      match (*(members)) {
        Lists::Node::Nil => {
          match count {
            1 => {  1 } ,
            _ => {  0 } ,
          } } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(_) => {  muts_indc_count_is_one(rest, count + 1) } ,
            _ => {  muts_indc_count_is_one(rest, count) } ,
          } } ,
      }
    }
⟧

def rec_to_parent_addr := aiur_fn⟦
  fn rec_to_parent_addr(ty: KernelTypes::KExpr, n_p: Field, n_mot: Field, n_min: Field,
                               n_i: Field) -> Bytes::AddressRef {
      let skip = n_p + n_mot + n_min + n_i;
      let after_skip = peel_n_foralls(ty, skip);
      match (*(after_skip)) {
        KernelTypes::KExprNode::Forall(major_ty, _, _) => {
          match KernelTypes::collect_spine(major_ty) {
            (head, _) => {
              match (*(head)) {
                KernelTypes::KExprNode::Const(caddr, _) => {  caddr } ,
              } } ,
          } } ,
      }
    }
⟧

def extract_aux_occ_us := aiur_fn⟦
  fn extract_aux_occ_us(rec_ci: KernelTypes::KConstantInfo) -> Lists::List<KernelTypes::KLevel> {
      match rec_ci {
        KernelTypes::KConstantInfo::Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) => {
          let skip = ((np + nmot) + nmin) + ni;
          match (*(peel_n_foralls(ty, skip))) {
            KernelTypes::KExprNode::Forall(major_ty, _, _) => {
              match KernelTypes::collect_spine(major_ty) {
                (head, _) => {
                  match (*(head)) {
                    KernelTypes::KExprNode::Const(_, us) => {  us } ,
                    _ => {  (&(Lists::Node::Nil)) } ,
                  } } ,
              } } ,
            _ => {  (&(Lists::Node::Nil)) } ,
          } } ,
        _ => {  (&(Lists::Node::Nil)) } ,
      }
    }
⟧

def extract_aux_spec_params := aiur_fn⟦
  fn extract_aux_spec_params(ty: KernelTypes::KExpr, n_p: Field, n_mot: Field, n_min: Field,
                                     n_i: Field, ext_np: Field) -> Lists::List<KernelTypes::KExpr> {
      let skip = n_p + n_mot + n_min + n_i;
      let after_skip = peel_n_foralls(ty, skip);
      match (*(after_skip)) {
        KernelTypes::KExprNode::Forall(major_ty, _, _) => {
          match KernelTypes::collect_spine(major_ty) {
            (_head, args) => {

              spec_params_lower(Lists::take(args, ext_np),
                (n_mot + n_min) + n_i) } ,
          } } ,
      }
    }
⟧

def spec_params_lower := aiur_fn⟦
  fn spec_params_lower(sps: Lists::List<KernelTypes::KExpr>, d: Field) -> Lists::List<KernelTypes::KExpr> {
      match (*(sps)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(sp, rest) => {
          assert_eq!(KernelSubst::has_bvar_in_range(sp, 0, d), 0,
            "nested occurrence's parameter references a motive, minor, or index binder");
          (&(Lists::Node::Cons(KernelSubst::expr_lower(sp, d, 0),
                              spec_params_lower(rest, d)))) } ,
      }
    }
⟧

def build_param_lvls_range := aiur_fn⟦
  fn build_param_lvls_range(start: Field, count: Field, i: Field) -> Lists::List<KernelTypes::KLevel> {
      match count - i {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          (&(Lists::Node::Cons(
            (&(KernelTypes::KLevelNode::Param(start + i))),
            build_param_lvls_range(start, count, i + 1)))) } ,
      }
    }
⟧

def build_flat_originals := aiur_fn⟦
  inline fn build_flat_originals(block_addr: Bytes::AddressRef, univ_offset: Field)
                                  -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      let block_c = Ingress::load_verified_constant(block_addr);
      match block_c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              flat_originals_walk(members, members, block_addr,
                univ_offset, 0) } ,
            _ => {

              let ci = (*(Ingress::get_ci(block_addr)));
              match ci {
                KernelTypes::KConstantInfo::Induct(nlvls, _, _, _, _, _, _, _) => {
                  let occ = build_param_lvls_range(univ_offset, nlvls, 0);
                  (&(Lists::Node::Cons(
                    (block_addr, 0, (&(Lists::Node::Nil)), occ),
                    (&(Lists::Node::Nil))))) } ,
                _ => {  (&(Lists::Node::Nil)) } ,
              } } ,
          } } ,
      }
    }
⟧

def flat_originals_walk := aiur_fn⟦
  fn flat_originals_walk(all_members: Lists::List<Ixon::MutConst>,
                                cur: Lists::List<Ixon::MutConst>, block_addr: Bytes::AddressRef,
                                univ_offset: Field, pos: Field)
                                -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      match (*(cur)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Indc(_) => {
              let member_addr = Ingress::projection_addr(all_members, block_addr, pos);
              let member_ci = (*(Ingress::get_ci_iprj(block_addr, pos)));
              let nlvls = match member_ci {
                KernelTypes::KConstantInfo::Induct(nl, _, _, _, _, _, _, _) => {  nl } ,
                _ => {  0 } ,
              };
              let occ = build_param_lvls_range(univ_offset, nlvls, 0);
              (&(Lists::Node::Cons(
                (member_addr, 0, (&(Lists::Node::Nil)), occ),
                flat_originals_walk(all_members, rest, block_addr,
                  univ_offset, pos + 1)))) } ,
            _ => {
              flat_originals_walk(all_members, rest, block_addr,
                univ_offset, pos + 1) } ,
          } } ,
      }
    }
⟧

def aux_already_in := aiur_fn⟦
  fn aux_already_in(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                            target_addr: Bytes::AddressRef,
                            target_sp: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(flat)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (addr, is_aux, sp, _ou) => {
              match is_aux {
                1 => {
                  match Bytes::address_eq(addr, target_addr) {
                    1 => {
                      match spec_params_ptr_eq(sp, target_sp) {
                        1 => {  1 } ,
                        _ => {  aux_already_in(rest, target_addr, target_sp) } ,
                      } } ,
                    _ => {  aux_already_in(rest, target_addr, target_sp) } ,
                  } } ,
                _ => {  aux_already_in(rest, target_addr, target_sp) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- Binders are structurally equal when their domains and bodies are and their data
  -- (D2) agree: equal zero sets, the kernel's `m₁.pw = m₂.pw`.

def kexpr_binder_struct_eq := aiur_fn⟦
  fn kexpr_binder_struct_eq(ta: KernelTypes::KExpr, ba: KernelTypes::KExpr, la: KernelTypes::KLevel,
                            tb: KernelTypes::KExpr, bb: KernelTypes::KExpr, lb: KernelTypes::KLevel) -> Field {
      match KernelLevels::pw_eq(la, lb) {
        1 => {
          match kexpr_struct_eq(ta, tb) {
            1 => {  kexpr_struct_eq(ba, bb) } ,
            _ => {  0 } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def kexpr_struct_eq := aiur_fn⟦
  fn kexpr_struct_eq(a: KernelTypes::KExpr, b: KernelTypes::KExpr) -> Field {
      match (*(a)) {
            KernelTypes::KExprNode::BVar(ia) => {
              match (*(b)) {
                KernelTypes::KExprNode::BVar(ib) => {
                  match ia - ib { 0 => {  1 } , _ => {  0 } , } } ,
                _ => {  0 } ,
              } } ,
            KernelTypes::KExprNode::Srt(la) => {
              match (*(b)) {
                KernelTypes::KExprNode::Srt(lb) => {  KernelLevels::level_struct_eq(la, lb) } ,
                _ => {  0 } ,
              } } ,
            KernelTypes::KExprNode::Const(ca, lsa) => {
              match (*(b)) {
                KernelTypes::KExprNode::Const(cb, lsb) => {
                  match Bytes::address_eq(ca, cb) {
                    1 => {  level_list_struct_eq(lsa, lsb) } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
            KernelTypes::KExprNode::App(fa, aa) => {
              match (*(b)) {
                KernelTypes::KExprNode::App(fb, ab) => {
                  match kexpr_struct_eq(fa, fb) {
                    1 => {  kexpr_struct_eq(aa, ab) } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
            KernelTypes::KExprNode::Lam(ta, ba, la) => {
              match (*(b)) {
                KernelTypes::KExprNode::Lam(tb, bb, lb) => {  kexpr_binder_struct_eq(ta, ba, la, tb, bb, lb) } ,
                _ => {  0 } ,
              } } ,
            KernelTypes::KExprNode::Forall(da, xa, la) => {
              match (*(b)) {
                KernelTypes::KExprNode::Forall(db, xb, lb) => {  kexpr_binder_struct_eq(da, xa, la, db, xb, lb) } ,
                _ => {  0 } ,
              } } ,
            KernelTypes::KExprNode::Let(ta, va, ba) => {
              match (*(b)) {
                KernelTypes::KExprNode::Let(tb, vb, bb) => {
                  match kexpr_struct_eq(ta, tb) {
                    1 => {
                      match kexpr_struct_eq(va, vb) {
                        1 => {  kexpr_struct_eq(ba, bb) } ,
                        _ => {  0 } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
            KernelTypes::KExprNode::Lit(la) => {
              match (*(b)) {
                KernelTypes::KExprNode::Lit(lb) => {  KernelLevels::literal_eq(la, lb) } ,
                _ => {  0 } ,
              } } ,
            KernelTypes::KExprNode::Proj(sa, fa2, ea) => {
              match (*(b)) {
                KernelTypes::KExprNode::Proj(sb, fb2, eb) => {
                  match Bytes::address_eq(sa, sb) {
                    1 => {
                      match fa2 - fb2 {
                        0 => {  kexpr_struct_eq(ea, eb) } ,
                        _ => {  0 } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
          }
    }
⟧

def level_list_struct_eq := aiur_fn⟦
  fn level_list_struct_eq(a: Lists::List<KernelTypes::KLevel>, b: Lists::List<KernelTypes::KLevel>) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          match (*(b)) {
            Lists::Node::Nil => {  1 } ,
            _ => {  0 } ,
          } } ,
        Lists::Node::Cons(x, xr) => {
          match (*(b)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(y, yr) => {
              match KernelLevels::level_struct_eq(x, y) {
                1 => {  level_list_struct_eq(xr, yr) } ,
                _ => {  0 } ,
              } } ,
          } } ,
      }
    }
⟧

def spec_params_ptr_eq := aiur_fn⟦
  fn spec_params_ptr_eq(a: Lists::List<KernelTypes::KExpr>, b: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(a)) {
        Lists::Node::Nil => {
          match (*(b)) {
            Lists::Node::Nil => {  1 } ,
            _ => {  0 } ,
          } } ,
        Lists::Node::Cons(x, xr) => {
          match (*(b)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(y, yr) => {
              match kexpr_struct_eq(x, y) {
                1 => {  spec_params_ptr_eq(xr, yr) } ,
                _ => {  0 } ,
              } } ,
          } } ,
      }
    }
⟧

def extract_aux_spec_params_from_rec := aiur_fn⟦
  fn extract_aux_spec_params_from_rec(rec_ci: KernelTypes::KConstantInfo,
                                             ext_np: Field) -> Lists::List<KernelTypes::KExpr> {
      match rec_ci {
        KernelTypes::KConstantInfo::Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) => {
          extract_aux_spec_params(ty, np, nmot, nmin, ni, ext_np) } ,
        _ => {  (&(Lists::Node::Nil)) } ,
      }
    }
⟧

def primary_parent_block_of := aiur_fn⟦
  inline fn primary_parent_block_of(rec_block_addr: Bytes::AddressRef, fallback: Bytes::AddressRef) -> Bytes::AddressRef {
      let block_c = Ingress::load_verified_constant(rec_block_addr);
      match block_c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              first_recr_parent_block(members, members, rec_block_addr, 0,
                fallback) } ,
            _ => {  fallback } ,
          } } ,
      }
    }
⟧

def first_recr_parent_block := aiur_fn⟦
  fn first_recr_parent_block(all_members: Lists::List<Ixon::MutConst>,
                                    cur: Lists::List<Ixon::MutConst>, block_addr: Bytes::AddressRef,
                                    pos: Field, fallback: Bytes::AddressRef) -> Bytes::AddressRef {
      match (*(cur)) {
        Lists::Node::Nil => {  fallback } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Recr(_) => {
              let wrapper = Ingress::projection_addr(all_members, block_addr, pos);
              let rec_ci = (*(Ingress::get_ci(wrapper)));
              match rec_ci {
                KernelTypes::KConstantInfo::Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) => {
                  let parent = rec_to_parent_addr(ty, np, nmot, nmin, ni);
                  let parent_ci = (*(Ingress::get_ci(parent)));
                  match parent_ci {
                    KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, pb, _) => {  pb } ,
                    _ => {  fallback } ,
                  } } ,
                _ => {  fallback } ,
              } } ,
            _ => {  first_recr_parent_block(all_members, rest, block_addr,
                   pos + 1, fallback) } ,
          } } ,
      }
    }
⟧

def build_flat_block := aiur_fn⟦
  fn build_flat_block(rec_block_addr: Bytes::AddressRef, parent_block_addr: Bytes::AddressRef,
                               univ_offset: Field)
                              -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {

      let primary_block = primary_parent_block_of(rec_block_addr,
        parent_block_addr);
      let originals = build_flat_originals(primary_block, univ_offset);
      match is_muts_block(rec_block_addr) {
        0 => {  originals } ,
        _ => {
          detect_aux_from_recrs_ex(rec_block_addr, primary_block,
                                         univ_offset, originals) } ,
      }
    }
⟧

def detect_aux_from_recrs_ex := aiur_fn⟦
  fn detect_aux_from_recrs_ex(rec_block_addr: Bytes::AddressRef,
                                      parent_block_addr: Bytes::AddressRef,
                                      univ_offset: Field,
                                      originals: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>)
                                     -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      let block_c = Ingress::load_verified_constant(rec_block_addr);
      match block_c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              aux_from_recrs_walk_ex(members, members, rec_block_addr,
                                          parent_block_addr, univ_offset,
                                          originals, 0) } ,
            _ => {  originals } ,
          } } ,
      }
    }
⟧

def aux_from_recrs_walk_ex := aiur_fn⟦
  fn aux_from_recrs_walk_ex(all_members: Lists::List<Ixon::MutConst>,
                                    cur: Lists::List<Ixon::MutConst>,
                                    rec_block_addr: Bytes::AddressRef,
                                    primary_parent_block: Bytes::AddressRef,
                                    univ_offset: Field,
                                    acc: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                    pos: Field)
                                   -> Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)> {
      match (*(cur)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Recr(_) => {
              let rec_wrapper = Ingress::projection_addr(all_members, rec_block_addr, pos);
              let rec_ci = (*(Ingress::get_ci(rec_wrapper)));
              let entry_opt = match rec_ci {
                KernelTypes::KConstantInfo::Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) => {
                  let parent_addr = rec_to_parent_addr(ty, np, nmot, nmin, ni);
                  let parent_ci = (*(Ingress::get_ci(parent_addr)));
                  match parent_ci {
                    KernelTypes::KConstantInfo::Induct(pnlvls, _, pnp, _, _, _, pblock, _) => {
                      match Bytes::address_eq(pblock, primary_parent_block) {
                        1 => {  (0, parent_addr, 0, pnp, pnlvls) } ,
                        _ => {  (1, parent_addr, 1, pnp, pnlvls) } ,
                      } } ,
                    _ => {  (0, parent_addr, 0, 0, 0) } ,
                  } } ,
                _ => {  (0, primary_parent_block, 0, 0, 0) } ,
              };
              match entry_opt {
                (0, _, _, _, _) => {
                  aux_from_recrs_walk_ex(all_members, rest, rec_block_addr,
                    primary_parent_block, univ_offset, acc, pos + 1) } ,
                (_, parent_addr, _, pnp, pnlvls) => {
                  let spec_params = extract_aux_spec_params_from_rec(
                    rec_ci, pnp);
                  let occ = extract_aux_occ_us(rec_ci);
                  match aux_already_in(acc, parent_addr, spec_params) {
                    1 => {
                      aux_from_recrs_walk_ex(all_members, rest, rec_block_addr,
                        primary_parent_block, univ_offset, acc, pos + 1) } ,
                    _ => {
                      let new_acc = Lists::snoc(acc,
                        (parent_addr, 1, spec_params, occ));
                      aux_from_recrs_walk_ex(all_members, rest, rec_block_addr,
                        primary_parent_block, univ_offset, new_acc, pos + 1) } ,
                  } } ,
              } } ,
            _ => {
              aux_from_recrs_walk_ex(all_members, rest, rec_block_addr,
                primary_parent_block, univ_offset, acc, pos + 1) } ,
          } } ,
      }
    }
⟧

def flat_find_pos := aiur_fn⟦
  fn flat_find_pos(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                          target_addr: Bytes::AddressRef, pos: Field) -> (Field, Field) {
      match (*(flat)) {
        Lists::Node::Nil => {  (0, 0) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (member_addr, _is_aux, _sp, _ou) => {
              match Bytes::address_eq(member_addr, target_addr) {
                1 => {  (1, pos) } ,
                _ => {  flat_find_pos(rest, target_addr, pos + 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def flat_find_pos_kind := aiur_fn⟦
  fn flat_find_pos_kind(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                               target_addr: Bytes::AddressRef,
                               want_aux: Field,
                               want_sp: Lists::List<KernelTypes::KExpr>,
                               pos: Field) -> (Field, Field) {
      match (*(flat)) {
        Lists::Node::Nil => {  (0, 0) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (member_addr, is_aux, sp, _ou) => {
              let addr_match = Bytes::address_eq(member_addr, target_addr);
              let kind_eq = match want_aux - is_aux {
                0 => {  1 } ,
                _ => {  0 } ,
              };
              let sp_eq = match want_aux {
                1 => {  spec_params_ptr_eq(sp, want_sp) } ,
                _ => {  1 } ,
              };
              match (addr_match * kind_eq) * sp_eq {
                1 => {  (1, pos) } ,
                _ => {  flat_find_pos_kind(rest, target_addr, want_aux,
                                             want_sp, pos + 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def flat_member_at := aiur_fn⟦
  fn flat_member_at(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                           pos: Field) -> (Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>) {
      match (*(flat)) {
        Lists::Node::Nil => {  ((&([UInt8::BYTE_0; 32])), 0, (&(Lists::Node::Nil)),
                         (&(Lists::Node::Nil))) } ,
        Lists::Node::Cons(m, rest) => {
          match pos {
            0 => {  m } ,
            _ => {  flat_member_at(rest, pos - 1) } ,
          } } ,
      }
    }
⟧

def subst_param_for := aiur_fn⟦
  fn subst_param_for(j: Field, n_rec_params: Field, is_aux: Field,
                            spec_params: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match is_aux {
        0 => {  (&(KernelTypes::KExprNode::BVar((n_rec_params - 1) - j))) } ,
        _ => {
          let len = Lists::length(spec_params);
          match UInt32::less_than_fields(j, len) {
            1 => {  Lists::lookup(spec_params, j) } ,
            _ => {  (&(KernelTypes::KExprNode::BVar((n_rec_params - 1) - j))) } ,
          } } ,
      }
    }
⟧

def peel_motive_params_subst := aiur_fn⟦
  fn peel_motive_params_subst(ty: KernelTypes::KExpr, n: Field, n_rec_params: Field,
                                      is_aux: Field, spec_params: Lists::List<KernelTypes::KExpr>,
                                      j: Field) -> KernelTypes::KExpr {
      match n {
        0 => {  ty } ,
        _ => {
          match (*(ty)) {
            KernelTypes::KExprNode::Forall(_, body, _) => {
              let p = subst_param_for(j, n_rec_params, is_aux, spec_params);
              let body_substed = KernelSubst::expr_inst1(body, p, 0);
              peel_motive_params_subst(body_substed, n - 1, n_rec_params,
                is_aux, spec_params, j + 1) } ,
          } } ,
      }
    }
⟧

  -- The first `n` binder domains of the telescope `ty`, head-normalizing where it is
  -- not syntactically a `∀`. `types` holds the types of the binders `ty` is under
  -- (the recursor's parameters, then the domains peeled so far), so that the
  -- head normalization runs in their context.

def collect_index_doms := aiur_fn⟦
  fn collect_index_doms(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, n: Field,
                        types: Lists::List<KernelTypes::KExpr>) -> Lists::List<KernelTypes::KExpr> {
      match n {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          match (*(ty)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              (&(Lists::Node::Cons(dom,
                collect_index_doms(rc, body, n - 1, (&(Lists::Node::Cons(dom, types))))))) } ,
            _ => {
              match (*(KernelWhnf::whnf(rc, ty, types))) {
                KernelTypes::KExprNode::Forall(dom, body, _) => {
                  (&(Lists::Node::Cons(dom,
                    collect_index_doms(rc, body, n - 1, (&(Lists::Node::Cons(dom, types))))))) } ,
                _ => {  (&(Lists::Node::Nil)) } ,
              } } ,
          } } ,
      }
    }
⟧

def build_major_params := aiur_fn⟦
  fn build_major_params(head: KernelTypes::KExpr, n_rec_params: Field, depth: Field,
                               i: Field) -> KernelTypes::KExpr {
      match n_rec_params - i {
        0 => {  head } ,
        _ => {
          let v = (&(KernelTypes::KExprNode::BVar(((n_rec_params - 1) - i) + depth)));
          build_major_params((&(KernelTypes::KExprNode::App(head, v))),
            n_rec_params, depth, i + 1) } ,
      }
    }
⟧

def apply_spec_params_lifted := aiur_fn⟦
  fn apply_spec_params_lifted(head: KernelTypes::KExpr, spec_params: Lists::List<KernelTypes::KExpr>,
                                      depth: Field) -> KernelTypes::KExpr {
      match (*(spec_params)) {
        Lists::Node::Nil => {  head } ,
        Lists::Node::Cons(sp, rest) => {
          let lifted = KernelSubst::expr_lift(sp, depth, 0);
          apply_spec_params_lifted((&(KernelTypes::KExprNode::App(head, lifted))),
            rest, depth) } ,
      }
    }
⟧

def build_major_args_for_member := aiur_fn⟦
  inline fn build_major_args_for_member(head: KernelTypes::KExpr, n_rec_params: Field,
                                         depth: Field, is_aux: Field,
                                         spec_params: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match is_aux {
        0 => {  build_major_params(head, n_rec_params, depth, 0) } ,
        _ => {  apply_spec_params_lifted(head, spec_params, depth) } ,
      }
    }
⟧

def build_major_indices := aiur_fn⟦
  fn build_major_indices(head: KernelTypes::KExpr, n_indices: Field, i: Field) -> KernelTypes::KExpr {
      match n_indices - i {
        0 => {  head } ,
        _ => {
          let v = (&(KernelTypes::KExprNode::BVar((n_indices - 1) - i)));
          build_major_indices((&(KernelTypes::KExprNode::App(head, v))),
            n_indices, i + 1) } ,
      }
    }
⟧

def wrap_foralls := aiur_fn⟦
  fn wrap_foralls(body: KernelTypes::KExpr, doms: Lists::List<KernelTypes::KExpr>, dl: KernelTypes::KLevel) -> KernelTypes::KExpr {
      match (*(doms)) {
        Lists::Node::Nil => {  body } ,
        Lists::Node::Cons(dom, rest) => {
          (&(KernelTypes::KExprNode::Forall(dom, wrap_foralls(body, rest, dl), dl))) } ,
      }
    }
⟧

  -- The first `n` binder domains of the telescope `ty` and what follows them,
  -- head-normalizing where it is not syntactically a `∀`, in the context `types`
  -- extended by the domains peeled so far.

def collect_n_doms_whnf := aiur_fn⟦
  fn collect_n_doms_whnf(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, n: Field,
                         types: Lists::List<KernelTypes::KExpr>) -> (Lists::List<KernelTypes::KExpr>, KernelTypes::KExpr) {
      match n {
        0 => {  ((&(Lists::Node::Nil)), ty) } ,
        _ => {

          match (*(ty)) {
            KernelTypes::KExprNode::Forall(dom, body, _) => {
              match collect_n_doms_whnf(rc, body, n - 1, (&(Lists::Node::Cons(dom, types)))) {
                (rest, after) => {  ((&(Lists::Node::Cons(dom, rest))), after) } ,
              } } ,
            _ => {
              match (*(KernelWhnf::whnf(rc, ty, types))) {
                KernelTypes::KExprNode::Forall(dom, body, _) => {
                  match collect_n_doms_whnf(rc, body, n - 1, (&(Lists::Node::Cons(dom, types)))) {
                    (rest, after) => {  ((&(Lists::Node::Cons(dom, rest))), after) } ,
                  } } ,

                _ => {  ((&(Lists::Node::Nil)), ty) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- The context of a recursor's parameters, innermost first (a `types` list): the
  -- parameter domains of its block's first type at the recursor's levels, as
  -- `build_rec_type_from` peels them. Field and index types written in terms of the
  -- parameters are head-normalized in this context.

def rec_param_ctx := aiur_fn⟦
  fn rec_param_ctx(rc: KernelRoles::RoleCtx,
                   flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                   n_params: Field) -> Lists::List<KernelTypes::KExpr> {
      match flat_member_at(flat, 0) {
        (prim_addr, _pia, _pisp, prim_us) => {
          match (*(Ingress::get_ci(prim_addr))) {
            KernelTypes::KConstantInfo::Induct(_, prim_ty, _, _, _, _, _, _) => {
              match collect_n_doms_whnf(rc, KernelLevels::expr_inst_levels(prim_ty, prim_us), n_params,
                      (&(Lists::Node::Nil))) {
                (doms, _) => {  Lists::reverse(doms) } ,
              } } ,
            _ => {  (&(Lists::Node::Nil)) } ,
          } } ,
      }
    }
⟧

def list_lift_indices := aiur_fn⟦
  fn list_lift_indices(doms: Lists::List<KernelTypes::KExpr>, shift: Field, i: Field) -> Lists::List<KernelTypes::KExpr> {
      match (*(doms)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(d, rest) => {
          (&(Lists::Node::Cons(KernelSubst::expr_lift(d, shift, i),
                              list_lift_indices(rest, shift, i + 1)))) } ,
      }
    }
⟧

def build_major_args_for_self := aiur_fn⟦
  inline fn build_major_args_for_self(head: KernelTypes::KExpr, n_rec_params: Field,
                                       top_bvar: Field, spec_lift: Field,
                                       is_aux: Field,
                                       spec_params: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match is_aux {
        1 => {  apply_spec_params_lifted(head, spec_params, spec_lift) } ,
        _ => {  build_apply_bvars_decreasing(head, n_rec_params, top_bvar, 0) } ,
      }
    }
⟧

def apply_indices_in_conclusion := aiur_fn⟦
  fn apply_indices_in_conclusion(head: KernelTypes::KExpr, n_indices: Field, i: Field) -> KernelTypes::KExpr {
      match n_indices - i {
        0 => {  head } ,
        _ => {
          let v = (&(KernelTypes::KExprNode::BVar(n_indices - i)));
          apply_indices_in_conclusion((&(KernelTypes::KExprNode::App(head, v))),
            n_indices, i + 1) } ,
      }
    }
⟧

def build_motive_type_flat := aiur_fn⟦
  fn build_motive_type_flat(rc: KernelRoles::RoleCtx, member_addr: Bytes::AddressRef, ind_ty: KernelTypes::KExpr,
                                    n_own_params: Field, n_indices: Field,
                                    occurrence_us: Lists::List<KernelTypes::KLevel>,
                                    elim_level: KernelTypes::KLevel,
                                    n_rec_params: Field,
                                    is_aux: Field,
                                    spec_params: Lists::List<KernelTypes::KExpr>,
                                    ptypes: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let ind_ty_inst = KernelLevels::expr_inst_levels(ind_ty, occurrence_us);
      let after_params = peel_motive_params_subst(ind_ty_inst, n_own_params,
        n_rec_params, is_aux, spec_params, 0);
      let index_doms = collect_index_doms(rc, after_params, n_indices, ptypes);
      let head = (&(KernelTypes::KExprNode::Const(member_addr, occurrence_us)));
      let with_args = build_major_args_for_member(head, n_rec_params,
        n_indices, is_aux, spec_params);
      let major_ty = build_major_indices(with_args, n_indices, 0);
      let sort_e = (&(KernelTypes::KExprNode::Srt(elim_level)));
      let never = (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))));
      let with_major = (&(KernelTypes::KExprNode::Forall(major_ty, sort_e, never)));
      wrap_foralls(with_major, index_doms, never)
    }
⟧

def build_all_motives := aiur_fn⟦
  fn build_all_motives(rc: KernelRoles::RoleCtx, flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                              elim_level: KernelTypes::KLevel, n_rec_params: Field)
                              -> Lists::List<KernelTypes::KExpr> {
      build_all_motives_walk(rc, flat, elim_level, n_rec_params, 0,
        rec_param_ctx(rc, flat, n_rec_params))
    }
⟧

def build_motive_apps := aiur_fn⟦
  fn build_motive_apps(head: KernelTypes::KExpr, n_motives: Field, start: Field,
                               i: Field) -> KernelTypes::KExpr {
      match n_motives - i {
        0 => {  head } ,
        _ => {
          let v = (&(KernelTypes::KExprNode::BVar(start - i)));
          build_motive_apps((&(KernelTypes::KExprNode::App(head, v))), n_motives,
            start, i + 1) } ,
      }
    }
⟧

def build_minor_apps := aiur_fn⟦
  fn build_minor_apps(head: KernelTypes::KExpr, n_minors: Field, start: Field,
                              i: Field) -> KernelTypes::KExpr {
      match n_minors - i {
        0 => {  head } ,
        _ => {
          let v = (&(KernelTypes::KExprNode::BVar(start - i)));
          build_minor_apps((&(KernelTypes::KExprNode::App(head, v))), n_minors,
            start, i + 1) } ,
      }
    }
⟧

def wrap_lams := aiur_fn⟦
  fn wrap_lams(body: KernelTypes::KExpr, doms: Lists::List<KernelTypes::KExpr>, dl: KernelTypes::KLevel) -> KernelTypes::KExpr {
      match (*(doms)) {
        Lists::Node::Nil => {  body } ,
        Lists::Node::Cons(dom, rest) => {
          (&(KernelTypes::KExprNode::Lam(dom, wrap_lams(body, rest, dl), dl))) } ,
      }
    }
⟧

def build_rec_type := aiur_fn⟦
  fn build_rec_type(rc: KernelRoles::RoleCtx, ind_ty: KernelTypes::KExpr, ind_nlvls: Field, n_params: Field, n_indices: Field,
                            elim_level: KernelTypes::KLevel, univ_offset: Field,
                            flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                            flat_own_params: Lists::List<Field>, self_pos: Field) -> KernelTypes::KExpr {

      match flat_member_at(flat, 0) {
        (prim_addr, _pia, _pisp, _piou) => {
          match (*(Ingress::get_ci(prim_addr))) {
            KernelTypes::KConstantInfo::Induct(prim_nlvls, prim_ty, _, _, _, _, _, _) => {
              build_rec_type_from(rc, prim_ty, prim_nlvls, ind_ty, ind_nlvls,
                n_params, n_indices, elim_level, univ_offset, flat,
                flat_own_params, self_pos) } ,
            _ => {
              build_rec_type_from(rc, ind_ty, ind_nlvls, ind_ty, ind_nlvls,
                n_params, n_indices, elim_level, univ_offset, flat,
                flat_own_params, self_pos) } ,
          } } ,
      }
    }
⟧

def build_rec_type_from := aiur_fn⟦
  fn build_rec_type_from(rc: KernelRoles::RoleCtx, prim_ty: KernelTypes::KExpr, prim_nlvls: Field,
                                 ind_ty: KernelTypes::KExpr, ind_nlvls: Field,
                                 n_params: Field, n_indices: Field,
                                 elim_level: KernelTypes::KLevel, univ_offset: Field,
                                 flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                 flat_own_params: Lists::List<Field>, self_pos: Field) -> KernelTypes::KExpr {
      let n_motives = Lists::length(flat);
      let motive_base = n_params;

      let p_us = build_param_lvls_range(univ_offset, prim_nlvls, 0);
      match collect_n_doms_whnf(rc, KernelLevels::expr_inst_levels(prim_ty, p_us), n_params,
              (&(Lists::Node::Nil))) {
        (param_doms, after_params) => {
          let motive_doms = build_all_motives(rc, flat, elim_level, n_params);
          let minor_doms = build_all_minors(rc, flat, flat_own_params, n_params,
            n_motives, motive_base, elim_level);
          let n_minors = Lists::length(minor_doms);
          let (self_addr, self_is_aux, self_spec_params, self_occ_us) =
            flat_member_at(flat, self_pos);

          let KernelTypes::KConstantInfo::Induct(_, self_ind_ty, self_own_params,
            _, _, _, _, _) = (*(Ingress::get_ci(self_addr)));
          let self_ty_inst = KernelLevels::expr_inst_levels(self_ind_ty, self_occ_us);
          let self_after_params = peel_motive_params_subst(self_ty_inst,
            self_own_params, n_params, self_is_aux, self_spec_params, 0);
          let index_doms_raw = collect_index_doms(rc, self_after_params,
            n_indices, Lists::reverse(param_doms));
          let index_doms = list_lift_indices(index_doms_raw,
            n_motives + n_minors, 0);
          let head = (&(KernelTypes::KExprNode::Const(self_addr, self_occ_us)));
          let pre_major_depth = ((n_params + n_motives) + n_minors) + n_indices;
          let with_args = build_major_args_for_self(head, n_params,
            pre_major_depth - 1, (n_motives + n_minors) + n_indices,
            self_is_aux, self_spec_params);
          let major_ty = build_major_indices(with_args, n_indices, 0);

          let depth_after_major = pre_major_depth + 1;
          let motive_var = (depth_after_major - 1) - (motive_base + self_pos);
          let motive_ref = (&(KernelTypes::KExprNode::BVar(motive_var)));
          let with_indices = apply_indices_in_conclusion(motive_ref,
            n_indices, 0);
          let conclusion = (&(KernelTypes::KExprNode::App(with_indices,
            (&(KernelTypes::KExprNode::BVar(0))))));
          let with_major = (&(KernelTypes::KExprNode::Forall(major_ty, conclusion, elim_level)));
          let with_idx_foralls = wrap_foralls(with_major, index_doms, elim_level);
          let with_minors = wrap_foralls(with_idx_foralls, minor_doms, elim_level);
          let with_motives = wrap_foralls(with_minors, motive_doms, elim_level);
          wrap_foralls(with_motives, param_doms, elim_level) } ,
      }
    }
⟧

def check_recursor_canonical_full := aiur_fn⟦
  fn check_recursor_canonical_full(rc: KernelRoles::RoleCtx, rec_ci: KernelTypes::KConstantInfo, addr: Bytes::AddressRef,
                                            parent_ci: KernelTypes::KConstantInfo,
                                            parent_addr: Bytes::AddressRef) -> () {
      match rec_ci {
        KernelTypes::KConstantInfo::Rec(nlvls, ty, n_p, n_i, n_mot, n_min, rules,
                            _k_flag, _uns, rec_block_addr, _rec_idx) => {
          match parent_ci {
            KernelTypes::KConstantInfo::Induct(pnlvls, pty, pnp, pni, num_ctors, _,
                                   parent_block_addr, parent_ind_idx) => {
              let single_ctor_pair = match num_ctors {
                1 => {
                  let cci = (*(Ingress::get_ci_cprj(parent_block_addr,
                    parent_ind_idx, 0)));
                  (1, cci) } ,
                _ => {
                  (0, KernelTypes::KConstantInfo::Axiom(0, (&(KernelTypes::KExprNode::Srt(
                    (&(KernelTypes::KLevelNode::Zero))))), 0)) } ,
              };
              let result_level = get_result_sort_level(rc, pty, pnp + pni,
                (&(Lists::Node::Nil)));
              let univ_offset = is_large_eliminator(rc, result_level,
                num_ctors, single_ctor_pair,
                ind_is_solo(parent_block_addr, parent_addr));
              let elim_level = match univ_offset {
                1 => {  (&(KernelTypes::KLevelNode::Param(0))) } ,
                _ => {  (&(KernelTypes::KLevelNode::Zero)) } ,
              };
              let rec_lvls_list = build_rec_lvls_list(nlvls, 0);
              let flat = build_flat_block(rec_block_addr, parent_block_addr,
                                                univ_offset);
              let peer_recs = build_peer_recs(flat, rec_block_addr, addr);
              let flat_own_params = build_flat_own_params(flat);
              let rec_is_aux = is_muts_block(rec_block_addr) *
                is_muts_block(parent_block_addr) *
                (1 - Bytes::address_eq(rec_block_addr, parent_block_addr));
              let rec_spec_params = match rec_is_aux {
                1 => {  extract_aux_spec_params_from_rec(rec_ci, pnp) } ,
                _ => {  (&(Lists::Node::Nil)) } ,
              };

              let kind_hit = flat_find_pos_kind(flat, parent_addr,
                                                      rec_is_aux,
                                                      rec_spec_params, 0);
              match kind_hit {
                (1, self_pos) => {
                  canonical_rules_at_pos(rc, flat, self_pos, num_ctors,
                    parent_block_addr, parent_ind_idx, n_p, n_mot, n_min,
                    rec_lvls_list, peer_recs, flat_own_params, rules,
                    ty, pty, pnlvls, pni, elim_level, univ_offset) } ,
                _ => {
                  match flat_find_pos(flat, parent_addr, 0) {
                    (1, self_pos) => {
                      canonical_rules_at_pos(rc, flat, self_pos, num_ctors,
                        parent_block_addr, parent_ind_idx, n_p, n_mot,
                        n_min, rec_lvls_list, peer_recs, flat_own_params,
                        rules, ty, pty, pnlvls, pni, elim_level, univ_offset) } ,
                  } } ,
              } } ,
            _ => {  () } ,
          } } ,
      }
    }
⟧

def canonical_rules_at_pos := aiur_fn⟦
  fn canonical_rules_at_pos(rc: KernelRoles::RoleCtx, flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                   self_pos: Field, num_ctors: Field,
                                   parent_block_addr: Bytes::AddressRef,
                                   parent_ind_idx: Field, n_p: Field, n_mot: Field,
                                   n_min: Field, rec_lvls_list: Lists::List<KernelTypes::KLevel>,
                                   peer_recs: Lists::List<Bytes::AddressRef>,
                                   flat_own_params: Lists::List<Field>,
                                   rules: Lists::List<KernelTypes::KRecRule>,
                                   ty: KernelTypes::KExpr, pty: KernelTypes::KExpr, pnlvls: Field, pni: Field,
                                   elim_level: KernelTypes::KLevel, univ_offset: Field) -> () {
      match flat_member_at(flat, self_pos) {
        (_, is_aux, spec_params, occ_us) => {

          let canonical_ty = build_rec_type(rc, pty, pnlvls, n_p, pni, elim_level,
            univ_offset, flat, flat_own_params, self_pos);
          assert_eq!(KernelDefEq::k_is_def_eq(rc, ty, canonical_ty, (&(Lists::Node::Nil))), 1,
            "recursor's declared type is not def-eq to the canonical reconstruction");

          let canon_n_motives = Lists::length(flat);
          let canon_n_minors = Lists::length(build_all_minors(rc, flat,
            flat_own_params, n_p, canon_n_motives, n_p, elim_level));
          assert_eq!(n_mot, canon_n_motives,
            "recursor motive count disagrees with the canonical reconstruction");
          assert_eq!(n_min, canon_n_minors,
            "recursor minor count disagrees with the canonical reconstruction");
          let self_ctors_offset = ctors_before_pos(flat, self_pos, 0);
          let canonical = populate_rules(rc, num_ctors, self_ctors_offset,
            parent_block_addr, parent_ind_idx, n_p, n_mot, n_min, occ_us,
            rec_lvls_list, flat, peer_recs, flat_own_params, is_aux,
            spec_params, 0, elim_level);
          compare_rules(rc, rules, canonical, n_p, n_mot, n_min,
            parent_block_addr, parent_ind_idx, num_ctors, 0, elim_level) } ,
      }
    }
⟧

def ctors_before_pos := aiur_fn⟦
  fn ctors_before_pos(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                              target_pos: Field, cur_pos: Field) -> Field {
      match cur_pos - target_pos {
        0 => {  0 } ,
        _ => {
          match (*(flat)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(m, rest) => {
              match m {
                (addr, _, _, _) => {
                  let ci = (*(Ingress::get_ci(addr)));
                  let n = match ci {
                    KernelTypes::KConstantInfo::Induct(_, _, _, _, nc, _, _, _) => {  nc } ,
                    _ => {  0 } ,
                  };
                  n + ctors_before_pos(rest, target_pos, cur_pos + 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def populate_rules := aiur_fn⟦
  fn populate_rules(rc: KernelRoles::RoleCtx, num_ctors: Field, self_ctors_offset: Field,
                            block_addr: Bytes::AddressRef, ind_idx: Field,
                            n_params: Field, n_motives: Field, n_minors: Field,
                            occurrence_us: Lists::List<KernelTypes::KLevel>,
                            rec_lvls_list: Lists::List<KernelTypes::KLevel>,
                            flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                            peer_recs: Lists::List<Bytes::AddressRef>,
                            flat_own_params: Lists::List<Field>,
                            is_aux: Field, spec_params: Lists::List<KernelTypes::KExpr>,
                            cidx: Field, elim: KernelTypes::KLevel) -> Lists::List<KernelTypes::KExpr> {
      match num_ctors - cidx {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          let ctor_ci = (*(Ingress::get_ci_cprj(block_addr, ind_idx, cidx)));
          match ctor_ci {
            KernelTypes::KConstantInfo::Ctor(_, ctor_ty, _, _, _, np, _, _) => {
              let ctor_minor_index = self_ctors_offset + cidx;
              let rhs = build_rule_rhs(rc, ctor_ty, ctor_minor_index,
                n_params, n_motives, n_minors, np, occurrence_us,
                rec_lvls_list, flat, peer_recs, flat_own_params,
                is_aux, spec_params, elim);
              (&(Lists::Node::Cons(rhs,
                populate_rules(rc, num_ctors, self_ctors_offset, block_addr,
                  ind_idx, n_params, n_motives, n_minors, occurrence_us,
                  rec_lvls_list, flat, peer_recs, flat_own_params, is_aux,
                  spec_params, cidx + 1, elim)))) } ,
            _ => {  (&(Lists::Node::Nil)) } ,
          } } ,
      }
    }
⟧

def compare_rules := aiur_fn⟦
  fn compare_rules(rc: KernelRoles::RoleCtx, stored: Lists::List<KernelTypes::KRecRule>, canonical: Lists::List<KernelTypes::KExpr>,
                          n_p: Field, n_mot: Field, n_min: Field,
                          block_addr: Bytes::AddressRef, ind_idx: Field, num_ctors: Field, pos: Field,
                          elim: KernelTypes::KLevel) -> () {
      match (*(stored)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          match r {
            KernelTypes::KRecRule::Mk(cidx, nf, rhs) => {

              assert_eq!(cidx, pos,
                "recursor rule is out of ctor order");
              assert_eq!(UInt32::less_than_fields(cidx, num_ctors), 1,
                "recursor rule names a ctor index out of range");
              let ctor_ci = (*(Ingress::get_ci_cprj(block_addr, ind_idx, cidx)));
              match ctor_ci {
                KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, _, c_nf, _) => {
                  assert_eq!(nf, c_nf,
                    "recursor rule field count differs from the ctor's");
                  () } ,
              };
              match (*(canonical)) {
                Lists::Node::Nil => {  () } ,
                Lists::Node::Cons(cbody, crest) => {
                  let total = ((n_p + n_mot) + n_min) + nf;
                  match peel_rule_lams(rhs, total, 0,
                          (&(Lists::Node::Nil)), elim) {
                    (stored_body, peeled, _) => {
                      assert_eq!(peeled, total,
                        "recursor rule rhs has too few binders to peel");

                      assert_eq!(KernelDefEq::k_is_def_eq(rc, stored_body, cbody,
                          (&(Lists::Node::Nil))), 1,
                        "recursor rule rhs differs from canonical reconstruction");
                      () } ,
                  };
                  compare_rules(rc, rest, crest, n_p, n_mot, n_min,
                    block_addr, ind_idx, num_ctors, pos + 1, elim) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- The rule's inductive hypotheses, one per recursive field. `norm_doms` are the
  -- fields' types with every step of their telescopes head-normalized
  -- (`walk_fields_classify`), so the field's arguments `xs` and the indices of its
  -- type are read off syntactically.

def apply_ihs_full := aiur_fn⟦
  fn apply_ihs_full(head: KernelTypes::KExpr, rec_indices: Lists::List<Field>,
                            rec_member_idxs: Lists::List<Field>,
                            norm_doms: Lists::List<KernelTypes::KExpr>,
                            peer_recs: Lists::List<Bytes::AddressRef>,
                            flat_own_params: Lists::List<Field>,
                            n_params: Field, n_motives: Field, n_minors: Field,
                            n_fields: Field, rec_lvls_list: Lists::List<KernelTypes::KLevel>,
                            k: Field, elim: KernelTypes::KLevel) -> KernelTypes::KExpr {
      match (*(rec_indices)) {
        Lists::Node::Nil => {  head } ,
        Lists::Node::Cons(field_idx, rest) => {
          let mem_idx = Lists::lookup_or_default(rec_member_idxs, k, 0);
          let target_rec = Lists::lookup_or_default(peer_recs, mem_idx,
            (&([UInt8::BYTE_0; 32])));
          let target_n_params = Lists::lookup_or_default(flat_own_params,
            mem_idx, 0);
          let body_depth = ((n_params + n_motives) + n_minors) + n_fields;
          let dom = Lists::lookup(norm_doms, field_idx);
          let dom_s1 = KernelSubst::expr_lift(dom, n_fields - field_idx, 0);
          let dom_lifted = KernelSubst::expr_lift(dom_s1, n_motives + n_minors, n_fields);
          match peel_leading_foralls(dom_lifted) {
            (forall_doms, inner_body) => {
              let n_xs = Lists::length(forall_doms);
              let inner_depth = body_depth + n_xs;
              let rec_const = (&(KernelTypes::KExprNode::Const(target_rec, rec_lvls_list)));
              let with_params = build_apply_bvars_decreasing(rec_const,
                n_params, inner_depth - 1, 0);
              let with_motives = build_motive_apps(with_params, n_motives,
                (inner_depth - 1) - n_params, 0);
              let with_minors = build_minor_apps(with_motives, n_minors,
                ((inner_depth - 1) - n_params) - n_motives, 0);

              match KernelTypes::collect_spine(inner_body) {
                (_dh, dargs) => {
                  let idx_args = Lists::drop(dargs, target_n_params);
                  let with_idx = apply_spine_expr(with_minors, idx_args);
                  let field_base = ((n_fields - 1) - field_idx) + n_xs;
                  let field_ref = (&(KernelTypes::KExprNode::BVar(field_base)));
                  let field_app = build_apply_xs(field_ref, n_xs, 0);
                  let ih_inner = (&(KernelTypes::KExprNode::App(with_idx, field_app)));
                  let ih = wrap_lams(ih_inner, forall_doms, elim);
                  let new_head = (&(KernelTypes::KExprNode::App(head, ih)));
                  apply_ihs_full(new_head, rest, rec_member_idxs,
                    norm_doms, peer_recs, flat_own_params, n_params,
                    n_motives, n_minors, n_fields, rec_lvls_list, k + 1, elim) } ,
              } } ,
          } } ,
      }
    }
⟧

def build_rule_rhs := aiur_fn⟦
  fn build_rule_rhs(rc: KernelRoles::RoleCtx, ctor_ty: KernelTypes::KExpr, ctor_minor_index: Field,
                            n_params: Field, n_motives: Field, n_minors: Field,
                            n_own_params: Field,
                            occurrence_us: Lists::List<KernelTypes::KLevel>,
                            rec_lvls_list: Lists::List<KernelTypes::KLevel>,
                            flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                            peer_recs: Lists::List<Bytes::AddressRef>,
                            flat_own_params: Lists::List<Field>,
                            is_aux: Field, spec_params: Lists::List<KernelTypes::KExpr>, elim: KernelTypes::KLevel) -> KernelTypes::KExpr {
      let ctor_ty_inst = KernelLevels::expr_inst_levels(ctor_ty, occurrence_us);
      let after_params_raw = peel_n_foralls(ctor_ty_inst, n_own_params);
      let n_fields = count_foralls_body(after_params_raw, 0);
      let body_depth = ((n_params + n_motives) + n_minors) + n_fields;

      let ptypes = rec_param_ctx(rc, flat, n_params);
      let after_params = peel_ctor_params_subst(rc, ctor_ty_inst, n_own_params,
        n_own_params, 0, is_aux, spec_params, 0, ptypes);

      match walk_fields_classify(rc, after_params, flat, (&(Lists::Node::Nil)),
              (&(Lists::Node::Nil)), (&(Lists::Node::Nil)), (&(Lists::Node::Nil)), 0, 0, ptypes) {
        (_field_doms, rec_indices, rec_member_idxs, _ret_ty, norm_doms) => {
          let minor_var = (body_depth - 1) - ((n_params + n_motives) +
                                                ctor_minor_index);
          let base = (&(KernelTypes::KExprNode::BVar(minor_var)));
          let with_fields = build_apply_field_bvars(base, n_fields,
            n_fields, 0);
          apply_ihs_full(with_fields, rec_indices, rec_member_idxs,
            norm_doms, peer_recs, flat_own_params, n_params, n_motives,
            n_minors, n_fields, rec_lvls_list, 0, elim) } ,
      }
    }
⟧

def build_peer_recs := aiur_fn⟦
  fn build_peer_recs(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                            rec_block_addr: Bytes::AddressRef,
                            rec_self_addr: Bytes::AddressRef) -> Lists::List<Bytes::AddressRef> {
      match (*(flat)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (member_addr, is_aux, sp, _ou) => {
              let peer = find_peer_recursor_with_spec(rec_block_addr,
                member_addr, sp, is_aux, rec_self_addr);
              (&(Lists::Node::Cons(peer,
                build_peer_recs(rest, rec_block_addr, rec_self_addr)))) } ,
          } } ,
      }
    }
⟧

def find_peer_recursor_with_spec := aiur_fn⟦
  fn find_peer_recursor_with_spec(block_addr: Bytes::AddressRef,
                                          target_ind_addr: Bytes::AddressRef,
                                          target_sp: Lists::List<KernelTypes::KExpr>,
                                          target_is_aux: Field,
                                          rec_self_addr: Bytes::AddressRef) -> Bytes::AddressRef {
      let block_c = Ingress::load_verified_constant(block_addr);
      match block_c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              find_peer_rec_spec_walk(members, members, block_addr,
                target_ind_addr, target_sp, target_is_aux, rec_self_addr, 0) } ,
            _ => {  rec_self_addr } ,
          } } ,
      }
    }
⟧

def find_peer_rec_spec_walk := aiur_fn⟦
  fn find_peer_rec_spec_walk(all_members: Lists::List<Ixon::MutConst>,
                                     cur: Lists::List<Ixon::MutConst>, block_addr: Bytes::AddressRef,
                                     target_ind_addr: Bytes::AddressRef,
                                     target_sp: Lists::List<KernelTypes::KExpr>,
                                     target_is_aux: Field,
                                     rec_self_addr: Bytes::AddressRef, pos: Field) -> Bytes::AddressRef {
      match (*(cur)) {
        Lists::Node::Nil => {  rec_self_addr } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Recr(_) => {
              let rec_wrapper = Ingress::projection_addr(all_members, block_addr, pos);
              let rec_ci = (*(Ingress::get_ci(rec_wrapper)));
              let is_match = match rec_ci {
                KernelTypes::KConstantInfo::Rec(_, ty, np, ni, nmot, nmin, _, _, _, _, _) => {
                  let parent = rec_to_parent_addr(ty, np, nmot, nmin, ni);
                  let parent_ci = (*(Ingress::get_ci(parent)));
                  let pnp = match parent_ci {
                    KernelTypes::KConstantInfo::Induct(_, _, p, _, _, _, _, _) => {  p } ,
                    _ => {  0 } ,
                  };
                  let addr_m = Bytes::address_eq(parent, target_ind_addr);
                  match addr_m {
                    1 => {
                      match target_is_aux {
                        0 => {  1 } ,
                        _ => {
                          let rec_sp = extract_aux_spec_params(ty, np,
                            nmot, nmin, ni, pnp);
                          spec_params_ptr_eq(rec_sp, target_sp) } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              };
              match is_match {
                1 => {  rec_wrapper } ,
                _ => {
                  find_peer_rec_spec_walk(all_members, rest, block_addr,
                    target_ind_addr, target_sp, target_is_aux,
                    rec_self_addr, pos + 1) } ,
              } } ,
            _ => {
              find_peer_rec_spec_walk(all_members, rest, block_addr,
                target_ind_addr, target_sp, target_is_aux, rec_self_addr,
                pos + 1) } ,
          } } ,
      }
    }
⟧

def build_flat_own_params := aiur_fn⟦
  fn build_flat_own_params(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>)
                                    -> Lists::List<Field> {
      match (*(flat)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (member_addr, _is_aux, _sp, _ou) => {
              let ci = (*(Ingress::get_ci(member_addr)));
              let np = match ci {
                KernelTypes::KConstantInfo::Induct(_, _, n, _, _, _, _, _) => {  n } ,
                _ => {  0 } ,
              };
              (&(Lists::Node::Cons(np,
                build_flat_own_params(rest)))) } ,
          } } ,
      }
    }
⟧

def projection_addr_ctor := aiur_fn⟦
  fn projection_addr_ctor(ind_idx: Field, cidx: Field,
                                  block_addr: Bytes::AddressRef) -> Bytes::AddressRef {
      let idx_u64 = UInt64::from_field(ind_idx);
      let cidx_u64 = UInt64::from_field(cidx);
      let info = Ixon::ConstantInfo::CPrj(Ixon::ConstructorProj::Mk(idx_u64, cidx_u64,
        block_addr));
      let proj_c = Ixon::Constant::Mk(info,
        (&(Lists::Node::Nil)), (&(Lists::Node::Nil)), (&(Lists::Node::Nil)));
      let bytes = IxonSerialize::put_constant(proj_c, (&(Lists::Node::Nil)));
      Blake3::bytes_to_addr(bytes)
    }
⟧

def build_minor_doms := aiur_fn⟦
  fn build_minor_doms(rc: KernelRoles::RoleCtx, member_addr: Bytes::AddressRef, is_aux: Field,
                              spec_params: Lists::List<KernelTypes::KExpr>,
                              occurrence_us: Lists::List<KernelTypes::KLevel>,
                              flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                              flat_own_params: Lists::List<Field>,
                              n_rec_params: Field, n_motives: Field,
                              motive_base: Field, self_mem_idx: Field,
                              block_addr: Bytes::AddressRef, ind_idx: Field,
                              num_ctors: Field, prev_minors: Field,
                              cidx: Field, elim: KernelTypes::KLevel) -> Lists::List<KernelTypes::KExpr> {
      match num_ctors - cidx {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          let ctor_ci = (*(Ingress::get_ci_cprj(block_addr, ind_idx, cidx)));
          match ctor_ci {
            KernelTypes::KConstantInfo::Ctor(_, ctor_ty, _, _, _, np, _nf, _) => {
              let ctor_addr = projection_addr_ctor(ind_idx, cidx, block_addr);
              let minor = build_minor_at_depth(rc, ctor_addr, ctor_ty, np,
                is_aux, spec_params, occurrence_us, flat, flat_own_params,
                n_rec_params, n_motives, prev_minors, motive_base,
                self_mem_idx, elim);
              (&(Lists::Node::Cons(minor,
                build_minor_doms(rc, member_addr, is_aux, spec_params,
                  occurrence_us, flat, flat_own_params, n_rec_params,
                  n_motives, motive_base, self_mem_idx, block_addr, ind_idx,
                  num_ctors, prev_minors + 1, cidx + 1, elim)))) } ,

          } } ,
      }
    }
⟧

def build_all_minors := aiur_fn⟦
  fn build_all_minors(rc: KernelRoles::RoleCtx, flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                              flat_own_params: Lists::List<Field>,
                              n_rec_params: Field, n_motives: Field,
                              motive_base: Field, elim: KernelTypes::KLevel) -> Lists::List<KernelTypes::KExpr> {
      build_all_minors_walk(rc, flat, flat, flat_own_params, n_rec_params,
        n_motives, motive_base, 0, 0, elim)
    }
⟧

def build_all_minors_walk := aiur_fn⟦
  fn build_all_minors_walk(rc: KernelRoles::RoleCtx, flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                   full_flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                   flat_own_params: Lists::List<Field>,
                                   n_rec_params: Field, n_motives: Field,
                                   motive_base: Field, prev_minors: Field,
                                   mem_pos: Field, elim: KernelTypes::KLevel) -> Lists::List<KernelTypes::KExpr> {
      match (*(flat)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (member_addr, is_aux, spec_params, occ_us) => {
              let ci = (*(Ingress::get_ci(member_addr)));
              match ci {
                KernelTypes::KConstantInfo::Induct(_, _, _, _, num_ctors, _,
                                       mem_block_addr, mem_ind_idx) => {
                  let m_minors = build_minor_doms(rc, member_addr, is_aux,
                    spec_params, occ_us, full_flat, flat_own_params,
                    n_rec_params, n_motives, motive_base, mem_pos,
                    mem_block_addr, mem_ind_idx, num_ctors, prev_minors, 0, elim);
                  let added = Lists::length(m_minors);
                  let rest_minors = build_all_minors_walk(rc, rest, full_flat,
                    flat_own_params, n_rec_params, n_motives, motive_base,
                    prev_minors + added, mem_pos + 1, elim);
                  Lists::concat(m_minors, rest_minors) } ,
                _ => {
                  build_all_minors_walk(rc, rest, full_flat, flat_own_params,
                    n_rec_params, n_motives, motive_base, prev_minors,
                    mem_pos + 1, elim) } ,
              } } ,
          } } ,
      }
    }
⟧

def ctor_subst_param_for := aiur_fn⟦
  fn ctor_subst_param_for(j: Field, depth: Field, spec_lift: Field, is_aux: Field,
                                  spec_params: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match is_aux {
        0 => {  (&(KernelTypes::KExprNode::BVar((depth - 1) - j))) } ,
        _ => {
          let len = Lists::length(spec_params);
          match UInt32::less_than_fields(j, len) {
            1 => {  KernelSubst::expr_lift(Lists::lookup(spec_params, j), spec_lift, 0) } ,
            _ => {  (&(KernelTypes::KExprNode::BVar((depth - 1) - j))) } ,
          } } ,
      }
    }
⟧

def count_foralls_body := aiur_fn⟦
  fn count_foralls_body(ty: KernelTypes::KExpr, acc: Field) -> Field {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(_, body, _) => {  count_foralls_body(body, acc + 1) } ,
        _ => {  acc } ,
      }
    }
⟧

  -- A constructor's type with its first `n` parameters instantiated by the recursor's
  -- (`ctor_subst_param_for`), head-normalizing where it is not syntactically a `∀` in
  -- the context `types` of the binders the instantiation refers to.

def peel_ctor_params_subst := aiur_fn⟦
  fn peel_ctor_params_subst(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr, n: Field, depth: Field, spec_lift: Field,
                                    is_aux: Field, spec_params: Lists::List<KernelTypes::KExpr>,
                                    j: Field, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match n {
        0 => {  ty } ,
        _ => {

          match (*(ty)) {
            KernelTypes::KExprNode::Forall(_, body, _) => {
              let p = ctor_subst_param_for(j, depth, spec_lift, is_aux,
                spec_params);
              let body_substed = KernelSubst::expr_inst1(body, p, 0);
              peel_ctor_params_subst(rc, body_substed, n - 1, depth,
                spec_lift, is_aux, spec_params, j + 1, types) } ,
            _ => {
              match (*(KernelWhnf::whnf(rc, ty, types))) {
                KernelTypes::KExprNode::Forall(_, body, _) => {
                  let p = ctor_subst_param_for(j, depth, spec_lift, is_aux,
                    spec_params);
                  let body_substed = KernelSubst::expr_inst1(body, p, 0);
                  peel_ctor_params_subst(rc, body_substed, n - 1, depth,
                    spec_lift, is_aux, spec_params, j + 1, types) } ,
              } } ,
          } } ,
      }
    }
⟧

def build_minor_at_depth := aiur_fn⟦
  fn build_minor_at_depth(rc: KernelRoles::RoleCtx, ctor_addr: Bytes::AddressRef, ctor_ty: KernelTypes::KExpr,
                                  n_own_params: Field,
                                  is_aux: Field, spec_params: Lists::List<KernelTypes::KExpr>,
                                  occurrence_us: Lists::List<KernelTypes::KLevel>,
                                  flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                  flat_own_params: Lists::List<Field>,
                                  n_rec_params: Field, n_motives: Field,
                                  prev_minors: Field, motive_base: Field,
                                  self_mem_idx: Field, elim: KernelTypes::KLevel) -> KernelTypes::KExpr {
      let ctor_ty_inst = KernelLevels::expr_inst_levels(ctor_ty, occurrence_us);
      let minor_saved = n_rec_params + n_motives + prev_minors;
      let below_params = n_motives + prev_minors;
      -- The fields are read in the parameters' frame, whose context is known (the
      -- recursor's parameters), then lifted over the motives and earlier minors.
      let ptypes = rec_param_ctx(rc, flat, n_rec_params);
      let after_params = peel_ctor_params_subst(rc, ctor_ty_inst, n_own_params,
        n_rec_params, 0, is_aux, spec_params, 0, ptypes);
      match walk_fields_classify(rc, after_params, flat, (&(Lists::Node::Nil)),
              (&(Lists::Node::Nil)), (&(Lists::Node::Nil)), (&(Lists::Node::Nil)), 0, 0, ptypes) {
        (pf_doms, rec_indices, rec_member_idxs, pf_ret, pf_norm) => {
          let n_fields = Lists::length(pf_doms);
          let field_doms = list_lift_indices(pf_doms, below_params, 0);
          let norm_doms = list_lift_indices(pf_norm, below_params, 0);
          let ret_ty = KernelSubst::expr_lift(pf_ret, below_params, n_fields);
          let n_ihs = Lists::length(rec_indices);
          let n_binders = n_fields + n_ihs;
          let depth_now = minor_saved + n_binders;
          match KernelTypes::collect_spine(ret_ty) {
            (_ret_head, ret_args) => {
              let ret_indices = Lists::drop(ret_args, n_own_params);
              let ret_indices_lifted = list_lift_each(ret_indices, n_ihs, 0);
              let motive_var = (depth_now - 1) - (motive_base + self_mem_idx);
              let motive_ref = (&(KernelTypes::KExprNode::BVar(motive_var)));
              let with_indices = apply_spine_expr(motive_ref,
                ret_indices_lifted);
              let ctor_head = (&(KernelTypes::KExprNode::Const(ctor_addr, occurrence_us)));
              let with_params = build_ctor_app_params(ctor_head,
                n_own_params, n_rec_params, depth_now, is_aux, spec_params);
              let ctor_app = build_apply_field_bvars(with_params,
                n_fields, n_binders, 0);
              let conclusion = (&(KernelTypes::KExprNode::App(with_indices, ctor_app)));
              let ih_doms = build_ih_doms(rec_indices, rec_member_idxs,
                norm_doms, flat_own_params, motive_base, n_fields,
                minor_saved, 0, elim);
              let with_ihs = wrap_foralls(conclusion, ih_doms, elim);
              wrap_foralls(with_ihs, field_doms, elim) } ,
          } } ,
      }
    }
⟧

  -- The binders of a telescope, read syntactically. The inductive-hypothesis builders
  -- apply it to field types whose telescopes are head-normalized at every step
  -- (`whnf_tele`), so a `∀` that only head normalization exposes is peeled too.

def peel_leading_foralls := aiur_fn⟦
  fn peel_leading_foralls(ty: KernelTypes::KExpr) -> (Lists::List<KernelTypes::KExpr>, KernelTypes::KExpr) {
      let pair = peel_leading_foralls_acc(ty, (&(Lists::Node::Nil)));
      match pair {
        (rev_acc, body) => {  (Lists::reverse(rev_acc), body) } ,
      }
    }
⟧

def peel_leading_foralls_acc := aiur_fn⟦
  fn peel_leading_foralls_acc(ty: KernelTypes::KExpr, acc: Lists::List<KernelTypes::KExpr>)
                                      -> (Lists::List<KernelTypes::KExpr>, KernelTypes::KExpr) {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          peel_leading_foralls_acc(body, (&(Lists::Node::Cons(dom, acc)))) } ,
        _ => {  (acc, ty) } ,
      }
    }
⟧

def build_apply_xs := aiur_fn⟦
  fn build_apply_xs(head: KernelTypes::KExpr, n_xs: Field, i: Field) -> KernelTypes::KExpr {
      match n_xs - i {
        0 => {  head } ,
        _ => {
          let v = (&(KernelTypes::KExprNode::BVar((n_xs - 1) - i)));
          build_apply_xs((&(KernelTypes::KExprNode::App(head, v))), n_xs, i + 1) } ,
      }
    }
⟧

  -- The minor's inductive-hypothesis binders, one per recursive field, from the
  -- fields' head-normalized telescopes `norm_doms` (`walk_fields_classify`).

def build_ih_doms := aiur_fn⟦
  fn build_ih_doms(rec_indices: Lists::List<Field>, rec_member_idxs: Lists::List<Field>,
                          norm_doms: Lists::List<KernelTypes::KExpr>,
                          flat_own_params: Lists::List<Field>,
                          motive_base: Field, n_fields: Field, minor_saved: Field,
                          k: Field, elim: KernelTypes::KLevel) -> Lists::List<KernelTypes::KExpr> {
      match (*(rec_indices)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(field_idx, rest) => {
          let mem_idx = Lists::lookup_or_default(rec_member_idxs, k, 0);
          let target_n_params = Lists::lookup_or_default(flat_own_params,
            mem_idx, 0);
          let depth = minor_saved + n_fields + k;
          let dom = Lists::lookup(norm_doms, field_idx);
          let dom_lifted = KernelSubst::expr_lift(dom, (n_fields - field_idx) + k, 0);
          match peel_leading_foralls(dom_lifted) {
            (forall_doms, inner_body) => {
              let n_xs = Lists::length(forall_doms);
              let inner_depth = depth + n_xs;
              let motive_bvar = (inner_depth - 1) - (motive_base + mem_idx);
              let field_bvar = (inner_depth - 1) - (minor_saved + field_idx);

              match KernelTypes::collect_spine(inner_body) {
                (_h, dom_args) => {
                  let idx_args = Lists::drop(dom_args, target_n_params);
                  let motive_ref = (&(KernelTypes::KExprNode::BVar(motive_bvar)));
                  let with_indices = apply_spine_expr(motive_ref, idx_args);
                  let field_ref = (&(KernelTypes::KExprNode::BVar(field_bvar)));
                  let field_app = build_apply_xs(field_ref, n_xs, 0);
                  let ih_body = (&(KernelTypes::KExprNode::App(with_indices, field_app)));
                  let ih_dom = wrap_foralls(ih_body, forall_doms, elim);
                  (&(Lists::Node::Cons(ih_dom,
                    build_ih_doms(rest, rec_member_idxs, norm_doms,
                      flat_own_params, motive_base, n_fields, minor_saved,
                      k + 1, elim)))) } ,
              } } ,
          } } ,
      }
    }
⟧

def list_lift_each := aiur_fn⟦
  fn list_lift_each(es: Lists::List<KernelTypes::KExpr>, shift: Field, cutoff: Field)
                            -> Lists::List<KernelTypes::KExpr> {
      match (*(es)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(e, rest) => {
          (&(Lists::Node::Cons(KernelSubst::expr_lift(e, shift, cutoff),
            list_lift_each(rest, shift, cutoff)))) } ,
      }
    }
⟧

def build_apply_bvars_decreasing := aiur_fn⟦
  fn build_apply_bvars_decreasing(head: KernelTypes::KExpr, n: Field, start: Field,
                                          j: Field) -> KernelTypes::KExpr {
      match n - j {
        0 => {  head } ,
        _ => {
          let v = (&(KernelTypes::KExprNode::BVar(start - j)));
          build_apply_bvars_decreasing((&(KernelTypes::KExprNode::App(head, v))),
            n, start, j + 1) } ,
      }
    }
⟧

def build_apply_field_bvars := aiur_fn⟦
  fn build_apply_field_bvars(head: KernelTypes::KExpr, n_fields: Field, n_binders: Field,
                                     i: Field) -> KernelTypes::KExpr {
      match n_fields - i {
        0 => {  head } ,
        _ => {
          let v = (&(KernelTypes::KExprNode::BVar((n_binders - 1) - i)));
          build_apply_field_bvars((&(KernelTypes::KExprNode::App(head, v))),
            n_fields, n_binders, i + 1) } ,
      }
    }
⟧

def build_ctor_app_params := aiur_fn⟦
  fn build_ctor_app_params(head: KernelTypes::KExpr, n_own_params: Field, n_rec_params: Field,
                                   depth_now: Field, is_aux: Field,
                                   spec_params: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match is_aux {
        0 => {  build_apply_bvars_decreasing(head, n_rec_params,
               depth_now - 1, 0) } ,
        _ => {  apply_spec_params_lifted(head, spec_params,
               depth_now - n_rec_params) } ,
      }
    }
⟧

  -- A field type with its telescope head-normalized at every step, as Lean's kernel
  -- reads a recursive argument (`is_rec_argument`: `whnf`, then the body of each `∀`
  -- in the context extended by its domain). `types` is the context of `ty`.

def whnf_tele := aiur_fn⟦
  fn whnf_tele(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr,
               types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let w = KernelWhnf::whnf(rc, ty, types);
      match (*(w)) {
        KernelTypes::KExprNode::Forall(dom, body, bl) => {
          (&(KernelTypes::KExprNode::Forall(dom,
            whnf_tele(rc, body, (&(Lists::Node::Cons(dom, types)))), bl))) } ,
        _ => {  w } ,
      }
    }
⟧

  -- Whether a head-normalized field telescope (`whnf_tele`) ends in a member of the
  -- flat block, and which.

def is_rec_field_peel := aiur_fn⟦
  fn is_rec_field_peel(ty: KernelTypes::KExpr, flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                              spec_lift_by: Field) -> (Field, Field) {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(_, body, _) => {
          is_rec_field_peel(body, flat, spec_lift_by) } ,
        _ => {
          match KernelTypes::collect_spine(ty) {
            (head, args) => {
              match (*(head)) {
                KernelTypes::KExprNode::Const(caddr, _) => {
                  flat_find_matching(flat, caddr, args, spec_lift_by, 0) } ,
                _ => {  (0, 0) } ,
              } } ,
          } } ,
      }
    }
⟧

def flat_find_matching := aiur_fn⟦
  fn flat_find_matching(flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                caddr: Bytes::AddressRef, dom_args: Lists::List<KernelTypes::KExpr>,
                                spec_lift_by: Field, pos: Field) -> (Field, Field) {
      match (*(flat)) {
        Lists::Node::Nil => {  (0, 0) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (member_addr, is_aux, sp, _) => {
              let addr_match = Bytes::address_eq(member_addr, caddr);
              let spec_match = match is_aux {
                0 => {  1 } ,
                _ => {  spec_params_dom_prefix_match(sp, dom_args,
                       spec_lift_by) } ,
              };
              match addr_match * spec_match {
                1 => {  (1, pos) } ,
                _ => {  flat_find_matching(rest, caddr, dom_args,
                       spec_lift_by, pos + 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def spec_params_dom_prefix_match := aiur_fn⟦
  fn spec_params_dom_prefix_match(sp: Lists::List<KernelTypes::KExpr>,
                                          args: Lists::List<KernelTypes::KExpr>,
                                          lift_by: Field) -> Field {
      match (*(sp)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(s, sr) => {
          match (*(args)) {
            Lists::Node::Nil => {  0 } ,
            Lists::Node::Cons(a, ar) => {
              let s_lifted = KernelSubst::expr_lift(s, lift_by, 0);
              match kexpr_struct_eq(s_lifted, a) {
                1 => {  spec_params_dom_prefix_match(sr, ar, lift_by) } ,
                _ => {  0 } ,
              } } ,
          } } ,
      }
    }
⟧

  -- A constructor's fields after its parameters: their types, the recursive ones
  -- (field index and flat member), the return type, and each field's type
  -- head-normalized at every step of its telescope (`whnf_tele`), in the context
  -- `types` of the binders the field is under (the recursor's parameters, then the
  -- earlier fields).

def walk_fields_classify := aiur_fn⟦
  fn walk_fields_classify(rc: KernelRoles::RoleCtx, ty: KernelTypes::KExpr,
                                  flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                  doms_acc: Lists::List<KernelTypes::KExpr>, rec_acc: Lists::List<Field>,
                                  rec_mem_acc: Lists::List<Field>, norm_acc: Lists::List<KernelTypes::KExpr>,
                                  fidx: Field, spec_lift_by: Field,
                                  types: Lists::List<KernelTypes::KExpr>)
                                  -> (Lists::List<KernelTypes::KExpr>, Lists::List<Field>, Lists::List<Field>, KernelTypes::KExpr,
                                      Lists::List<KernelTypes::KExpr>) {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          let nd = whnf_tele(rc, dom, types);
          let r = is_rec_field_peel(nd, flat, spec_lift_by + fidx);
          let new_doms = (&(Lists::Node::Cons(dom, doms_acc)));
          let new_norm = (&(Lists::Node::Cons(nd, norm_acc)));
          let types2 = (&(Lists::Node::Cons(dom, types)));
          match r {
            (1, mem_idx) => {
              let new_rec = (&(Lists::Node::Cons(fidx, rec_acc)));
              let new_mem = (&(Lists::Node::Cons(mem_idx, rec_mem_acc)));
              walk_fields_classify(rc, body, flat, new_doms, new_rec,
                new_mem, new_norm, fidx + 1, spec_lift_by, types2) } ,
            _ => {
              walk_fields_classify(rc, body, flat, new_doms, rec_acc,
                rec_mem_acc, new_norm, fidx + 1, spec_lift_by, types2) } ,
          } } ,
        _ => {  (Lists::reverse(doms_acc), Lists::reverse(rec_acc),
                Lists::reverse(rec_mem_acc), ty, Lists::reverse(norm_acc)) } ,
      }
    }
⟧

def build_all_motives_walk := aiur_fn⟦
  fn build_all_motives_walk(rc: KernelRoles::RoleCtx, flat: Lists::List<(Bytes::AddressRef, Field, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KLevel>)>,
                                    elim_level: KernelTypes::KLevel, n_rec_params: Field,
                                    j: Field, ptypes: Lists::List<KernelTypes::KExpr>) -> Lists::List<KernelTypes::KExpr> {
      match (*(flat)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            (member_addr, is_aux, spec_params, occ_us) => {
              let ci = (*(Ingress::get_ci(member_addr)));
              match ci {
                KernelTypes::KConstantInfo::Induct(_, m_ind_ty, m_own_params, m_n_indices,
                                       _, _, _, _) => {
                  let mt = build_motive_type_flat(rc, member_addr, m_ind_ty,
                    m_own_params, m_n_indices, occ_us, elim_level,
                    n_rec_params, is_aux, spec_params, ptypes);
                  let mt_lifted = KernelSubst::expr_lift(mt, j, 0);
                  (&(Lists::Node::Cons(mt_lifted,
                    build_all_motives_walk(rc, rest, elim_level, n_rec_params,
                      j + 1, ptypes)))) } ,
                _ => {
                  build_all_motives_walk(rc, rest, elim_level, n_rec_params, j, ptypes) } ,
              } } ,
          } } ,
      }
    }
⟧

def check_recursor_member := aiur_fn⟦
  fn check_recursor_member(rc: KernelRoles::RoleCtx, rec_ci: KernelTypes::KConstantInfo, addr: Bytes::AddressRef) -> () {
      match rec_ci {
        KernelTypes::KConstantInfo::Rec(nlvls, ty, n_p, n_i, n_mot, n_min, rules, k_flag,
                            _uns, rec_block_addr, _rec_idx) => {
          let parent_addr = rec_to_parent_addr(ty, n_p, n_mot, n_min, n_i);
          let parent_ci = (*(Ingress::get_ci(parent_addr)));
          match parent_ci {
            KernelTypes::KConstantInfo::Induct(_parent_nlvls, _, parent_np, parent_ni,
                                   num_ctors, _,
                                   parent_block_addr, parent_ind_idx) => {

              let is_aux = is_muts_block(rec_block_addr) *
                is_muts_block(parent_block_addr) *
                (1 - Bytes::address_eq(rec_block_addr, parent_block_addr));
              assert_eq!(is_aux, 0,
                "a recursor of a native block eliminates an auxiliary family");
              assert_eq!(Lists::length(rules), num_ctors,
                "recursor rule count differs from the inductive's ctor count");
              peel_n_foralls(ty,
                ((n_p + n_mot) + n_min + n_i) + 1);
              check_rec_rules_wellscoped(rules,
                n_p + n_mot + n_min, nlvls);

              match is_aux {
                1 => {  () } ,
                _ => {
                  assert_eq!(n_p, parent_np,
                    "recursor parameter count differs from its inductive's");
                  assert_eq!(n_i, parent_ni,
                    "recursor index count differs from its inductive's");
                  check_rec_major_spine(ty, n_p, n_mot, n_min, n_i,
                                             parent_np + parent_ni) } ,
              };

              let computed_k = compute_k_target(rc, parent_ci, parent_addr);
              assert_eq!(k_flag, computed_k,
                "recursor k_flag disagrees with its inductive's K eligibility");

              check_parent_inductive_shape(rc, parent_ci);

              check_recursor_canonical_full(rc, rec_ci, addr, parent_ci, parent_addr) } ,
          } } ,
      }
    }
⟧

def check_rec_major_spine := aiur_fn⟦
  fn check_rec_major_spine(ty: KernelTypes::KExpr, n_p: Field, n_mot: Field, n_min: Field,
                                  n_i: Field, expected_args: Field) -> () {
      let skip = n_p + n_mot + n_min + n_i;
      let after_skip = peel_n_foralls(ty, skip);
      match (*(after_skip)) {
        KernelTypes::KExprNode::Forall(major_ty, _, _) => {
          match KernelTypes::collect_spine(major_ty) {
            (_head, args) => {
              assert_eq!(Lists::length(args), expected_args,
                "recursor major premise has the wrong number of spine args");
              () } ,
          } } ,
      }
    }
⟧

def apply_spine_expr := aiur_fn⟦
  fn apply_spine_expr(head: KernelTypes::KExpr, args: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(args)) {
        Lists::Node::Nil => {  head } ,
        Lists::Node::Cons(a, rest) => {
          apply_spine_expr((&(KernelTypes::KExprNode::App(head, a))), rest) } ,
      }
    }
⟧

def build_rec_lvls_list := aiur_fn⟦
  fn build_rec_lvls_list(total: Field, i: Field) -> Lists::List<KernelTypes::KLevel> {
      match total - i {
        0 => {  (&(Lists::Node::Nil)) } ,
        _ => {
          (&(Lists::Node::Cons(
            (&(KernelTypes::KLevelNode::Param(i))),
            build_rec_lvls_list(total, i + 1)))) } ,
      }
    }
⟧

def check_rec_rules_wellscoped := aiur_fn⟦
  fn check_rec_rules_wellscoped(rules: Lists::List<KernelTypes::KRecRule>,
                                       outer_depth: Field, nlvls: Field) -> () {
      match (*(rules)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          match r {
            KernelTypes::KRecRule::Mk(_, nf, rhs) => {
              validate_expr_well_scoped(rhs, outer_depth + nf, nlvls);
              check_rec_rules_wellscoped(rest, outer_depth, nlvls) } ,
          } } ,
      }
    }
⟧

def peel_n_lams_collect := aiur_fn⟦
  fn peel_n_lams_collect(e: KernelTypes::KExpr, n: Field, peeled: Field, acc: Lists::List<KernelTypes::KExpr>)
                                -> (KernelTypes::KExpr, Field, Lists::List<KernelTypes::KExpr>) {
      match n {
        0 => {  (e, peeled, acc) } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::Lam(dom, body, _) => {
              peel_n_lams_collect(body, n - 1, peeled + 1,
                (&(Lists::Node::Cons(dom, acc)))) } ,
            _ => {  (e, peeled, acc) } ,
          } } ,
      }
    }
⟧

  -- `peel_n_lams_collect` for a recursor rule (D2): each peeled λ must carry the
  -- elimination level's zero-ness, as the kernel's canonical rules do.

def peel_rule_lams := aiur_fn⟦
  fn peel_rule_lams(e: KernelTypes::KExpr, n: Field, peeled: Field, acc: Lists::List<KernelTypes::KExpr>,
                         elim: KernelTypes::KLevel)
                                -> (KernelTypes::KExpr, Field, Lists::List<KernelTypes::KExpr>) {
      match n {
        0 => {  (e, peeled, acc) } ,
        _ => {
          match (*(e)) {
            KernelTypes::KExprNode::Lam(dom, body, bl) => {
              -- The rule's λs are the kernel's canonical ones, whose data are the
              -- elimination level's zero-ness (the body's type is a motive application).
              assert_eq!(KernelLevels::pw_eq(bl, elim), 1,
                "a recursor rule's binder datum is not the zero-ness of its elimination level");
              peel_rule_lams(body, n - 1, peeled + 1,
                (&(Lists::Node::Cons(dom, acc))), elim) } ,
            _ => {  (e, peeled, acc) } ,
          } } ,
      }
    }
⟧

def muts_has_kind := aiur_fn⟦
  fn muts_has_kind(members: Lists::List<Ixon::MutConst>, kind: Field) -> Field {
      match (*(members)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(m, rest) => {
          let hit = match m {
            Ixon::MutConst::Indc(_) => {
              match kind {
                0 => {  1 } ,
                _ => {  0 } ,
              } } ,
            Ixon::MutConst::Defn(_) => {
              match kind {
                1 => {  1 } ,
                _ => {  0 } ,
              } } ,
            Ixon::MutConst::Recr(_) => {
              match kind {
                2 => {  1 } ,
                _ => {  0 } ,
              } } ,
          };
          match hit {
            1 => {  1 } ,
            _ => {  muts_has_kind(rest, kind) } ,
          } } ,
      }
    }
⟧

def check_block_member_kinds := aiur_fn⟦
  fn check_block_member_kinds(block_addr: Bytes::AddressRef) -> () {
      let c = Ingress::load_verified_constant(block_addr);
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {
              let has_defn = muts_has_kind(members, 1);
              assert_eq!(has_defn * muts_has_kind(members, 0), 0,
                "mutual block mixes a definition member with inductives");
              let (n_unsafe, n_all) = muts_safety_counts(members, 0, 0);
              assert_eq!(n_unsafe * (n_all - n_unsafe), 0,
                "mutual block mixes safe members with unsafe or partial ones");
              assert_eq!(has_defn * muts_has_kind(members, 2), 0,
                "mutual block mixes a definition member with recursors");
              () } ,
            _ => {  () } ,
          } } ,
      }
    }
⟧

  -- One safety per block (D20): Lean's `inductDecl` and mutual definitions carry one
  -- flag for the whole block, so a safe seed reaches no unsafe or partial co-member
  -- through its block. Counts the block's constants (members and constructors) and
  -- those outside the logic (`Ingress::defn_is_unsafe_ci` on definitions, the flag
  -- elsewhere), as `KernelClaim::muts_unsafe` reads them.

def muts_safety_counts := aiur_fn⟦
  fn muts_safety_counts(ms: Lists::List<Ixon::MutConst>, u: Field, n: Field) -> (Field, Field) {
      match (*(ms)) {
        Lists::Node::Nil => {  (u, n) } ,
        Lists::Node::Cons(m, rest) => {
          match m {
            Ixon::MutConst::Defn(d) => {
              match d {
                Ixon::Definition::Mk(kind, safety, _, _, _) => {
                  muts_safety_counts(rest, u + Ingress::defn_is_unsafe_ci(kind, safety), n + 1) } ,
              } } ,
            Ixon::MutConst::Indc(ind) => {
              match ind {
                Ixon::Inductive::Mk(is_unsafe, _, _, _, _, ctors) => {
                  let iu = match is_unsafe {
                    0 => {  0 } ,
                    _ => {  1 } ,
                  };
                  let (cu, cn) = ctors_safety_counts(ctors, 0, 0);
                  muts_safety_counts(rest, u + iu + cu, n + 1 + cn) } ,
              } } ,
            Ixon::MutConst::Recr(r) => {
              match r {
                Ixon::Recursor::Mk(_, is_unsafe, _, _, _, _, _, _, _) => {
                  let ru = match is_unsafe {
                    0 => {  0 } ,
                    _ => {  1 } ,
                  };
                  muts_safety_counts(rest, u + ru, n + 1) } ,
              } } ,
          } } ,
      }
    }
⟧

def ctors_safety_counts := aiur_fn⟦
  fn ctors_safety_counts(cs: Lists::List<Ixon::Constructor>, u: Field, n: Field) -> (Field, Field) {
      match (*(cs)) {
        Lists::Node::Nil => {  (u, n) } ,
        Lists::Node::Cons(c, rest) => {
          match c {
            Ixon::Constructor::Mk(is_unsafe, _, _, _, _, _) => {
              let cu = match is_unsafe {
                0 => {  0 } ,
                _ => {  1 } ,
              };
              ctors_safety_counts(rest, u + cu, n + 1) } ,
          } } ,
      }
    }
⟧

def check_const := aiur_fn⟦
  fn check_const(rc: KernelRoles::RoleCtx, ci: KernelTypes::KConstantInfo, addr: Bytes::AddressRef) -> () {
      let u = is_unsafe_ci(ci);
      match ci {
        KernelTypes::KConstantInfo::Axiom(nlvls, ty, _) => {
          validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_safety(u, ty);

          match u {
            1 => {  () } ,
            _ => {
              match KernelRoles::axiom_standing(rc, addr) {
                0 => {
                  assert_eq!(0, 1, "an axiom that is not one of Lean's standard axioms");
                  () } ,
                _ => {  () } ,
              } } ,
          } } ,
        KernelTypes::KConstantInfo::Defn(nlvls, ty, val, _, _) => {
          validate_expr_well_scoped(ty, 0, nlvls);
          validate_expr_well_scoped(val, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_safety(u, ty);
          assert_safety(u, val);
          KernelInfer::k_check(rc, val, ty, (&(Lists::Node::Nil))) } ,
        KernelTypes::KConstantInfo::Thm(nlvls, ty, val) => {
          validate_expr_well_scoped(ty, 0, nlvls);
          validate_expr_well_scoped(val, 0, nlvls);
          let lvl = KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_eq!(KernelLevels::level_equal(lvl, (&(KernelTypes::KLevelNode::Zero))), 1,
            "theorem's type is not a Prop");
          assert_safety(u, ty);
          assert_safety(u, val);
          KernelInfer::k_check(rc, val, ty, (&(Lists::Node::Nil))) } ,
        KernelTypes::KConstantInfo::Opaque(nlvls, ty, val, _) => {
          validate_expr_well_scoped(ty, 0, nlvls);
          validate_expr_well_scoped(val, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_safety(u, ty);
          assert_safety(u, val);
          KernelInfer::k_check(rc, val, ty, (&(Lists::Node::Nil))) } ,
        KernelTypes::KConstantInfo::Quot(nlvls, ty, kind) => {
          validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_safety(u, ty);
          check_quot(rc, addr, kind) } ,
        KernelTypes::KConstantInfo::Induct(nlvls, ty, n_params, n_indices, num_ctors,
                              ind_is_unsafe, ind_block, ind_idx) => {
          validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_safety(u, ty);

          check_block_member_kinds(ind_block);

          match KernelModeled::block_is_modeled(ind_block) {
            0 => {
              check_inductive_shape(rc, ty, n_params, n_indices, num_ctors,
                                         nlvls, ind_block, ind_idx,
                                         ind_is_unsafe);
              check_block_peer_param_agreement(rc, ci, addr) } ,
            _ => {
              -- the modeled route: the declared shape, then the family against
              -- its model (`KernelModeled::check_family`)
              let KernelTypes::KExprNode::Srt(_) = (*(peel_n_foralls(ty, n_params + n_indices)));
              check_modeled_ctors(rc, n_params, n_indices, num_ctors, nlvls,
                                  ind_block, ind_idx, ind_is_unsafe, 0);
              match ind_is_unsafe {
                0 => {  KernelModeled::check_modeled_block(rc, ind_block) } ,
                _ => {  () } ,
              } } ,
          } } ,
        KernelTypes::KConstantInfo::Ctor(nlvls, ty, block_addr, ind_idx, _cidx,
                           num_params, num_fields, _) => {
          validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_safety(u, ty);
          let ind_ci = (*(ctor_parent_ind_ci(block_addr, ind_idx)));
          match ind_ci {
            KernelTypes::KConstantInfo::Induct(ind_nlvls, ind_ty, ind_n_params,
                                  ind_n_indices, _, ind_is_unsafe, _, _) => {
              assert_eq!(nlvls, ind_nlvls,
                "ctor universe count differs from its inductive's");
              assert_eq!(num_params, ind_n_params,
                "ctor parameter count differs from its inductive's");
              assert_eq!(u, ind_is_unsafe,
                "ctor safety differs from its inductive's");
              check_ctor_return_type(ty, num_params, ind_n_indices,
                                          num_fields, ind_nlvls, block_addr,
                                          ind_idx);
              match KernelModeled::block_is_modeled(block_addr) {
                0 => {
                  check_param_agreement(rc, ind_ty, ty, ind_n_params);
                  let ind_level = get_result_sort_level(rc, ind_ty,
                    ind_n_params + ind_n_indices, (&(Lists::Node::Nil)));
                  check_field_universes(rc, ty, num_params, ind_level);

                  match ind_is_unsafe {
                    0 => {  check_positivity(rc, ty, num_params, block_addr,
                                               (&(Lists::Node::Nil))) } ,
                    _ => {  () } ,
                  } } ,
                _ => {
                  match ind_is_unsafe {
                    0 => {  KernelModeled::check_modeled_block(rc, block_addr) } ,
                    _ => {  () } ,
                  } } ,
              } } ,
          } } ,
        KernelTypes::KConstantInfo::Rec(nlvls, ty, _, _, n_mot, _, _, k_flag, rec_uns, rec_block, _) => {
          validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_safety(u, ty);
          check_block_member_kinds(rec_block);
          let family = KernelModeled::rec_family_block(addr);
          match KernelModeled::block_is_modeled(family) {
            0 => {
              -- the native route: the block's one recursor (`nativeShape?`)
              assert_eq!(n_mot, 1, "a recursor of a native block with more than one motive");
              check_recursor_member(rc, ci, addr) } ,
            _ => {
              -- the modeled route: no K; the recursor's whole family record
              -- against the block's model
              assert_eq!(k_flag, 0, "a recursor of a mutual or nested block declares K");
              match rec_uns {
                0 => {  KernelModeled::check_family(rc, family, rec_block) } ,
                _ => {  () } ,
              } } ,
          } } ,
      }
    }
⟧

end

end IxVM
