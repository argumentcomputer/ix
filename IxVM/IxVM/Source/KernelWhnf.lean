import Aiur.Modules.Function

/-! # IxVM module `KernelWhnf`

Weak head normalization.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelWhnf where

def apply_spine := aiur_fn⟦
  fn apply_spine(head: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(spine)) {
        Lists::Node::Nil => {  head } ,
        Lists::Node::Cons(a, rest) => {
          apply_spine((&(KernelTypes::KExprNode::App(head, a))), rest) } ,
      }
    }
⟧

def peel_beta := aiur_fn⟦
  fn peel_beta(lam: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>, acc: Lists::List<KernelTypes::KExpr>)
                    -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KExpr>) {
      match (*(lam)) {
        KernelTypes::KExprNode::Lam(_, body) => {
          match (*(spine)) {
            Lists::Node::Cons(a, rest) => {
              peel_beta(body, rest, (&(Lists::Node::Cons(a, acc)))) } ,
            Lists::Node::Nil => {  (lam, acc, spine) } ,
          } } ,
        _ => {  (lam, acc, spine) } ,
      }
    }
⟧

def whnf_apply_beta := aiur_fn⟦
  fn whnf_apply_beta(rc: KernelRoles::RoleCtx, spine: Lists::List<KernelTypes::KExpr>, lam: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match peel_beta(lam, spine, (&(Lists::Node::Nil))) {
        (deep, consumed, rest) => {
          match Lists::length(consumed) {
            0 => {  apply_spine(lam, spine) } ,
            1 => {
              let body2 = KernelSubst::expr_inst1(deep, Lists::lookup(consumed, 0), 0);
              whnf_with_spine(rc, body2, rest, types) } ,
            _ => {
              let body2 = KernelSubst::expr_inst_many(deep, consumed, 0);
              whnf_with_spine(rc, body2, rest, types) } ,
          } } ,
      }
    }
⟧

def whnf_with_spine := aiur_fn⟦
  fn whnf_with_spine(rc: KernelRoles::RoleCtx, head: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(head)) {
        KernelTypes::KExprNode::App(f, a) => {
          match KernelTypes::collect_spine(head) {
            (inner_head, inner_spine) => {
              whnf_with_spine(rc, inner_head, Lists::concat(inner_spine, spine), types) } ,
          } } ,
        KernelTypes::KExprNode::Lam(ty, body) => {
          whnf_apply_beta(rc, spine, head, types) } ,
        KernelTypes::KExprNode::Const(addr, lvls) => {
          whnf_const_head(rc, addr, lvls, head, spine, types) } ,
        KernelTypes::KExprNode::Let(_, val, body) => {
          let next = KernelSubst::expr_inst1(body, val, 0);
          whnf_with_spine(rc, next, spine, types) } ,
        KernelTypes::KExprNode::Proj(struct_addr, fidx, inner) => {
          whnf_proj_head(rc, struct_addr, fidx, inner, spine, types) } ,
        _ => {  apply_spine(head, spine) } ,
      }
    }
⟧

def whnf_proj_head := aiur_fn⟦
  fn whnf_proj_head(rc: KernelRoles::RoleCtx, struct_addr: Bytes::AddressRef, fidx: Field, inner: KernelTypes::KExpr,
                          spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let inner_whnf = whnf(rc, inner, types);

      let inner_exp = KernelNatPrim::str_lit_to_ctor_app_or_self(rc, inner_whnf, types);
      match KernelTypes::collect_spine(inner_exp) {
        (inner_head, inner_args) => {
          match (*(inner_head)) {
            KernelTypes::KExprNode::Const(_, _) => {
              match (*(whnf_get_ctor_or_none(inner_head))) {
                KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, nparams, _, _) => {
                  let field = Lists::lookup(inner_args, nparams + fidx);
                  whnf_with_spine(rc, field, spine, types) } ,
                _ => {
                  let stuck = (&(KernelTypes::KExprNode::Proj(struct_addr, fidx, inner_whnf)));
                  apply_spine(stuck, spine) } ,
              } } ,
            _ => {
              let stuck = (&(KernelTypes::KExprNode::Proj(struct_addr, fidx, inner_whnf)));
              apply_spine(stuck, spine) } ,
          } } ,
      }
    }
⟧

def whnf_get_ctor_or_none := aiur_fn⟦
  fn whnf_get_ctor_or_none(head: KernelTypes::KExpr) -> &KernelTypes::KConstantInfo {
      match (*(head)) {
        KernelTypes::KExprNode::Const(addr, _) => {  Ingress::get_ci(addr) } ,
        _ => {
          (&(KernelTypes::KConstantInfo::Axiom(0, (&(KernelTypes::KExprNode::Srt((&(KernelTypes::KLevelNode::Zero))))), 0))) } ,
      }
    }
⟧

def whnf_spine := aiur_fn⟦
  fn whnf_spine(rc: KernelRoles::RoleCtx, spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> Lists::List<KernelTypes::KExpr> {
      match (*(spine)) {
        Lists::Node::Nil => {  (&(Lists::Node::Nil)) } ,
        Lists::Node::Cons(a, rest) => {
          let aw = whnf(rc, a, types);
          (&(Lists::Node::Cons(aw, whnf_spine(rc, rest, types)))) } ,
      }
    }
⟧

def try_nat_dispatch_prewhnf := aiur_fn⟦
  fn try_nat_dispatch_prewhnf(rc: KernelRoles::RoleCtx, head_addr: Bytes::AddressRef, op: Field, spine: Lists::List<KernelTypes::KExpr>,
                                      types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let spine_w = whnf_spine(rc, spine, types);
      KernelNatPrim::try_nat_dispatch(rc, head_addr, op, spine_w, types)
    }
⟧

def bitvec_prep_spine := aiur_fn⟦
  fn bitvec_prep_spine(rc: KernelRoles::RoleCtx, spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>)
                              -> Lists::List<KernelTypes::KExpr> {
      let spine_w = whnf_spine(rc, spine, types);
      match (*(spine_w)) {
        Lists::Node::Nil => {  spine_w } ,
        Lists::Node::Cons(width_e, rest) => {
          match (*(rest)) {
            Lists::Node::Nil => {  spine_w } ,
            Lists::Node::Cons(val_e, tail) => {
              match KernelTypes::collect_spine(val_e) {
                (vh, va) => {
                  let va_w = whnf_spine(rc, va, types);
                  let val_e2 = apply_spine(vh, va_w);
                  let width_w = whnf(rc, width_e, types);
                  (&(Lists::Node::Cons(width_w,
                    (&(Lists::Node::Cons(val_e2, tail)))))) } ,
              } } ,
          } } ,
      }
    }
⟧

def prim_family := aiur_fn⟦
  fn prim_family(rc: KernelRoles::RoleCtx, a: Bytes::AddressRef) -> (Field, Field) {
      let r1 = KernelRoles::role_index_of(rc, a);
      let (f, op) = match r1 { 0 => {  (0, 0) } , _ => {  KernelRoleSpec::role_prim_family(r1 - 1) } , };
      match f {
        0 => {  (0, 0) } ,
        _ => {  match KernelRoles::role_of(rc, a) { 0 => {  (0, 0) } , _ => {  (f, op) } , } } ,
      }
    }
⟧

def try_prim_dispatch := aiur_fn⟦
  fn try_prim_dispatch(rc: KernelRoles::RoleCtx, addr: Bytes::AddressRef, lvls: Lists::List<KernelTypes::KLevel>,
                              spine: Lists::List<KernelTypes::KExpr>,
                              types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let (fam, op) = prim_family(rc, addr);
      match fam {
        1 => {  try_nat_dispatch_prewhnf(rc, addr, op, spine, types) } ,
        2 => {
          let spine_w = whnf_spine(rc, spine, types);
          KernelNatPrim::try_str_dispatch(rc, addr, op, spine_w, types) } ,
        3 => {  KernelNatPrim::try_bitvec_dispatch(rc, op, spine, types) } ,
        5 => {  KernelInfer::try_dec_dispatch(rc, addr, op, lvls, spine, types) } ,
        6 => {  KernelNatPrim::try_int_prim_dispatch(rc, op, spine, types) } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def try_quot_iota := aiur_fn⟦
  fn try_quot_iota(rc: KernelRoles::RoleCtx, addr: Bytes::AddressRef, spine: Lists::List<KernelTypes::KExpr>,
                           types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match KernelRoles::role_is(rc, addr, KernelRoleSpec::role_quot_lift()) {
        1 => {  try_quot_lift(rc, spine, types) } ,
        _ => {
          match KernelRoles::role_is(rc, addr, KernelRoleSpec::role_quot_ind()) {
            1 => {  try_quot_ind(rc, spine, types) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
      }
    }
⟧

def try_quot_lift := aiur_fn⟦
  fn try_quot_lift(rc: KernelRoles::RoleCtx, spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let n = Lists::length(spine);
      match UInt32::less_than_fields(n, 6) {
        1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        _ => {
          let f = Lists::lookup(spine, 3);
          let q = Lists::lookup(spine, 5);
          match quot_extract_arg(rc, q, types) {
            (1, a) => {
              let post = Lists::drop(spine, 6);
              (1, apply_spine((&(KernelTypes::KExprNode::App(f, a))), post)) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
      }
    }
⟧

def try_quot_ind := aiur_fn⟦
  fn try_quot_ind(rc: KernelRoles::RoleCtx, spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let n = Lists::length(spine);
      match UInt32::less_than_fields(n, 5) {
        1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        _ => {
          let m = Lists::lookup(spine, 3);
          let q = Lists::lookup(spine, 4);
          match quot_extract_arg(rc, q, types) {
            (1, a) => {
              let post = Lists::drop(spine, 5);
              (1, apply_spine((&(KernelTypes::KExprNode::App(m, a))), post)) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
      }
    }
⟧

def quot_extract_arg := aiur_fn⟦
  fn quot_extract_arg(rc: KernelRoles::RoleCtx, q: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let q_w = whnf(rc, q, types);
      match KernelTypes::collect_spine(q_w) {
        (head, args) => {
          match (*(head)) {
            KernelTypes::KExprNode::Const(caddr, _) => {
              match KernelRoles::role_is(rc, caddr, KernelRoleSpec::role_quot_mk()) {
                1 => {
                  match Lists::length(args) - 3 {
                    0 => {  (1, Lists::lookup(args, 2)) } ,
                    _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                  } } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
      }
    }
⟧

def whnf_const_head := aiur_fn⟦
  fn whnf_const_head(rc: KernelRoles::RoleCtx, addr: Bytes::AddressRef, lvls: Lists::List<KernelTypes::KLevel>, head: KernelTypes::KExpr,
                           spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let prim = try_prim_dispatch(rc, addr, lvls, spine, types);
      match prim {
        (1, reduced) => {  whnf(rc, reduced, types) } ,

        (2, stuck) => {  stuck } ,
        _ => {
      let ci = (*(Ingress::get_ci(addr)));
      match ci {
        KernelTypes::KConstantInfo::Defn(_, _, value, _, _) => {
          let pd = try_reduce_projection_definition(value, spine);
          match pd {
            (1, reduced) => {  whnf(rc, reduced, types) } ,
            _ => {
              let body = KernelLevels::expr_inst_levels(value, lvls);
              whnf_with_spine(rc, body, spine, types) } ,
          } } ,

        KernelTypes::KConstantInfo::Thm(_, _, _) => {  apply_spine(head, spine) } ,
        KernelTypes::KConstantInfo::Quot(_, _, _) => {
          let quot = try_quot_iota(rc, addr, spine, types);
          match quot {
            (1, reduced) => {  whnf(rc, reduced, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        KernelTypes::KConstantInfo::Rec(nlvls, rec_ty, nparams, nindices, nmotives, nminors,
                            rules, k_flag, _unsafe, _block, _ridx) => {

          let k_skip = ((nparams + nmotives) + nminors) + nindices;
          let k_pre = match k_flag {
            1 => {

              match se_parent_addr(rec_ty, k_skip) {
                (_, rec_parent) => {
                  try_k_synth_iota(rc, lvls, spine, nparams, nmotives,
                                      nminors, nindices, rules,
                                      rec_parent, types) } ,
              } } ,
            _ => {  (0, head) } ,
          };
          match k_pre {
            (1, k_reduct) => {  k_reduct } ,
            _ => {
          let iota = try_iota(rc, lvls, spine, nparams, nmotives, nminors,
                                   nindices, rules, types, head,
                                   KernelCheck::rec_to_parent_addr(rec_ty, nparams, nmotives,
                                     nminors, nindices));
          match iota {
            (1, reduced) => {  whnf(rc, reduced, types) } ,
            (2, stuck) => {
              match k_flag {

                1 => {  stuck } ,
                _ => {

                  match try_struct_eta_iota(rc, rec_ty, lvls, spine, nparams,
                          nmotives, nminors, nindices, rules, types) {
                    (1, r) => {  whnf(rc, r, types) } ,
                    _ => {  stuck } ,
                  } } ,
              } } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
          } } ,
        _ => {  apply_spine(head, spine) } ,
      } } ,
      }
    }
⟧

def try_reduce_projection_definition := aiur_fn⟦
  fn try_reduce_projection_definition(value: KernelTypes::KExpr,
                                            spine: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match projection_definition_info(value, 0) {
        (1, arity, struct_addr, field, struct_arg_idx) => {
          match UInt32::less_than_fields(Lists::length(spine), arity) {
            1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
            _ => {
              let target_arg = Lists::lookup(spine, struct_arg_idx);
              let proj_expr = (&(KernelTypes::KExprNode::Proj(struct_addr, field, target_arg)));
              let post = Lists::drop(spine, arity);
              (1, apply_spine(proj_expr, post)) } ,
          } } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def projection_definition_info := aiur_fn⟦
  fn projection_definition_info(val: KernelTypes::KExpr, arity: Field)
                                      -> (Field, Field, Bytes::AddressRef, Field, Field) {
      match (*(val)) {
        KernelTypes::KExprNode::Lam(_, body) => {
          projection_definition_info(body, arity + 1) } ,
        KernelTypes::KExprNode::Proj(struct_addr, field, projected) => {
          match (*(projected)) {
            KernelTypes::KExprNode::BVar(i) => {
              match UInt32::less_than_fields(i, arity) {
                1 => {  (1, arity, struct_addr, field, (arity - 1) - i) } ,
                _ => {  (0, 0, (&([UInt8::BYTE_0; 32])), 0, 0) } ,
              } } ,
            _ => {  (0, 0, (&([UInt8::BYTE_0; 32])), 0, 0) } ,
          } } ,
        _ => {  (0, 0, (&([UInt8::BYTE_0; 32])), 0, 0) } ,
      }
    }
⟧

def nat_lit_to_ctor_or_self := aiur_fn⟦
  fn nat_lit_to_ctor_or_self(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Lit(lit) => {
          match lit {
            KernelTypes::KLiteral::Nat(klimbs) => {
              match KernelKlimbs::klimbs_is_zero(klimbs) {
                1 => {  (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_nat_zero()),
                                            (&(Lists::Node::Nil))))) } ,
                _ => {
                  let pred_limbs = KernelKlimbs::klimbs_normalize(KernelKlimbs::klimbs_dec(klimbs));
                  let pred = (&(KernelTypes::KExprNode::Lit(KernelTypes::KLiteral::Nat(pred_limbs))));
                  let succ_const = (&(KernelTypes::KExprNode::Const(KernelRoles::role_addr(rc, KernelRoleSpec::role_nat_succ()),
                                                         (&(Lists::Node::Nil)))));
                  (&(KernelTypes::KExprNode::App(succ_const, pred))) } ,
              } } ,
            _ => {  e } ,
          } } ,
        _ => {  e } ,
      }
    }
⟧

def try_k_synth_iota := aiur_fn⟦
  fn try_k_synth_iota(rc: KernelRoles::RoleCtx, lvls: Lists::List<KernelTypes::KLevel>, spine: Lists::List<KernelTypes::KExpr>,
                            nparams: Field, nmotives: Field, nminors: Field, nindices: Field,
                            rules: Lists::List<KernelTypes::KRecRule>,
                            rec_parent: Bytes::AddressRef, types: Lists::List<KernelTypes::KExpr>)
                            -> (Field, KernelTypes::KExpr) {
      match (*(rules)) {
        Lists::Node::Cons(r, _) => {
          match r {
            KernelTypes::KRecRule::Mk(cidx, _rfields, rrhs) => {
              let major_idx = nparams + nmotives + nminors + nindices;

              match UInt32::less_than_fields(major_idx, Lists::length(spine)) {
                0 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                _ => {
                  let raw_major = Lists::lookup(spine, major_idx);
                  match k_synth_gate(rc, raw_major, cidx, nparams, rec_parent, types) {
                    0 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                    _ => {
                      let rhs_lvled = KernelLevels::expr_inst_levels(rrhs, lvls);
                      let pmm_end = nparams + nmotives + nminors;
                      let pmm = Lists::take(spine, pmm_end);
                      let post_major = Lists::drop(spine, major_idx + 1);
                      let r1 = apply_spine(rhs_lvled, pmm);
                      let r3 = apply_spine(r1, post_major);
                      (1, whnf(rc, r3, types)) } ,
                  } } ,
              } } ,
          } } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def k_synth_gate := aiur_fn⟦
  fn k_synth_gate(rc: KernelRoles::RoleCtx, raw_major: KernelTypes::KExpr, cidx: Field, nparams: Field,
                        rec_parent: Bytes::AddressRef, types: Lists::List<KernelTypes::KExpr>) -> Field {
      let major_ty = KernelInfer::k_infer(rc, raw_major, types);
      let major_ty_w = whnf(rc, major_ty, types);
      match KernelTypes::collect_spine(major_ty_w) {
        (ty_head, ty_args) => {
          match (*(ty_head)) {
            KernelTypes::KExprNode::Const(ind_addr, ctor_us) => {

              match Bytes::address_eq(ind_addr, rec_parent) {
                0 => {  0 } ,
                _ => {
                  let ind_ci = (*(Ingress::get_ci(ind_addr)));
                  match ind_ci {
                    KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, ind_block, ind_idx) => {
                      let cprj = KernelCheck::projection_addr_ctor(ind_idx, cidx, ind_block);
                      let ctor_head = (&(KernelTypes::KExprNode::Const(cprj, ctor_us)));
                      let params = Lists::take(ty_args, nparams);
                      let ctor_app = apply_spine(ctor_head, params);
                      let ctor_ty = KernelInfer::k_infer(rc, ctor_app, types);
                      KernelDefEq::k_is_def_eq(rc, major_ty_w, ctor_ty, types) } ,
                    _ => {  0 } ,
                  } } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def replace_spine_major := aiur_fn⟦
  fn replace_spine_major(spine: Lists::List<KernelTypes::KExpr>, major_idx: Field, major_w: KernelTypes::KExpr)
                               -> Lists::List<KernelTypes::KExpr> {
      let pre = Lists::take(spine, major_idx);
      let post = Lists::drop(spine, major_idx + 1);
      let with_major = Lists::concat(pre,
        (&(Lists::Node::Cons(major_w, (&(Lists::Node::Nil))))));
      Lists::concat(with_major, post)
    }
⟧

def whnf_iota_major := aiur_fn⟦
  fn whnf_iota_major(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let w = whnf(rc, e, types);
      match KernelTypes::collect_spine(w) {
        (h, sp) => {
          match (*(h)) {
            KernelTypes::KExprNode::Const(addr, lvls) => {
              match (*(Ingress::get_ci(addr))) {
                KernelTypes::KConstantInfo::Thm(_, _, value) => {
                  let body = KernelLevels::expr_inst_levels(value, lvls);
                  whnf_iota_major(rc, whnf_with_spine(rc, body, sp, types), types) } ,
                _ => {  w } ,
              } } ,
            _ => {  w } ,
          } } ,
      }
    }
⟧

def try_iota := aiur_fn⟦
  fn try_iota(rc: KernelRoles::RoleCtx, lvls: Lists::List<KernelTypes::KLevel>, spine: Lists::List<KernelTypes::KExpr>,
                    nparams: Field, nmotives: Field, nminors: Field, nindices: Field,
                    rules: Lists::List<KernelTypes::KRecRule>, types: Lists::List<KernelTypes::KExpr>,
                    head: KernelTypes::KExpr, rec_parent: Bytes::AddressRef) -> (Field, KernelTypes::KExpr) {
      let major_idx = nparams + nmotives + nminors + nindices;
      let spine_len = Lists::length(spine);
      match UInt32::less_than_fields(major_idx, spine_len) {
        0 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        _ => {

          let lin = KernelNatPrim::try_nat_linear_rec(rc, spine, nparams, nmotives, nminors, major_idx);
          match lin {
            (1, r) => {  (1, r) } ,
            _ => {
          let raw_major = Lists::lookup(spine, major_idx);

          let major_clean1 = KernelNatPrim::cleanup_nat_offset_major(rc, raw_major);
          let major_w = whnf_iota_major(rc, major_clean1, types);
          let major_clean2 = KernelNatPrim::cleanup_nat_offset_major(rc, major_w);
          let major = nat_lit_to_ctor_or_self(rc, major_clean2);
          match collect_spine_of_ctor(major) {
            (1, ctor_cidx, ctor_parent, ctor_args) => {

              assert_eq!(Bytes::address_eq(ctor_parent, rec_parent), 1,
                "iota: major's constructor belongs to a different inductive");
              let rule = find_rule(rules, ctor_cidx);
              match rule {
                (0, _, _) => {

                  let new_spine = replace_spine_major(spine, major_idx, major_w);
                  (2, apply_spine(head, new_spine)) } ,
                (1, rfields, rrhs) => {
                  -- D7: a modeled recursor's rule fires only at the comparands
                  -- its model's iota theorem covers (`paramsBlind := false`)
                  match KernelModeled::fire_ok(rc, head, lvls, spine, major, types) {
                    0 => {
                      let new_spine = replace_spine_major(spine, major_idx, major_w);
                      (2, apply_spine(head, new_spine)) } ,
                    _ => {
                  let rhs_lvled = KernelLevels::expr_inst_levels(rrhs, lvls);
                  let pmm_end = nparams + nmotives + nminors;
                  let pmm = Lists::take(spine, pmm_end);
                  let ctor_fields_len = Lists::length(ctor_args);
                  let field_start = ctor_fields_len - rfields;
                  let field_args = Lists::drop(ctor_args, field_start);
                  let post_major = Lists::drop(spine, major_idx + 1);
                  let r1 = apply_spine(rhs_lvled, pmm);
                  let r2 = apply_spine(r1, field_args);
                  let r3 = apply_spine(r2, post_major);
                  (1, r3) } ,
                  } } ,
              } } ,
            _ => {

              let new_spine = replace_spine_major(spine, major_idx, major_w);
              (2, apply_spine(head, new_spine)) } ,
          } } ,
          } } ,
      }
    }
⟧

def collect_spine_of_ctor := aiur_fn⟦
  fn collect_spine_of_ctor(e: KernelTypes::KExpr) -> (Field, Field, Bytes::AddressRef, Lists::List<KernelTypes::KExpr>) {
      match KernelTypes::collect_spine(e) {
        (head, args) => {
          match (*(head)) {
            KernelTypes::KExprNode::Const(addr, _) => {
              let ci = (*(Ingress::get_ci(addr)));
              match ci {
                KernelTypes::KConstantInfo::Ctor(_, _, block_addr, ind_idx, cidx, _, _, _) => {
                  (1, cidx, KernelDefEq::compute_iprj_addr(block_addr, ind_idx), args) } ,
                _ => {  (0, 0, (&([UInt8::BYTE_0; 32])), (&(Lists::Node::Nil))) } ,
              } } ,
            _ => {  (0, 0, (&([UInt8::BYTE_0; 32])), (&(Lists::Node::Nil))) } ,
          } } ,
      }
    }
⟧

def find_rule := aiur_fn⟦
  fn find_rule(rules: Lists::List<KernelTypes::KRecRule>, cidx: Field) -> (Field, Field, KernelTypes::KExpr) {
      match (*(rules)) {
        Lists::Node::Nil => {  (0, 0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        Lists::Node::Cons(r, rest) => {
          match r {
            KernelTypes::KRecRule::Mk(rcidx, nfields, rhs) => {
              match rcidx - cidx {
                0 => {  (1, nfields, rhs) } ,
                _ => {  find_rule(rest, cidx) } ,
              } } ,
          } } ,
      }
    }
⟧

def try_struct_eta_iota := aiur_fn⟦
  fn try_struct_eta_iota(rc: KernelRoles::RoleCtx, rec_ty: KernelTypes::KExpr, lvls: Lists::List<KernelTypes::KLevel>,
                                 spine: Lists::List<KernelTypes::KExpr>, nparams: Field, nmotives: Field,
                                 nminors: Field, nindices: Field,
                                 rules: Lists::List<KernelTypes::KRecRule>,
                                 types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match (*(rules)) {
        Lists::Node::Nil => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        Lists::Node::Cons(r, rest) => {
          match (*(rest)) {
            Lists::Node::Cons(_, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
            Lists::Node::Nil => {
              match r {
                KernelTypes::KRecRule::Mk(_, nf, rhs) => {
                  let skip = ((nparams + nmotives) + nminors) + nindices;
                  match se_parent_addr(rec_ty, skip) {
                    (0, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                    (_, parent) => {
                      let ci = (*(Ingress::get_ci(parent)));
                      match ci {
                        KernelTypes::KConstantInfo::Induct(_, _, _, ind_nidx, num_ctors,
                                               _, _, _) => {
                          match num_ctors - 1 {
                            0 => {
                              match ind_nidx {
                                0 => {
                                  match struct_is_rec(parent) {
                                    1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                                    _ => {
                                      let major = Lists::lookup(spine, skip);

                                      match UInt32::less_than_fields(Lists::length(types),
                                          KernelSubst::expr_lbr(major)) {
                                        1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                                        _ => {
                                          let major_ty = KernelInfer::k_infer(rc, major, types);
                                          match KernelDefEq::is_prop_type(rc, major_ty, types) {
                                            1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                                            _ => {
                                              let rhs_inst = KernelLevels::expr_inst_levels(rhs, lvls);
                                              let pmm = Lists::take(spine,
                                                (nparams + nmotives) + nminors);
                                              let after_pmm = apply_spine(rhs_inst, pmm);
                                              let with_projs = apply_n_projs(
                                                after_pmm, parent, major, nf, 0);
                                              let post = Lists::drop(spine, skip + 1);
                                              (1, apply_spine(with_projs, post)) } ,
                                          } } ,
                                      } } ,
                                  } } ,
                                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                              } } ,
                            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                          } } ,
                        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def se_parent_addr := aiur_fn⟦
  fn se_parent_addr(rec_ty: KernelTypes::KExpr, skip: Field) -> (Field, Bytes::AddressRef) {
      match skip {
        0 => {
          match (*(rec_ty)) {
            KernelTypes::KExprNode::Forall(dom, _) => {
              match KernelTypes::collect_spine(dom) {
                (h, _) => {
                  match (*(h)) {
                    KernelTypes::KExprNode::Const(a, _) => {  (1, a) } ,
                    _ => {  (0, (&([UInt8::BYTE_0; 32]))) } ,
                  } } ,
              } } ,
            _ => {  (0, (&([UInt8::BYTE_0; 32]))) } ,
          } } ,
        _ => {
          match (*(rec_ty)) {
            KernelTypes::KExprNode::Forall(_, body) => {  se_parent_addr(body, skip - 1) } ,
            _ => {  (0, (&([UInt8::BYTE_0; 32]))) } ,
          } } ,
      }
    }
⟧

def apply_n_projs := aiur_fn⟦
  fn apply_n_projs(head: KernelTypes::KExpr, parent: Bytes::AddressRef, major: KernelTypes::KExpr,
                          n_fields: Field, i: Field) -> KernelTypes::KExpr {
      match n_fields - i {
        0 => {  head } ,
        _ => {
          let p = (&(KernelTypes::KExprNode::Proj(parent, i, major)));
          apply_n_projs((&(KernelTypes::KExprNode::App(head, p))), parent, major,
            n_fields, i + 1) } ,
      }
    }
⟧

def struct_is_rec := aiur_fn⟦
  fn struct_is_rec(parent: Bytes::AddressRef) -> Field {
      let ci = (*(Ingress::get_ci(parent)));
      match ci {
        KernelTypes::KConstantInfo::Induct(_, _, n_params, _, num_ctors, _, block, idx) => {
          -- D6/D7: no structure eta at a member of a mutual or nested block
          -- (the kernel grants none without a model theorem; Lean's `is_rec`)
          match KernelModeled::block_is_modeled(block) {
            0 => {
              let members = struct_block_member_addrs(parent, block);
              struct_scan_ctors(block, idx, num_ctors, n_params, members, 0) } ,
            _ => {  1 } ,
          } } ,
        _ => {  1 } ,
      }
    }
⟧

def struct_block_member_addrs := aiur_fn⟦
  fn struct_block_member_addrs(parent: Bytes::AddressRef, block: Bytes::AddressRef) -> Lists::List<Bytes::AddressRef> {
      let c = Ingress::load_verified_constant(block);
      match c {
        Ixon::Constant::Mk(info, _, _, _) => {
          match info {
            Ixon::ConstantInfo::Muts(members) => {  Ingress::build_recur_addrs(members, block) } ,
            _ => {  (&(Lists::Node::Cons(parent, (&(Lists::Node::Nil))))) } ,
          } } ,
      }
    }
⟧

def struct_scan_ctors := aiur_fn⟦
  fn struct_scan_ctors(block: Bytes::AddressRef, idx: Field, num_ctors: Field, n_params: Field,
                               members: Lists::List<Bytes::AddressRef>, c: Field) -> Field {
      match num_ctors - c {
        0 => {  0 } ,
        _ => {
          let cci = (*(Ingress::get_ci_cprj(block, idx, c)));
          match cci {
            KernelTypes::KConstantInfo::Ctor(_, cty, _, _, _, _, _, _) => {
              let after = se_peel_tol(cty, n_params);
              match se_scan_fields(after, members) {
                1 => {  1 } ,
                _ => {  struct_scan_ctors(block, idx, num_ctors, n_params,
                       members, c + 1) } ,
              } } ,
            _ => {  1 } ,
          } } ,
      }
    }
⟧

def se_peel_tol := aiur_fn⟦
  fn se_peel_tol(ty: KernelTypes::KExpr, n: Field) -> KernelTypes::KExpr {
      match n {
        0 => {  ty } ,
        _ => {
          match (*(ty)) {
            KernelTypes::KExprNode::Forall(_, body) => {  se_peel_tol(body, n - 1) } ,
            _ => {  ty } ,
          } } ,
      }
    }
⟧

def se_scan_fields := aiur_fn⟦
  fn se_scan_fields(ty: KernelTypes::KExpr, members: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(dom, body) => {
          match se_mentions(dom, members) {
            1 => {  1 } ,
            _ => {  se_scan_fields(body, members) } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def se_mentions := aiur_fn⟦
  fn se_mentions(e: KernelTypes::KExpr, members: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(e)) {
        KernelTypes::KExprNode::Const(a, _) => {  se_addr_in(a, members) } ,
        KernelTypes::KExprNode::App(f, x) => {
          match se_mentions(f, members) {
            1 => {  1 } ,
            _ => {  se_mentions(x, members) } ,
          } } ,
        KernelTypes::KExprNode::Lam(t, b) => {
          match se_mentions(t, members) {
            1 => {  1 } ,
            _ => {  se_mentions(b, members) } ,
          } } ,
        KernelTypes::KExprNode::Forall(t, b) => {
          match se_mentions(t, members) {
            1 => {  1 } ,
            _ => {  se_mentions(b, members) } ,
          } } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          match se_mentions(t, members) {
            1 => {  1 } ,
            _ => {
              match se_mentions(v, members) {
                1 => {  1 } ,
                _ => {  se_mentions(b, members) } ,
              } } ,
          } } ,
        KernelTypes::KExprNode::Proj(_, _, inner) => {  se_mentions(inner, members) } ,
        _ => {  0 } ,
      }
    }
⟧

def se_addr_in := aiur_fn⟦
  fn se_addr_in(a: Bytes::AddressRef, xs: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(xs)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(x, rest) => {
          match Bytes::address_eq(a, x) {
            1 => {  1 } ,
            _ => {  se_addr_in(a, rest) } ,
          } } ,
      }
    }
⟧

def whnf := aiur_fn⟦
  fn whnf(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Srt(_) => {  e } ,
        KernelTypes::KExprNode::Lit(_) => {  e } ,
        KernelTypes::KExprNode::Lam(_, _) => {  e } ,
        KernelTypes::KExprNode::Forall(_, _) => {  e } ,
        KernelTypes::KExprNode::BVar(_) => {  e } ,
        _ => {  whnf_core(rc, e, KernelSubst::ctx_trim(types, KernelSubst::expr_lbr(e))) } ,
      }
    }
⟧

def whnf_core := aiur_fn⟦
  inline fn whnf_core(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      whnf_with_spine(rc, e, (&(Lists::Node::Nil)), types)
    }
⟧

def whnf_struct_core := aiur_fn⟦
  fn whnf_struct_core(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Srt(_) => {  e } ,
        KernelTypes::KExprNode::Lit(_) => {  e } ,
        KernelTypes::KExprNode::Lam(_, _) => {  e } ,
        KernelTypes::KExprNode::Forall(_, _) => {  e } ,
        KernelTypes::KExprNode::BVar(_) => {  e } ,
        _ => {  whnf_struct_core_spine(rc, e, (&(Lists::Node::Nil)),
               KernelSubst::ctx_trim(types, KernelSubst::expr_lbr(e))) } ,
      }
    }
⟧

def whnf_struct_core_spine := aiur_fn⟦
  fn whnf_struct_core_spine(rc: KernelRoles::RoleCtx, head: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>,
                                   types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(head)) {
        KernelTypes::KExprNode::App(_, _) => {
          match KernelTypes::collect_spine(head) {
            (h, s) => {  whnf_struct_core_spine(rc, h, Lists::concat(s, spine), types) } ,
          } } ,
        KernelTypes::KExprNode::Lam(_, _) => {
          match peel_beta(head, spine, (&(Lists::Node::Nil))) {
            (deep, consumed, rest) => {
              match Lists::length(consumed) {
                0 => {  apply_spine(head, spine) } ,
                1 => {  whnf_struct_core_spine(rc,
                       KernelSubst::expr_inst1(deep, Lists::lookup(consumed, 0), 0), rest, types) } ,
                _ => {  whnf_struct_core_spine(rc,
                       KernelSubst::expr_inst_many(deep, consumed, 0), rest, types) } ,
              } } ,
          } } ,
        KernelTypes::KExprNode::Let(_, val, body) => {
          whnf_struct_core_spine(rc, KernelSubst::expr_inst1(body, val, 0), spine, types) } ,
        KernelTypes::KExprNode::Proj(struct_addr, fidx, inner) => {
          whnf_struct_core_proj(rc, struct_addr, fidx, inner, spine, types, head) } ,
        KernelTypes::KExprNode::Const(addr, lvls) => {
          whnf_struct_core_const(rc, addr, lvls, head, spine, types) } ,
        _ => {  apply_spine(head, spine) } ,
      }
    }
⟧

def whnf_struct_core_proj := aiur_fn⟦
  fn whnf_struct_core_proj(rc: KernelRoles::RoleCtx, struct_addr: Bytes::AddressRef, fidx: Field, inner: KernelTypes::KExpr,
                                  spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>,
                                  original: KernelTypes::KExpr) -> KernelTypes::KExpr {
      let inner_w = whnf_struct_core(rc, inner, types);
      match KernelTypes::collect_spine(inner_w) {
        (ih, ia) => {
          match (*(ih)) {
            KernelTypes::KExprNode::Const(_, _) => {
              match (*(whnf_get_ctor_or_none(ih))) {
                KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, nparams, _, _) => {
                  whnf_struct_core_spine(rc, Lists::lookup(ia, nparams + fidx),
                                          spine, types) } ,
                _ => {  apply_spine(original, spine) } ,
              } } ,
            _ => {  apply_spine(original, spine) } ,
          } } ,
      }
    }
⟧

def whnf_struct_core_const := aiur_fn⟦
  fn whnf_struct_core_const(rc: KernelRoles::RoleCtx, addr: Bytes::AddressRef, lvls: Lists::List<KernelTypes::KLevel>, head: KernelTypes::KExpr,
                                   spine: Lists::List<KernelTypes::KExpr>,
                                   types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(Ingress::get_ci(addr))) {
        KernelTypes::KConstantInfo::Rec(_, rec_ty, nparams, nindices, nmotives, nminors,
                            rules, _k, _unsafe, _block, _ridx) => {
          match try_iota(rc, lvls, spine, nparams, nmotives, nminors, nindices,
                  rules, types, head,
                  KernelCheck::rec_to_parent_addr(rec_ty, nparams, nmotives, nminors,
                    nindices)) {
            (1, reduced) => {  whnf_struct_core(rc, reduced, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        _ => {  apply_spine(head, spine) } ,
      }
    }
⟧

def whnf_nd := aiur_fn⟦
  fn whnf_nd(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::Srt(_) => {  e } ,
        KernelTypes::KExprNode::Lit(_) => {  e } ,
        KernelTypes::KExprNode::Lam(_, _) => {  e } ,
        KernelTypes::KExprNode::Forall(_, _) => {  e } ,
        KernelTypes::KExprNode::BVar(_) => {  e } ,
        _ => {  whnf_nd_core(rc, e, KernelSubst::ctx_trim(types, KernelSubst::expr_lbr(e))) } ,
      }
    }
⟧

def whnf_nd_core := aiur_fn⟦
  inline fn whnf_nd_core(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      whnf_nd_with_spine(rc, e, (&(Lists::Node::Nil)), types)
    }
⟧

def whnf_nd_with_spine := aiur_fn⟦
  fn whnf_nd_with_spine(rc: KernelRoles::RoleCtx, head: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>,
                              types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(head)) {
        KernelTypes::KExprNode::App(f, a) => {
          match KernelTypes::collect_spine(head) {
            (inner_head, inner_spine) => {
              whnf_nd_with_spine(rc, inner_head, Lists::concat(inner_spine, spine), types) } ,
          } } ,
        KernelTypes::KExprNode::Lam(ty, body) => {
          whnf_nd_apply_beta(rc, spine, head, types) } ,
        KernelTypes::KExprNode::Const(addr, lvls) => {
          whnf_nd_const_head(rc, addr, lvls, head, spine, types) } ,
        KernelTypes::KExprNode::Let(_, val, body) => {
          let next = KernelSubst::expr_inst1(body, val, 0);
          whnf_nd_with_spine(rc, next, spine, types) } ,
        KernelTypes::KExprNode::Proj(struct_addr, fidx, inner) => {
          whnf_nd_proj_head(rc, struct_addr, fidx, inner, spine, types) } ,
        _ => {  apply_spine(head, spine) } ,
      }
    }
⟧

def whnf_nd_apply_beta := aiur_fn⟦
  fn whnf_nd_apply_beta(rc: KernelRoles::RoleCtx, spine: Lists::List<KernelTypes::KExpr>, lam: KernelTypes::KExpr,
                              types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match peel_beta(lam, spine, (&(Lists::Node::Nil))) {
        (deep, consumed, rest) => {
          match Lists::length(consumed) {
            0 => {  apply_spine(lam, spine) } ,
            1 => {
              let body2 = KernelSubst::expr_inst1(deep, Lists::lookup(consumed, 0), 0);
              whnf_nd_with_spine(rc, body2, rest, types) } ,
            _ => {
              let body2 = KernelSubst::expr_inst_many(deep, consumed, 0);
              whnf_nd_with_spine(rc, body2, rest, types) } ,
          } } ,
      }
    }
⟧

def whnf_nd_proj_head := aiur_fn⟦
  fn whnf_nd_proj_head(rc: KernelRoles::RoleCtx, struct_addr: Bytes::AddressRef, fidx: Field, inner: KernelTypes::KExpr,
                             spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let inner_whnf = whnf_nd(rc, inner, types);

      let inner_exp = KernelNatPrim::str_lit_to_ctor_app_or_self(rc, inner_whnf, types);
      match KernelTypes::collect_spine(inner_exp) {
        (inner_head, inner_args) => {
          match (*(inner_head)) {
            KernelTypes::KExprNode::Const(_, _) => {
              match (*(whnf_get_ctor_or_none(inner_head))) {
                KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, nparams, _, _) => {
                  let field = Lists::lookup(inner_args, nparams + fidx);
                  whnf_nd_with_spine(rc, field, spine, types) } ,
                _ => {
                  let stuck = (&(KernelTypes::KExprNode::Proj(struct_addr, fidx, inner_whnf)));
                  apply_spine(stuck, spine) } ,
              } } ,
            _ => {
              let stuck = (&(KernelTypes::KExprNode::Proj(struct_addr, fidx, inner_whnf)));
              apply_spine(stuck, spine) } ,
          } } ,
      }
    }
⟧

def whnf_nd_const_head := aiur_fn⟦
  fn whnf_nd_const_head(rc: KernelRoles::RoleCtx, addr: Bytes::AddressRef, lvls: Lists::List<KernelTypes::KLevel>, head: KernelTypes::KExpr,
                              spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {

      let (fam, _op) = prim_family(rc, addr);
      let prim = match fam {
        0 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        1 => {
          let whole = apply_spine(head, spine);
          match KernelSubst::expr_lbr(whole) {
            0 => {  try_prim_dispatch(rc, addr, lvls, spine, types) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
        _ => {  try_prim_dispatch(rc, addr, lvls, spine, types) } ,
      };
      match prim {
        (1, reduced) => {  whnf_nd(rc, reduced, types) } ,

        (2, stuck) => {  stuck } ,
        _ => {
      let ci = (*(Ingress::get_ci(addr)));
      match ci {
        KernelTypes::KConstantInfo::Defn(_, _, value, _, _) => {
          let pd = try_reduce_projection_definition(value, spine);
          match pd {
            (1, reduced) => {  whnf_nd(rc, reduced, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        KernelTypes::KConstantInfo::Quot(_, _, _) => {
          let quot = try_quot_iota(rc, addr, spine, types);
          match quot {
            (1, reduced) => {  whnf_nd(rc, reduced, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        KernelTypes::KConstantInfo::Rec(nlvls, rec_ty, nparams, nindices, nmotives, nminors,
                            rules, k_flag, _unsafe, _block, _ridx) => {

          let k_skip = ((nparams + nmotives) + nminors) + nindices;
          let k_pre = match k_flag {
            1 => {
              match se_parent_addr(rec_ty, k_skip) {
                (_, rec_parent) => {
                  try_k_synth_iota(rc, lvls, spine, nparams, nmotives,
                                      nminors, nindices, rules,
                                      rec_parent, types) } ,
              } } ,
            _ => {  (0, head) } ,
          };
          match k_pre {
            (1, k_reduct) => {  k_reduct } ,
            _ => {
          let iota = try_iota(rc, lvls, spine, nparams, nmotives, nminors,
                                   nindices, rules, types, head,
                                   KernelCheck::rec_to_parent_addr(rec_ty, nparams, nmotives,
                                     nminors, nindices));
          match iota {
            (1, reduced) => {  whnf_nd(rc, reduced, types) } ,
            (2, stuck) => {
              match k_flag {
                1 => {  stuck } ,
                _ => {
                  match try_struct_eta_iota(rc, rec_ty, lvls, spine, nparams,
                          nmotives, nminors, nindices, rules, types) {
                    (1, r) => {  whnf_nd(rc, r, types) } ,
                    _ => {  stuck } ,
                  } } ,
              } } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
          } } ,
        _ => {  apply_spine(head, spine) } ,
      } } ,
      }
    }
⟧

end

end IxVM
