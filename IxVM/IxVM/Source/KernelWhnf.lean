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
        KernelTypes::KExprNode::Lam(_, body, bl) => {
          match (*(spine)) {
            Lists::Node::Cons(a, rest) => {
              match KernelLevels::level_is_not_zero(bl) {
                1 => {  peel_beta(body, rest, (&(Lists::Node::Cons(a, acc)))) } ,
                _ => {  (lam, acc, spine) } ,
              } } ,
            Lists::Node::Nil => {  (lam, acc, spine) } ,
          } } ,
        _ => {  (lam, acc, spine) } ,
      }
    }
⟧

  -- Rule-shaped core (lane cx). Each kernel rule IxVM uses has one step function,
  -- called by all three head normalizers (`whnf`, `whnf_struct_core`, `whnf_nd`):
  --   `red_beta`   Red.beta / Red.betaGate, one step per consumed argument;
  --   `red_proj`   Red.proj, the scrutinee already reduced by the caller (Red.projArg);
  --   `red_unfold` Red.delta (definitions) and Red.deltaThm (theorems);
  --   `red_iota`   Red.iota on a prepared major (`try_iota` prepares it);
  --   `red_rec`    the recursor dispatch: K (Red.rescueK), ι, structure-η ι (Red.rescueEta).
  -- A step function returns a tag (0 = no move) and the one-step reduct; the caller
  -- chains it (Red.trans, Red.appFn) and picks the normalizer that continues.

def red_beta := aiur_fn⟦
  fn red_beta(rc: KernelRoles::RoleCtx, lam: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>,
              types: Lists::List<KernelTypes::KExpr>)
              -> (Field, KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match peel_beta(lam, spine, (&(Lists::Node::Nil))) {
        (deep, consumed, rest) => {
          match beta_more(rc, deep, rest, consumed, types) {
            (deep2, consumed2, rest2) => {
              match (*(consumed2)) {
                Lists::Node::Nil => {  (0, lam, spine) } ,
                Lists::Node::Cons(a, more) => {
                  match (*(more)) {
                    Lists::Node::Nil => {  (1, KernelSubst::expr_inst1(deep2, a, 0), rest2) } ,
                    Lists::Node::Cons(_, _) => {  (1, KernelSubst::expr_inst_many(deep2, consumed2, 0), rest2) } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

  -- Fix A at β. `peel_beta` consumes arguments while the λs' data are never
  -- (Red.betaGate). Where it stops at a λ whose datum may be zero with arguments left,
  -- `peel_beta_cert` goes on: each such λ needs its certificate (Red.beta: the argument's
  -- io-grade type is definitionally equal to the domain, instantiated by the arguments
  -- already consumed); it stops at the first certificate that fails. The consumed
  -- arguments are substituted at once.

def beta_more := aiur_fn⟦
  inline fn beta_more(rc: KernelRoles::RoleCtx, deep: KernelTypes::KExpr, rest: Lists::List<KernelTypes::KExpr>,
                      consumed: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>)
                      -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KExpr>) {
      match (*(rest)) {
        Lists::Node::Nil => {  (deep, consumed, rest) } ,
        Lists::Node::Cons(_, _) => {
          match (*(deep)) {
            KernelTypes::KExprNode::Lam(_, _, _) => {  peel_beta_cert(rc, deep, rest, consumed, types) } ,
            _ => {  (deep, consumed, rest) } ,
          } } ,
      }
    }
⟧

def peel_beta_cert := aiur_fn⟦
  fn peel_beta_cert(rc: KernelRoles::RoleCtx, lam: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>,
                    acc: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>)
                    -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>, Lists::List<KernelTypes::KExpr>) {
      match (*(lam)) {
        KernelTypes::KExprNode::Lam(ty, body, bl) => {
          match (*(spine)) {
            Lists::Node::Cons(a, rest) => {
              let ok = match KernelLevels::level_is_not_zero(bl) {
                1 => {  1 } ,
                _ => {
                  let ta = KernelInferOnly::k_infer_only(rc, a, types);
                  KernelDefEq::k_is_def_eq(rc, ta, KernelInfer::inst_subs(ty, acc), types) } ,
              };
              match ok {
                1 => {  peel_beta_cert(rc, body, rest, (&(Lists::Node::Cons(a, acc))), types) } ,
                _ => {  (lam, acc, spine) } ,
              } } ,
            Lists::Node::Nil => {  (lam, acc, spine) } ,
          } } ,
        _ => {  (lam, acc, spine) } ,
      }
    }
⟧

  -- Red.proj. Fires only when the constructor belongs to the projected structure, the
  -- structure has one constructor and no indices (D5), the field exists, the
  -- constructor application has exactly `nparams + nfields` arguments and the right
  -- number of levels, and the structure's sort at those levels is never zero. At a
  -- never-zero structure the rule's `FireSem` guard is vacuous and every slot of the
  -- licensed `Certs` walk is a `.never` skip, so no certificate is needed; a
  -- projection out of a possibly-`Prop` structure is left stuck (completeness only).

def red_proj := aiur_fn⟦
  fn red_proj(rc: KernelRoles::RoleCtx, struct_addr: Bytes::AddressRef, fidx: Field, scrut: KernelTypes::KExpr,
              types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match KernelTypes::collect_spine(scrut) {
        (head, args) => {
          match (*(head)) {
            KernelTypes::KExprNode::Const(caddr, clvls) => {
              match (*(Ingress::get_ci(caddr))) {
                KernelTypes::KConstantInfo::Ctor(cnl, _, cblock, cind, _, nparams, nfields, _) => {
                  match (*(Ingress::get_ci(struct_addr))) {
                    KernelTypes::KConstantInfo::Induct(snl, sty, snp, sni, snc, _, sblock, sidx) => {
                      let owner = (Bytes::address_eq(cblock, sblock) * Fields::is_zero(cind - sidx)) * Fields::is_zero(snl - cnl);
                      let shape = (Fields::is_zero(sni) * Fields::is_zero(snc - 1)) * Fields::is_zero(snp - nparams);
                      let arity = Fields::is_zero(Lists::length(args) - (nparams + nfields))
                                  * Fields::is_zero(Lists::length(clvls) - cnl);
                      match ((owner * shape) * arity) * UInt32::less_than_fields(fidx, nfields) {
                        1 => {
                          match type_sort_never(sty, snp, clvls) {
                            1 => {  (1, Lists::lookup(args, nparams + fidx)) } ,
                            _ => {  (0, scrut) } ,
                          } } ,
                        _ => {  (0, scrut) } ,
                      } } ,
                    _ => {  (0, scrut) } ,
                  } } ,
                _ => {  (0, scrut) } ,
              } } ,
            _ => {  (0, scrut) } ,
          } } ,
      }
    }
⟧

  -- Whether the sort a stored type former's telescope ends in, after `n` binders and
  -- at the levels `lvls`, is never zero (`level_is_not_zero`, IxC's `isNeverZero`).
  -- A type that is not syntactically such a telescope answers 0.

def type_sort_never := aiur_fn⟦
  fn type_sort_never(ty: KernelTypes::KExpr, n: Field, lvls: Lists::List<KernelTypes::KLevel>) -> Field {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(_, body, _) => {
          match n {
            0 => {  0 } ,
            _ => {  type_sort_never(body, n - 1, lvls) } ,
          } } ,
        KernelTypes::KExprNode::Srt(l) => {
          match n {
            0 => {  KernelLevels::level_is_not_zero(KernelLevels::level_inst_params(l, lvls)) } ,
            _ => {  0 } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def red_unfold := aiur_fn⟦
  inline fn red_unfold(ci: KernelTypes::KConstantInfo, lvls: Lists::List<KernelTypes::KLevel>) -> (Field, KernelTypes::KExpr) {
      match ci {
        KernelTypes::KConstantInfo::Defn(nl, _, value, _, _) => {
          match Lists::length(lvls) - nl {
            0 => {  (1, KernelLevels::expr_inst_levels(value, lvls)) } ,
            _ => {  (0, value) } ,
          } } ,
        KernelTypes::KConstantInfo::Thm(nl, _, value) => {
          match Lists::length(lvls) - nl {
            0 => {  (2, KernelLevels::expr_inst_levels(value, lvls)) } ,
            _ => {  (0, value) } ,
          } } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
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
        KernelTypes::KExprNode::Lam(ty, body, _) => {
          match red_beta(rc, head, spine, types) {
            (1, reduct, rest) => {  whnf_with_spine(rc, reduct, rest, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
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
      match red_proj(rc, struct_addr, fidx, inner_exp, types) {
        (1, field) => {  whnf_with_spine(rc, field, spine, types) } ,
        _ => {
          let stuck = (&(KernelTypes::KExprNode::Proj(struct_addr, fidx, inner_whnf)));
          apply_spine(stuck, spine) } ,
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
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def try_quot_iota := aiur_fn⟦
  fn try_quot_iota(rc: KernelRoles::RoleCtx, addr: Bytes::AddressRef, lvls: Lists::List<KernelTypes::KLevel>,
                   spine: Lists::List<KernelTypes::KExpr>,
                   types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match KernelRoles::role_is(rc, addr, KernelRoleSpec::role_quot_lift()) {
        1 => {  red_quot(rc, 1, addr, lvls, spine, types) } ,
        _ => {
          match KernelRoles::role_is(rc, addr, KernelRoleSpec::role_quot_ind()) {
            1 => {  red_quot(rc, 0, addr, lvls, spine, types) } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
      }
    }
⟧

  -- The quotient's ι (the kernel stores `Quot.lift`/`Quot.ind` as recursors with one
  -- rule for `Quot.mk`): `Quot.lift α r β f h q post ↦ f a post` and
  -- `Quot.ind α r β m q post ↦ m a post` when `q` head-normalizes to
  -- `Quot.mk α' r' a`. Premises: the level counts, the rule's level comparand
  -- (`Quot.mk`'s level against the eliminator's first), and Fix A's licensed
  -- certificates of both spines: the eliminator's at a possibly-zero motive
  -- (`Quot.lift`'s `β : Sort v`; `Quot.ind`'s motive is `Prop`, so always), and
  -- `Quot.mk`'s at a possibly-zero `α : Sort u`.

def red_quot := aiur_fn⟦
  fn red_quot(rc: KernelRoles::RoleCtx, is_lift: Field, addr: Bytes::AddressRef, lvls: Lists::List<KernelTypes::KLevel>,
              spine: Lists::List<KernelTypes::KExpr>,
              types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let major_idx = 4 + is_lift;
      match UInt32::less_than_fields(major_idx, Lists::length(spine)) * Fields::is_zero(Lists::length(lvls) - (1 + is_lift)) {
        1 => {
          let q_w = whnf(rc, Lists::lookup(spine, major_idx), types);
          match KernelTypes::collect_spine(q_w) {
            (qh, qargs) => {
              match (*(qh)) {
                KernelTypes::KExprNode::Const(mk_addr, mk_lvls) => {
                  let shape = (KernelRoles::role_is(rc, mk_addr, KernelRoleSpec::role_quot_mk())
                               * Fields::is_zero(Lists::length(qargs) - 3)) * Fields::is_zero(Lists::length(mk_lvls) - 1);
                  match shape {
                    1 => {
                      match KernelLevels::level_equal(Lists::lookup(mk_lvls, 0), Lists::lookup(lvls, 0)) {
                        1 => {
                          match quot_certs(rc, is_lift, addr, lvls, Lists::snoc(Lists::take(spine, major_idx), q_w),
                                           mk_addr, mk_lvls, qargs, types) {
                            1 => {
                              let elim = Lists::lookup(spine, 3);
                              (1, apply_spine((&(KernelTypes::KExprNode::App(elim, Lists::lookup(qargs, 2)))),
                                              Lists::drop(spine, major_idx + 1))) } ,
                            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                          } } ,
                        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                      } } ,
                    _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                  } } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
          } } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

def quot_certs := aiur_fn⟦
  fn quot_certs(rc: KernelRoles::RoleCtx, is_lift: Field, addr: Bytes::AddressRef, lvls: Lists::List<KernelTypes::KLevel>,
                rec_args: Lists::List<KernelTypes::KExpr>, mk_addr: Bytes::AddressRef,
                mk_lvls: Lists::List<KernelTypes::KLevel>, mk_args: Lists::List<KernelTypes::KExpr>,
                types: Lists::List<KernelTypes::KExpr>) -> Field {
      let rec_never = match is_lift {
        1 => {  KernelLevels::level_is_not_zero(Lists::lookup(lvls, 1)) } ,
        _ => {  0 } ,
      };
      let c1 = match rec_never {
        1 => {  1 } ,
        _ => {
          certs_all(rc, KernelLevels::expr_inst_levels(KernelInfer::const_type_of((*(Ingress::get_ci(addr)))), lvls),
                    rec_args, (&(Lists::Node::Nil)), types) } ,
      };
      match c1 {
        1 => {
          match KernelLevels::level_is_not_zero(Lists::lookup(mk_lvls, 0)) {
            1 => {  1 } ,
            _ => {
              certs_all(rc, KernelLevels::expr_inst_levels(KernelInfer::const_type_of((*(Ingress::get_ci(mk_addr)))), mk_lvls),
                        mk_args, (&(Lists::Node::Nil)), types) } ,
          } } ,
        _ => {  0 } ,
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
        KernelTypes::KConstantInfo::Defn(nl, _, value, _, _) => {
          let pd = try_reduce_projection_definition(value, nl, lvls, spine);
          match pd {
            (1, reduced) => {  whnf(rc, reduced, types) } ,
            _ => {
              match red_unfold(ci, lvls) {
                (1, body) => {  whnf_with_spine(rc, body, spine, types) } ,
                _ => {  apply_spine(head, spine) } ,
              } } ,
          } } ,

        KernelTypes::KConstantInfo::Thm(_, _, _) => {  apply_spine(head, spine) } ,
        KernelTypes::KConstantInfo::Quot(_, _, _) => {
          let quot = try_quot_iota(rc, addr, lvls, spine, types);
          match quot {
            (1, reduced) => {  whnf(rc, reduced, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        KernelTypes::KConstantInfo::Rec(rnl, rec_ty, nparams, nindices, nmotives, nminors,
                            rules, k_flag, _, _, _) => {
          match red_rec(rc, rnl, rec_ty, lvls, head, spine, nparams, nindices, nmotives, nminors,
                        rules, k_flag, types) {
            (1, reduced) => {  whnf(rc, reduced, types) } ,
            (2, stuck) => {  stuck } ,
            (3, k_reduct) => {  whnf(rc, k_reduct, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        _ => {  apply_spine(head, spine) } ,
      } } ,
      }
    }
⟧

  -- The recursor dispatch, shared by `whnf` and `whnf_nd`: K first when the record's
  -- K flag is set, else ι; when ι is stuck and the K flag is clear, structure-η ι.
  -- Tags: 0 no move; 1 ι or structure-η ι reduct; 2 stuck, with the prepared major
  -- in place; 3 the K reduct (both callers continue it with full `whnf`).

def red_rec := aiur_fn⟦
  fn red_rec(rc: KernelRoles::RoleCtx, nlvls: Field, rec_ty: KernelTypes::KExpr, lvls: Lists::List<KernelTypes::KLevel>,
             head: KernelTypes::KExpr, spine: Lists::List<KernelTypes::KExpr>,
             nparams: Field, nindices: Field, nmotives: Field, nminors: Field,
             rules: Lists::List<KernelTypes::KRecRule>, k_flag: Field,
             types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match Lists::length(lvls) - nlvls {
        0 => {
      let k_pre = match k_flag {
        1 => {
          match se_parent_addr(rec_ty, ((nparams + nmotives) + nminors) + nindices) {
            (_, rec_parent) => {
              try_k_synth_iota(rc, rec_ty, lvls, spine, nparams, nmotives,
                                  nminors, nindices, rules,
                                  rec_parent, types) } ,
          } } ,
        _ => {  (0, head) } ,
      };
      match k_pre {
        (1, k_reduct) => {  (3, k_reduct) } ,
        _ => {
          let iota = try_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors,
                              nindices, rules, types, head,
                              KernelCheck::rec_to_parent_addr(rec_ty, nparams, nmotives,
                                nminors, nindices));
          match iota {
            (1, reduced) => {  (1, reduced) } ,
            (2, stuck) => {
              match k_flag {
                1 => {  (2, stuck) } ,
                _ => {
                  match try_struct_eta_iota(rc, rec_ty, lvls, spine, nparams,
                          nmotives, nminors, nindices, rules, types) {
                    (1, r) => {  (1, r) } ,
                    _ => {  (2, stuck) } ,
                  } } ,
              } } ,
            _ => {  (0, head) } ,
          } } ,
      } } ,
        _ => {  (0, head) } ,
      }
    }
⟧

def try_reduce_projection_definition := aiur_fn⟦
  fn try_reduce_projection_definition(value: KernelTypes::KExpr, nl: Field, lvls: Lists::List<KernelTypes::KLevel>,
                                            spine: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match projection_definition_info(value, 0) {
        (1, arity, struct_addr, field, struct_arg_idx) => {
          match (1 - UInt32::less_than_fields(Lists::length(spine), arity)) * Fields::is_zero(Lists::length(lvls) - nl) {
            1 => {
              match lams_never(value, arity, lvls) {
                1 => {
                  let target_arg = Lists::lookup(spine, struct_arg_idx);
              let proj_expr = (&(KernelTypes::KExprNode::Proj(struct_addr, field, target_arg)));
              let post = Lists::drop(spine, arity);
              (1, apply_spine(proj_expr, post)) } ,
                _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
              } } ,
            _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
          } } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

  -- The projection-function shortcut is δ and then β at each of the value's λs; it takes
  -- them as gated steps (Red.betaGate), so it fires only when every one of those λs has a
  -- never datum at the use's levels (otherwise δ and `red_beta`'s certificates run).

def lams_never := aiur_fn⟦
  fn lams_never(v: KernelTypes::KExpr, n: Field, lvls: Lists::List<KernelTypes::KLevel>) -> Field {
      match n {
        0 => {  1 } ,
        _ => {
          match (*(v)) {
            KernelTypes::KExprNode::Lam(_, body, bl) => {
              match KernelLevels::level_is_not_zero(bl) {
                1 => {  lams_never(body, n - 1, lvls) } ,
                _ => {
                  match KernelLevels::level_is_not_zero(KernelLevels::level_inst_params(bl, lvls)) {
                    1 => {  lams_never(body, n - 1, lvls) } ,
                    _ => {  0 } ,
                  } } ,
              } } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def projection_definition_info := aiur_fn⟦
  fn projection_definition_info(val: KernelTypes::KExpr, arity: Field)
                                      -> (Field, Field, Bytes::AddressRef, Field, Field) {
      match (*(val)) {
        KernelTypes::KExprNode::Lam(_, body, _) => {
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
  fn try_k_synth_iota(rc: KernelRoles::RoleCtx, rec_ty: KernelTypes::KExpr, lvls: Lists::List<KernelTypes::KLevel>,
                            spine: Lists::List<KernelTypes::KExpr>,
                            nparams: Field, nmotives: Field, nminors: Field, nindices: Field,
                            rules: Lists::List<KernelTypes::KRecRule>,
                            rec_parent: Bytes::AddressRef, types: Lists::List<KernelTypes::KExpr>)
                            -> (Field, KernelTypes::KExpr) {
      match (*(rules)) {
        Lists::Node::Cons(r, _) => {
          match r {
            KernelTypes::KRecRule::Mk(cidx, _rfields, _rrhs) => {
              let major_idx = nparams + nmotives + nminors + nindices;

              match UInt32::less_than_fields(major_idx, Lists::length(spine)) {
                0 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                _ => {
                  let raw_major = Lists::lookup(spine, major_idx);
                  match k_synth_fab(rc, raw_major, cidx, nparams, rec_parent, types) {
                    (1, fab) => {
                      red_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors, nindices,
                               rules, rec_parent, fab, types) } ,
                    _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                  } } ,
              } } ,
          } } ,
        _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
      }
    }
⟧

  -- Red.rescueK: the major's type is the recursor's inductive; `fab` is the first
  -- rule's constructor applied to that type's parameters; the major's type is
  -- definitionally equal to `fab`'s, and both types are propositions, so `fab` and
  -- the major are definitionally equal by proof irrelevance (DefEq.proofIrrel: both
  -- sorts zero). ι then fires on `fab` (`red_iota`).

def k_synth_fab := aiur_fn⟦
  fn k_synth_fab(rc: KernelRoles::RoleCtx, raw_major: KernelTypes::KExpr, cidx: Field, nparams: Field,
                 rec_parent: Bytes::AddressRef, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let major_ty = KernelInfer::k_infer(rc, raw_major, types);
      let major_ty_w = whnf(rc, major_ty, types);
      match KernelTypes::collect_spine(major_ty_w) {
        (ty_head, ty_args) => {
          match (*(ty_head)) {
            KernelTypes::KExprNode::Const(ind_addr, ctor_us) => {
              match Bytes::address_eq(ind_addr, rec_parent) {
                1 => {
                  match (*(Ingress::get_ci(ind_addr))) {
                    KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, ind_block, ind_idx) => {
                      let cprj = KernelCheck::projection_addr_ctor(ind_idx, cidx, ind_block);
                      let fab = apply_spine((&(KernelTypes::KExprNode::Const(cprj, ctor_us))),
                                            Lists::take(ty_args, nparams));
                      let fab_ty = KernelInfer::k_infer(rc, fab, types);
                      match KernelDefEq::k_is_def_eq(rc, major_ty_w, fab_ty, types) {
                        1 => {
                          match KernelDefEq::is_prop_type(rc, major_ty, types) {
                            1 => {  (KernelDefEq::is_prop_type(rc, fab_ty, types), fab) } ,
                            _ => {  (0, fab) } ,
                          } } ,
                        _ => {  (0, fab) } ,
                      } } ,
                    _ => {  (0, raw_major) } ,
                  } } ,
                _ => {  (0, raw_major) } ,
              } } ,
            _ => {  (0, raw_major) } ,
          } } ,
      }
    }
⟧



def whnf_iota_major := aiur_fn⟦
  fn whnf_iota_major(rc: KernelRoles::RoleCtx, e: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let w = whnf(rc, e, types);
      match KernelTypes::collect_spine(w) {
        (h, sp) => {
          match (*(h)) {
            KernelTypes::KExprNode::Const(addr, lvls) => {
              match red_unfold((*(Ingress::get_ci(addr))), lvls) {
                (2, body) => {  whnf_iota_major(rc, whnf_with_spine(rc, body, sp, types), types) } ,
                _ => {  w } ,
              } } ,
            _ => {  w } ,
          } } ,
      }
    }
⟧

  -- ι with the major's preparation (the `Red` premise on the major): the linear
  -- `Nat.rec` fold, the `Nat.add` offset rewrite, `whnf` with theorem unfolding, the
  -- literal-to-constructor step. The firing itself is `red_iota`. Tags: 0 no move;
  -- 1 the reduct; 2 stuck, with the prepared major in place.

def try_iota := aiur_fn⟦
  fn try_iota(rc: KernelRoles::RoleCtx, rec_ty: KernelTypes::KExpr, lvls: Lists::List<KernelTypes::KLevel>, spine: Lists::List<KernelTypes::KExpr>,
                    nparams: Field, nmotives: Field, nminors: Field, nindices: Field,
                    rules: Lists::List<KernelTypes::KRecRule>, types: Lists::List<KernelTypes::KExpr>,
                    head: KernelTypes::KExpr, rec_parent: Bytes::AddressRef) -> (Field, KernelTypes::KExpr) {
      let major_idx = nparams + nmotives + nminors + nindices;
      let spine_len = Lists::length(spine);
      match UInt32::less_than_fields(major_idx, spine_len) {
        0 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
        _ => {

          let raw_major = Lists::lookup(spine, major_idx);

          let major_clean1 = KernelNatPrim::cleanup_nat_offset_major(rc, raw_major);
          let major_w = whnf_iota_major(rc, major_clean1, types);
          let major_clean2 = KernelNatPrim::cleanup_nat_offset_major(rc, major_w);
          let major = nat_lit_to_ctor_or_self(rc, major_clean2);
          match red_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors, nindices,
                         rules, rec_parent, major, types) {
            (1, r3) => {  (1, r3) } ,
            _ => {
              (2, apply_spine(head, spine)) } ,
          } } ,
      }
    }
⟧

  -- Red.iota on a prepared major: the rule for the major's constructor fires on the
  -- recursor's parameters, motives and minors, the constructor's fields and the
  -- arguments after the major. Tag 0: no rule matches (or the major is no
  -- constructor application).

def red_iota := aiur_fn⟦
  fn red_iota(rc: KernelRoles::RoleCtx, rec_ty: KernelTypes::KExpr, lvls: Lists::List<KernelTypes::KLevel>,
              spine: Lists::List<KernelTypes::KExpr>,
              nparams: Field, nmotives: Field, nminors: Field, nindices: Field,
              rules: Lists::List<KernelTypes::KRecRule>, rec_parent: Bytes::AddressRef,
              major: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match KernelTypes::collect_spine(major) {
        (mh, margs) => {
          match (*(mh)) {
            KernelTypes::KExprNode::Const(caddr, clvls) => {
              match (*(Ingress::get_ci(caddr))) {
                KernelTypes::KConstantInfo::Ctor(cnl, cty, cblock, cind, cidx, cnp, cnf, _) => {

                  assert_eq!(Bytes::address_eq(KernelDefEq::compute_iprj_addr(cblock, cind), rec_parent), 1,
                    "iota: major's constructor belongs to a different inductive");
                  match find_rule(rules, cidx) {
                    (1, rfields, rrhs) => {
                      let shape = (Fields::is_zero(Lists::length(margs) - (cnp + cnf)) * Fields::is_zero(rfields - cnf))
                                  * Fields::is_zero(Lists::length(clvls) - cnl);
                      let pmm_end = nparams + nmotives + nminors;
                      let major_idx = pmm_end + nindices;
                      match shape {
                        1 => {
                          let rec_ty_i = KernelLevels::expr_inst_levels(rec_ty, lvls);
                          let pre = Lists::take(spine, major_idx);
                          match iota_cmp(rc, rec_ty_i, pre, major_idx, cty, clvls, cnp, margs, nindices, types)
                                * iota_certs(rc, rec_ty_i, nparams, Lists::snoc(pre, major), cty, cblock, cind, clvls, margs, types) {
                            1 => {
                              let rhs_lvled = KernelLevels::expr_inst_levels(rrhs, lvls);
                              let r1 = apply_spine(rhs_lvled, Lists::take(spine, pmm_end));
                              let r2 = apply_spine(r1, Lists::drop(margs, cnp));
                              (1, apply_spine(r2, Lists::drop(spine, major_idx + 1))) } ,
                            _ => {  (0, major) } ,
                          } } ,
                        _ => {  (0, major) } ,
                      } } ,
                    _ => {  (0, major) } ,
                  } } ,
                _ => {  (0, major) } ,
              } } ,
            _ => {  (0, major) } ,
          } } ,
      }
    }
⟧

  -- Red.iota's comparisons (never skipped): the constructor's levels against the
  -- levels of the major's domain in the recursor's type (the rule's level comparands),
  -- the constructor's parameters against that domain's parameters (the parameter
  -- comparison; the domain's parameters are the recursor's parameter arguments), and,
  -- for an indexed family, the constructor type's residual indices against the
  -- domain's (the recursor's index arguments).

def iota_cmp := aiur_fn⟦
  fn iota_cmp(rc: KernelRoles::RoleCtx, rec_ty_i: KernelTypes::KExpr, pre: Lists::List<KernelTypes::KExpr>,
              major_idx: Field, cty: KernelTypes::KExpr, clvls: Lists::List<KernelTypes::KLevel>, cnp: Field,
              margs: Lists::List<KernelTypes::KExpr>, nindices: Field,
              types: Lists::List<KernelTypes::KExpr>) -> Field {
      match pi_peel(rec_ty_i, pre, (&(Lists::Node::Nil)), major_idx) {
        (1, md) => {
          match KernelTypes::collect_spine(md) {
            (mdh, mda) => {
              match (*(mdh)) {
                KernelTypes::KExprNode::Const(_, mlvls) => {
                  match KernelDefEq::level_list_eq(clvls, mlvls) {
                    1 => {
                      match KernelDefEq::de_args(rc, Lists::take(margs, cnp), Lists::take(mda, cnp), types) {
                        1 => {
                          match nindices {
                            0 => {  1 } ,
                            _ => {
                              match pi_residual(KernelLevels::expr_inst_levels(cty, clvls), margs, (&(Lists::Node::Nil))) {
                                (1, res) => {
                                  match KernelTypes::collect_spine(res) {
                                    (_, ra) => {  KernelDefEq::de_args(rc, Lists::drop(ra, cnp), Lists::drop(mda, cnp), types) } ,
                                  } } ,
                                _ => {  0 } ,
                              } } ,
                          } } ,
                        _ => {  0 } ,
                      } } ,
                    _ => {  0 } ,
                  } } ,
                _ => {  0 } ,
              } } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

  -- Fix A at ι (RULES-GAP PM-C): Red.iota's two licensed `Certs` walks. The binder
  -- datum of every slot of a stored type former's telescope is the zero-ness of the
  -- sort it ends in (D2's entry point for stored declaration types): for the
  -- recursor, its motive's sort; for the constructor, its inductive's sort. At a
  -- never-zero datum every slot skips; otherwise every argument is certified.

def iota_certs := aiur_fn⟦
  fn iota_certs(rc: KernelRoles::RoleCtx, rec_ty_i: KernelTypes::KExpr, nparams: Field,
                rec_args: Lists::List<KernelTypes::KExpr>, cty: KernelTypes::KExpr, cblock: Bytes::AddressRef,
                cind: Field, clvls: Lists::List<KernelTypes::KLevel>, margs: Lists::List<KernelTypes::KExpr>,
                types: Lists::List<KernelTypes::KExpr>) -> Field {
      let c1 = match rec_slots_never(rec_ty_i, nparams) {
        1 => {  1 } ,
        _ => {  certs_all(rc, rec_ty_i, rec_args, (&(Lists::Node::Nil)), types) } ,
      };
      match c1 {
        1 => {
          match (*(Ingress::get_ci_iprj(cblock, cind))) {
            KernelTypes::KConstantInfo::Induct(_, ind_ty, inp, ini, _, _, _, _) => {
              match type_sort_never(ind_ty, inp + ini, clvls) {
                1 => {  1 } ,
                _ => {  certs_all(rc, KernelLevels::expr_inst_levels(cty, clvls), margs, (&(Lists::Node::Nil)), types) } ,
              } } ,
            _ => {  0 } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

  -- The datum of a recursor type's slots: whether its (first) motive's type ends in
  -- a never-zero sort. The recursor type must be syntactically a telescope there.

def rec_slots_never := aiur_fn⟦
  fn rec_slots_never(t: KernelTypes::KExpr, nparams: Field) -> Field {
      match (*(t)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          match nparams {
            0 => {  final_sort_never(dom) } ,
            _ => {  rec_slots_never(body, nparams - 1) } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def final_sort_never := aiur_fn⟦
  fn final_sort_never(t: KernelTypes::KExpr) -> Field {
      match (*(t)) {
        KernelTypes::KExprNode::Forall(_, body, _) => {  final_sort_never(body) } ,
        KernelTypes::KExprNode::Srt(l) => {  KernelLevels::level_is_not_zero(l) } ,
        _ => {  0 } ,
      }
    }
⟧

  -- The `n`-th binder domain of the telescope `t`, its earlier binders instantiated
  -- by `args` (`subs_rev` accumulates them, innermost first). Tag 0: `t` is not such
  -- a telescope.

def pi_peel := aiur_fn⟦
  fn pi_peel(t: KernelTypes::KExpr, args: Lists::List<KernelTypes::KExpr>, subs_rev: Lists::List<KernelTypes::KExpr>,
             n: Field) -> (Field, KernelTypes::KExpr) {
      match (*(t)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
          match n {
            0 => {  (1, KernelInfer::inst_subs(dom, subs_rev)) } ,
            _ => {
              match (*(args)) {
                Lists::Node::Cons(a, rest) => {
                  pi_peel(body, rest, (&(Lists::Node::Cons(a, subs_rev))), n - 1) } ,
                Lists::Node::Nil => {  (0, t) } ,
              } } ,
          } } ,
        _ => {  (0, t) } ,
      }
    }
⟧

  -- The codomain of the telescope `t` after all of `args` (`piResidual`). Tag 0: `t`
  -- has fewer binders than `args`.

def pi_residual := aiur_fn⟦
  fn pi_residual(t: KernelTypes::KExpr, args: Lists::List<KernelTypes::KExpr>,
                 subs_rev: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      match (*(args)) {
        Lists::Node::Nil => {  (1, KernelInfer::inst_subs(t, subs_rev)) } ,
        Lists::Node::Cons(a, rest) => {
          match (*(t)) {
            KernelTypes::KExprNode::Forall(_, body, _) => {
              pi_residual(body, rest, (&(Lists::Node::Cons(a, subs_rev)))) } ,
            _ => {  (0, t) } ,
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
        Lists::Node::Cons(_, rest) => {
          match (*(rest)) {
            Lists::Node::Cons(_, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
            Lists::Node::Nil => {
              let skip = ((nparams + nmotives) + nminors) + nindices;
              match se_parent_addr(rec_ty, skip) {
                (0, _) => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                (_, parent) => {
                  match (*(Ingress::get_ci(parent))) {
                    KernelTypes::KConstantInfo::Induct(_, ind_ty, ind_np, ind_nidx, num_ctors, _, block, idx) => {
                      match Fields::is_zero(num_ctors - 1) * Fields::is_zero(ind_nidx) {
                        1 => {
                          match struct_is_rec(parent) {
                            0 => {
                              let major = Lists::lookup(spine, skip);
                              match UInt32::less_than_fields(Lists::length(types), KernelSubst::expr_lbr(major)) {
                                1 => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
                                _ => {
                                  match eta_iota_fab(rc, ind_ty, ind_np, block, idx, parent, major, types) {
                                    (1, fab) => {
                                      red_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors, nindices,
                                               rules, parent, fab, types) } ,
                                    _ => {  (0, (&(KernelTypes::KExprNode::BVar(0)))) } ,
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
      }
    }
⟧

  -- Red.rescueEta: the major's type head-normalizes to the structure `parent` at
  -- exactly its parameters; the structure's sort at the type's levels is never zero
  -- (`capsNeverZero`, D4: no structure-η ι at `Sort u` structures); `fab` is the
  -- constructor applied to the type's parameters and the major's projections. The
  -- rule's final `DefEq fab major` is DefEq.structEta, whose comparisons are
  -- reflexive here (`fab`'s parameters are the type's, its fields the major's
  -- projections) and whose unlicensed `Certs` of the type's arguments are checked
  -- (`certs_all`). ι then fires on `fab` (`red_iota`).

def eta_iota_fab := aiur_fn⟦
  fn eta_iota_fab(rc: KernelRoles::RoleCtx, ind_ty: KernelTypes::KExpr, ind_np: Field,
                  block: Bytes::AddressRef, idx: Field, parent: Bytes::AddressRef,
                  major: KernelTypes::KExpr, types: Lists::List<KernelTypes::KExpr>) -> (Field, KernelTypes::KExpr) {
      let major_ty_w = whnf(rc, KernelInfer::k_infer(rc, major, types), types);
      match KernelTypes::collect_spine(major_ty_w) {
        (th, targs) => {
          match (*(th)) {
            KernelTypes::KExprNode::Const(taddr, tus) => {
              match Bytes::address_eq(taddr, parent) * Fields::is_zero(Lists::length(targs) - ind_np) {
                1 => {
                  match type_sort_never(ind_ty, ind_np, tus) {
                    1 => {
                      match certs_all(rc, KernelLevels::expr_inst_levels(ind_ty, tus), targs, (&(Lists::Node::Nil)), types) {
                        1 => {
                          match (*(Ingress::get_ci_cprj(block, idx, 0))) {
                            KernelTypes::KConstantInfo::Ctor(_, _, _, _, _, _, nf, _) => {
                              let cprj = KernelCheck::projection_addr_ctor(idx, 0, block);
                              let fab0 = apply_spine((&(KernelTypes::KExprNode::Const(cprj, tus))), targs);
                              (1, apply_n_projs(fab0, parent, major, nf, 0)) } ,
                            _ => {  (0, major) } ,
                          } } ,
                        _ => {  (0, major) } ,
                      } } ,
                    _ => {  (0, major) } ,
                  } } ,
                _ => {  (0, major) } ,
              } } ,
            _ => {  (0, major) } ,
          } } ,
      }
    }
⟧

  -- The unlicensed telescope certificate (`Certs env d false`): each argument's
  -- io-inferred type is definitionally equal to its binder's domain, the domains
  -- instantiated along the spine; a telescope that is not syntactically a ∀ is
  -- head-normalized first.

def certs_all := aiur_fn⟦
  fn certs_all(rc: KernelRoles::RoleCtx, t: KernelTypes::KExpr, args: Lists::List<KernelTypes::KExpr>,
               subs_rev: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> Field {
      match (*(args)) {
        Lists::Node::Nil => {  1 } ,
        Lists::Node::Cons(a, rest) => {
          match (*(t)) {
            KernelTypes::KExprNode::Forall(dom, cod, _) => {
              let ta = KernelInferOnly::k_infer_only(rc, a, types);
              match KernelDefEq::k_is_def_eq(rc, ta, KernelInfer::inst_subs(dom, subs_rev), types) {
                1 => {  certs_all(rc, cod, rest, (&(Lists::Node::Cons(a, subs_rev))), types) } ,
                _ => {  0 } ,
              } } ,
            _ => {
              let t_w = whnf(rc, KernelInfer::inst_subs(t, subs_rev), types);
              match (*(t_w)) {
                KernelTypes::KExprNode::Forall(_, _, _) => {  certs_all(rc, t_w, args, (&(Lists::Node::Nil)), types) } ,
                _ => {  0 } ,
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
            KernelTypes::KExprNode::Forall(dom, _, _) => {
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
            KernelTypes::KExprNode::Forall(_, body, _) => {  se_parent_addr(body, skip - 1) } ,
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
        KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, block, _) => {
          let members = struct_block_member_addrs(parent, block);
          struct_scan_members(members, members) } ,
        _ => {  1 } ,
      }
    }
⟧

  -- D6 (Lean's `is_rec`, a block-level flag): whether any constructor of any inductive
  -- member of the block mentions a member of the block.

def struct_scan_members := aiur_fn⟦
  fn struct_scan_members(ms: Lists::List<Bytes::AddressRef>, members: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(ms)) {
        Lists::Node::Nil => {  0 } ,
        Lists::Node::Cons(m, rest) => {
          match (*(Ingress::get_ci(m))) {
            KernelTypes::KConstantInfo::Induct(_, _, n_params, _, num_ctors, _, block, idx) => {
              match struct_scan_ctors(block, idx, num_ctors, n_params, members, 0) {
                1 => {  1 } ,
                _ => {  struct_scan_members(rest, members) } ,
              } } ,
            _ => {  struct_scan_members(rest, members) } ,
          } } ,
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
            KernelTypes::KExprNode::Forall(_, body, _) => {  se_peel_tol(body, n - 1) } ,
            _ => {  ty } ,
          } } ,
      }
    }
⟧

def se_scan_fields := aiur_fn⟦
  fn se_scan_fields(ty: KernelTypes::KExpr, members: Lists::List<Bytes::AddressRef>) -> Field {
      match (*(ty)) {
        KernelTypes::KExprNode::Forall(dom, body, _) => {
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
        KernelTypes::KExprNode::Lam(t, b, _) => {
          match se_mentions(t, members) {
            1 => {  1 } ,
            _ => {  se_mentions(b, members) } ,
          } } ,
        KernelTypes::KExprNode::Forall(t, b, _) => {
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
        KernelTypes::KExprNode::Lam(_, _, _) => {  e } ,
        KernelTypes::KExprNode::Forall(_, _, _) => {  e } ,
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
        KernelTypes::KExprNode::Lam(_, _, _) => {  e } ,
        KernelTypes::KExprNode::Forall(_, _, _) => {  e } ,
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
        KernelTypes::KExprNode::Lam(_, _, _) => {
          match red_beta(rc, head, spine, types) {
            (1, reduct, rest) => {  whnf_struct_core_spine(rc, reduct, rest, types) } ,
            _ => {  apply_spine(head, spine) } ,
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
      match red_proj(rc, struct_addr, fidx, inner_w, types) {
        (1, field) => {  whnf_struct_core_spine(rc, field, spine, types) } ,
        _ => {  apply_spine(original, spine) } ,
      }
    }
⟧

def whnf_struct_core_const := aiur_fn⟦
  fn whnf_struct_core_const(rc: KernelRoles::RoleCtx, addr: Bytes::AddressRef, lvls: Lists::List<KernelTypes::KLevel>, head: KernelTypes::KExpr,
                                   spine: Lists::List<KernelTypes::KExpr>,
                                   types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      match (*(Ingress::get_ci(addr))) {
        KernelTypes::KConstantInfo::Rec(rnl, rec_ty, nparams, nindices, nmotives, nminors,
                            rules, _, _, _, _) => {
          match Lists::length(lvls) - rnl {
            0 => {
              match try_iota(rc, rec_ty, lvls, spine, nparams, nmotives, nminors, nindices,
                      rules, types, head,
                      KernelCheck::rec_to_parent_addr(rec_ty, nparams, nmotives, nminors,
                        nindices)) {
                (1, reduced) => {  whnf_struct_core(rc, reduced, types) } ,
                _ => {  apply_spine(head, spine) } ,
              } } ,
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
        KernelTypes::KExprNode::Lam(_, _, _) => {  e } ,
        KernelTypes::KExprNode::Forall(_, _, _) => {  e } ,
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
        KernelTypes::KExprNode::Lam(ty, body, _) => {
          match red_beta(rc, head, spine, types) {
            (1, reduct, rest) => {  whnf_nd_with_spine(rc, reduct, rest, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
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

def whnf_nd_proj_head := aiur_fn⟦
  fn whnf_nd_proj_head(rc: KernelRoles::RoleCtx, struct_addr: Bytes::AddressRef, fidx: Field, inner: KernelTypes::KExpr,
                             spine: Lists::List<KernelTypes::KExpr>, types: Lists::List<KernelTypes::KExpr>) -> KernelTypes::KExpr {
      let inner_whnf = whnf_nd(rc, inner, types);

      let inner_exp = KernelNatPrim::str_lit_to_ctor_app_or_self(rc, inner_whnf, types);
      match red_proj(rc, struct_addr, fidx, inner_exp, types) {
        (1, field) => {  whnf_nd_with_spine(rc, field, spine, types) } ,
        _ => {
          let stuck = (&(KernelTypes::KExprNode::Proj(struct_addr, fidx, inner_whnf)));
          apply_spine(stuck, spine) } ,
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
        KernelTypes::KConstantInfo::Defn(nl, _, value, _, _) => {
          let pd = try_reduce_projection_definition(value, nl, lvls, spine);
          match pd {
            (1, reduced) => {  whnf_nd(rc, reduced, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        KernelTypes::KConstantInfo::Quot(_, _, _) => {
          let quot = try_quot_iota(rc, addr, lvls, spine, types);
          match quot {
            (1, reduced) => {  whnf_nd(rc, reduced, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        KernelTypes::KConstantInfo::Rec(rnl, rec_ty, nparams, nindices, nmotives, nminors,
                            rules, k_flag, _, _, _) => {
          match red_rec(rc, rnl, rec_ty, lvls, head, spine, nparams, nindices, nmotives, nminors,
                        rules, k_flag, types) {
            (1, reduced) => {  whnf_nd(rc, reduced, types) } ,
            (2, stuck) => {  stuck } ,
            (3, k_reduct) => {  whnf(rc, k_reduct, types) } ,
            _ => {  apply_spine(head, spine) } ,
          } } ,
        _ => {  apply_spine(head, spine) } ,
      } } ,
      }
    }
⟧

end

end IxVM
