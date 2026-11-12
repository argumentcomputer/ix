import Aiur.Modules.Function

/-! # IxVM module `KernelRoles`

Role binding tables and their evidence, which name the constants the kernel treats as primitives.

Named Aiur declarations, elaborated together by `IxVM.Program`. -/

namespace IxVM

aiur_module KernelRoles where

aiur_decls⟦
module KernelRoles {
  enum RoleEvidence {
      Defeq,
      Proof(Bytes::AddressRef)
    }

  enum RoleTableNode {
      Mk(Bytes::AddressRef, RoleMap<Bytes::AddressRef>, RBTreeMap::RBTreeMap<Field>, RoleMap<Lists::List<RoleEvidence>>)
    }

  type RoleTable = &RoleTableNode;

  enum RoleCtxNode {
      Mk(RoleTable, Field, RBTreeMap::RBTreeMap<Field>),
      Assumed(RoleTable, RBTreeMap::RBTreeMap<Field>)
    }

  type RoleCtx = &RoleCtxNode;

  -- Port divergence: role-indexed maps, separate from the address-keyed
  -- `RBTreeMap::RBTreeMap` (see `role_map_lookup_or_default`).
  enum RoleMap<V> {
      Nil,
      Node(Field, Field, V, &RoleMap<V>, &RoleMap<V>)
    }
}
⟧

def load_role_table := aiur_fn⟦
  fn load_role_table(binding: Bytes::AddressRef) -> RoleTable {
      let raw = (*(binding));
      let (idx, len) = IxVMCompat::io_get_info(6, raw);
      let bytes = IxByteStream::read_finite_byte_stream(6, idx, len);
      Blake3::verify_bytes_against(bytes, raw);
      let (t0, s) = IxonDeserialize::read_byte(bytes);
      assert_eq!(UInt8::to_field(t0), 232, "role table: not a binding section");
      let (t1, s) = IxonDeserialize::read_byte(s);
      assert_eq!(UInt8::to_field(t1), 3, "role table: not a binding section");
      let (version, s) = IxonDeserialize::read_byte(s);
      assert_eq!(UInt8::to_field(version), KernelRoleSpec::spec_version(),
        "role table: made for another specification version");
      let (n, s) = IxonDeserialize::read_byte(s);
      let (by_role, by_addr, _next, s) =
        read_role_bindings(s, UInt8::to_field(n), 0, RBTreeMap::RBTreeMap::Nil);
      let (m, s) = IxonDeserialize::read_byte(s);
      let (evidence, _next, s) = read_role_evidence(s, UInt8::to_field(m), 0);
      let Lists::Node::Nil = (*(s));
      (&(RoleTableNode::Mk(binding, by_role, by_addr, evidence)))
    }
⟧

def read_role_bindings := aiur_fn⟦
  fn read_role_bindings(s: Bytes::Stream, count: Field, next: Field, by_addr: RBTreeMap::RBTreeMap<Field>)
        -> (RoleMap<Bytes::AddressRef>, RBTreeMap::RBTreeMap<Field>, Field, Bytes::Stream) {
      match count {
        0 => {  (RoleMap::Nil, by_addr, next, s) } ,
        _ => {
          let [b0, _, _, _, _, _, _, _] = UInt8::raw_bit_decomposition(count);
          let half = (count - b0) / 2;
          let (left, by_addr, next, s) = read_role_bindings(s, half, next, by_addr);
          let (rb, s) = IxonDeserialize::read_byte(s);
          let r = UInt8::to_field(rb);
          assert_eq!(UInt32::less_than_fields(r, KernelRoleSpec::role_count()), 1, "role table: unknown role");
          assert_eq!(UInt32::less_than_fields(r, next), 0, "role table: roles out of order");
          let (a, s) = IxonDeserialize::get_address(s);
          assert_eq!(RBTreeMap::rbtree_map_lookup_or_default(a, by_addr, 0), 0,
            "role table: an address is bound to two roles");
          let by_addr = RBTreeMap::rbtree_map_insert(a, r + 1, by_addr);
          let (right, by_addr, next, s) =
            read_role_bindings(s, count - (half + 1), r + 1, by_addr);
          (RoleMap::Node(1, r, a, (&(left)), (&(right))), by_addr, next, s) } ,
      }
    }
⟧

def read_role_evidence := aiur_fn⟦
  fn read_role_evidence(s: Bytes::Stream, count: Field, next: Field)
        -> (RoleMap<Lists::List<RoleEvidence>>, Field, Bytes::Stream) {
      match count {
        0 => {  (RoleMap::Nil, next, s) } ,
        _ => {
          let [b0, _, _, _, _, _, _, _] = UInt8::raw_bit_decomposition(count);
          let half = (count - b0) / 2;
          let (left, next, s) = read_role_evidence(s, half, next);
          let (rb, s) = IxonDeserialize::read_byte(s);
          let r = UInt8::to_field(rb);
          assert_eq!(UInt32::less_than_fields(r, KernelRoleSpec::role_count()), 1, "role table: unknown role");
          assert_eq!(UInt32::less_than_fields(r, next), 0, "role table: evidence out of order");
          let (kb, s) = IxonDeserialize::read_byte(s);
          let (entries, s) = read_evidence_entries(s, UInt8::to_field(kb));
          let (right, next, s) = read_role_evidence(s, count - (half + 1), r + 1);
          (RoleMap::Node(1, r, entries, (&(left)), (&(right))), next, s) } ,
      }
    }
⟧

def read_evidence_entries := aiur_fn⟦
  fn read_evidence_entries(s: Bytes::Stream, count: Field) -> (Lists::List<RoleEvidence>, Bytes::Stream) {
      match count {
        0 => {  ((&(Lists::Node::Nil)), s) } ,
        _ => {
          let (tag, s) = IxonDeserialize::read_byte(s);
          match UInt8::to_field(tag) {
            0 => {
              let (rest, s) = read_evidence_entries(s, count - 1);
              ((&(Lists::Node::Cons(RoleEvidence::Defeq, rest))), s) } ,
            1 => {
              let (a, s) = IxonDeserialize::get_address(s);
              let (rest, s) = read_evidence_entries(s, count - 1);
              ((&(Lists::Node::Cons(RoleEvidence::Proof(a), rest))), s) } ,
          } } ,
      }
    }
⟧

def role_ctx_assumed := aiur_fn⟦
  fn role_ctx_assumed(binding: Bytes::AddressRef) -> RoleCtx {
      (&(RoleCtxNode::Assumed(load_role_table(binding), RBTreeMap::RBTreeMap::Nil)))
    }
⟧

def role_ctx_for_validator := aiur_fn⟦
  fn role_ctx_for_validator(binding: Bytes::AddressRef, validator: Field) -> RoleCtx {
      load_role_ctx(binding, validator, Options::Option::None)
    }
⟧

def validate_user_axioms := aiur_fn⟦
  fn validate_user_axioms(tbl: RoleTable, leaves: Lists::List<Bytes::AddressRef>, acc: RBTreeMap::RBTreeMap<Field>)
        -> RBTreeMap::RBTreeMap<Field> {
      match (*(leaves)) {
        Lists::Node::Nil => {  acc } ,
        Lists::Node::Cons(a, rest) => {
          assert_eq!(RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0), 0,
            "claim: user axiom is bound in the role table");
          match (*(Ingress::get_ci(a))) {
            KernelTypes::KConstantInfo::Axiom(_, _, u) => {
              assert_eq!(u, 0, "claim: user axiom is unsafe");
              validate_user_axioms(tbl, rest, RBTreeMap::rbtree_map_insert(a, 1, acc)) } ,
            _ => {
              assert_eq!(0, 1, "claim: axioms tree entry is not an axiom");
              acc } ,
          } } ,
      }
    }
⟧

  -- A claim with user axioms needs the table to bind `propext`, `Classical.choice` and
  -- `sorryAx`: an unbound one's own axiom is an unbound safe axiom, which the claim could
  -- otherwise list as a user axiom (the kernel's admission of a table under user axioms).

def assert_axiom_roles_bound := aiur_fn⟦
  fn assert_axiom_roles_bound(tbl: RoleTable) -> () {
      assert_eq!(role_is_bound(tbl, KernelRoleSpec::role_propext()), 1,
        "claim: user axioms need propext, Classical.choice and sorryAx bound");
      assert_eq!(role_is_bound(tbl, KernelRoleSpec::role_choice()), 1,
        "claim: user axioms need propext, Classical.choice and sorryAx bound");
      assert_eq!(role_is_bound(tbl, KernelRoleSpec::role_sorry_ax()), 1,
        "claim: user axioms need propext, Classical.choice and sorryAx bound");
      ()
    }
⟧

def load_role_ctx := aiur_fn⟦
  fn load_role_ctx(binding: Bytes::AddressRef, validator: Field, axioms_opt: Options::Option<Bytes::AddressRef>) -> RoleCtx {
      let tbl = load_role_table(binding);
      let axioms = match axioms_opt {
        Options::Option::None => {  RBTreeMap::RBTreeMap::Nil } ,
        Options::Option::Some(ax_root) => {
          assert_axiom_roles_bound(tbl);
          validate_user_axioms(tbl, KernelClaim::load_assumption_tree(ax_root), RBTreeMap::RBTreeMap::Nil) } ,
      };
      match validator {
        3 => {  (&(RoleCtxNode::Mk(tbl, KernelRoleSpec::group_count(), axioms))) } ,
        4 => {  (&(RoleCtxNode::Assumed(tbl, axioms))) } ,
        _ => {
          assert_eq!(0, 1, "claim: wrong validator identity");
          (&(RoleCtxNode::Mk(tbl, KernelRoleSpec::group_count(), axioms))) } ,
      }
    }
⟧

def role_ctx_validator := aiur_fn⟦
  fn role_ctx_validator(rc: RoleCtx) -> Field {
      3 + role_ctx_is_assumed(rc)
    }
⟧

def role_ctx_table := aiur_fn⟦
  fn role_ctx_table(rc: RoleCtx) -> RoleTable {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, _, _) => {  tbl } ,
        RoleCtxNode::Assumed(tbl, _) => {  tbl } ,
      }
    }
⟧

def role_ctx_axioms := aiur_fn⟦
  fn role_ctx_axioms(rc: RoleCtx) -> RBTreeMap::RBTreeMap<Field> {
      match (*(rc)) {
        RoleCtxNode::Mk(_, _, axioms) => {  axioms } ,
        RoleCtxNode::Assumed(_, axioms) => {  axioms } ,
      }
    }
⟧

def role_ctx_is_assumed := aiur_fn⟦
  fn role_ctx_is_assumed(rc: RoleCtx) -> Field {
      match (*(rc)) {
        RoleCtxNode::Mk(_, _, _) => {  0 } ,
        RoleCtxNode::Assumed(_, _) => {  1 } ,
      }
    }
⟧

def role_ctx_binding := aiur_fn⟦
  fn role_ctx_binding(rc: RoleCtx) -> Bytes::AddressRef {
      match (*(role_ctx_table(rc))) {
        RoleTableNode::Mk(binding, _, _, _) => {  binding } ,
      }
    }
⟧

def role_bound_addr_or_zero := aiur_fn⟦
  fn role_bound_addr_or_zero(tbl: RoleTable, r: Field) -> Bytes::AddressRef {
      match (*(tbl)) {
        RoleTableNode::Mk(_, by_role, _, _) => {
          role_map_lookup_or_default(r, by_role, (&([UInt8::BYTE_0; 32]))) } ,
      }
    }
⟧

def role_is_bound := aiur_fn⟦
  fn role_is_bound(tbl: RoleTable, r: Field) -> Field {
      let a = role_bound_addr_or_zero(tbl, r);
      match RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0) - (r + 1) {
        0 => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

def role_bound_addr := aiur_fn⟦
  fn role_bound_addr(tbl: RoleTable, r: Field) -> Bytes::AddressRef {
      assert_eq!(role_is_bound(tbl, r), 1,
        "role table does not bind a role the claim needs");
      role_bound_addr_or_zero(tbl, r)
    }
⟧

def role_addr_index := aiur_fn⟦
  fn role_addr_index(tbl: RoleTable) -> RBTreeMap::RBTreeMap<Field> {
      match (*(tbl)) {
        RoleTableNode::Mk(_, _, by_addr, _) => {  by_addr } ,
      }
    }
⟧

def role_of := aiur_fn⟦
  fn role_of(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, limit, _) => {
          let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
          match r1 {
            0 => {  0 } ,
            _ => {
              match UInt32::less_than_fields(KernelRoleSpec::role_group(r1 - 1), limit) {
                1 => {
                  group_admit(tbl, KernelRoleSpec::role_group(r1 - 1));
                  r1 } ,
                _ => {  0 } ,
              } } ,
          } } ,
        RoleCtxNode::Assumed(tbl, _) => {
          RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0) } ,
      }
    }
⟧

def role_index_of := aiur_fn⟦
  fn role_index_of(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(role_ctx_table(rc)), 0)
    }
⟧

def role_is_inert := aiur_fn⟦
  fn role_is_inert(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      -- 1 when the binding binds `a` to an inert role (specification kind 4: `sorryAx` and
      -- Lean's compiler-trust axioms), 0 otherwise.
      let r1 = role_index_of(rc, a);
      match r1 {
        0 => {  0 } ,
        _ => {
          match KernelRoleSpec::role_spec_kind(r1 - 1) - 4 {
            0 => {  1 } ,
            _ => {  0 } ,
          } } ,
      }
    }
⟧

def role_is := aiur_fn⟦
  fn role_is(rc: RoleCtx, a: Bytes::AddressRef, r: Field) -> Field {
      match role_index_of(rc, a) - (r + 1) {
        0 => {
          match role_of(rc, a) {
            0 => {  0 } ,
            _ => {  1 } ,
          } } ,
        _ => {  0 } ,
      }
    }
⟧

def role_addr := aiur_fn⟦
  fn role_addr(rc: RoleCtx, r: Field) -> Bytes::AddressRef {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, limit, _) => {
          assert_eq!(UInt32::less_than_fields(KernelRoleSpec::role_group(r), limit), 1,
            "a role is used before its group is admitted");
          let a = role_bound_addr(tbl, r);
          group_admit(tbl, KernelRoleSpec::role_group(r));
          a } ,
        RoleCtxNode::Assumed(tbl, _) => {  role_bound_addr(tbl, r) } ,
      }
    }
⟧

def role_used_implicitly := aiur_fn⟦
  fn role_used_implicitly(rc: RoleCtx, r: Field) -> Bytes::AddressRef {
      let a = role_addr(rc, r);
      KernelClaim::run_check_transitive(rc, a);
      a
    }
⟧

def group_admit := aiur_fn⟦
  fn group_admit(tbl: RoleTable, g: Field) -> () {
      group_admit_needs(tbl, KernelRoleSpec::group_needs(g));
      let rc = (&(RoleCtxNode::Mk(tbl, group_validation_limit(g), RBTreeMap::RBTreeMap::Nil)));
      validate_group_roles(rc, tbl, KernelRoleSpec::group_roles(g))
    }
⟧

def group_validation_limit := aiur_fn⟦
  fn group_validation_limit(g: Field) -> Field {
      let first_wf = KernelRoleSpec::first_well_founded_group();
      match UInt32::less_than_fields(g, first_wf) {
        1 => {  g } ,
        _ => {
          let first_equation = KernelRoleSpec::first_equation_group();
          match UInt32::less_than_fields(g, first_equation) {
            1 => {  first_wf } ,
            _ => {  first_equation } ,
          } } ,
      }
    }
⟧

def role_admission_checks := aiur_fn⟦
  fn role_admission_checks(r: Field) -> Field {
      match KernelRoleSpec::role_spec_kind(r) {
        0 => {
          match KernelRoleSpec::role_member_kind(r) {
            0 => {  1 } ,
            1 => {  1 } ,
            2 => {  1 } ,
            _ => {  0 } ,
          } } ,
        2 => {  1 } ,
        5 => {  1 } ,
        _ => {  0 } ,
      }
    }
⟧

def walk_ctx := aiur_fn⟦
  fn walk_ctx(rc: RoleCtx, a: Bytes::AddressRef) -> RoleCtx {
      match (*(rc)) {
        RoleCtxNode::Mk(tbl, limit, _) => {
          let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
          match r1 {
            0 => {  rc } ,
            _ => {
              let g = KernelRoleSpec::role_group(r1 - 1);
              match UInt32::less_than_fields(g, limit) * role_admission_checks(r1 - 1) {
                0 => {  rc } ,
                _ => {  (&(RoleCtxNode::Mk(tbl, group_validation_limit(g), RBTreeMap::RBTreeMap::Nil))) } ,
              } } ,
          } } ,
        RoleCtxNode::Assumed(_, _) => {  rc } ,
      }
    }
⟧

def walk_covered := aiur_fn⟦
  fn walk_covered(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      match (*(rc)) {
        RoleCtxNode::Mk(_, _, _) => {  0 } ,
        RoleCtxNode::Assumed(tbl, _) => {
          let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
          match r1 {
            0 => {  0 } ,
            _ => {  role_admission_checks(r1 - 1) } ,
          } } ,
      }
    }
⟧

def validate_binding := aiur_fn⟦
  fn validate_binding(binding: Bytes::AddressRef) -> () {
      let tbl = load_role_table(binding);
      assert_all_roles_bound(tbl, 0);
      admit_all_groups(tbl, 0)
    }
⟧

def assert_all_roles_bound := aiur_fn⟦
  fn assert_all_roles_bound(tbl: RoleTable, r: Field) -> () {
      match r - KernelRoleSpec::role_count() {
        0 => {  () } ,
        _ => {
          assert_eq!(role_is_bound(tbl, r), 1, "binding claim: a role is unbound");
          assert_all_roles_bound(tbl, r + 1) } ,
      }
    }
⟧

def admit_all_groups := aiur_fn⟦
  fn admit_all_groups(tbl: RoleTable, g: Field) -> () {
      match g - KernelRoleSpec::group_count() {
        0 => {  () } ,
        _ => {
          group_admit(tbl, g);
          admit_all_groups(tbl, g + 1) } ,
      }
    }
⟧

def group_admit_needs := aiur_fn⟦
  fn group_admit_needs(tbl: RoleTable, needs: Lists::List<Field>) -> () {
      match (*(needs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          group_admit(tbl, KernelRoleSpec::role_group(r));
          group_admit_needs(tbl, rest) } ,
      }
    }
⟧

def validate_group_roles := aiur_fn⟦
  fn validate_group_roles(rc: RoleCtx, tbl: RoleTable, rs: Lists::List<Field>) -> () {
      match (*(rs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(r, rest) => {
          validate_role(rc, tbl, r);
          validate_group_roles(rc, tbl, rest) } ,
      }
    }
⟧

def validate_role := aiur_fn⟦
  fn validate_role(rc: RoleCtx, tbl: RoleTable, r: Field) -> () {
      let a = role_bound_addr(tbl, r);
      let ci = (*(Ingress::get_ci(a)));
      assert_eq!(KernelInfer::const_num_lvls(ci), KernelRoleSpec::role_levels(r),
        "a bound role has the wrong number of universe parameters");
      match KernelRoleSpec::role_spec_kind(r) {
        0 => {  validate_member(rc, tbl, r, a, ci) } ,
        1 => {  validate_anchor(rc, tbl, r, ci) } ,
        2 => {  validate_op(rc, tbl, r, a, ci) } ,
        3 => {  validate_standard_axiom(rc, tbl, r, ci) } ,
        4 => {  validate_inert_axiom(rc, tbl, r, ci) } ,
        5 => {  validate_eqns(rc, tbl, r, a, ci) } ,
      }
    }
⟧

def assert_type_meets := aiur_fn⟦
  fn assert_type_meets(rc: RoleCtx, ty: KernelTypes::KExpr, spec: KernelTypes::KExpr) -> () {
      assert_eq!(KernelDefEq::k_is_def_eq(rc, ty, spec, (&(Lists::Node::Nil))), 1,
            "a bound role's type does not meet its specification");
          ()
    }
⟧

def assert_type_pinned := aiur_fn⟦
  fn assert_type_pinned(ty: KernelTypes::KExpr, spec: KernelTypes::KExpr) -> () {
      assert_eq!(KernelCheck::kexpr_struct_eq(ty, spec), 1,
            "a bound role's type does not meet its specification");
          ()
    }
⟧

def assert_safe_role := aiur_fn⟦
  fn assert_safe_role(ci: KernelTypes::KConstantInfo) -> () {
      assert_eq!(KernelCheck::is_unsafe_ci(ci), 0, "a bound role is unsafe");
      ()
    }
⟧

def validate_member := aiur_fn⟦
  fn validate_member(rc: RoleCtx, tbl: RoleTable, r: Field, a: Bytes::AddressRef,
        ci: KernelTypes::KConstantInfo) -> () {
      assert_safe_role(ci);
      assert_type_pinned(KernelInfer::const_type_of(ci), KernelRoleSpec::role_type(tbl, r));
      match KernelRoleSpec::role_member_kind(r) {
        0 => {
          match ci {
            KernelTypes::KConstantInfo::Induct(_, _, _, _, nctors, _, _, _) => {
              assert_eq!(nctors, KernelRoleSpec::role_ctor_count(r),
                "a bound inductive has the wrong number of constructors");
              KernelClaim::run_check_transitive(rc, a) } ,
          } } ,
        1 => {
          match ci {
            KernelTypes::KConstantInfo::Ctor(_, _, block, ind_idx, cidx, nparams, nfields, _) => {
              let (ind_role, want_cidx, want_params, want_fields) = KernelRoleSpec::role_ctor_of(r);
              match (*(Ingress::get_ci(role_bound_addr(tbl, ind_role)))) {
                KernelTypes::KConstantInfo::Induct(_, _, _, _, _, _, ind_block, ind_ind_idx) => {
                  assert_eq!(Bytes::address_eq(block, ind_block), 1,
                    "a bound constructor is not its inductive's");
                  assert_eq!(ind_idx, ind_ind_idx,
                    "a bound constructor is not its inductive's");
                  () } ,
              };
              assert_eq!(cidx, want_cidx, "a bound constructor has the wrong index");
              assert_eq!(nparams, want_params,
                "a bound constructor has the wrong number of parameters");
              assert_eq!(nfields, want_fields,
                "a bound constructor has the wrong number of fields");
              KernelClaim::run_check_transitive(rc, a) } ,
          } } ,
        2 => {
          match ci {
            KernelTypes::KConstantInfo::Rec(_, _, _, _, _, _, _, _, _, _, _) => {
              KernelClaim::run_check_transitive(rc, a) } ,
          } } ,
        3 => {
          match ci {
            KernelTypes::KConstantInfo::Axiom(_, ty, _) => {
              KernelCheck::validate_expr_well_scoped(ty, 0, KernelRoleSpec::role_levels(r));
              KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
              () } ,
          } } ,
        4 => {  assert_quot_kind(ci, 0) } ,
        5 => {  assert_quot_kind(ci, 1) } ,
        6 => {  assert_quot_kind(ci, 2) } ,
        7 => {  assert_quot_kind(ci, 3) } ,
      }
    }
⟧

def assert_quot_kind := aiur_fn⟦
  fn assert_quot_kind(ci: KernelTypes::KConstantInfo, want: Field) -> () {
      match ci {
        KernelTypes::KConstantInfo::Quot(_, _, kind) => {
          let k = match kind {
            Ixon::QuotKind::Typ => {  0 } ,
            Ixon::QuotKind::Ctor => {  1 } ,
            Ixon::QuotKind::Lift => {  2 } ,
            Ixon::QuotKind::Ind => {  3 } ,
          };
          assert_eq!(k, want, "a bound quotient constant has the wrong kind");
          () } ,
      }
    }
⟧

def validate_anchor := aiur_fn⟦
  fn validate_anchor(rc: RoleCtx, tbl: RoleTable, r: Field, ci: KernelTypes::KConstantInfo) -> () {
      assert_safe_role(ci);
      let ty = KernelInfer::const_type_of(ci);
      -- the anchor's type is closed and a type, before it is compared with the role's spec
      KernelCheck::validate_expr_well_scoped(ty, 0, KernelInfer::const_num_lvls(ci));
      KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
      let spec = KernelRoleSpec::role_type(tbl, r);
      match r {
        7 => {  assert_type_pinned(ty, spec) } ,
        20 => {  assert_type_pinned(ty, spec) } ,
        21 => {  assert_type_pinned(ty, spec) } ,
        22 => {  assert_type_pinned(ty, spec) } ,
        _ => {  assert_type_meets(rc, ty, spec) } ,
      }
    }
⟧

def validate_standard_axiom := aiur_fn⟦
  fn validate_standard_axiom(rc: RoleCtx, tbl: RoleTable, r: Field,
        ci: KernelTypes::KConstantInfo) -> () {
      match ci {
        KernelTypes::KConstantInfo::Axiom(nlvls, ty, u) => {
          assert_eq!(u, 0, "a bound standard axiom is unsafe");
          KernelCheck::validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_type_pinned(ty, KernelRoleSpec::role_type(tbl, r)) } ,
      }
    }
⟧

def validate_inert_axiom := aiur_fn⟦
  fn validate_inert_axiom(rc: RoleCtx, tbl: RoleTable, r: Field,
        ci: KernelTypes::KConstantInfo) -> () {
      match ci {
        KernelTypes::KConstantInfo::Axiom(nlvls, ty, u) => {
          assert_eq!(u, 0, "a bound inert axiom is unsafe");
          KernelCheck::validate_expr_well_scoped(ty, 0, nlvls);
          KernelInfer::k_ensure_sort(rc, ty, (&(Lists::Node::Nil)));
          assert_type_pinned(ty, KernelRoleSpec::role_type(tbl, r)) } ,
      }
    }
⟧

def role_evidence := aiur_fn⟦
  fn role_evidence(tbl: RoleTable, r: Field) -> Lists::List<RoleEvidence> {
      match (*(tbl)) {
        RoleTableNode::Mk(_, _, _, evidence) => {
          role_map_lookup_or_default(r, evidence, (&(Lists::Node::Nil))) } ,
      }
    }
⟧

def validate_op := aiur_fn⟦
  fn validate_op(rc: RoleCtx, tbl: RoleTable, r: Field, a: Bytes::AddressRef,
        ci: KernelTypes::KConstantInfo) -> () {
      match ci {
        KernelTypes::KConstantInfo::Defn(_, ty, _, safety, _) => {
          match safety {
            Ixon::DefinitionSafety::Safe => {  () } ,
            _ => {
              assert_eq!(0, 1, "a bound operation is not a safe definition");
              () } ,
          };
          assert_type_pinned(ty, KernelRoleSpec::role_type(tbl, r));
          KernelClaim::run_check_transitive(rc, a);
          let ev = role_evidence(tbl, r);
          assert_eq!(Lists::length(ev), KernelRoleSpec::op_equation_count(r),
            "an operation's evidence does not match its equations");
          validate_op_equations(rc, tbl, r, ev, 0) } ,
      }
    }
⟧

def validate_op_equations := aiur_fn⟦
  fn validate_op_equations(rc: RoleCtx, tbl: RoleTable, r: Field,
        ev: Lists::List<RoleEvidence>, k: Field) -> () {
      match (*(ev)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(e, rest) => {
          match KernelRoleSpec::op_evidence_is_proof(r) {
            0 => {
              match e {
                RoleEvidence::Defeq => {
                  assert_eq!(KernelDefEq::k_is_def_eq(rc, KernelRoleSpec::op_equation_lhs(tbl, r, k),
                      KernelRoleSpec::op_equation_rhs(tbl, r, k), (&(Lists::Node::Nil))), 1,
                    "an operation's equation does not hold by definition");
                  () } ,
                RoleEvidence::Proof(_) => {
                  assert_eq!(0, 1, "a structural operation's evidence must be definitional");
                  () } ,
              } } ,
            _ => {
              match e {
                RoleEvidence::Defeq => {
                  assert_eq!(0, 1, "a well-founded operation's evidence must be proofs");
                  () } ,
                RoleEvidence::Proof(thm) => {
                  match (*(Ingress::get_ci(thm))) {
                    KernelTypes::KConstantInfo::Thm(nlvls, tty, _) => {
                      assert_eq!(nlvls, 0, "certificate theorem has universe parameters");
                      KernelClaim::run_check_transitive(rc, thm);
                      assert_type_meets(rc, tty, KernelRoleSpec::op_certificate(tbl, r, k)) } ,
                  } } ,
              } } ,
          };
          validate_op_equations(rc, tbl, r, rest, k + 1) } ,
      }
    }
⟧

def validate_eqns := aiur_fn⟦
  fn validate_eqns(rc: RoleCtx, tbl: RoleTable, r: Field, a: Bytes::AddressRef,
        ci: KernelTypes::KConstantInfo) -> () {
      match ci {
        KernelTypes::KConstantInfo::Defn(nlvls, ty, _, safety, _) => {
          match safety {
            Ixon::DefinitionSafety::Safe => {  () } ,
            _ => {
              assert_eq!(0, 1, "a bound definition is not safe");
              () } ,
          };
          assert_eq!(nlvls, KernelRoleSpec::role_levels(r),
            "a bound definition has another number of universe parameters");
          assert_type_meets(rc, ty, KernelRoleSpec::role_type(tbl, r));
          KernelClaim::run_check_transitive(rc, a);
          let ev = role_evidence(tbl, r);
          assert_eq!(Lists::length(ev), KernelRoleSpec::eqns_equation_count(r),
            "a definition's evidence does not match its equations");
          validate_eqns_equations(rc, tbl, r, ev, 0) } ,
      }
    }
⟧

def validate_eqns_equations := aiur_fn⟦
  fn validate_eqns_equations(rc: RoleCtx, tbl: RoleTable, r: Field,
        ev: Lists::List<RoleEvidence>, k: Field) -> () {
      match (*(ev)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(e, rest) => {
          match e {
            RoleEvidence::Defeq => {
              assert_eq!(KernelRoleSpec::eqns_conditional(r, k), 0,
                "a conditional equation's evidence must be a proof");
              assert_eq!(KernelDefEq::k_is_def_eq(rc, KernelRoleSpec::eqns_lhs(tbl, r, k), KernelRoleSpec::eqns_rhs(tbl, r, k),
                  (&(Lists::Node::Nil))), 1,
                "a definition's equation does not hold by definition");
              () } ,
            RoleEvidence::Proof(thm) => {
              match (*(Ingress::get_ci(thm))) {
                KernelTypes::KConstantInfo::Thm(nlvls, tty, _) => {
                  assert_eq!(nlvls, KernelRoleSpec::role_levels(r),
                    "an equation's proof has another number of universe parameters");
                  KernelClaim::run_check_transitive(rc, thm);
                  assert_type_meets(rc, tty, KernelRoleSpec::eqns_statement(tbl, r, k)) } ,
              } } ,
          };
          validate_eqns_equations(rc, tbl, r, rest, k + 1) } ,
      }
    }
⟧

def axiom_standing := aiur_fn⟦
  fn axiom_standing(rc: RoleCtx, a: Bytes::AddressRef) -> Field {
      let tbl = role_ctx_table(rc);
      let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
      match r1 {
        0 => {  RBTreeMap::rbtree_map_lookup_or_default(a, role_ctx_axioms(rc), 0) } ,
        _ => {
          let standing = axiom_role_standing(r1);
          match standing {
            0 => {  0 } ,
            _ => {
              match role_of(rc, a) {
                0 => {  0 } ,
                _ => {  standing } ,
              } } ,
          } } ,
      }
    }
⟧

def axiom_role_standing := aiur_fn⟦
  fn axiom_role_standing(r1: Field) -> Field {
      -- 1: a standard axiom (`propext`, `Classical.choice`, `Quot.sound`); 2: an inert one
      -- (specification kind 4: `sorryAx` and Lean's compiler-trust axioms), which may be
      -- declared but which no constant may use (`assert_ref_allowed`); 0: any other role.
      match r1 {
        0 => {  0 } ,
        _ => {
          let r = r1 - 1;
          match r - KernelRoleSpec::role_propext() {
            0 => {  1 } ,
            _ => {
              match r - KernelRoleSpec::role_choice() {
                0 => {  1 } ,
                _ => {
                  match r - KernelRoleSpec::role_quot_sound() {
                    0 => {  1 } ,
                    _ => {
                      match KernelRoleSpec::role_spec_kind(r) - 4 {
                        0 => {  2 } ,
                        _ => {  0 } ,
                      } } ,
                  } } ,
              } } ,
          } } ,
      }
    }
⟧

def assert_ref_allowed := aiur_fn⟦
  fn assert_ref_allowed(rc: RoleCtx, a: Bytes::AddressRef) -> () {
      match axiom_standing(rc, a) {
        2 => {
          assert_eq!(0, 1, "a constant uses an inert axiom");
          () } ,
        _ => {  () } ,
      }
    }
⟧


  -- Port divergence: role-indexed maps (keys are role indices) are separate from
  -- the address-keyed `RBTreeMap::RBTreeMap`.

def role_map_lookup_or_default := aiur_fn⟦
  fn role_map_lookup_or_default<V>(key: Field, tree: RoleMap<V>, default: V) -> V {
      match tree {
        RoleMap::Nil => {  default } ,
        RoleMap::Node(_, k, v, left, right) => {
          let eq = key - k;
          match eq {
            0 => {  v } ,
            _ => {
              match UInt32::less_than_fields(key, k) {
                1 => {  role_map_lookup_or_default(key, (*(left)), default) } ,
                _ => {  role_map_lookup_or_default(key, (*(right)), default) } ,
              } } ,
          } } ,
      }
    }
⟧


  -- Port divergence: role contexts are compared by their limits, not by pointer.

def role_ctx_limit := aiur_fn⟦
  fn role_ctx_limit(rc: RoleCtx) -> Field {
      match (*(rc)) {
        RoleCtxNode::Assumed(_, _) => {  0 } ,
        RoleCtxNode::Mk(_, limit, _) => {  limit } ,
      }
    }
⟧

end

end IxVM
