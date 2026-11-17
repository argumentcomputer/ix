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
      evidence_roles_have_equations(evidence);
      let Lists::Node::Nil = (*(s));
      (&(RoleTableNode::Mk(binding, by_role, by_addr, evidence)))
    }
⟧

  -- An evidence entry is for a role with equations: an operation or a definition role
  -- whose specification lists at least one (the kernel's `RoleTable.check`: `evidence for
  -- a role which has no equations`). A role without them has no entry, not an empty one.

def evidence_roles_have_equations := aiur_fn⟦
  fn evidence_roles_have_equations(ev: RoleMap<Lists::List<RoleEvidence>>) -> () {
      match ev {
        RoleMap::Nil => {  () } ,
        RoleMap::Node(_, r, _, left, right) => {
          assert_eq!(Fields::is_zero(KernelRoleSpec::op_equation_count(r) + KernelRoleSpec::eqns_equation_count(r)), 0,
            "role table: evidence for a role with no equations");
          evidence_roles_have_equations((*(left)));
          evidence_roles_have_equations((*(right))) } ,
      }
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
            KernelTypes::KConstantInfo::Axiom(nl, ty, u) => {
              assert_eq!(u, 0, "claim: user axiom is unsafe");
              assert_not_axiom_spec(tbl, nl, ty);
              validate_user_axioms(tbl, rest, RBTreeMap::rbtree_map_insert(a, 1, acc)) } ,
            _ => {
              assert_eq!(0, 1, "claim: axioms tree entry is not an axiom");
              acc } ,
          } } ,
      }
    }
⟧

  -- A user axiom may not restate the specification of an axiom role (`propext`,
  -- `Classical.choice`, `sorryAx`, and `Quot.sound` where the table binds it): the same level
  -- count and the same type once every binder datum is erased (the kernel's `axiomRoleSpecHit?`,
  -- `ConstantVal.matchesPin`). Such an axiom is the role's own under another address.

def assert_not_axiom_spec := aiur_fn⟦
  fn assert_not_axiom_spec(tbl: RoleTable, nl: Field, ty: KernelTypes::KExpr) -> () {
      assert_eq!(restates_role(tbl, nl, ty, KernelRoleSpec::role_propext()), 0,
        "claim: a user axiom restates an axiom role's specification");
      assert_eq!(restates_role(tbl, nl, ty, KernelRoleSpec::role_choice()), 0,
        "claim: a user axiom restates an axiom role's specification");
      assert_eq!(restates_role(tbl, nl, ty, KernelRoleSpec::role_sorry_ax()), 0,
        "claim: a user axiom restates an axiom role's specification");
      match role_is_bound(tbl, KernelRoleSpec::role_quot_sound()) {
        1 => {
          assert_eq!(restates_role(tbl, nl, ty, KernelRoleSpec::role_quot_sound()), 0,
            "claim: a user axiom restates an axiom role's specification");
          () } ,
        _ => {  () } ,
      }
    }
⟧

def restates_role := aiur_fn⟦
  fn restates_role(tbl: RoleTable, nl: Field, ty: KernelTypes::KExpr, r: Field) -> Field {
      match nl - KernelRoleSpec::role_levels(r) {
        0 => {
          KernelCheck::kexpr_struct_eq(erase_data(ty), erase_data(KernelRoleSpec::role_type(tbl, r))) } ,
        _ => {  0 } ,
      }
    }
⟧

  -- Every binder datum set to never zero (the kernel's `Expr.erasePw`).

def erase_data := aiur_fn⟦
  fn erase_data(e: KernelTypes::KExpr) -> KernelTypes::KExpr {
      match (*(e)) {
        KernelTypes::KExprNode::App(f, a) => {
          (&(KernelTypes::KExprNode::App(erase_data(f), erase_data(a)))) } ,
        KernelTypes::KExprNode::Lam(t, b, _) => {
          (&(KernelTypes::KExprNode::Lam(erase_data(t), erase_data(b),
            (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))))))) } ,
        KernelTypes::KExprNode::Forall(t, b, _) => {
          (&(KernelTypes::KExprNode::Forall(erase_data(t), erase_data(b),
            (&(KernelTypes::KLevelNode::Succ((&(KernelTypes::KLevelNode::Zero)))))))) } ,
        KernelTypes::KExprNode::Let(t, v, b) => {
          (&(KernelTypes::KExprNode::Let(erase_data(t), erase_data(v), erase_data(b)))) } ,
        KernelTypes::KExprNode::Proj(s, i, x) => {
          (&(KernelTypes::KExprNode::Proj(s, i, erase_data(x)))) } ,
        _ => {  e } ,
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
          let first_literal = KernelRoleSpec::first_literal_group();
          match UInt32::less_than_fields(g, first_literal) {
            1 => {  first_wf } ,
            _ => {
              let first_equation = KernelRoleSpec::first_equation_group();
              match UInt32::less_than_fields(g, first_equation) {
                1 => {  first_literal } ,
                _ => {  first_equation } ,
              } } ,
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
              assert_op_reached_in_order(r1 - 1, g, limit);
              match UInt32::less_than_fields(g, limit) * role_admission_checks(r1 - 1) {
                0 => {  rc } ,
                _ => {  (&(RoleCtxNode::Mk(tbl, group_validation_limit(g), RBTreeMap::RBTreeMap::Nil))) } ,
              } } ,
          } } ,
        RoleCtxNode::Assumed(_, _) => {  rc } ,
      }
    }
⟧

  -- A validation below the well-founded block never reaches an operation whose group is not
  -- below its limit: every group there needs only earlier operations, so such a reference is
  -- out of order (an operation's own record reached through a reference included). Inside
  -- the block every group is validated at one limit, so the context does not say which group
  -- is validated; there `op_order_scan` makes the check against the group's needs.

def assert_op_reached_in_order := aiur_fn⟦
  fn assert_op_reached_in_order(r: Field, g: Field, limit: Field) -> () {
      match KernelRoleSpec::role_spec_kind(r) {
        2 => {
          match UInt32::less_than_fields(limit, KernelRoleSpec::first_well_founded_group()) {
            1 => {
              assert_eq!(UInt32::less_than_fields(g, limit), 1,
                "an operation is reached before its group is validated");
              () } ,
            _ => {  () } ,
          } } ,
        _ => {  () } ,
      }
    }
⟧

  -- Inside the well-founded block: what `a` references, up to the records whose roles are in
  -- force (each checked in its own group's validation, under the same rule), reaches an
  -- operation only if that operation's group is below `limit` or among `needs`, the needs of
  -- the group being validated. A referenced operation is not entered: its own validation
  -- scanned its closure.

def op_order_scan := aiur_fn⟦
  fn op_order_scan(tbl: RoleTable, limit: Field, needs: Lists::List<Field>, a: Bytes::AddressRef) -> () {
      let r1 = RBTreeMap::rbtree_map_lookup_or_default(a, role_addr_index(tbl), 0);
      match r1 {
        0 => {  op_order_scan_refs(tbl, limit, needs, a) } ,
        _ => {
          let r = r1 - 1;
          let in_force = UInt32::less_than_fields(KernelRoleSpec::role_group(r), limit);
          match KernelRoleSpec::role_spec_kind(r) {
            2 => {
              let ok = match in_force {
                1 => {  1 } ,
                _ => {  KernelClaim::g_list_has(needs, r) } ,
              };
              assert_eq!(ok, 1, "an operation reaches an operation its group does not need");
              () } ,
            _ => {
              match in_force {
                1 => {  () } ,
                _ => {  op_order_scan_refs(tbl, limit, needs, a) } ,
              } } ,
          } } ,
      }
    }
⟧

  -- The references of `a`'s record, as the walk follows them: a projection's block, and every
  -- reference the record uses (`KernelClaim::const_idxs_of`).

def op_order_scan_refs := aiur_fn⟦
  fn op_order_scan_refs(tbl: RoleTable, limit: Field, needs: Lists::List<Field>, a: Bytes::AddressRef) -> () {
      let c = Ingress::load_verified_constant(a);
      match c {
        Ixon::Constant::Mk(info, _, refs, _, _) => {
          match info {
            Ixon::ConstantInfo::IPrj(p) => {
              match p { Ixon::InductiveProj::Mk(_, b) => {  op_order_scan(tbl, limit, needs, b) } , } } ,
            Ixon::ConstantInfo::CPrj(p) => {
              match p { Ixon::ConstructorProj::Mk(_, _, b) => {  op_order_scan(tbl, limit, needs, b) } , } } ,
            Ixon::ConstantInfo::RPrj(p) => {
              match p { Ixon::RecursorProj::Mk(_, b) => {  op_order_scan(tbl, limit, needs, b) } , } } ,
            Ixon::ConstantInfo::DPrj(p) => {
              match p { Ixon::DefinitionProj::Mk(_, b) => {  op_order_scan(tbl, limit, needs, b) } , } } ,
            _ => {  () } ,
          };
          op_order_scan_list(tbl, limit, needs, refs, KernelClaim::const_idxs_of(c), 0) } ,
      }
    }
⟧

def op_group_needs := aiur_fn⟦
  fn op_group_needs(r: Field) -> Lists::List<Field> {
      KernelRoleSpec::group_needs(KernelRoleSpec::role_group(r))
    }
⟧

def op_order_scan_list := aiur_fn⟦
  fn op_order_scan_list(tbl: RoleTable, limit: Field, needs: Lists::List<Field>,
                        refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(b, rest) => {
          match KernelClaim::g_list_has(used, i) {
            1 => {  op_order_scan(tbl, limit, needs, b) } ,
            _ => {  () } ,
          };
          op_order_scan_list(tbl, limit, needs, rest, used, i + 1) } ,
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
        4 => {  assert_type_pinned(ty, spec) } ,
        5 => {  assert_type_pinned(ty, spec) } ,
        6 => {  assert_type_pinned(ty, spec) } ,
        7 => {  assert_type_pinned(ty, spec) } ,
        20 => {  assert_type_pinned(ty, spec) } ,
        21 => {  assert_type_pinned(ty, spec) } ,
        22 => {  assert_type_pinned(ty, spec) } ,
        29 => {  assert_type_pinned(ty, spec) } ,
        30 => {  assert_type_pinned(ty, spec) } ,
        31 => {  assert_type_pinned(ty, spec) } ,
        37 => {  assert_type_pinned(ty, spec) } ,
        38 => {  assert_type_pinned(ty, spec) } ,
        39 => {  assert_type_pinned(ty, spec) } ,
        40 => {  assert_type_pinned(ty, spec) } ,
        _ => {  assert_type_meets(rc, ty, spec) } ,
      };
      -- the record itself, with its closure, in this group's validation context: the anchor's
      -- own role is not in force here, every role the record may use is
      match anchor_walked(r) {
        1 => {  KernelClaim::run_check_transitive(rc, role_bound_addr(tbl, r)) } ,
        _ => {  () } ,
      }
    }
⟧

  -- The anchors whose records role validation checks with their closures, each in its own
  -- group: `Bool`, `Bool.false`, `Bool.true`, `Bool.rec` (4-7), `And`, `And.intro`, `And.rec`
  -- (20-22), and the literal support `List`, `List.nil`, `List.cons` (29-31), `String`,
  -- `String.ofList`, `Char`, `Char.ofNat` (37-40).

def anchor_walked := aiur_fn⟦
  fn anchor_walked(r: Field) -> Field {
      match r {
        4 => {  1 } ,
        5 => {  1 } ,
        6 => {  1 } ,
        7 => {  1 } ,
        20 => {  1 } ,
        21 => {  1 } ,
        22 => {  1 } ,
        29 => {  1 } ,
        30 => {  1 } ,
        31 => {  1 } ,
        37 => {  1 } ,
        38 => {  1 } ,
        39 => {  1 } ,
        40 => {  1 } ,
        _ => {  0 } ,
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
          assert_type_pinned(ty, KernelRoleSpec::role_type(tbl, r));
          -- what the bound record references is checked here, in this group's context; not
          -- the axiom itself, which is not in force in its own group (the axiom arm refuses it)
          let c = Ingress::load_verified_constant(role_bound_addr(tbl, r));
          match c {
            Ixon::Constant::Mk(_, _, refs, _, _) => {
              KernelClaim::walk_refs_transitive(rc, refs, KernelClaim::const_idxs_of(c), 0) } ,
          } } ,
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
        KernelTypes::KConstantInfo::Defn(_, ty, val, safety, _) => {
          match safety {
            Ixon::DefinitionSafety::Safe => {  () } ,
            _ => {
              assert_eq!(0, 1, "a bound operation is not a safe definition");
              () } ,
          };
          assert_type_pinned(ty, KernelRoleSpec::role_type(tbl, r));
          KernelClaim::run_check_transitive(rc, a);
          -- inside the well-founded block, the operations the record reaches are in order
          match KernelRoleSpec::op_evidence_is_proof(r) {
            1 => {  op_order_scan_refs(tbl, role_ctx_limit(rc), op_group_needs(r), a) } ,
            _ => {  () } ,
          };
          let ev = role_evidence(tbl, r);
          assert_eq!(Lists::length(ev), KernelRoleSpec::op_equation_count(r),
            "an operation's evidence does not match its equations");
          validate_op_equations(rc, tbl, r, a, val, ev, 0) } ,
      }
    }
⟧

  -- An operation's equations hold for its value: each side opened under two `Nat` variables
  -- (`x` is `BVar(1)`, `y` is `BVar(0)`), with every occurrence of the operation replaced by its
  -- record's value `val` (closed), so that nothing here needs the operation stored.

def validate_op_equations := aiur_fn⟦
  fn validate_op_equations(rc: RoleCtx, tbl: RoleTable, r: Field, a: Bytes::AddressRef,
        val: KernelTypes::KExpr, ev: Lists::List<RoleEvidence>, k: Field) -> () {
      match (*(ev)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(e, rest) => {
          match KernelRoleSpec::op_evidence_is_proof(r) {
            0 => {
              match e {
                RoleEvidence::Defeq => {
                  let (lhs, types) = open_two_lams(KernelRoleSpec::op_equation_lhs(tbl, r, k));
                  let (rhs, _) = open_two_lams(KernelRoleSpec::op_equation_rhs(tbl, r, k));
                  assert_eq!(KernelDefEq::k_is_def_eq(rc, KernelSubst::subst_const(lhs, a, val),
                      KernelSubst::subst_const(rhs, a, val), types), 1,
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
                    KernelTypes::KConstantInfo::Thm(nlvls, _, pval) => {
                      assert_eq!(nlvls, 0, "certificate theorem has universe parameters");
                      -- the proof with the operation replaced by its value, closed and level-free;
                      -- the theorem record itself is not walked and its type is not used
                      let p = KernelSubst::subst_const(pval, a, val);
                      KernelCheck::validate_expr_well_scoped(p, 0, 0);
                      -- what the proof names, the theorem's references but the operation, checked
                      -- with their closures; none of them reaches the operation (the order rule)
                      let tc = Ingress::load_verified_constant(thm);
                      match tc {
                        Ixon::Constant::Mk(_, _, refs, _, _) => {
                          let used = KernelClaim::const_idxs_of(tc);
                          walk_refs_except(rc, refs, used, 0, a);
                          op_order_scan_except(tbl, role_ctx_limit(rc), op_group_needs(r), refs, used, 0, a) } ,
                      };
                      -- the certificate opened: its hypotheses are the context, innermost first,
                      -- its equation the expected type at depth 2 + n, and the proof is applied to
                      -- x, y and the hypotheses' variables
                      let (eqn, types) = open_foralls(
                        KernelSubst::subst_const(KernelRoleSpec::op_certificate(tbl, r, k), a, val),
                        (&(Lists::Node::Nil)));
                      let d = Lists::length(types);
                      KernelInfer::k_check(rc, KernelWhnf::apply_spine(p, KernelModeled::bvars_desc(d, d)),
                        eqn, types) } ,
                  } } ,
              } } ,
          };
          validate_op_equations(rc, tbl, r, a, val, rest, k + 1) } ,
      }
    }
⟧

  -- A rendered certificate `∀ x y h₁ … hₙ, E`: `E`, open at depth `2 + n`, and the binders'
  -- types, innermost first.

def open_foralls := aiur_fn⟦
  fn open_foralls(e: KernelTypes::KExpr, acc: Lists::List<KernelTypes::KExpr>)
        -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match (*(e)) {
        KernelTypes::KExprNode::Forall(t, body, _) => {
          open_foralls(body, (&(Lists::Node::Cons(t, acc)))) } ,
        _ => {  (e, acc) } ,
      }
    }
⟧

  -- The references `refs` (used at the indices `used`) walked as `KernelClaim::walk_refs_transitive`
  -- walks them, except `a`.

def walk_refs_except := aiur_fn⟦
  fn walk_refs_except(rc: RoleCtx, refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>,
                      i: Field, a: Bytes::AddressRef) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(b, rest) => {
          match KernelClaim::g_list_has(used, i) * (1 - Bytes::address_eq(b, a)) {
            1 => {
              assert_ref_allowed(rc, b);
              match walk_covered(rc, b) {
                0 => {  KernelClaim::run_check_transitive(walk_ctx(rc, b), b) } ,
                _ => {  () } ,
              } } ,
            _ => {  () } ,
          };
          walk_refs_except(rc, rest, used, i + 1, a) } ,
      }
    }
⟧

  -- `op_order_scan` on the references `refs` (used at the indices `used`), except `a`.

def op_order_scan_except := aiur_fn⟦
  fn op_order_scan_except(tbl: RoleTable, limit: Field, needs: Lists::List<Field>,
                          refs: Lists::List<Bytes::AddressRef>, used: Lists::List<Field>, i: Field,
                          a: Bytes::AddressRef) -> () {
      match (*(refs)) {
        Lists::Node::Nil => {  () } ,
        Lists::Node::Cons(b, rest) => {
          match KernelClaim::g_list_has(used, i) * (1 - Bytes::address_eq(b, a)) {
            1 => {  op_order_scan(tbl, limit, needs, b) } ,
            _ => {  () } ,
          };
          op_order_scan_except(tbl, limit, needs, rest, used, i + 1, a) } ,
      }
    }
⟧

  -- A rendered equation side `fun (x : Nat) (y : Nat) => body`: the body, open at depth 2, and
  -- the two binders' types, innermost first.

def open_two_lams := aiur_fn⟦
  fn open_two_lams(e: KernelTypes::KExpr) -> (KernelTypes::KExpr, Lists::List<KernelTypes::KExpr>) {
      match (*(e)) {
        KernelTypes::KExprNode::Lam(t1, inner, _) => {
          match (*(inner)) {
            KernelTypes::KExprNode::Lam(t2, body, _) => {
              (body, (&(Lists::Node::Cons(t2, (&(Lists::Node::Cons(t1, (&(Lists::Node::Nil))))))))) } ,
          } } ,
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
