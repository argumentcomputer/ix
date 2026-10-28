module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Ingress

public section

namespace IxVM

/-! ## Roles — the claim's binding, read and validated in the circuit

A typing claim names a role binding (`Ix.ClaimContext.binding`): the BLAKE3
hash of a role table's `E8 03` section, which binds IxC's roles
(`Ix.Kernel.Role`) to constants and carries the evidence of the `Nat`
operations. IxVM recognizes its primitives only through that table: a
constant plays a role because the table binds it, never because of its
address.

The table is prover data, so no role is used before it is validated
against IxC's specification of it (`Ix/IxVM/Kernel/RoleSpec.lean`, rendered
from `Ix.Kernel.Role.spec`). Roles are validated by group, as the
specifications group them (`Role.block`), in the order of the rendered
`group_roles`, and a group is admitted whole or not at all:

- a basis block member must be a safe constant of the kind IxVM expects
  (inductive, constructor, recursor, quotient or axiom) with the specified
  level count and type, and its constructors must be the block's own; the
  member is then checked like any constant, so its recursor's rules are the
  canonical ones for the specified inductive;
- an anchor (the literal support, `Bool` and the standard axioms' families)
  must be safe, with the specified level count and type: its type alone, as
  IxC and the Rust kernel validate it;
- a standard axiom (`propext`, `Classical.choice`) must be a safe axiom of
  the specified type; `sorryAx` must be an axiom with one universe
  parameter, and no use of it is accepted;
- an operation must be a safe level-0 definition of the specified type that
  checks, and its equations must hold: each structural equation by
  definitional equality, each well-founded one by a theorem of the
  certificate's statement, which is checked with its dependencies.

A group is validated under a role context (`RoleCtx`) that admits only the
groups before it, so an operation's own fast path cannot take part in
validating it. The well-founded operations' groups come last and share one
context, the one before the first of them (`group_validation_limit`): no
well-founded operation's fast path takes part in validating any of them,
and the dependencies they share (the well-founded recursion and the `Nat`
lemmas their certificates use) are checked once. Validation is lazy and
memoized: it runs the first time a claim uses a role of the group, once per
claim. A binding that does not meet the specifications makes every claim
that uses the failing role abort; it never makes a role usable.

A walk over a claim's dependencies that reaches a bound role whose
admission checks it with its dependencies (a basis inductive, constructor
or recursor, or an operation) checks it under the context its group is
validated in (`walk_ctx`), not the claim's. When the claim also uses the
role, the check is the admission's own, done once; when it does not, the
walk admits nothing and checks the constant as its group would. Checking
under fewer usable roles is never weaker. Under the standard axiom policy it
declines a little more: a constant bound to such a role whose dependencies
use a standard axiom whose group comes after its own is declined even when
the claim never uses the role, as its group's validation would decline it.

A claim covers a constant's dependencies, not a whole environment, so the
constants the kernel introduces into a claim's terms without the claim
referencing them (a string literal's type and the constants of its
constructor form) are dependencies the claim checks like referenced ones
(`role_used_implicitly`). That check runs under the claim's context, not
while a group is validated.

The role context is threaded through the kernel: every function that may
reach a primitive takes it. -/

def roles := ⟦
  enum RoleEvidence {
    Defeq,
    Proof(Addr)
  }

  -- A role table: its binding hash, the bound address by role, 1 + the role
  -- by bound address (keyed by the address's interned pointer, which
  -- content addressing makes unique), and the evidence entries by role.
  enum RoleTableNode {
    Mk(Addr, RBTreeMap‹Addr›, RBTreeMap‹G›, RBTreeMap‹List‹RoleEvidence››)
  }

  type RoleTable = &RoleTableNode

  -- A role context: a table, and the number of groups usable under it; or
  -- a table assumed to meet the specifications (a claim that assumes its
  -- binding), under which every bound role is usable and none is admitted.
  enum RoleCtxNode {
    Mk(RoleTable, G),
    Assumed(RoleTable)
  }

  type RoleCtx = &RoleCtxNode

  -- ==========================================================================
  -- Reading the table (channel 6, keyed by the binding hash).
  --
  -- `E8 03 v n (r a)ⁿ m (r k e₁…e_k)ᵐ`, one byte per integer; `e` is `00`
  -- (definitional) or `01` and an address (proof). Role indices strictly
  -- increase in both lists, as the canonical codec requires.
  -- ==========================================================================
  fn load_role_table(binding: Addr) -> RoleTable {
    let raw = load(binding);
    let (idx, len) = io_get_info(6, raw);
    let bytes = read_finite_byte_stream(6, idx, len);
    verify_bytes_against(bytes, raw);
    let (t0, s) = read_byte(bytes);
    assert_eq!(t0, 0xE8u8, "role table: not a binding section");
    let (t1, s) = read_byte(s);
    assert_eq!(t1, 0x03u8, "role table: not a binding section");
    let (version, s) = read_byte(s);
    assert_eq!(to_field(version), spec_version(),
      "role table: made for another specification version");
    let (n, s) = read_byte(s);
    let (by_role, by_addr, _next, s) =
      read_role_bindings(s, to_field(n), 0, RBTreeMap.Nil);
    let (m, s) = read_byte(s);
    let (evidence, _next, s) = read_role_evidence(s, to_field(m), 0);
    assert_eq!(load(s), ListNode.Nil, "role table: trailing bytes");
    store(RoleTableNode.Mk(binding, by_role, by_addr, evidence))
  }

  -- The two maps keyed by role are read straight into balanced trees: the
  -- entries arrive in strictly increasing role order, so the first half of
  -- a run is the left subtree, the next entry the root and the rest the
  -- right subtree, and no insertion or rebalancing is needed. Lookups ignore
  -- colours, and nothing inserts into a table once it is read. The index by
  -- address is keyed by interned pointers, in no particular order, so it is
  -- built by insertion.

  -- `count` bindings, in order, each role index at least `next`: the tree
  -- by role, the index by address extended, and the least role index the
  -- next binding may have.
  fn read_role_bindings(s: ByteStream, count: G, next: G, by_addr: RBTreeMap‹G›)
      -> (RBTreeMap‹Addr›, RBTreeMap‹G›, G, ByteStream) {
    match count {
      0 => (RBTreeMap.Nil, by_addr, next, s),
      _ =>
        let half = to_field(u8_shift_right(u8_from_field_unsafe(count)));
        let (left, by_addr, next, s) = read_role_bindings(s, half, next, by_addr);
        let (rb, s) = read_byte(s);
        let r = to_field(rb);
        assert_eq!(u32_less_than(r, role_count()), 1, "role table: unknown role");
        assert_eq!(u32_less_than(r, next), 0, "role table: roles out of order");
        let (a, s) = get_address(s);
        assert_eq!(rbtree_map_lookup_or_default(ptr_val(a), by_addr, 0), 0,
          "role table: an address is bound to two roles");
        let by_addr = rbtree_map_insert(ptr_val(a), r + 1, by_addr);
        let (right, by_addr, next, s) =
          read_role_bindings(s, count - (half + 1), r + 1, by_addr);
        (RBTreeMap.Node(1, r, a, store(left), store(right)), by_addr, next, s),
    }
  }

  -- `count` evidence entries, in order, each role index at least `next`:
  -- the tree by role and the least role index the next entry may have.
  fn read_role_evidence(s: ByteStream, count: G, next: G)
      -> (RBTreeMap‹List‹RoleEvidence››, G, ByteStream) {
    match count {
      0 => (RBTreeMap.Nil, next, s),
      _ =>
        let half = to_field(u8_shift_right(u8_from_field_unsafe(count)));
        let (left, next, s) = read_role_evidence(s, half, next);
        let (rb, s) = read_byte(s);
        let r = to_field(rb);
        assert_eq!(u32_less_than(r, role_count()), 1, "role table: unknown role");
        assert_eq!(u32_less_than(r, next), 0, "role table: evidence out of order");
        let (kb, s) = read_byte(s);
        let (entries, s) = read_evidence_entries(s, to_field(kb));
        let (right, next, s) = read_role_evidence(s, count - (half + 1), r + 1);
        (RBTreeMap.Node(1, r, entries, store(left), store(right)), next, s),
    }
  }

  fn read_evidence_entries(s: ByteStream, count: G) -> (List‹RoleEvidence›, ByteStream) {
    match count {
      0 => (store(ListNode.Nil), s),
      _ =>
        let (tag, s) = read_byte(s);
        match tag {
          0 =>
            let (rest, s) = read_evidence_entries(s, count - 1);
            (store(ListNode.Cons(RoleEvidence.Defeq, rest)), s),
          1 =>
            let (a, s) = get_address(s);
            let (rest, s) = read_evidence_entries(s, count - 1);
            (store(ListNode.Cons(RoleEvidence.Proof(a), rest)), s),
        },
    }
  }

  -- ==========================================================================
  -- Role contexts and admission.
  -- ==========================================================================

  -- The context a claim is checked under: its binding's table, every group
  -- usable.
  fn role_ctx_of_binding(binding: Addr) -> RoleCtx {
    store(RoleCtxNode.Mk(load_role_table(binding), group_count()))
  }

  -- The context of a claim that assumes its binding meets the
  -- specifications: its binding's table, read but not validated.
  fn role_ctx_assumed(binding: Addr) -> RoleCtx {
    store(RoleCtxNode.Assumed(load_role_table(binding)))
  }

  -- The context of a claim, by its validator: 3 validates the binding, 4
  -- assumes it.
  fn role_ctx_for_validator(binding: Addr, validator: G) -> RoleCtx {
    match validator {
      3 => role_ctx_of_binding(binding),
      4 => role_ctx_assumed(binding),
      _ =>
        assert_eq!(0, 1, "claim: wrong validator identity");
        role_ctx_of_binding(binding),
    }
  }

  -- The validator a claim checked under `rc` names: 3, or 4 when it
  -- assumes its binding.
  fn role_ctx_validator(rc: RoleCtx) -> G {
    3 + role_ctx_is_assumed(rc)
  }

  fn role_ctx_table(rc: RoleCtx) -> RoleTable {
    match load(rc) {
      RoleCtxNode.Mk(tbl, _) => tbl,
      RoleCtxNode.Assumed(tbl) => tbl,
    }
  }

  -- 1 iff `rc` assumes its binding.
  fn role_ctx_is_assumed(rc: RoleCtx) -> G {
    match load(rc) {
      RoleCtxNode.Mk(_, _) => 0,
      RoleCtxNode.Assumed(_) => 1,
    }
  }

  -- The binding hash `rc` reads roles through.
  fn role_ctx_binding(rc: RoleCtx) -> Addr {
    match load(role_ctx_table(rc)) {
      RoleTableNode.Mk(binding, _, _, _) => binding,
    }
  }

  -- The address the table binds to `r`, or the zero address when it binds
  -- none.
  fn role_bound_addr_or_zero(tbl: RoleTable, r: G) -> Addr {
    match load(tbl) {
      RoleTableNode.Mk(_, by_role, _, _) =>
        rbtree_map_lookup_or_default(r, by_role, store([0u8; 32])),
    }
  }

  -- 1 iff the table binds role `r`: its address maps back to `r`.
  fn role_is_bound(tbl: RoleTable, r: G) -> G {
    let a = role_bound_addr_or_zero(tbl, r);
    match rbtree_map_lookup_or_default(ptr_val(a), role_addr_index(tbl), 0) - (r + 1) {
      0 => 1,
      _ => 0,
    }
  }

  -- The address the table binds to `r`; the table must bind it. Used to
  -- read specifications, which name other roles by their bound addresses.
  fn role_bound_addr(tbl: RoleTable, r: G) -> Addr {
    assert_eq!(role_is_bound(tbl, r), 1,
      "role table does not bind a role the claim needs");
    role_bound_addr_or_zero(tbl, r)
  }

  fn role_addr_index(tbl: RoleTable) -> RBTreeMap‹G› {
    match load(tbl) {
      RoleTableNode.Mk(_, _, by_addr, _) => by_addr,
    }
  }

  -- 1 + the role bound at `a` when its group is usable under `rc`, after
  -- admitting that group; 0 when `a` plays no usable role. Every use of a
  -- role's meaning goes through here or `role_addr`, so nothing is read from
  -- a role that has not been validated, or, under an assumed binding, that
  -- the claim's condition does not cover.
  fn role_of(rc: RoleCtx, a: Addr) -> G {
    match load(rc) {
      RoleCtxNode.Mk(tbl, limit) =>
        let r1 = rbtree_map_lookup_or_default(ptr_val(a), role_addr_index(tbl), 0);
        match r1 {
          0 => 0,
          _ =>
            match u32_less_than(role_group(r1 - 1), limit) {
              1 =>
                group_admit(tbl, role_group(r1 - 1));
                r1,
              _ => 0,
            },
        },
      RoleCtxNode.Assumed(tbl) =>
        rbtree_map_lookup_or_default(ptr_val(a), role_addr_index(tbl), 0),
    }
  }

  -- 1 iff `a` is the bound address of role `r`, usable under `rc` (and so
  -- admitted).
  fn role_is(rc: RoleCtx, a: Addr, r: G) -> G {
    match role_of(rc, a) - (r + 1) {
      0 => 1,
      _ => 0,
    }
  }

  -- The address bound to role `r`, after admitting its group; the role must
  -- be usable under `rc`.
  fn role_addr(rc: RoleCtx, r: G) -> Addr {
    match load(rc) {
      RoleCtxNode.Mk(tbl, limit) =>
        assert_eq!(u32_less_than(role_group(r), limit), 1,
          "a role is used before its group is admitted");
        let a = role_bound_addr(tbl, r);
        group_admit(tbl, role_group(r));
        a,
      RoleCtxNode.Assumed(tbl) => role_bound_addr(tbl, r),
    }
  }

  -- The address bound to role `r`, for a constant the kernel introduces into
  -- a claim's terms without the claim referencing it: the constant is then
  -- a dependency of the claim, checked with its own dependencies under `rc`.
  fn role_used_implicitly(rc: RoleCtx, r: G) -> Addr {
    let a = role_addr(rc, r);
    run_check_transitive(rc, a);
    a
  }

  -- 1 iff role `r` is bound and usable under `rc`; admits it when it is.
  fn role_usable(rc: RoleCtx, r: G) -> G {
    match load(rc) {
      RoleCtxNode.Mk(tbl, limit) =>
        match u32_less_than(role_group(r), limit) * role_is_bound(tbl, r) {
          0 => 0,
          _ =>
            group_admit(tbl, role_group(r));
            1,
        },
      RoleCtxNode.Assumed(tbl) => role_is_bound(tbl, r),
    }
  }

  -- Validate group `g` of `tbl`, once: the groups it needs first, then each
  -- of its roles under a context that admits only the earlier groups.
  fn group_admit(tbl: RoleTable, g: G) {
    group_admit_needs(tbl, group_needs(g));
    let rc = store(RoleCtxNode.Mk(tbl, group_validation_limit(g)));
    validate_group_roles(rc, tbl, group_roles(g))
  }

  -- The number of groups usable while group `g` is validated: the groups
  -- before it, or, for a well-founded operation's group, the groups before
  -- the first of those.
  fn group_validation_limit(g: G) -> G {
    let first_wf = first_well_founded_group();
    match u32_less_than(g, first_wf) {
      1 => g,
      _ => first_wf,
    }
  }

  -- 1 iff role `r`'s admission checks its bound constant with its
  -- dependencies: a basis inductive, constructor or recursor, or an
  -- operation. Anchors, quotient members and axioms are validated by type.
  fn role_admission_checks(r: G) -> G {
    match role_spec_kind(r) {
      0 =>
        match role_member_kind(r) {
          0 => 1,
          1 => 1,
          2 => 1,
          _ => 0,
        },
      2 => 1,
      _ => 0,
    }
  }

  -- The context a walk under `rc` checks the constant at `a` in: for a role
  -- usable under `rc` whose admission checks it, the context its group is
  -- validated in, so the walk's check is the admission's own; otherwise
  -- `rc`. Admits nothing.
  fn walk_ctx(rc: RoleCtx, a: Addr) -> RoleCtx {
    match load(rc) {
      RoleCtxNode.Mk(tbl, limit) =>
        let r1 = rbtree_map_lookup_or_default(ptr_val(a), role_addr_index(tbl), 0);
        match r1 {
          0 => rc,
          _ =>
            let g = role_group(r1 - 1);
            match u32_less_than(g, limit) * role_admission_checks(r1 - 1) {
              0 => rc,
              _ => store(RoleCtxNode.Mk(tbl, group_validation_limit(g))),
            },
        },
      RoleCtxNode.Assumed(_) => rc,
    }
  }

  -- 1 iff a walk under `rc` leaves the constant at `a` to the binding claim:
  -- under an assumed binding, a role whose admission checks it with its
  -- dependencies (a basis inductive, constructor or recursor, or an
  -- operation). The claim's condition, that the binding meets the
  -- specifications, covers that check; anchors, quotient members and axioms,
  -- which are validated by type, are still checked as dependencies.
  fn walk_covered(rc: RoleCtx, a: Addr) -> G {
    match load(rc) {
      RoleCtxNode.Mk(_, _) => 0,
      RoleCtxNode.Assumed(tbl) =>
        let r1 = rbtree_map_lookup_or_default(ptr_val(a), role_addr_index(tbl), 0);
        match r1 {
          0 => 0,
          _ => role_admission_checks(r1 - 1),
        },
    }
  }

  -- Validate every group of the binding `binding`, which must bind every
  -- role: what a `binding` claim states.
  fn validate_binding(binding: Addr) {
    let tbl = load_role_table(binding);
    assert_all_roles_bound(tbl, 0);
    admit_all_groups(tbl, 0)
  }

  fn assert_all_roles_bound(tbl: RoleTable, r: G) {
    match r - role_count() {
      0 => (),
      _ =>
        assert_eq!(role_is_bound(tbl, r), 1, "binding claim: a role is unbound");
        assert_all_roles_bound(tbl, r + 1),
    }
  }

  fn admit_all_groups(tbl: RoleTable, g: G) {
    match g - group_count() {
      0 => (),
      _ =>
        group_admit(tbl, g);
        admit_all_groups(tbl, g + 1),
    }
  }

  fn group_admit_needs(tbl: RoleTable, needs: List‹G›) {
    match load(needs) {
      ListNode.Nil => (),
      ListNode.Cons(r, rest) =>
        group_admit(tbl, role_group(r));
        group_admit_needs(tbl, rest),
    }
  }

  fn validate_group_roles(rc: RoleCtx, tbl: RoleTable, rs: List‹G›) {
    match load(rs) {
      ListNode.Nil => (),
      ListNode.Cons(r, rest) =>
        validate_role(rc, tbl, r);
        validate_group_roles(rc, tbl, rest),
    }
  }

  -- ==========================================================================
  -- Validators.
  -- ==========================================================================

  fn validate_role(rc: RoleCtx, tbl: RoleTable, r: G) {
    let a = role_bound_addr(tbl, r);
    let ci = load(get_ci(a));
    assert_eq!(const_num_lvls(ci), role_levels(r),
      "a bound role has the wrong number of universe parameters");
    match role_spec_kind(r) {
      0 => validate_member(rc, tbl, r, a, ci),
      1 => validate_anchor(rc, tbl, r, ci),
      2 => validate_op(rc, tbl, r, a, ci),
      3 => validate_standard_axiom(rc, tbl, r, ci),
      4 => validate_inert_axiom(rc, ci),
    }
  }

  -- `ty` meets the specified type: the same term, or one definitionally
  -- equal to it under the earlier groups.
  fn assert_type_meets(rc: RoleCtx, ty: KExpr, spec: KExpr) {
    match ptr_val(ty) - ptr_val(spec) {
      0 => (),
      _ =>
        assert_eq!(k_is_def_eq(rc, ty, spec, store(ListNode.Nil)), 1,
          "a bound role's type does not meet its specification");
        (),
    }
  }

  fn assert_safe_role(ci: KConstantInfo) {
    assert_eq!(is_unsafe_ci(ci), 0, "a bound role is unsafe");
    ()
  }

  fn validate_member(rc: RoleCtx, tbl: RoleTable, r: G, a: Addr,
      ci: KConstantInfo) {
    assert_safe_role(ci);
    assert_type_meets(rc, const_type_of(ci), role_type(tbl, r));
    match role_member_kind(r) {
      0 =>
        match ci {
          KConstantInfo.Induct(_, _, _, _, nctors, _, _, _) =>
            assert_eq!(nctors, role_ctor_count(r),
              "a bound inductive has the wrong number of constructors");
            run_check_transitive(rc, a),
        },
      1 =>
        match ci {
          KConstantInfo.Ctor(_, _, block, ind_idx, cidx, nparams, nfields, _) =>
            let (ind_role, want_cidx, want_params, want_fields) = role_ctor_of(r);
            match load(get_ci(role_bound_addr(tbl, ind_role))) {
              KConstantInfo.Induct(_, _, _, _, _, _, ind_block, ind_ind_idx) =>
                assert_eq!(address_eq(block, ind_block), 1,
                  "a bound constructor is not its inductive's");
                assert_eq!(ind_idx, ind_ind_idx,
                  "a bound constructor is not its inductive's");
                (),
            };
            assert_eq!(cidx, want_cidx, "a bound constructor has the wrong index");
            assert_eq!(nparams, want_params,
              "a bound constructor has the wrong number of parameters");
            assert_eq!(nfields, want_fields,
              "a bound constructor has the wrong number of fields");
            run_check_transitive(rc, a),
        },
      2 =>
        match ci {
          KConstantInfo.Rec(_, _, _, _, _, _, _, _, _, _, _) =>
            run_check_transitive(rc, a),
        },
      3 =>
        match ci {
          KConstantInfo.Axiom(_, ty, _) =>
            validate_expr_well_scoped(ty, 0, role_levels(r));
            k_ensure_sort(rc, ty, store(ListNode.Nil));
            (),
        },
      4 => assert_quot_kind(ci, 0),
      5 => assert_quot_kind(ci, 1),
      6 => assert_quot_kind(ci, 2),
      7 => assert_quot_kind(ci, 3),
    }
  }

  fn assert_quot_kind(ci: KConstantInfo, want: G) {
    match ci {
      KConstantInfo.Quot(_, _, kind) =>
        let k = match kind {
          QuotKind.Typ => 0,
          QuotKind.Ctor => 1,
          QuotKind.Lift => 2,
          QuotKind.Ind => 3,
        };
        assert_eq!(k, want, "a bound quotient constant has the wrong kind");
        (),
    }
  }

  fn validate_anchor(rc: RoleCtx, tbl: RoleTable, r: G, ci: KConstantInfo) {
    assert_safe_role(ci);
    assert_type_meets(rc, const_type_of(ci), role_type(tbl, r))
  }

  -- `propext` and `Classical.choice`: safe axioms of the specified types.
  -- Checked here rather than through `check_const`, whose axiom policy
  -- admits a standard axiom only once its group is admitted.
  fn validate_standard_axiom(rc: RoleCtx, tbl: RoleTable, r: G,
      ci: KConstantInfo) {
    match ci {
      KConstantInfo.Axiom(nlvls, ty, u) =>
        assert_eq!(u, 0, "a bound standard axiom is unsafe");
        validate_expr_well_scoped(ty, 0, nlvls);
        k_ensure_sort(rc, ty, store(ListNode.Nil));
        assert_type_meets(rc, ty, role_type(tbl, r)),
    }
  }

  -- `sorryAx`: an axiom with one universe parameter; its type is free and
  -- any use of it declines.
  fn validate_inert_axiom(rc: RoleCtx, ci: KConstantInfo) {
    match ci {
      KConstantInfo.Axiom(nlvls, ty, _) =>
        validate_expr_well_scoped(ty, 0, nlvls);
        k_ensure_sort(rc, ty, store(ListNode.Nil));
        (),
    }
  }

  fn role_evidence(tbl: RoleTable, r: G) -> List‹RoleEvidence› {
    match load(tbl) {
      RoleTableNode.Mk(_, _, _, evidence) =>
        rbtree_map_lookup_or_default(r, evidence, store(ListNode.Nil)),
    }
  }

  fn validate_op(rc: RoleCtx, tbl: RoleTable, r: G, a: Addr,
      ci: KConstantInfo) {
    match ci {
      KConstantInfo.Defn(_, ty, _, safety, _) =>
        match safety {
          DefinitionSafety.Safe => (),
          _ =>
            assert_eq!(0, 1, "a bound operation is not a safe definition");
            (),
        };
        assert_type_meets(rc, ty, role_type(tbl, r));
        run_check_transitive(rc, a);
        let ev = role_evidence(tbl, r);
        assert_eq!(list_length(ev), op_equation_count(r),
          "an operation's evidence does not match its equations");
        validate_op_equations(rc, tbl, r, ev, 0),
    }
  }

  fn validate_op_equations(rc: RoleCtx, tbl: RoleTable, r: G,
      ev: List‹RoleEvidence›, k: G) {
    match load(ev) {
      ListNode.Nil => (),
      ListNode.Cons(e, rest) =>
        match op_evidence_is_proof(r) {
          0 =>
            match e {
              RoleEvidence.Defeq =>
                assert_eq!(k_is_def_eq(rc, op_equation_lhs(tbl, r, k),
                    op_equation_rhs(tbl, r, k), store(ListNode.Nil)), 1,
                  "an operation's equation does not hold by definition");
                (),
              RoleEvidence.Proof(_) =>
                assert_eq!(0, 1, "a structural operation's evidence must be definitional");
                (),
            },
          _ =>
            match e {
              RoleEvidence.Defeq =>
                assert_eq!(0, 1, "a well-founded operation's evidence must be proofs");
                (),
              RoleEvidence.Proof(thm) =>
                match load(get_ci(thm)) {
                  KConstantInfo.Thm(nlvls, tty, _) =>
                    assert_eq!(nlvls, 0, "certificate theorem has universe parameters");
                    run_check_transitive(rc, thm);
                    assert_type_meets(rc, tty, op_certificate(tbl, r, k)),
                },
            },
        };
        validate_op_equations(rc, tbl, r, rest, k + 1),
    }
  }

  -- ==========================================================================
  -- The axiom policy: Lean's theory over its standard axioms.
  -- ==========================================================================

  -- How a safe axiom at `a` stands in the claim's theory: 1 for a standard
  -- axiom (`propext`, `Classical.choice`, `Quot.sound`, as the binding binds
  -- them), 2 for the binding's `sorryAx`, which may be declared but not
  -- used, and 0 for any other, which is declined. The one place a standard
  -- axiom is recognized. Recognition admits the axiom's group like any
  -- role's, under `rc`'s earlier-groups rule, and no other group: an
  -- address that binds no axiom role admits nothing.
  fn axiom_standing(rc: RoleCtx, a: Addr) -> G {
    let tbl = role_ctx_table(rc);
    let r1 = rbtree_map_lookup_or_default(ptr_val(a), role_addr_index(tbl), 0);
    let standing = axiom_role_standing(r1);
    match standing {
      0 => 0,
      _ =>
        match role_of(rc, a) {
          0 => 0,
          _ => standing,
        },
    }
  }

  -- The standing of 1 + role `r1` (0: no role).
  fn axiom_role_standing(r1: G) -> G {
    match r1 {
      0 => 0,
      _ =>
        let r = r1 - 1;
        match r - role_propext() {
          0 => 1,
          _ =>
            match r - role_choice() {
              0 => 1,
              _ =>
                match r - role_quot_sound() {
                  0 => 1,
                  _ =>
                    match r - role_sorry_ax() {
                      0 => 2,
                      _ => 0,
                    },
                },
            },
        },
    }
  }

  -- A checked constant references `a` as a constant: `sorryAx` may be
  -- declared but no constant may use it.
  fn assert_ref_allowed(rc: RoleCtx, a: Addr) {
    match axiom_standing(rc, a) {
      2 =>
        assert_eq!(0, 1, "a constant uses `sorryAx`");
        (),
      _ => (),
    }
  }
⟧

end IxVM

end
