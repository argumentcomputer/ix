"""User-axiom support for the donor kernel.

A claim context may commit the canonical Merkle root of safe axioms beyond
the standard three (`Ix.ClaimContext.axioms`). The donor revision rejects any
such commitment. These edits are upstream Ix commit
e8ee6f7b4d2e988ca15e24398a9579fbb8375956 restricted to that support, applied
to the donor's `Kernel/Roles` and `Kernel/Claim` sources before adaptation;
the rest of that commit (inlined constant functions, regenerated role
specifications, grouped circuits, the single-pass byte stream, `role_is`'s
lookup order) is not taken.

- `RoleCtxNode` carries the claim's axiom set;
- `load_role_ctx` validates every committed leaf as a safe axiom that binds
  no role, and builds the set;
- `axiom_standing` grants standing 1 to a member of the set;
- `get_claim_context` returns the axioms root instead of rejecting it, and
  the typing variants pass it to `load_role_ctx`;
- an unsharded `CheckEnv` with axioms walks its leaves under the claim's
  context (`run_check_transitive`): `check_owned` rebuilds the context from
  the binding and validator alone, and would drop the axioms.
"""

ROLES = [
    ('''    Mk(RoleTable, G),
    Assumed(RoleTable)
''', '''    Mk(RoleTable, G, RBTreeMap‹G›),
    Assumed(RoleTable, RBTreeMap‹G›)
''', 1),
    ('store(RoleCtxNode.Mk(load_role_table(binding), group_count()))',
     'store(RoleCtxNode.Mk(load_role_table(binding), group_count(), RBTreeMap.Nil))', 1),
    ('store(RoleCtxNode.Assumed(load_role_table(binding)))',
     'store(RoleCtxNode.Assumed(load_role_table(binding), RBTreeMap.Nil))', 1),
    ('''  fn role_ctx_for_validator(binding: Addr, validator: G) -> RoleCtx {
    match validator {
      3 => role_ctx_of_binding(binding),
      4 => role_ctx_assumed(binding),
      _ =>
        assert_eq!(0, 1, "claim: wrong validator identity");
        role_ctx_of_binding(binding),
    }
  }''', '''  fn role_ctx_for_validator(binding: Addr, validator: G) -> RoleCtx {
    load_role_ctx(binding, validator, Option.None)
  }

  -- Validate every leaf in the claim's `axioms` tree: each must be a safe
  -- `KConstantInfo.Axiom` not bound in `tbl`.
  fn validate_user_axioms(tbl: RoleTable, leaves: List‹Addr›, acc: RBTreeMap‹G›)
      -> RBTreeMap‹G› {
    match load(leaves) {
      ListNode.Nil => acc,
      ListNode.Cons(a, rest) =>
        assert_eq!(rbtree_map_lookup_or_default(ptr_val(a), role_addr_index(tbl), 0), 0,
          "claim: user axiom is bound in the role table");
        match load(get_ci(a)) {
          KConstantInfo.Axiom(_, _, u) =>
            assert_eq!(u, 0, "claim: user axiom is unsafe");
            validate_user_axioms(tbl, rest, rbtree_map_insert(ptr_val(a), 1, acc)),
          _ =>
            assert_eq!(0, 1, "claim: axioms tree entry is not an axiom");
            acc,
        },
    }
  }

  -- Load the role context for `(binding, validator, axioms_opt)`.
  fn load_role_ctx(binding: Addr, validator: G, axioms_opt: Option‹Addr›) -> RoleCtx {
    let tbl = load_role_table(binding);
    let axioms = match axioms_opt {
      Option.None => RBTreeMap.Nil,
      Option.Some(ax_root) =>
        validate_user_axioms(tbl, load_assumption_tree(ax_root), RBTreeMap.Nil),
    };
    match validator {
      3 => store(RoleCtxNode.Mk(tbl, group_count(), axioms)),
      4 => store(RoleCtxNode.Assumed(tbl, axioms)),
      _ =>
        assert_eq!(0, 1, "claim: wrong validator identity");
        store(RoleCtxNode.Mk(tbl, group_count(), axioms)),
    }
  }''', 1),
    ('''      RoleCtxNode.Mk(tbl, _) => tbl,
      RoleCtxNode.Assumed(tbl) => tbl,
    }
  }
''', '''      RoleCtxNode.Mk(tbl, _, _) => tbl,
      RoleCtxNode.Assumed(tbl, _) => tbl,
    }
  }

  fn role_ctx_axioms(rc: RoleCtx) -> RBTreeMap‹G› {
    match load(rc) {
      RoleCtxNode.Mk(_, _, axioms) => axioms,
      RoleCtxNode.Assumed(_, axioms) => axioms,
    }
  }
''', 1),
    ('RoleCtxNode.Mk(_, _) =>', 'RoleCtxNode.Mk(_, _, _) =>', 2),
    ('RoleCtxNode.Assumed(_) =>', 'RoleCtxNode.Assumed(_, _) =>', 2),
    ('RoleCtxNode.Mk(tbl, limit) =>', 'RoleCtxNode.Mk(tbl, limit, _) =>', 4),
    ('RoleCtxNode.Assumed(tbl) =>', 'RoleCtxNode.Assumed(tbl, _) =>', 4),
    ('store(RoleCtxNode.Mk(tbl, group_validation_limit(g)))',
     'store(RoleCtxNode.Mk(tbl, group_validation_limit(g), RBTreeMap.Nil))', 2),
    ('''    let standing = axiom_role_standing(r1);
    match standing {
      0 => 0,
      _ =>
        match role_of(rc, a) {
          0 => 0,
          _ => standing,
        },
    }''', '''    match r1 {
      0 => rbtree_map_lookup_or_default(ptr_val(a), role_ctx_axioms(rc), 0),
      _ =>
        let standing = axiom_role_standing(r1);
        match standing {
          0 => 0,
          _ =>
            match role_of(rc, a) {
              0 => 0,
              _ => standing,
            },
        },
    }''', 1),
]

CLAIM = [
    ('''        walk_leaves_owned(rc, load_assumption_tree(env_root)),''',
     '''        let leaves = load_assumption_tree(env_root);
        match role_ctx_axioms(rc) {
          RBTreeMap.Nil => walk_leaves_owned(rc, leaves),
          RBTreeMap.Node(_, _, _, _, _) => walk_leaves_transitive(rc, leaves),
        },''', 1),
    ('''  fn walk_leaves_owned(rc: RoleCtx, leaves: List‹Addr›) {''',
     '''  fn walk_leaves_transitive(rc: RoleCtx, leaves: List‹Addr›) {
    match load(leaves) {
      ListNode.Nil => (),
      ListNode.Cons(a, rest) =>
        run_check_transitive(rc, a);
        walk_leaves_transitive(rc, rest),
    }
  }

  fn walk_leaves_owned(rc: RoleCtx, leaves: List‹Addr›) {''', 1),
    ('''  fn get_claim_context(stream: ByteStream) -> (Addr, ByteStream) {''',
     '''  fn get_claim_context(stream: ByteStream) -> (Addr, Option‹Addr›, ByteStream) {''', 1),
    ('''    let (axioms, s3) = get_opt_addr(s2);
    match axioms {
      Option.None => (binding, s3),
      Option.Some(_) =>
        assert_eq!(0, 1, "claim: axioms beyond the standard three are not admitted");
        (binding, s3),
    }''', '''    let (axioms, s3) = get_opt_addr(s2);
    (binding, axioms, s3)''', 1),
    ('''        let (binding, s) = get_claim_context(s);
        let rc = role_ctx_of_binding(binding);''',
     '''        let (binding, axioms, s) = get_claim_context(s);
        let rc = load_role_ctx(binding, 3, axioms);''', 1),
    ('''        let (binding, s) = get_claim_context(s);
        let rc = role_ctx_for_validator(binding, to_field(validator));''',
     '''        let (binding, axioms, s) = get_claim_context(s);
        let rc = load_role_ctx(binding, to_field(validator), axioms);''', 2),
]

EDITS = {'Kernel/Roles': ROLES, 'Kernel/Claim': CLAIM}


def apply(name, text):
    for old, new, count in EDITS.get(name, []):
        found = text.count(old)
        if found != count:
            raise ValueError(f'user axioms: {name} has {found} copies of an edit site, expected {count}:\n{old}')
        text = text.replace(old, new)
    return text
