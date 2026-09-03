module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Check
public import Ix.IxVM.Ingress

public section

namespace IxVM

/-! ## Claim — the claim-variant runners behind `verify_claim`

`run_claim` parses the claim at ch 0 and dispatches to one of these:

* `run_check` — typecheck a single constant.
* `run_check_transitive` — a constant plus everything reachable through
  refs, with no ownership set (Check claims assert nothing about which
  shard owns what).
* `run_check_env` — every leaf of an owned merkle tree, walking with an
  assumption cutoff and a strict owned-membership rule.
* `run_reveal` — selective field revelation of a committed constant.
* `run_contains` — merkle membership of a target in a tree.
-/

def claim := ⟦
  -- Single-const check. Loads `addr`'s KConstantInfo lazily and
  -- typechecks it. Every ref discovered during typechecking is
  -- resolved via nested `get_ci`, faulting bytes from IOBuffer
  -- on first touch.
  fn run_check(addr: Addr) {
    let ci = load(get_ci(addr));
    check_const(ci, addr)
  }

  -- Which entries of a constant's `refs` are CONSTANT addresses — the
  -- indices the walk must recurse into.
  --
  -- An address is a constant when an Expr node references it as one:
  -- `Ref(i, ..)` and `Prj(i, ..)` index a constant, while `Str(i)` and
  -- `Nat(i)` index a blob payload. An address reached from outside any
  -- Expr — a claim target, a block address — is a constant reference by
  -- Ixon convention and is walked by its own path.
  --
  -- The rule is deliberately POSITIVE: walk index `i` iff some Expr uses
  -- it as a constant. The inverse formulation — skip whatever looks like
  -- a blob — is unsound, because the Exprs are authored by the prover and
  -- `refs` is one index space shared by all four node kinds. Under that
  -- rule a single `Nat(i)` node anywhere in the constant suppresses the
  -- walk of `refs[i]` used as a `Ref` everywhere else, and the entry need
  -- not even be live: `sharing` is traversed here in full but converted
  -- only where an `Expr.Share` reaches it, so a dead `Nat(i)` entry costs
  -- the prover nothing and hides an arbitrary dependency from the
  -- checker. `k_infer` then reads that dependency's DECLARED type without
  -- ever checking it, which is a wrong answer rather than an abort.
  --
  -- Over-approximating this set is safe: a walk into a non-constant
  -- address faults an unseeded key and aborts, which only costs a
  -- dishonest prover. Under-approximating it is not.
  --
  -- Note the same BYTES may be readable as both a constant and a Nat or
  -- utf-8 string; only this Expr context disambiguates, so byte inspection
  -- could not replace it.
  -- Direct recursion, no accumulator: each function is a pure function of
  -- the node it is given, so Aiur memoizes per-pointer and a shared
  -- subexpression is traversed once no matter how many parents reach it.
  -- Threading an accumulator would defeat that — the accumulator differs at
  -- every call site, so no two calls would ever share a memo entry.
  fn const_idxs_expr(e: &Expr) -> List‹G› {
    match load(e) {
      -- `Ref(i, _)` resolves refs[i] as a constant; `Prj(i, _, inner)`
      -- resolves refs[i] as the projected structure's type constant.
      -- These two are the ONLY Expr nodes that name a constant through
      -- the refs table — `Rec` resolves through `recur_addrs`, and a
      -- projection's block comes from the ConstantInfo payload, both
      -- walked separately.
      Expr.Ref(i, _) =>
        store(ListNode.Cons(flatten_u64(i), store(ListNode.Nil))),
      Expr.Prj(i, _, inner) =>
        store(ListNode.Cons(flatten_u64(i), const_idxs_expr(inner))),
      Expr.App(f, a) => list_concat(const_idxs_expr(f), const_idxs_expr(a)),
      Expr.Lam(_, t, b) => list_concat(const_idxs_expr(t), const_idxs_expr(b)),
      Expr.All(_, _, t, b) => list_concat(const_idxs_expr(t), const_idxs_expr(b)),
      Expr.Let(_, t, v, b) =>
        list_concat(const_idxs_expr(t),
          list_concat(const_idxs_expr(v), const_idxs_expr(b))),
      -- `Share` is deliberately NOT followed: the Expr is a DAG, and
      -- following share edges expands it exponentially. Every shared
      -- subexpression is itself an entry in `sharing`, which is walked
      -- once below, so coverage is complete and the traversal stays linear.
      _ => store(ListNode.Nil),
    }
  }

  fn const_idxs_exprs(es: List‹&Expr›) -> List‹G› {
    match load(es) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(e, rest) =>
        list_concat(const_idxs_expr(e), const_idxs_exprs(rest)),
    }
  }

  fn const_idxs_rules(rs: List‹RecursorRule›) -> List‹G› {
    match load(rs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(r, rest) =>
        match r {
          RecursorRule.Mk(_, rhs) =>
            list_concat(const_idxs_expr(rhs), const_idxs_rules(rest)),
        },
    }
  }

  fn const_idxs_ctors(cs: List‹Constructor›) -> List‹G› {
    match load(cs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, rest) =>
        match c {
          Constructor.Mk(_, _, _, _, _, typ) =>
            list_concat(const_idxs_expr(typ), const_idxs_ctors(rest)),
        },
    }
  }

  fn const_idxs_muts(ms: List‹MutConst›) -> List‹G› {
    match load(ms) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(m, rest) =>
        match m {
          MutConst.Defn(d) =>
            match d {
              Definition.Mk(_, _, _, typ, value) =>
                list_concat(
                  list_concat(const_idxs_expr(typ), const_idxs_expr(value)),
                  const_idxs_muts(rest)),
            },
          MutConst.Indc(i) =>
            match i {
              Inductive.Mk(_, _, _, _, typ, ctors) =>
                list_concat(
                  list_concat(const_idxs_expr(typ), const_idxs_ctors(ctors)),
                  const_idxs_muts(rest)),
            },
          MutConst.Recr(r) =>
            match r {
              Recursor.Mk(_, _, _, _, _, _, _, typ, rules) =>
                list_concat(
                  list_concat(const_idxs_expr(typ), const_idxs_rules(rules)),
                  const_idxs_muts(rest)),
            },
        },
    }
  }

  fn const_idxs_of(c: Constant) -> List‹G› {
    match c {
      Constant.Mk(info, sharing, _, _) =>
        let shared = const_idxs_exprs(sharing);
        match info {
          ConstantInfo.Defn(d) =>
            match d {
              Definition.Mk(_, _, _, typ, value) =>
                list_concat(shared,
                  list_concat(const_idxs_expr(typ), const_idxs_expr(value))),
            },
          ConstantInfo.Recr(r) =>
            match r {
              Recursor.Mk(_, _, _, _, _, _, _, typ, rules) =>
                list_concat(shared,
                  list_concat(const_idxs_expr(typ), const_idxs_rules(rules))),
            },
          ConstantInfo.Axio(a) =>
            match a {
              Axiom.Mk(_, _, typ) =>
                list_concat(shared, const_idxs_expr(typ)),
            },
          ConstantInfo.Quot(q) =>
            match q {
              Quotient.Mk(_, _, typ) =>
                list_concat(shared, const_idxs_expr(typ)),
            },
          ConstantInfo.Muts(members) =>
            list_concat(shared, const_idxs_muts(members)),
          -- Projection wrappers carry no Exprs of their own.
          _ => shared,
        },
    }
  }

  fn g_list_has(xs: List‹G›, x: G) -> G {
    match load(xs) {
      ListNode.Nil => 0,
      ListNode.Cons(y, rest) =>
        match y - x {
          0 => 1,
          _ => g_list_has(rest, x),
        },
    }
  }

  -- Transitive check: verify `addr` + every constant reachable via
  -- refs. Refs are BLOCK-level addresses — the acyclic dep DAG lives
  -- at block granularity (mutual constants inside a single Muts block;
  -- block refs form a DAG). Aiur memoizes per-addr so shared
  -- subgraphs check once.
  --
  -- Projection wrappers (DPrj/IPrj/CPrj/RPrj) have empty refs of their
  -- own; the actual dep list lives on their target BLOCK's
  -- Constant.Mk. Unwrap to the block via run_check_transitive
  -- recursion, which then walks the block's refs.
  --
  -- Every address that reaches here is a CONSTANT: the caller admits only
  -- indices `const_idxs_of` saw used as constants, and a claim target or a
  -- block address is a constant reference by convention. The decision to
  -- check is never taken from IO-buffer metadata.
  fn run_check_transitive(addr: Addr) {
    let c = load_verified_constant(addr);
    match c {
      Constant.Mk(info, _, refs, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            check_muts_all(addr, members, members, 0),
          ConstantInfo.DPrj(dprj) =>
            match dprj {
              DefinitionProj.Mk(_, block_addr) =>
                run_check(addr);
                run_check_transitive(block_addr),
            },
          ConstantInfo.IPrj(iprj) =>
            match iprj {
              InductiveProj.Mk(_, block_addr) =>
                run_check(addr);
                run_check_transitive(block_addr),
            },
          ConstantInfo.CPrj(cprj) =>
            match cprj {
              ConstructorProj.Mk(_, _, block_addr) =>
                run_check(addr);
                run_check_transitive(block_addr),
            },
          ConstantInfo.RPrj(rprj) =>
            match rprj {
              RecursorProj.Mk(_, block_addr) =>
                run_check(addr);
                run_check_transitive(block_addr),
            },
          _ => run_check(addr),
        };
        walk_refs_transitive(refs, const_idxs_of(c), 0),
    }
  }

  -- Recurse into exactly the refs the constant's own Exprs use as
  -- CONSTANTS; everything else is a blob payload or unreferenced. The
  -- decision comes from `const_idxs_of`, i.e. from bytes already bound by
  -- blake3 — not from an IO probe the prover answers.
  fn walk_refs_transitive(refs: List‹Addr›, consts: List‹G›, i: G) {
    match load(refs) {
      ListNode.Nil => (),
      ListNode.Cons(a, rest) =>
        match g_list_has(consts, i) {
          1 => run_check_transitive(a),
          _ => (),
        };
        walk_refs_transitive(rest, consts, i + 1),
    }
  }

  -- Check every member of a Muts block. Each member is checked through
  -- the projection ci (via get_ci_iprj/cprj/rprj/dprj) so all block
  -- members get their full soundness gauntlet.
  fn check_muts_all(block_addr: Addr, all_members: List‹MutConst›,
                          cur: List‹MutConst›, pos: G) {
    match load(cur) {
      ListNode.Nil => (),
      ListNode.Cons(m, rest) =>
        check_muts_member_at(block_addr, all_members, m, pos);
        check_muts_all(block_addr, all_members, rest, pos + 1),
    }
  }

  fn check_muts_member_at(block_addr: Addr,
                                all_members: List‹MutConst›,
                                m: MutConst, pos: G) {
    let member_addr = projection_addr(all_members, block_addr, pos);
    let ci = load(get_ci(member_addr));
    check_const(ci, member_addr)
  }

  -- ============================================================================
  -- Assumption / env tree: leaf list serialization (ch 1). The format
  -- matches the Rust implementation in crates/kernel/src, so the same
  -- witness buffers feed either checker. The tree is bound to its ch 1
  -- key by recomputing the merkle root, not by hashing the bytes — see
  -- the channel table in Ix/IxVM/ClaimHarness.lean.
  -- ============================================================================
  fn leaf_hash(addr: Addr) -> Addr {
    let tail = put_address(addr, store(ListNode.Nil));
    let bytes = store(ListNode.Cons(0u8, tail));
    bytes_to_addr(bytes)
  }

  fn node_hash(l: Addr, r: Addr) -> Addr {
    let tail = put_address(l, put_address(r, store(ListNode.Nil)));
    let bytes = store(ListNode.Cons(1u8, tail));
    bytes_to_addr(bytes)
  }

  -- Assumption-tree parser / loader. Same as constants: load bytes,
  -- recompute root via merkle fold, assert match.
  fn parse_atree_body(stream: ByteStream) -> (Addr, List‹Addr›, ByteStream) {
    let (tag, s) = read_byte(stream);
    match tag {
      0 =>
        let (addr, s2) = get_address(s);
        let h = leaf_hash(addr);
        (h, store(ListNode.Cons(addr, store(ListNode.Nil))), s2),
      1 =>
        (store([0u8; 32]), store(ListNode.Nil), s),
      2 =>
        let (lh, ll, s2) = parse_atree_body(s);
        let (rh, rl, s3) = parse_atree_body(s2);
        let h = node_hash(lh, rh);
        (h, list_concat(ll, rl), s3),
    }
  }

  fn load_assumption_tree(root: Addr) -> List‹Addr› {
    let raw = load(root);
    let (idx, len) = io_get_info(1, raw);
    let bytes = #read_byte_stream(1, idx, len);
    let (tag, s) = get_tag4(bytes);
    let (flag, size) = tag;
    assert_eq!(flag, 0xE, "assumption tree: wrong tag4 flag");
    assert_eq!(to_field(size[0]), 2, "assumption tree: wrong tag4 variant");
    let (computed_root, leaves, rest) = parse_atree_body(s);
    assert_eq!(load(rest), ListNode.Nil,
      "assumption tree: trailing bytes after tree body");
    let computed_arr = load(computed_root);
    -- Binds ch 1 to its key: the recomputed merkle root must equal the
    -- address the tree was requested under.
    assert_eq!(computed_arr, raw,
      "assumption tree: recomputed merkle root != requested root");
    leaves
  }

  -- ============================================================================
  -- R1: asm-aware transitive walk. Shared by Check-with-asm and
  -- CheckEnv. Per visited constant addr:
  --   * addr ∈ asm: assumed well-typed by its owning shard — do not
  --     check, do not recurse. The asm tree is the thin FRONTIER of
  --     the owned closure's out-of-shard refs; the ref-walk can only
  --     leave the shard through a frontier member, so nothing below
  --     the frontier is visited. (Bytes below the frontier may still
  --     be faulted by get_ci during delta unfolding — that is the
  --     ch 2 byte scope, blake3-bound per addr, and deliberately NOT
  --     subject to this walk's membership rule.)
  --   * strict=1 (CheckEnv): addr must be ∈ owned — a walk-reachable
  --     constant in neither owned nor asm means the claim's owned
  --     tree does not cover its own closure (bad frontier); abort
  --     rather than silently absorb the check. Owned trees must list
  --     the full block-level closure (blocks and wrappers included),
  --     which is what `AssumptionTree.canonical` over a closure set
  --     produces.
  --   * otherwise: check the constant (Muts: every member) and
  --     recurse its block-level refs.
  -- Aiur memoizes per (addr, owned, asm, strict) — the list pointers
  -- are per-run constants, so shared subgraphs walk once.
  -- Addr-set membership via RBTreeMap keyed on the interned store
  -- pointer: content-addressed interning makes ptr equality ⇔ 32-byte
  -- equality in BOTH directions (each content has exactly one store
  -- slot), so a u32 ptr key is an exact membership test. O(log n) per
  -- query vs the O(n) list scan — the frontier list is the biggest
  -- per-visit cost on fat-frontier shards (e.g. 1977 asm leaves).
  fn addr_set_build(leaves: List‹Addr›, acc: RBTreeMap‹G›) -> RBTreeMap‹G› {
    match load(leaves) {
      ListNode.Nil => acc,
      ListNode.Cons(a, rest) =>
        addr_set_build(rest, rbtree_map_insert(ptr_val(a), 1, acc)),
    }
  }

  fn addr_set_member(a: Addr, tree: RBTreeMap‹G›) -> G {
    rbtree_map_lookup_or_default(ptr_val(a), tree, 0)
  }

  fn env_walk(addr: Addr, owned: RBTreeMap‹G›, asm: RBTreeMap‹G›,
                  strict: G) {
    -- Every address reaching here is a constant: the caller admits only
    -- indices the referring constant's own Exprs use as constants, and a
    -- walk root or block address is a constant reference by convention.
    -- Nothing here may
    -- branch on IO-buffer metadata — this walk decides both what gets checked
    -- and what strict membership covers, so a prover-steerable skip would
    -- exclude an owned leaf from both while the claim's merkle root still
    -- commits to it.
    match addr_set_member(addr, asm) {
      1 => (),
      _ =>
        match strict {
          1 =>
            assert_eq!(addr_set_member(addr, owned), 1,
              "CheckEnv: walk reached a constant outside the owned set");
            (),
          _ => (),
        };
        let c = load_verified_constant(addr);
        match c {
          Constant.Mk(info, _, refs, _) =>
            match info {
              ConstantInfo.Muts(members) =>
                check_muts_all(addr, members, members, 0),
              ConstantInfo.DPrj(dprj) =>
                match dprj {
                  DefinitionProj.Mk(_, block_addr) =>
                    run_check(addr);
                    env_walk(block_addr, owned, asm, strict),
                },
              ConstantInfo.IPrj(iprj) =>
                match iprj {
                  InductiveProj.Mk(_, block_addr) =>
                    run_check(addr);
                    env_walk(block_addr, owned, asm, strict),
                },
              ConstantInfo.CPrj(cprj) =>
                match cprj {
                  ConstructorProj.Mk(_, _, block_addr) =>
                    run_check(addr);
                    env_walk(block_addr, owned, asm, strict),
                },
              ConstantInfo.RPrj(rprj) =>
                match rprj {
                  RecursorProj.Mk(_, block_addr) =>
                    run_check(addr);
                    env_walk(block_addr, owned, asm, strict),
                },
              _ => run_check(addr),
            };
            env_walk_refs(refs, const_idxs_of(c), 0, owned, asm, strict),
        },
    }
  }

  fn env_walk_refs(refs: List‹Addr›, consts: List‹G›, i: G,
                       owned: RBTreeMap‹G›,
                       asm: RBTreeMap‹G›, strict: G) {
    match load(refs) {
      ListNode.Nil => (),
      ListNode.Cons(a, rest) =>
        match g_list_has(consts, i) {
          1 => env_walk(a, owned, asm, strict),
          _ => (),
        };
        env_walk_refs(rest, consts, i + 1, owned, asm, strict),
    }
  }

  fn env_walk_leaves(leaves: List‹Addr›, owned: RBTreeMap‹G›,
                         asm: RBTreeMap‹G›) {
    match load(leaves) {
      ListNode.Nil => (),
      ListNode.Cons(a, rest) =>
        env_walk(a, owned, asm, 1);
        env_walk_leaves(rest, owned, asm),
    }
  }

  -- CheckEnv: every owned leaf is checked TRANSITIVELY with the asm
  -- cutoff and strict owned-membership on the walk set. The walk has to
  -- be explicit because `get_ci` is lazy and consults a dependency's
  -- declared type without checking it: being loaded is not evidence of
  -- being well-typed, so every constant the claim covers must be
  -- reached by this walk or assumed via the frontier.
  fn run_check_env(env_root: Addr, asm: Option‹Addr›) {
    let owned = load_assumption_tree(env_root);
    let asm_leaves = match asm {
      Option.None => store(ListNode.Nil),
      Option.Some(r) => load_assumption_tree(r),
    };
    let owned_set = addr_set_build(owned, RBTreeMap.Nil);
    let asm_set = addr_set_build(asm_leaves, RBTreeMap.Nil);
    env_walk_leaves(owned, owned_set, asm_set)
  }

  -- Option<Address> deserializer, mirror (Kernel/Claim.lean:109).
  fn get_opt_addr(stream: ByteStream) -> (Option‹Addr›, ByteStream) {
    let (tag, s) = read_byte(stream);
    match tag {
      0 => (Option.None, s),
      1 =>
        let (addr, s2) = get_address(s);
        (Option.Some(addr), s2),
    }
  }

  -- ============================================================================
  -- Reveal claim (variant 6). Mirrors the Rust implementation in
  -- crates/kernel/src; the machinery is Ixon-level rather than
  -- typechecker-level: parse a `RevealConstantInfo` (per-field Option
  -- mirror of `ConstantInfo`, Expr fields as content hashes), load the
  -- committed constant, assert every Some(field) equals the real one.

  enum RevealRecursorRule {
    Mk(U64, U64, Addr)
  }

  enum RevealConstructorInfo {
    Mk(Option‹G›, Option‹U64›, Option‹U64›,
       Option‹U64›, Option‹U64›, Option‹Addr›)
  }

  enum RevealMutConstInfo {
    Defn(Option‹DefKind›, Option‹DefinitionSafety›,
         Option‹U64›, Option‹Addr›, Option‹Addr›),
    Indc(Option‹G›,
         Option‹U64›, Option‹U64›, Option‹U64›,
         Option‹Addr›,
         Option‹List‹(U64, RevealConstructorInfo)››),
    Recr(Option‹G›, Option‹G›,
         Option‹U64›, Option‹U64›, Option‹U64›,
         Option‹U64›, Option‹U64›,
         Option‹Addr›, Option‹List‹RevealRecursorRule››)
  }

  enum RevealConstantInfo {
    Defn(Option‹DefKind›, Option‹DefinitionSafety›,
         Option‹U64›, Option‹Addr›, Option‹Addr›),
    Recr(Option‹G›, Option‹G›,
         Option‹U64›, Option‹U64›, Option‹U64›,
         Option‹U64›, Option‹U64›,
         Option‹Addr›, Option‹List‹RevealRecursorRule››),
    Axio(Option‹G›, Option‹U64›, Option‹Addr›),
    Quot(Option‹QuotKind›, Option‹U64›, Option‹Addr›),
    CPrj(Option‹U64›, Option‹U64›, Option‹Addr›),
    RPrj(Option‹U64›, Option‹Addr›),
    IPrj(Option‹U64›, Option‹Addr›),
    DPrj(Option‹U64›, Option‹Addr›),
    Muts(List‹(U64, RevealMutConstInfo)›)
  }

  -- Bitmask-gated decoders for the per-field Reveal payloads.
  fn get_opt_u64_masked(mb: G, stream: ByteStream)
      -> (Option‹U64›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (n, s) = get_tag0(stream);
        (Option.Some(n), s),
    }
  }

  fn get_opt_addr_masked(mb: G, stream: ByteStream)
      -> (Option‹Addr›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (a, s) = get_address(stream);
        (Option.Some(a), s),
    }
  }

  fn get_opt_bool_masked(mb: G, stream: ByteStream)
      -> (Option‹G›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (b, s) = read_byte(stream);
        (Option.Some(to_field(b)), s),
    }
  }

  fn get_opt_def_kind_masked(mb: G, stream: ByteStream)
      -> (Option‹DefKind›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (b, s) = read_byte(stream);
        match b {
          0 => (Option.Some(DefKind.Definition), s),
          1 => (Option.Some(DefKind.Opaque), s),
          2 => (Option.Some(DefKind.Theorem), s),
        },
    }
  }

  fn get_opt_def_safety_masked(mb: G, stream: ByteStream)
      -> (Option‹DefinitionSafety›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (b, s) = read_byte(stream);
        match b {
          0 => (Option.Some(DefinitionSafety.Unsafe), s),
          1 => (Option.Some(DefinitionSafety.Safe), s),
          2 => (Option.Some(DefinitionSafety.Partial), s),
        },
    }
  }

  fn get_opt_quot_kind_masked(mb: G, stream: ByteStream)
      -> (Option‹QuotKind›, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (b, s) = read_byte(stream);
        match b {
          0 => (Option.Some(QuotKind.Typ), s),
          1 => (Option.Some(QuotKind.Ctor), s),
          2 => (Option.Some(QuotKind.Lift), s),
          3 => (Option.Some(QuotKind.Ind), s),
        },
    }
  }

  -- RevealRecursorRule list parser.
  -- Wire: `Tag0(count) + count × (Tag0(idx) + Tag0(fields) + Address)`.
  fn get_reveal_rule(stream: ByteStream) -> (RevealRecursorRule, ByteStream) {
    let (rule_idx, s) = get_tag0(stream);
    let (fields, s) = get_tag0(s);
    let (rhs, s) = get_address(s);
    (RevealRecursorRule.Mk(rule_idx, fields, rhs), s)
  }

  fn get_reveal_rule_list_inner(stream: ByteStream, count: U64)
      -> (List‹RevealRecursorRule›, ByteStream) {
    match u64_is_zero(count) {
      1 => (store(ListNode.Nil), stream),
      _ =>
        let (rule, s) = get_reveal_rule(stream);
        let (rest, s2) = get_reveal_rule_list_inner(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(rule, rest)), s2),
    }
  }

  fn get_opt_rule_list_masked(mb: G, stream: ByteStream)
      -> (Option‹List‹RevealRecursorRule››, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (count, s) = get_tag0(stream);
        let (rules, s2) = get_reveal_rule_list_inner(s, count);
        (Option.Some(rules), s2),
    }
  }

  -- RevealConstructorInfo parser. 6 optional fields, mask bits 0..5.
  fn get_reveal_ctor_info(stream: ByteStream)
      -> (RevealConstructorInfo, ByteStream) {
    let (mask, s) = get_tag0(stream);
    let mask_lo = u8_bit_decomposition(mask[0]);
    let [b0, b1, b2, b3, b4, b5, _, _] = mask_lo;
    let (is_unsafe, s) = get_opt_bool_masked(b0, s);
    let (lvls, s) = get_opt_u64_masked(b1, s);
    let (cidx, s) = get_opt_u64_masked(b2, s);
    let (params, s) = get_opt_u64_masked(b3, s);
    let (fields, s) = get_opt_u64_masked(b4, s);
    let (typ, s) = get_opt_addr_masked(b5, s);
    (RevealConstructorInfo.Mk(is_unsafe, lvls, cidx, params, fields, typ), s)
  }

  fn get_ctor_entry(stream: ByteStream)
      -> ((U64, RevealConstructorInfo), ByteStream) {
    let (idx, s) = get_tag0(stream);
    let (info, s) = get_reveal_ctor_info(s);
    ((idx, info), s)
  }

  fn get_ctor_entry_list_inner(stream: ByteStream, count: U64)
      -> (List‹(U64, RevealConstructorInfo)›, ByteStream) {
    match u64_is_zero(count) {
      1 => (store(ListNode.Nil), stream),
      _ =>
        let (entry, s) = get_ctor_entry(stream);
        let (rest, s2) = get_ctor_entry_list_inner(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(entry, rest)), s2),
    }
  }

  fn get_opt_ctor_entry_list_masked(mb: G, stream: ByteStream)
      -> (Option‹List‹(U64, RevealConstructorInfo)››, ByteStream) {
    match mb {
      0 => (Option.None, stream),
      _ =>
        let (count, s) = get_tag0(stream);
        let (list, s2) = get_ctor_entry_list_inner(s, count);
        (Option.Some(list), s2),
    }
  }

  -- RevealMutConstInfo parser. variant + mask + per-bit fields.
  fn get_reveal_mut_const_info(stream: ByteStream)
      -> (RevealMutConstInfo, ByteStream) {
    let (variant, s) = read_byte(stream);
    let (mask, s) = get_tag0(s);
    let mask_lo = u8_bit_decomposition(mask[0]);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = mask_lo;
    let mask_hi = u8_bit_decomposition(mask[1]);
    let [b8, _, _, _, _, _, _, _] = mask_hi;
    match variant {
      0 =>
        let (kind, s) = get_opt_def_kind_masked(b0, s);
        let (safety, s) = get_opt_def_safety_masked(b1, s);
        let (lvls, s) = get_opt_u64_masked(b2, s);
        let (typ, s) = get_opt_addr_masked(b3, s);
        let (value, s) = get_opt_addr_masked(b4, s);
        (RevealMutConstInfo.Defn(kind, safety, lvls, typ, value), s),
      1 =>
        let (is_unsafe, s) = get_opt_bool_masked(b0, s);
        let (lvls, s) = get_opt_u64_masked(b1, s);
        let (params, s) = get_opt_u64_masked(b2, s);
        let (indices, s) = get_opt_u64_masked(b3, s);
        let (typ, s) = get_opt_addr_masked(b4, s);
        let (ctors, s) = get_opt_ctor_entry_list_masked(b5, s);
        (RevealMutConstInfo.Indc(is_unsafe, lvls, params,
                                  indices, typ, ctors), s),
      2 =>
        let (k, s) = get_opt_bool_masked(b0, s);
        let (is_unsafe, s) = get_opt_bool_masked(b1, s);
        let (lvls, s) = get_opt_u64_masked(b2, s);
        let (params, s) = get_opt_u64_masked(b3, s);
        let (indices, s) = get_opt_u64_masked(b4, s);
        let (motives, s) = get_opt_u64_masked(b5, s);
        let (minors, s) = get_opt_u64_masked(b6, s);
        let (typ, s) = get_opt_addr_masked(b7, s);
        let (rules, s) = get_opt_rule_list_masked(b8, s);
        (RevealMutConstInfo.Recr(k, is_unsafe, lvls, params, indices,
                                  motives, minors, typ, rules), s),
    }
  }

  fn get_mut_entry(stream: ByteStream)
      -> ((U64, RevealMutConstInfo), ByteStream) {
    let (idx, s) = get_tag0(stream);
    let (info, s) = get_reveal_mut_const_info(s);
    ((idx, info), s)
  }

  fn get_mut_entry_list_inner(stream: ByteStream, count: U64)
      -> (List‹(U64, RevealMutConstInfo)›, ByteStream) {
    match u64_is_zero(count) {
      1 => (store(ListNode.Nil), stream),
      _ =>
        let (entry, s) = get_mut_entry(stream);
        let (rest, s2) = get_mut_entry_list_inner(s, relaxed_u64_pred(count));
        (store(ListNode.Cons(entry, rest)), s2),
    }
  }

  -- RevealConstantInfo parser. `variant + mask:Tag0 + per-bit fields`.
  fn get_reveal_info(stream: ByteStream) -> (RevealConstantInfo, ByteStream) {
    let (variant, s) = read_byte(stream);
    let (mask, s) = get_tag0(s);
    let mask_lo = u8_bit_decomposition(mask[0]);
    let [b0, b1, b2, b3, b4, b5, b6, b7] = mask_lo;
    let mask_hi = u8_bit_decomposition(mask[1]);
    let [b8, _, _, _, _, _, _, _] = mask_hi;
    match variant {
      0 =>
        let (kind, s) = get_opt_def_kind_masked(b0, s);
        let (safety, s) = get_opt_def_safety_masked(b1, s);
        let (lvls, s) = get_opt_u64_masked(b2, s);
        let (typ, s) = get_opt_addr_masked(b3, s);
        let (value, s) = get_opt_addr_masked(b4, s);
        (RevealConstantInfo.Defn(kind, safety, lvls, typ, value), s),
      1 =>
        let (k, s) = get_opt_bool_masked(b0, s);
        let (is_unsafe, s) = get_opt_bool_masked(b1, s);
        let (lvls, s) = get_opt_u64_masked(b2, s);
        let (params, s) = get_opt_u64_masked(b3, s);
        let (indices, s) = get_opt_u64_masked(b4, s);
        let (motives, s) = get_opt_u64_masked(b5, s);
        let (minors, s) = get_opt_u64_masked(b6, s);
        let (typ, s) = get_opt_addr_masked(b7, s);
        let (rules, s) = get_opt_rule_list_masked(b8, s);
        (RevealConstantInfo.Recr(k, is_unsafe, lvls, params, indices,
                                  motives, minors, typ, rules), s),
      2 =>
        let (is_unsafe, s) = get_opt_bool_masked(b0, s);
        let (lvls, s) = get_opt_u64_masked(b1, s);
        let (typ, s) = get_opt_addr_masked(b2, s);
        (RevealConstantInfo.Axio(is_unsafe, lvls, typ), s),
      3 =>
        let (kind, s) = get_opt_quot_kind_masked(b0, s);
        let (lvls, s) = get_opt_u64_masked(b1, s);
        let (typ, s) = get_opt_addr_masked(b2, s);
        (RevealConstantInfo.Quot(kind, lvls, typ), s),
      4 =>
        let (idx, s) = get_opt_u64_masked(b0, s);
        let (cidx, s) = get_opt_u64_masked(b1, s);
        let (block, s) = get_opt_addr_masked(b2, s);
        (RevealConstantInfo.CPrj(idx, cidx, block), s),
      5 =>
        let (idx, s) = get_opt_u64_masked(b0, s);
        let (block, s) = get_opt_addr_masked(b1, s);
        (RevealConstantInfo.RPrj(idx, block), s),
      6 =>
        let (idx, s) = get_opt_u64_masked(b0, s);
        let (block, s) = get_opt_addr_masked(b1, s);
        (RevealConstantInfo.IPrj(idx, block), s),
      7 =>
        let (idx, s) = get_opt_u64_masked(b0, s);
        let (block, s) = get_opt_addr_masked(b1, s);
        (RevealConstantInfo.DPrj(idx, block), s),
      8 =>
        let (components, s) = match b0 {
          0 => (store(ListNode.Nil), s),
          1 =>
            let (count, s2) = get_tag0(s);
            get_mut_entry_list_inner(s2, count),
        };
        (RevealConstantInfo.Muts(components), s),
    }
  }

  -- Content hash of an `Expr`: `blake3(put_expr expr)`.
  fn expr_addr(e_ref: &Expr) -> Addr {
    let bytes = put_expr(load(e_ref), store(ListNode.Nil));
    bytes_to_addr(bytes)
  }

  -- Per-field equality checks. None = no-op (selective reveal);
  -- Some(claimed) = assert equality with the real field.
  fn def_kind_tag(k: DefKind) -> G {
    match k {
      DefKind.Definition => 0,
      DefKind.Opaque => 1,
      DefKind.Theorem => 2,
    }
  }

  fn def_safety_tag(s: DefinitionSafety) -> G {
    match s {
      DefinitionSafety.Unsafe => 0,
      DefinitionSafety.Safe => 1,
      DefinitionSafety.Partial => 2,
    }
  }

  fn quot_kind_tag(k: QuotKind) -> G {
    match k {
      QuotKind.Typ => 0,
      QuotKind.Ctor => 1,
      QuotKind.Lift => 2,
      QuotKind.Ind => 3,
    }
  }

  fn check_opt_def_kind(real: DefKind, opt: Option‹DefKind›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(def_kind_tag(real), def_kind_tag(claimed),
          "Reveal: claimed definition kind != real");
        (),
    }
  }

  fn check_opt_def_safety(real: DefinitionSafety,
                          opt: Option‹DefinitionSafety›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(def_safety_tag(real), def_safety_tag(claimed),
          "Reveal: claimed definition safety != real");
        (),
    }
  }

  fn check_opt_quot_kind(real: QuotKind, opt: Option‹QuotKind›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(quot_kind_tag(real), quot_kind_tag(claimed),
          "Reveal: claimed quotient kind != real");
        (),
    }
  }

  fn check_opt_bool(real: G, opt: Option‹G›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(real, claimed, "Reveal: claimed flag != real");
        (),
    }
  }

  fn check_opt_u64(real: U64, opt: Option‹U64›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(real, claimed, "Reveal: claimed numeric field != real");
        (),
    }
  }

  fn check_opt_addr(real: Addr, opt: Option‹Addr›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        assert_eq!(load(real), load(claimed),
          "Reveal: claimed address field != real");
        (),
    }
  }

  fn check_opt_expr_addr(real_e: &Expr, opt: Option‹Addr›) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        let computed = expr_addr(real_e);
        assert_eq!(load(computed), load(claimed),
          "Reveal: claimed expr hash != hash of the real expr");
        (),
    }
  }

  -- Walk both lists in lockstep: claimed (idx, fields, rhs_addr) per
  -- entry vs real (fields, rhs:&Expr).
  --
  -- The claimed `idx` is part of the reveal's digest, so a consumer reads it
  -- and believes it identifies WHICH rule was revealed. The comparison here
  -- is positional, so without this assert a reveal could carry
  -- `ruleIdx: 7` while matching the rule at position 0 — the consumer then
  -- believes it learned rule 7 and it learned rule 0. Every sibling reveal
  -- check (CPrj/RPrj/IPrj/DPrj) already validates its index.
  fn check_recr_rules(real: List‹RecursorRule›,
                      claimed: List‹RevealRecursorRule›,
                      pos: U64) {
    match load(claimed) {
      ListNode.Nil =>
        match load(real) {
          ListNode.Nil => (),
        },
      ListNode.Cons(cr, rest_claimed) =>
        match load(real) {
          ListNode.Cons(rr, rest_real) =>
            match cr {
              RevealRecursorRule.Mk(c_idx, c_fields, c_rhs) =>
                match rr {
                  RecursorRule.Mk(r_fields, r_rhs) =>
                    assert_eq!(c_idx, pos,
                      "Reveal: claimed recursor rule index != its position");
                    assert_eq!(r_fields, c_fields,
                      "Reveal: claimed recursor rule field count != real");
                    check_opt_expr_addr(r_rhs, Option.Some(c_rhs));
                    check_recr_rules(rest_real, rest_claimed,
                      relaxed_u64_succ(pos)),
                },
            },
        },
    }
  }

  fn check_opt_recr_rules(real: List‹RecursorRule›,
                          opt: Option‹List‹RevealRecursorRule››) {
    match opt {
      Option.None => (),
      Option.Some(claimed) =>
        check_recr_rules(real, claimed,
          [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]),
    }
  }

  -- Constructor revelation: compare the Constructor at position `idx`
  -- in the real list against the per-field Option‹…› bits.
  fn check_ctor_entry(real_list: List‹Constructor›,
                      idx: U64,
                      info: RevealConstructorInfo) {
    let real_ctor = list_lookup_u64(real_list, idx);
    match info {
      RevealConstructorInfo.Mk(opt_unsafe, opt_lvls, opt_cidx,
                                opt_params, opt_fields, opt_typ) =>
        match real_ctor {
          Constructor.Mk(r_unsafe, r_lvls, r_cidx, r_params, r_fields, r_typ) =>
            check_opt_bool(r_unsafe, opt_unsafe);
            check_opt_u64(r_lvls, opt_lvls);
            check_opt_u64(r_cidx, opt_cidx);
            check_opt_u64(r_params, opt_params);
            check_opt_u64(r_fields, opt_fields);
            check_opt_expr_addr(r_typ, opt_typ),
        },
    }
  }

  fn check_ctor_entries(real_list: List‹Constructor›,
                        claimed: List‹(U64, RevealConstructorInfo)›) {
    match load(claimed) {
      ListNode.Nil => (),
      ListNode.Cons(entry, rest) =>
        match entry {
          (idx, info) =>
            check_ctor_entry(real_list, idx, info);
            check_ctor_entries(real_list, rest),
        },
    }
  }

  fn check_opt_ctor_entries(real_list: List‹Constructor›,
                            opt: Option‹List‹(U64, RevealConstructorInfo)››) {
    match opt {
      Option.None => (),
      Option.Some(claimed) => check_ctor_entries(real_list, claimed),
    }
  }

  -- MutConst revelation: dispatch on the real variant vs the claimed
  -- variant; mismatched pairs fail.
  fn check_mut_const(real: MutConst, claimed: RevealMutConstInfo) {
    match real {
      MutConst.Defn(d) =>
        match claimed {
          RevealMutConstInfo.Defn(opt_kind, opt_safety, opt_lvls,
                                   opt_typ, opt_value) =>
            match d {
              Definition.Mk(r_kind, r_safety, r_lvls, r_typ, r_value) =>
                check_opt_def_kind(r_kind, opt_kind);
                check_opt_def_safety(r_safety, opt_safety);
                check_opt_u64(r_lvls, opt_lvls);
                check_opt_expr_addr(r_typ, opt_typ);
                check_opt_expr_addr(r_value, opt_value),
            },
        },
      MutConst.Indc(i) =>
        match claimed {
          RevealMutConstInfo.Indc(opt_unsafe, opt_lvls,
                                   opt_params, opt_indices,
                                   opt_typ, opt_ctors) =>
            match i {
              Inductive.Mk(r_unsafe, r_lvls, r_params,
                            r_indices, r_typ, r_ctors) =>
                check_opt_bool(r_unsafe, opt_unsafe);
                check_opt_u64(r_lvls, opt_lvls);
                check_opt_u64(r_params, opt_params);
                check_opt_u64(r_indices, opt_indices);
                check_opt_expr_addr(r_typ, opt_typ);
                check_opt_ctor_entries(r_ctors, opt_ctors),
            },
        },
      MutConst.Recr(r) =>
        match claimed {
          RevealMutConstInfo.Recr(opt_k, opt_unsafe, opt_lvls, opt_params,
                                   opt_indices, opt_motives, opt_minors,
                                   opt_typ, opt_rules) =>
            match r {
              Recursor.Mk(r_k, r_unsafe, r_lvls, r_params, r_indices,
                           r_motives, r_minors, r_typ, r_rules) =>
                check_opt_bool(r_k, opt_k);
                check_opt_bool(r_unsafe, opt_unsafe);
                check_opt_u64(r_lvls, opt_lvls);
                check_opt_u64(r_params, opt_params);
                check_opt_u64(r_indices, opt_indices);
                check_opt_u64(r_motives, opt_motives);
                check_opt_u64(r_minors, opt_minors);
                check_opt_expr_addr(r_typ, opt_typ);
                check_opt_recr_rules(r_rules, opt_rules),
            },
        },
    }
  }

  fn check_muts_components(real: List‹MutConst›,
                           claimed: List‹(U64, RevealMutConstInfo)›) {
    match load(claimed) {
      ListNode.Nil => (),
      ListNode.Cons(entry, rest_claimed) =>
        match entry {
          (idx, info) =>
            let real_mc = list_lookup_u64(real, idx);
            check_mut_const(real_mc, info);
            check_muts_components(real, rest_claimed),
        },
    }
  }

  -- Reveal: real constant at `comm` must match the variant of `info`
  -- AND every Some-field's claimed value must equal the real field.
  fn run_reveal(comm_addr: Addr, info: RevealConstantInfo) {
    let c = load_verified_constant(comm_addr);
    match c {
      Constant.Mk(ci, _, _, _) =>
        match ci {
          ConstantInfo.Defn(d) =>
            match info {
              RevealConstantInfo.Defn(opt_kind, opt_safety, opt_lvls,
                                       opt_typ, opt_value) =>
                match d {
                  Definition.Mk(r_kind, r_safety, r_lvls, r_typ, r_value) =>
                    check_opt_def_kind(r_kind, opt_kind);
                    check_opt_def_safety(r_safety, opt_safety);
                    check_opt_u64(r_lvls, opt_lvls);
                    check_opt_expr_addr(r_typ, opt_typ);
                    check_opt_expr_addr(r_value, opt_value),
                },
            },
          ConstantInfo.Recr(r) =>
            match info {
              RevealConstantInfo.Recr(opt_k, opt_unsafe, opt_lvls, opt_params,
                                       opt_indices, opt_motives, opt_minors,
                                       opt_typ, opt_rules) =>
                match r {
                  Recursor.Mk(r_k, r_unsafe, r_lvls, r_params, r_indices,
                               r_motives, r_minors, r_typ, r_rules) =>
                    check_opt_bool(r_k, opt_k);
                    check_opt_bool(r_unsafe, opt_unsafe);
                    check_opt_u64(r_lvls, opt_lvls);
                    check_opt_u64(r_params, opt_params);
                    check_opt_u64(r_indices, opt_indices);
                    check_opt_u64(r_motives, opt_motives);
                    check_opt_u64(r_minors, opt_minors);
                    check_opt_expr_addr(r_typ, opt_typ);
                    check_opt_recr_rules(r_rules, opt_rules),
                },
            },
          ConstantInfo.Axio(a) =>
            match info {
              RevealConstantInfo.Axio(opt_unsafe, opt_lvls, opt_typ) =>
                match a {
                  Axiom.Mk(r_unsafe, r_lvls, r_typ) =>
                    check_opt_bool(r_unsafe, opt_unsafe);
                    check_opt_u64(r_lvls, opt_lvls);
                    check_opt_expr_addr(r_typ, opt_typ),
                },
            },
          ConstantInfo.Quot(q) =>
            match info {
              RevealConstantInfo.Quot(opt_kind, opt_lvls, opt_typ) =>
                match q {
                  Quotient.Mk(r_kind, r_lvls, r_typ) =>
                    check_opt_quot_kind(r_kind, opt_kind);
                    check_opt_u64(r_lvls, opt_lvls);
                    check_opt_expr_addr(r_typ, opt_typ),
                },
            },
          ConstantInfo.CPrj(p) =>
            match info {
              RevealConstantInfo.CPrj(opt_idx, opt_cidx, opt_block) =>
                match p {
                  ConstructorProj.Mk(r_idx, r_cidx, r_block) =>
                    check_opt_u64(r_idx, opt_idx);
                    check_opt_u64(r_cidx, opt_cidx);
                    check_opt_addr(r_block, opt_block),
                },
            },
          ConstantInfo.RPrj(p) =>
            match info {
              RevealConstantInfo.RPrj(opt_idx, opt_block) =>
                match p {
                  RecursorProj.Mk(r_idx, r_block) =>
                    check_opt_u64(r_idx, opt_idx);
                    check_opt_addr(r_block, opt_block),
                },
            },
          ConstantInfo.IPrj(p) =>
            match info {
              RevealConstantInfo.IPrj(opt_idx, opt_block) =>
                match p {
                  InductiveProj.Mk(r_idx, r_block) =>
                    check_opt_u64(r_idx, opt_idx);
                    check_opt_addr(r_block, opt_block),
                },
            },
          ConstantInfo.DPrj(p) =>
            match info {
              RevealConstantInfo.DPrj(opt_idx, opt_block) =>
                match p {
                  DefinitionProj.Mk(r_idx, r_block) =>
                    check_opt_u64(r_idx, opt_idx);
                    check_opt_addr(r_block, opt_block),
                },
            },
          ConstantInfo.Muts(real_mc_list) =>
            match info {
              RevealConstantInfo.Muts(claimed_components) =>
                check_muts_components(real_mc_list, claimed_components),
            },
        },
    }
  }

  -- Contains claim (variant 7): merkle membership of `target` in the
  -- tree at `tree_root`. Mirror run_contains.
  fn run_contains(tree_root: Addr, target: Addr) {
    let leaves = load_assumption_tree(tree_root);
    assert_eq!(se_addr_in(target, leaves), 1,
      "Contains: target is not a leaf of the claimed tree");
  }

  -- Claim dispatch. Loads claim bytes at ch 0 keyed by digest,
  -- blake3-verifies, and dispatches:
  --   variant 4 (Check target asm?)  → transitive check; with asm the
  --     walk stops at frontier members (no owned-membership rule —
  --     Check claims target + everything reachable, no ownership set).
  --   variant 5 (CheckEnv root asm?) → run_check_env: per-leaf
  --     transitive walk, asm cutoff, strict owned-membership.
  --   variant 6 (Reveal comm info)   → run_reveal: selective field
  --     revelation of the committed constant.
  --   variant 7 (Contains tree target) → run_contains: merkle
  --     membership.
  -- Variants without an arm here (notably 3, Eval) have no defined
  -- semantics upstream, so the match falls through and aborts rather
  -- than accepting a claim whose meaning is unspecified.
  fn run_claim(digest: [G; 8]) {
    -- `digest` is the packed-4-byte public claim digest; the ch-0 key uses
    -- the same packed form (io keys are execution-side only — no columns).
    let (idx, len) = io_get_info(0, digest);
    let bytes = #read_byte_stream(0, idx, len);
    -- Binding: the claim bytes must hash to the PUBLIC digest. Packed
    -- comparison (8 wiring-packed words), no byte-form digest needed.
    let h = @blake3(bytes);
    assert_eq!(@b3_pack(h), digest,
      "claim: bytes do not hash to the public claim digest");
    let (tag, s) = get_tag4(bytes);
    let (flag, size) = tag;
    assert_eq!(flag, 0xE, "claim: wrong tag4 flag");
    -- Dispatch on the FULL tag4 size, matching Rust `Claim::get` which
    -- matches `tag.size: u64`. The variant is only ever 4-7, so the high 7
    -- bytes must be zero; a size >= 256 whose low byte is 4/5/6/7 would
    -- otherwise dispatch here while Rust rejects it as an unknown variant.
    -- Sum is 0 iff every high byte is 0 (7 bytes, max sum 1785, no wrap).
    let [_, sz1, sz2, sz3, sz4, sz5, sz6, sz7] = size;
    assert_eq!(((((((to_field(sz1) + to_field(sz2)) + to_field(sz3))
                  + to_field(sz4)) + to_field(sz5)) + to_field(sz6))
                  + to_field(sz7)), 0,
      "claim: tag4 size exceeds a single byte");
    let variant = size[0];
    match variant {
      4 =>
        let (target, s2) = get_address(s);
        let (asm, _s3) = get_opt_addr(s2);
        match asm {
          Option.None => run_check_transitive(target),
          Option.Some(r) =>
            let asm_leaves = load_assumption_tree(r);
            let asm_set = addr_set_build(asm_leaves, RBTreeMap.Nil);
            env_walk(target, RBTreeMap.Nil, asm_set, 0),
        },
      5 =>
        let (root, s2) = get_address(s);
        let (asm, _s3) = get_opt_addr(s2);
        run_check_env(root, asm),
      6 =>
        let (comm, s2) = get_address(s);
        let (info, _s3) = get_reveal_info(s2);
        run_reveal(comm, info),
      7 =>
        let (tree, s2) = get_address(s);
        let (target, _s3) = get_address(s2);
        run_contains(tree, target),
    }
  }
⟧

end IxVM

end
