module
public import Ix.Aiur.Meta

public section

namespace IxVM

def ingress := ⟦
  -- ============================================================================
  -- Ingress — lazy fault-loading get_ci + IOBuffer channel wiring
  --
  -- Channels. Host side is `IxVM.ClaimHarness.addEntries`; that module's
  -- "IxVM IOBuffer interface" section is the normative table and these
  -- literals must stay in sync with it.
  --
  --   ch 0  claim wire bytes        key = blake3(claim_bytes) = claim digest
  --   ch 1  assumption tree bytes   key = tree.root
  --   ch 2  constant wire bytes     key = constant addr
  --   ch 3  Defn reducibility hint  key = defn addr
  --   ch 4  blob raw bytes          key = blob addr
  --
  -- One value shape per channel, and every key is the content address of
  -- the value it maps to. An address is seeded on ch 2 iff it is a
  -- constant and on ch 4 iff it is a blob; the two sets are disjoint.
  -- ch 0/1/2/4 are BOUND: the kernel re-derives the key from the bytes it
  -- read and asserts equality, so the host cannot substitute a payload
  -- (for ch 1 the derivation is a merkle-root recomputation, not a hash of
  -- the bytes). ch 3 is advisory — it selects a reduction heuristic, and
  -- def-eq is sound under any value.
  --
  -- The `idx`/`len` pair returned by `io_get_info` is unconstrained prover
  -- witness. It is safe solely as a locator for bytes that are then bound —
  -- a wrong span fails the re-hash. Never branch on it: that hands the
  -- prover a control-flow decision taken before anything is bound. Callers
  -- that need to know whether an address is a constant or a blob derive it
  -- from Expr context (see `blob_idxs_of` in Kernel/Claim.lean), never by
  -- probing a channel.
  -- ============================================================================

  -- Load and blake3-verify Ixon Constant bytes at `addr`.
  fn load_verified_constant(addr: Addr) -> Constant {
    let raw = load(addr);
    let (idx, len) = io_get_info(2, raw);
    let bytes = #read_byte_stream(2, idx, len);
    verify_bytes_against(bytes, raw);
    let (constant, rest) = get_constant(bytes);
    assert_eq!(load(rest), ListNode.Nil,
      "trailing bytes after constant on ch 2");
    constant
  }

  -- Load reducibility hint G for a Defn at `addr` (ch 3).
  -- Encoding: 0 = Opaque, 1+h = Regular(h), 0xFFFFFFFF = Abbrev.
  fn load_constant_hint(addr: Addr) -> G {
    let raw = load(addr);
    let (idx, len) = io_get_info(3, raw);
    let bytes = #read_byte_stream(3, idx, len);
    match load(bytes) {
      ListNode.Cons(b, _) => to_field(b),
    }
  }

  -- Load and blake3-verify blob bytes at `addr` from ch 4.
  fn load_verified_blob(addr: Addr) -> ByteStream {
    let raw = load(addr);
    let (idx, len) = io_get_info(4, raw);
    let bytes = #read_byte_stream(4, idx, len);
    verify_bytes_against(bytes, raw);
    bytes
  }

  -- ============================================================================
  -- get_ci: THE constant resolver.
  --
  -- Faults `addr`'s Ixon Constant from IOBuffer, blake3-verifies,
  -- deserializes, and converts to KConstantInfo. Aiur memoizes per `addr`
  -- pointer — each distinct addr resolves at most once per run.
  --
  -- / scope: Defn / Axiom / Quot. Projections (IPrj/CPrj/RPrj/DPrj)
  -- + Muts wrappers arrive here.2 (recursor + inductive support).
  -- ============================================================================
  -- Would this definition's KCI be classified UNSAFE by `is_unsafe_ci`
  -- (Kernel/Check.lean)? Mirrors `convert_definition`'s kind dispatch:
  -- `Theorem` becomes `KConstantInfo.Thm`, which is unconditionally
  -- safe, and `Opaque` keeps only `safety == Unsafe`.
  --
  -- The `Rec` slot is granted on exactly this condition, so the two can
  -- never disagree. Keying the slot on `safety` alone did disagree: with
  -- `kind` and `safety` independent bytes on the wire
  -- (`unpack_def_kind_safety`), `(Theorem, Unsafe)` and
  -- `(Opaque, Partial)` opened the slot while landing on a KCI variant
  -- that reports safe — so `theorem bad : False := bad` typechecked and
  -- stayed referenceable from safe code. The invariant to hold is
  -- "anything that may name itself is something no safe constant may
  -- reference", and it only holds if one predicate decides both.
  fn defn_is_unsafe_ci(kind: DefKind, safety: DefinitionSafety) -> G {
    match kind {
      DefKind.Theorem => 0,
      DefKind.Opaque =>
        match safety {
          DefinitionSafety.Unsafe => 1,
          _ => 0,
        },
      DefKind.Definition =>
        match safety {
          DefinitionSafety.Safe => 0,
          _ => 1,
        },
    }
  }

  -- Peer slots for a DEFINITION member of a mutual block. Safe members
  -- get none, for the same reason a standalone safe definition gets no
  -- self slot: `Rec` converts to a plain `Const` and `k_infer` reads a
  -- `Const`'s declared type without checking it, so a safe definition
  -- able to name a block peer — itself included — discharges its own
  -- type. `build_recur_addrs` handed every member the full list
  -- regardless, which is how the standalone guard was bypassed by
  -- wrapping the definition in a singleton block.
  --
  -- Inductive and recursor members keep the full list: mutual inductives
  -- genuinely need to name their peers, and neither kind checks a value
  -- against a declared type, so neither can close the cycle.
  fn defn_member_recur_addrs(d: Definition, members: List‹MutConst›,
                                  block_addr: Addr) -> List‹Addr› {
    match d {
      Definition.Mk(kind, safety, _, _, _) =>
        match defn_is_unsafe_ci(kind, safety) {
          0 => store(ListNode.Nil),
          _ => build_recur_addrs(members, block_addr),
        },
    }
  }

  fn get_ci(addr: Addr) -> &KConstantInfo {
    let c = load_verified_constant(addr);
    match c {
      Constant.Mk(info, sharing, refs, univs) =>
        match info {
          ConstantInfo.Defn(defn) =>
            let hint = #load_constant_hint(addr);
            -- Standalone Defn: a single recur slot naming ITSELF, and only
            -- for an unsafe definition.
            --
            -- `Rec` converts to a plain `Const`, and `k_infer` reads a
            -- `Const`'s DECLARED type without checking it. So a self slot
            -- lets a definition discharge its own type by citing itself:
            -- `theorem bad : False := bad` would typecheck, since the
            -- referent is the constant already under check and the
            -- ref-walk does not follow `Rec`. Lean forbids exactly this by
            -- checking a definition against an environment that does not
            -- yet contain it, admitting self-reference only for `unsafe`.
            --
            -- `unsafe` and `partial` are where self-reference is both
            -- legitimate and contained. Legitimate because the compiler
            -- emits a singleton or fully-collapsed mutual block as a
            -- standalone `Defn` whose body still says `Rec(0)`, and those
            -- blocks are exactly Lean's `unsafe`/`partial` recursive
            -- definitions — a `safe` recursive definition compiles its
            -- recursion into `.rec` applications instead. Contained
            -- because safe code may not reference either kind, so a
            -- self-reference cannot leak into the trusted fragment.
            --
            -- A definition classified safe gets an empty list, so its
            -- `Rec` aborts on the out-of-range lookup. Mutual blocks are
            -- covered by the same predicate via
            -- `defn_member_recur_addrs`.
            let self_recur = match defn {
              Definition.Mk(kind, safety, _, _, _) =>
                match defn_is_unsafe_ci(kind, safety) {
                  0 => store(ListNode.Nil),
                  _ => store(ListNode.Cons(addr, store(ListNode.Nil))),
                },
            };
            store(convert_definition(defn, sharing, refs,
                                          self_recur, univs, hint)),
          ConstantInfo.Axio(axio) =>
            -- Axiom bodies have no Rec refs; empty recur_addrs.
            store(convert_axiom(axio, sharing, refs,
                                     store(ListNode.Nil), univs)),
          ConstantInfo.Quot(quot) =>
            store(convert_quotient(quot, sharing, refs,
                                        store(ListNode.Nil), univs)),
          ConstantInfo.DPrj(prj) =>
            match prj {
              DefinitionProj.Mk(idx, block_addr) =>
                get_ci_dprj(addr, idx, block_addr),
            },
          ConstantInfo.IPrj(prj) =>
            match prj {
              InductiveProj.Mk(idx, block_addr) =>
                get_ci_iprj(block_addr, flatten_u64(idx)),
            },
          ConstantInfo.CPrj(prj) =>
            match prj {
              ConstructorProj.Mk(idx, cidx, block_addr) =>
                get_ci_cprj(block_addr, flatten_u64(idx), flatten_u64(cidx)),
            },
          ConstantInfo.RPrj(prj) =>
            match prj {
              RecursorProj.Mk(idx, block_addr) =>
                get_ci_rprj(block_addr, flatten_u64(idx)),
            },
          -- No `Muts` arm: a block address is not a constant, so an
          -- unmatched value aborts here, which is the reject.
          --
          -- This used to fall back to the FIRST member's KCI, which gave
          -- that member a SECOND working address — `Const(block)` and
          -- `Const(dprj{0, block})` both resolved to it. One constant at
          -- two addresses is exactly what content addressing is supposed
          -- to preclude, and it hands out a second lexicographic position
          -- wherever addresses are compared; `canon_addr_cmp` orders a
          -- block's members by their external refs.
          --
          -- The reference does not do this either: faulting a block
          -- address ingresses the members under their PROJECTION KIds and
          -- the block under `kenv.blocks`, leaving nothing at the block
          -- address itself, so asking for it errors
          -- (`crates/kernel/src/ingress.rs:4539-4544`).
          --
          -- Nothing in the kernel needed the fallback: `is_muts_block`
          -- and `check_block_peer_param_agreement` read blocks through
          -- `load_verified_constant`, and every member is reached by its
          -- projection.
          ConstantInfo.Recr(recr) =>
            -- Standalone Recr: single recur slot = self.
            let self_recur = store(ListNode.Cons(addr, store(ListNode.Nil)));
            store(convert_recursor(recr, addr, 0,
                                        sharing, refs, self_recur, univs)),
        },
    }
  }

  -- DPrj resolver: Defn projection.
  fn get_ci_dprj(dprj_addr: Addr, idx: U64, block_addr: Addr) -> &KConstantInfo {
    let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, sharing, refs, univs) =>
        match info {
          ConstantInfo.Muts(members) =>
            let mc = list_lookup_u64(members, idx);
            match mc {
              MutConst.Defn(d) =>
                let hint = #load_constant_hint(dprj_addr);
                let recur_addrs =
                  defn_member_recur_addrs(d, members, block_addr);
                store(convert_definition(d, sharing, refs, recur_addrs, univs, hint)),
            },
        },
    }
  }

  -- IPrj resolver: Inductive projection.
  fn get_ci_iprj(block_addr: Addr, idx: G) -> &KConstantInfo {
    let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, sharing, refs, univs) =>
        match info {
          ConstantInfo.Muts(members) =>
            let mc = muts_member_at(members, idx);
            match mc {
              MutConst.Indc(ind) =>
                let recur_addrs = build_recur_addrs(members, block_addr);
                store(convert_inductive(ind, block_addr, idx,
                                             sharing, refs, recur_addrs, univs)),
            },
        },
    }
  }

  -- CPrj resolver: Constructor projection.
  fn get_ci_cprj(block_addr: Addr, idx: G, cidx: G) -> &KConstantInfo {
    let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, sharing, refs, univs) =>
        match info {
          ConstantInfo.Muts(members) =>
            let mc = muts_member_at(members, idx);
            match mc {
              MutConst.Indc(ind) =>
                match ind {
                  Inductive.Mk(_, _, _, _, _, ctors) =>
                    let c = ctor_at(ctors, cidx);
                    let recur_addrs = build_recur_addrs(members, block_addr);
                    store(convert_constructor(c, block_addr, idx,
                                                  sharing, refs, recur_addrs, univs)),
                },
            },
        },
    }
  }

  -- RPrj resolver: Recursor projection.
  fn get_ci_rprj(block_addr: Addr, idx: G) -> &KConstantInfo {
let block_c = load_verified_constant(block_addr);
    match block_c {
      Constant.Mk(info, sharing, refs, univs) =>
        match info {
          ConstantInfo.Muts(members) =>
            let mc = muts_member_at(members, idx);
            match mc {
              MutConst.Recr(r) =>
                let recur_addrs = build_recur_addrs(members, block_addr);
                store(convert_recursor(r, block_addr, idx,
                                           sharing, refs, recur_addrs, univs)),
            },
        },
    }
  }

  -- G-indexed Muts member lookup.
  fn muts_member_at(members: List‹MutConst›, idx: G) -> MutConst {
    match load(members) {
      ListNode.Cons(m, rest) =>
        match idx {
          0 => m,
          _ => muts_member_at(rest, idx - 1),
        },
    }
  }

  -- Synthesize the projection-wrapper Addr for Muts member at idx.
  -- Serializes the projection Constant (empty sharing/refs/univs) and
  -- blake3-hashes it — same output as Ixon compile's emitted projection
  -- wrapper. Aiur memoizes per (members, block_addr, idx). Used by
  -- convert_expr's Rec arm to resolve intra-Muts references.
  fn projection_addr(members: List‹MutConst›, block_addr: Addr, idx: G) -> Addr {
    let mc = muts_member_at(members, idx);
    let idx_u64 = idx_to_u64(idx);
    let info = match mc {
      MutConst.Defn(_) =>
        ConstantInfo.DPrj(DefinitionProj.Mk(idx_u64, block_addr)),
      MutConst.Indc(_) =>
        ConstantInfo.IPrj(InductiveProj.Mk(idx_u64, block_addr)),
      MutConst.Recr(_) =>
        ConstantInfo.RPrj(RecursorProj.Mk(idx_u64, block_addr)),
    };
    let proj_c = Constant.Mk(info,
                              store(ListNode.Nil),
                              store(ListNode.Nil),
                              store(ListNode.Nil));
    let bytes = put_constant(proj_c, store(ListNode.Nil));
    bytes_to_addr(bytes)
  }

  -- Build List<Addr> of projection addrs for a block's members, parallel
  -- to `members`. Consumed by convert_expr Rec arm as recur_addrs.
  fn build_recur_addrs(members: List‹MutConst›, block_addr: Addr) -> List‹Addr› {
    build_recur_addrs_walk(members, block_addr, members, 0)
  }

  fn build_recur_addrs_walk(all_members: List‹MutConst›, block_addr: Addr,
                                 cur: List‹MutConst›, idx: G) -> List‹Addr› {
    match load(cur) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(_, rest) =>
        store(ListNode.Cons(
          projection_addr(all_members, block_addr, idx),
          build_recur_addrs_walk(all_members, block_addr, rest, idx + 1))),
    }
  }
⟧

end IxVM

end
