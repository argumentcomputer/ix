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
  fn get_ci(addr: Addr) -> &KConstantInfo {
    let c = load_verified_constant(addr);
    match c {
      Constant.Mk(info, sharing, refs, univs) =>
        match info {
          ConstantInfo.Defn(defn) =>
            let hint = #load_constant_hint(addr);
            -- Standalone Defn: single recur slot = self.
            let self_recur = store(ListNode.Cons(addr, store(ListNode.Nil)));
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
          ConstantInfo.Muts(members) =>
            -- Muts wrapper referenced directly: return the FIRST member's
            -- KCI. Rare — usually consumers reference via projections.
            get_ci_muts_member(addr, members, 0),
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
                let recur_addrs = build_recur_addrs(members, block_addr);
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

  -- Muts direct: return first member's KCI (fallback).
  fn get_ci_muts_member(muts_addr: Addr, members: List‹MutConst›,
                             idx: G) -> &KConstantInfo {
    let block_c = load_verified_constant(muts_addr);
    match block_c {
      Constant.Mk(_, sharing, refs, univs) =>
        let mc = muts_member_at(members, idx);
        let recur_addrs = build_recur_addrs(members, muts_addr);
        match mc {
          MutConst.Defn(d) =>
            let hint = #load_constant_hint(muts_addr);
            store(convert_definition(d, sharing, refs, recur_addrs, univs, hint)),
          MutConst.Indc(ind) =>
            store(convert_inductive(ind, muts_addr, idx,
                                         sharing, refs, recur_addrs, univs)),
          MutConst.Recr(r) =>
            store(convert_recursor(r, muts_addr, idx,
                                       sharing, refs, recur_addrs, univs)),
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

  -- Pack a member/ctor index into the u64 projection field as a
  -- little-endian [U8; 8].
  --
  -- The bytes come from the `unconstrained_g_to_bytes` hint and are then
  -- CONSTRAINED, because field -> bytes is not free: `flatten_u64` goes
  -- bytes -> field for nothing, but the reverse needs the bytes supplied
  -- as advice and pinned. Three obligations, all discharged here:
  --
  --   * every byte is range-checked into [0, 256) (`u8_range_check`
  --     takes a pair per lookup row, so eight bytes cost four);
  --   * the bytes must RECOMPOSE to `idx`;
  --   * the recomposition must be CANONICAL. This one is load-bearing:
  --     Goldilocks is 2^64 - 2^32 + 1, so an arbitrary eight-byte string
  --     is not injective into the field — values at or above `p` wrap,
  --     and a prover could hand over a second string recomposing to the
  --     same element.
  --
  -- Uniqueness is the soundness property, since the synthesized
  -- projection address is blake3 over these serialized bytes: a prover
  -- free to pick a different string for one index would get a second
  -- address for a member, or collide two members onto one address. The
  -- earlier `u8_from_field_unsafe` version truncated and did exactly
  -- that for members 0 and 256.
  --
  -- Indices at or beyond 2^56 fail the assert rather than truncating
  -- silently — a liveness bound only, and far past any real block or
  -- constructor count.
  fn idx_to_u64(idx: G) -> U64 {
    let [h0, h1, h2, h3, h4, h5, h6, h7] = unconstrained_g_to_bytes(idx);
    let (b0, b1) = u8_range_check(to_field(h0), to_field(h1));
    let (b2, b3) = u8_range_check(to_field(h2), to_field(h3));
    let (b4, b5) = u8_range_check(to_field(h4), to_field(h5));
    let (b6, b7) = u8_range_check(to_field(h6), to_field(h7));
    let bytes = [b0, b1, b2, b3, b4, b5, b6, b7];
    -- `flatten_u64` contributes the top-byte-is-zero assert and the sum.
    -- It does NOT range-check its input and so is not injective on its
    -- own; uniqueness here holds only because the range checks above
    -- bound every byte. Both halves are load-bearing — dropping either
    -- lets a prover pick a second byte string for the same index.
    assert_eq!(flatten_u64(bytes), idx,
      "projection index bytes do not recompose to the index");
    bytes
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
