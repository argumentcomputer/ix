module
import Ix.Aiur.Meta
public import Ix.Aiur.Stages.Source

public section

namespace IxVM

def ingress := ⟦
  -- Load a constant from IOBuffer by address, verify blake3, deserialize.
  fn load_verified_constant(addr: Addr) -> Constant {
    let raw = load(addr);
    let (idx, len) = io_get_info(0, raw);
    let bytes = #read_byte_stream(0, idx, len);
    let h = blake3(bytes);
    assert_eq!(
      [
        h[0][0], h[0][1], h[0][2], h[0][3],
        h[1][0], h[1][1], h[1][2], h[1][3],
        h[2][0], h[2][1], h[2][2], h[2][3],
        h[3][0], h[3][1], h[3][2], h[3][3],
        h[4][0], h[4][1], h[4][2], h[4][3],
        h[5][0], h[5][1], h[5][2], h[5][3],
        h[6][0], h[6][1], h[6][2], h[6][3],
        h[7][0], h[7][1], h[7][2], h[7][3]
      ],
      raw
    );
    let (constant, rest) = get_constant(bytes);
    assert_eq!(load(rest), ListNode.Nil);
    constant
  }

  -- Load a blob from IOBuffer by address, verify blake3, return raw bytes.
  -- Blobs live on channel 1; constants live on channel 0 with the same key.
  fn load_verified_blob(addr: Addr) -> ByteStream {
    let (idx, len) = io_get_info(1, load(addr));
    let bytes = #read_byte_stream(1, idx, len);
    let h = blake3(bytes);
    assert_eq!(
      [
        h[0][0], h[0][1], h[0][2], h[0][3],
        h[1][0], h[1][1], h[1][2], h[1][3],
        h[2][0], h[2][1], h[2][2], h[2][3],
        h[3][0], h[3][1], h[3][2], h[3][3],
        h[4][0], h[4][1], h[4][2], h[4][3],
        h[5][0], h[5][1], h[5][2], h[5][3],
        h[6][0], h[6][1], h[6][2], h[6][3],
        h[7][0], h[7][1], h[7][2], h[7][3]
      ],
      load(addr)
    );
    bytes
  }

  -- Compare two 32-byte addresses for equality
  fn address_eq(a: Addr, b: Addr) -> G {
    let [a0, a1, a2, a3, a4, a5, a6, a7,
         a8, a9, a10, a11, a12, a13, a14, a15,
         a16, a17, a18, a19, a20, a21, a22, a23,
         a24, a25, a26, a27, a28, a29, a30, a31] = load(a);
    let [b0, b1, b2, b3, b4, b5, b6, b7,
         b8, b9, b10, b11, b12, b13, b14, b15,
         b16, b17, b18, b19, b20, b21, b22, b23,
         b24, b25, b26, b27, b28, b29, b30, b31] = load(b);
    match [to_field(a0) - to_field(b0), to_field(a1) - to_field(b1),
           to_field(a2) - to_field(b2), to_field(a3) - to_field(b3),
           to_field(a4) - to_field(b4), to_field(a5) - to_field(b5),
           to_field(a6) - to_field(b6), to_field(a7) - to_field(b7),
           to_field(a8) - to_field(b8), to_field(a9) - to_field(b9),
           to_field(a10) - to_field(b10), to_field(a11) - to_field(b11),
           to_field(a12) - to_field(b12), to_field(a13) - to_field(b13),
           to_field(a14) - to_field(b14), to_field(a15) - to_field(b15),
           to_field(a16) - to_field(b16), to_field(a17) - to_field(b17),
           to_field(a18) - to_field(b18), to_field(a19) - to_field(b19),
           to_field(a20) - to_field(b20), to_field(a21) - to_field(b21),
           to_field(a22) - to_field(b22), to_field(a23) - to_field(b23),
           to_field(a24) - to_field(b24), to_field(a25) - to_field(b25),
           to_field(a26) - to_field(b26), to_field(a27) - to_field(b27),
           to_field(a28) - to_field(b28), to_field(a29) - to_field(b29),
           to_field(a30) - to_field(b30), to_field(a31) - to_field(b31)] {
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] => 1,
      _ => 0,
    }
  }

  -- Load reducibility hint G for a Defn at `addr`. Lives on channel 2.
  -- Encoding (mirror Lean.ReducibilityHints):
  --   0           = Opaque
  --   1 + h       = Regular(h)
  --   0xFFFFFFFF  = Abbrev
  -- Caller MUST only invoke this for Defn addrs; the harness only seeds
  -- channel 2 for defns. A missing key aborts execution (correct).
  fn load_constant_hint(addr: Addr) -> G {
    let (idx, len) = io_get_info(2, load(addr));
    let bytes = #read_byte_stream(2, idx, len);
    match load(bytes) {
      ListNode.Cons(b, _) => to_field(b),
    }
  }

  -- Build lit_blobs by loading and verifying each blob on demand.
  -- A ref is a blob if it's not in all_addrs (the constant address list).
  -- For constant refs, returns an empty ByteStream (never read by conversion).
  fn build_lit_blobs(refs: List‹Addr›, addr_pos_map: &RBTreeMap‹G›) -> List‹ByteStream› {
    match load(refs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(addr, rest) =>
        let blob = is_blob(addr, addr_pos_map);
        match blob {
          1 =>
            let bs = load_verified_blob(addr);
            store(ListNode.Cons(bs, build_lit_blobs(rest, addr_pos_map))),
          0 =>
            store(ListNode.Cons(store(ListNode.Nil), build_lit_blobs(rest, addr_pos_map))),
        },
    }
  }

  -- Check if an address is a blob: it's a blob iff it's NOT a constant,
  -- i.e. absent from `addr_pos_map` (which is keyed by every constant
  -- address — see `build_addr_pos_map`). Membership only; the stored
  -- position value (pos+1 ≥ 1) is irrelevant here, only "present vs 0".
  -- Blob addresses and constant addresses are different by design
  -- (different hash preimage structures). O(log N) tree lookup.
  fn is_blob(addr: Addr, addr_pos_map: &RBTreeMap‹G›) -> G {
    let hit = rbtree_map_lookup_or_default(ptr_val(addr), load(addr_pos_map), 0);
    match hit {
      0 => 1,
      _ => 0,
    }
  }

  -- Extract the Muts block address from a projection ConstantInfo.
  -- Returns [0; 32] for non-projection constants.
  fn get_proj_block_addr(info: ConstantInfo) -> Addr {
    match info {
      ConstantInfo.IPrj(prj) =>
        match prj { InductiveProj.Mk(_, addr) => addr, },
      ConstantInfo.CPrj(prj) =>
        match prj { ConstructorProj.Mk(_, _, addr) => addr, },
      ConstantInfo.RPrj(prj) =>
        match prj { RecursorProj.Mk(_, addr) => addr, },
      ConstantInfo.DPrj(prj) =>
        match prj { DefinitionProj.Mk(_, addr) => addr, },
      ConstantInfo.Defn(_) => store([0u8; 32]),
      ConstantInfo.Recr(_) => store([0u8; 32]),
      ConstantInfo.Axio(_) => store([0u8; 32]),
      ConstantInfo.Quot(_) => store([0u8; 32]),
      ConstantInfo.Muts(_) => store([0u8; 32]),
    }
  }

  -- ============================================================================
  -- Position map: maps loaded addresses to kernel constant positions.
  --
  -- When a Muts block is encountered, its members are expanded inline into
  -- kernel constants: each Indc becomes 1 Induct + N Ctors, each Recr becomes
  -- 1 Rec, each Defn becomes 1 Defn. Projection constants (IPrj, CPrj, RPrj,
  -- DPrj) are not emitted directly — instead they map to the position of their
  -- corresponding expanded member.
  -- ============================================================================

  -- Count the number of kernel entries a single MutConst member produces:
  -- Indc: 1 (inductive) + num_ctors
  -- Recr: 1
  -- Defn: 1
  fn member_kernel_size(mc: MutConst) -> G {
    match mc {
      MutConst.Indc(ind) =>
        match ind {
          Inductive.Mk(_, _, _, _, _, _, _, _, ctors) =>
            list_length(ctors) + 1,
        },
      MutConst.Recr(_) => 1,
      MutConst.Defn(_) => 1,
    }
  }

  -- Count total kernel entries for an entire List‹MutConst›
  fn block_kernel_size(members: List‹MutConst›) -> G {
    match load(members) {
      ListNode.Nil => 0,
      ListNode.Cons(mc, rest) =>
        member_kernel_size(mc) + block_kernel_size(rest),
    }
  }

  -- Compute the offset of member at member_idx within a block's expansion.
  -- Members before member_idx each contribute member_kernel_size entries.
  fn member_offset(members: List‹MutConst›, target_idx: G) -> G {
    match target_idx {
      0 => 0,
      _ =>
        match load(members) {
          ListNode.Cons(mc, rest) =>
            member_kernel_size(mc) + member_offset(rest, target_idx - 1),
        },
    }
  }

  -- Look up the kernel position for an address. Fast path: a ptr_val hit
  -- in the interned `addr_pos_map` (values stored as pos+1, so 0 = absent).
  -- Sound because ptr_val equality ⟹ content equality (the POSITIVE
  -- direction; see the invariant on `build_addr_pos_map`). On a miss — a
  -- de-interned pointer, or a genuine non-constant such as a blob ref —
  -- fall back to the content-based `address_eq` scan, which returns 0 when
  -- truly absent. Honest provers always intern, so the fallback adds ~0
  -- rows to the honest trace; the hot path is the O(log N) tree lookup.
  fn lookup_addr_pos(target: Addr, addr_pos_map: &RBTreeMap‹G›,
                     all_addrs: List‹Addr›, pos_map: List‹G›) -> G {
    let hit = rbtree_map_lookup_or_default(ptr_val(target), load(addr_pos_map), 0);
    match hit {
      0 => lookup_addr_pos_linear(target, all_addrs, pos_map),
      _ => hit - 1,
    }
  }

  -- Content-based fallback for `lookup_addr_pos`: O(N) parallel-list scan
  -- via `address_eq` (full 32-byte compare, sound under de-intern).
  -- Returns 0 if absent. Structurally identical to `lookup_block_start`;
  -- Aiur merges the two into one circuit.
  fn lookup_addr_pos_linear(target: Addr, all_addrs: List‹Addr›, pos_map: List‹G›) -> G {
    match load(all_addrs) {
      ListNode.Nil => 0,
      ListNode.Cons(addr, rest_addrs) =>
        match load(pos_map) {
          ListNode.Cons(pos, rest_pos) =>
            let eq = address_eq(target, addr);
            match eq {
              1 => pos,
              0 => lookup_addr_pos_linear(target, rest_addrs, rest_pos),
            },
        },
    }
  }

  -- Build the `ptr_val(addr) → (pos+1)` map keyed by every constant
  -- address. Serves two roles: `lookup_addr_pos`'s fast path (returns the
  -- kernel position) and `is_blob`'s membership test (present ⟺ constant).
  -- pos+1 so the lookup default 0 unambiguously means "absent". Head is
  -- inserted last (recurse first), so on any duplicate ptr_val the head
  -- wins — matching the linear scan's first-match.
  --
  -- ptr_val-key SOUNDNESS INVARIANT: a pointer maps to exactly one stored
  -- value (memory consistency), so ptr_val collision across DISTINCT
  -- contents is impossible — distinct addresses can never be conflated.
  -- A malicious prover's only freedom is de-interning (one content stored
  -- at several pointers), which makes a present key read as ABSENT. So a
  -- ptr_val-keyed map is sound ONLY where a false "absent" is conservative.
  -- `is_blob` is fine: a de-interned constant reads as a blob, content-bound
  -- and harmless. `lookup_addr_pos` is NOT fine on its own — a miss yields a
  -- usable position — so it falls back to the content-based `address_eq`
  -- scan on miss. Each Addr is also blake3-bound to its content and the
  -- checkEnv claim merkle-commits the address set.
  fn build_addr_pos_map(all_addrs: List‹Addr›, pos_map: List‹G›) -> RBTreeMap‹G› {
    match load(all_addrs) {
      ListNode.Nil => RBTreeMap.Nil,
      ListNode.Cons(addr, rest_addrs) =>
        match load(pos_map) {
          ListNode.Cons(pos, rest_pos) =>
            rbtree_map_insert(ptr_val(addr), pos + 1,
              build_addr_pos_map(rest_addrs, rest_pos)),
        },
    }
  }

  -- Find the start position of a block by its block address.
  fn lookup_block_start(target: Addr, block_addrs: List‹Addr›, block_starts: List‹G›) -> G {
    match load(block_addrs) {
      ListNode.Nil => 0,
      ListNode.Cons(addr, rest_addrs) =>
        match load(block_starts) {
          ListNode.Cons(start, rest_starts) =>
            let eq = address_eq(target, addr);
            match eq {
              1 => start,
              0 => lookup_block_start(target, rest_addrs, rest_starts),
            },
        },
    }
  }

  -- ============================================================================
  -- Layout pass: compute block start positions and total kernel size
  -- ============================================================================

  -- Returns 1 if `mptr` is in the seen list.
  fn is_mptr_seen(mptr: G, seen: List‹G›) -> G {
    match load(seen) {
      ListNode.Nil => 0,
      ListNode.Cons(s, rest) =>
        match s - mptr {
          0 => 1,
          _ => is_mptr_seen(mptr, rest),
        },
    }
  }

  -- Singleton-Indc Muts deduplication: structurally-identical singleton-Indc
  -- Muts wrappers (per-Lean-constant content) collapse to one canonical
  -- block to avoid emitting duplicate Ctor/Indc entries in `top` whose
  -- cross-references (induct_idx ↔ ctor_indices) wouldn't be consistent
  -- across the duplicates. Mirror Rust kernel's content-addressed dedup
  -- where the same Indc content has one shared kernel position.
  --
  -- Multi-member Muts (true mutual blocks) and non-singleton variants are
  -- not deduped (extract_muts_members_ptr returns 0 for them).
  fn extract_dedup_mptr(c: Constant) -> G {
    -- Dedup singleton-Indc Muts wrappers (Lean's per-constant canonical
    -- encoding). Key = full Constant.Mk ptr — Aiur store dedupes
    -- structurally identical Constants, so two wrapper aliases for the
    -- same logical Indc share this ptr. Inner-Indc-only dedup is too
    -- coarse: IXON canonicalization makes UInt8.Indc and UInt32.Indc
    -- collide at the Inductive.Mk level (literal width is a blob-ref
    -- index, not inline), but their wrapper Constants differ via refs.
    --
    -- Conservative: still gated on singleton-Indc Muts. Defn/Recr/multi-
    -- member Muts skip dedup (caller layout handles them positionally).
    match c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            match is_singleton_indc(members) {
              0 => 0,
              1 => ptr_val(store(c)),
            },
          _ => 0,
        },
    }
  }

  fn is_singleton_indc(members: List‹MutConst›) -> G {
    match load(members) {
      ListNode.Cons(m, rest) =>
        match load(rest) {
          ListNode.Nil =>
            match m {
              MutConst.Indc(_) => 1,
              _ => 0,
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Lookup canonical (first-occurrence) pos for an mptr in parallel
  -- (seen_mptrs, seen_poses) lists. Returns 0 if not found (caller
  -- guards via is_mptr_seen first).
  fn first_pos_for_mptr(mptr: G, seen_mptrs: List‹G›, seen_poses: List‹G›) -> G {
    match load(seen_mptrs) {
      ListNode.Nil => 0,
      ListNode.Cons(s, rest_m) =>
        match load(seen_poses) {
          ListNode.Cons(q, rest_p) =>
            match s - mptr {
              0 => q,
              _ => first_pos_for_mptr(mptr, rest_m, rest_p),
            },
        },
    }
  }

  fn compute_layout(
    consts: List‹&Constant›,
    addrs: List‹Addr›,
    pos: G
  ) -> (List‹Addr›, List‹G›, G) {
    compute_layout_walk(consts, addrs, pos, store(ListNode.Nil), store(ListNode.Nil))
  }

  fn compute_layout_walk(
    consts: List‹&Constant›,
    addrs: List‹Addr›,
    pos: G,
    seen_mptrs: List‹G›,
    seen_poses: List‹G›
  ) -> (List‹Addr›, List‹G›, G) {
    match load(consts) {
      ListNode.Nil => (store(ListNode.Nil), store(ListNode.Nil), pos),
      ListNode.Cons(&c, rest_consts) =>
        match load(addrs) {
          ListNode.Cons(addr, rest_addrs) =>
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.Muts(members) =>
                    let mptr = extract_dedup_mptr(c);
                    let dup = match mptr {
                      0 => 0,
                      _ => is_mptr_seen(mptr, seen_mptrs),
                    };
                    match dup {
                      1 =>
                        -- Duplicate Muts (same content, different wrapper addr).
                        -- Don't advance pos; record this wrapper's addr → first
                        -- occurrence's pos so refs via Expr.Ref(this_wrapper_addr)
                        -- and IPrj/CPrj/RPrj/DPrj.block_addr=this_wrapper_addr
                        -- resolve to canonical pos.
                        let first_pos = first_pos_for_mptr(mptr, seen_mptrs, seen_poses);
                        let (ba, bs, next) = compute_layout_walk(rest_consts, rest_addrs, pos, seen_mptrs, seen_poses);
                        (store(ListNode.Cons(addr, ba)),
                         store(ListNode.Cons(first_pos, bs)),
                         next),
                      0 =>
                        let size = block_kernel_size(members);
                        let new_seen_m = match mptr {
                          0 => seen_mptrs,
                          _ => store(ListNode.Cons(mptr, seen_mptrs)),
                        };
                        let new_seen_p = match mptr {
                          0 => seen_poses,
                          _ => store(ListNode.Cons(pos, seen_poses)),
                        };
                        let (ba, bs, next) = compute_layout_walk(rest_consts, rest_addrs, pos + size, new_seen_m, new_seen_p);
                        (store(ListNode.Cons(addr, ba)),
                         store(ListNode.Cons(pos, bs)),
                         next),
                    },
                  ConstantInfo.IPrj(_) =>
                    compute_layout_walk(rest_consts, rest_addrs, pos, seen_mptrs, seen_poses),
                  ConstantInfo.CPrj(_) =>
                    compute_layout_walk(rest_consts, rest_addrs, pos, seen_mptrs, seen_poses),
                  ConstantInfo.RPrj(_) =>
                    compute_layout_walk(rest_consts, rest_addrs, pos, seen_mptrs, seen_poses),
                  ConstantInfo.DPrj(_) =>
                    compute_layout_walk(rest_consts, rest_addrs, pos, seen_mptrs, seen_poses),
                  ConstantInfo.Defn(_) =>
                    compute_layout_walk(rest_consts, rest_addrs, pos + 1, seen_mptrs, seen_poses),
                  ConstantInfo.Axio(_) =>
                    compute_layout_walk(rest_consts, rest_addrs, pos + 1, seen_mptrs, seen_poses),
                  ConstantInfo.Quot(_) =>
                    compute_layout_walk(rest_consts, rest_addrs, pos + 1, seen_mptrs, seen_poses),
                  ConstantInfo.Recr(_) =>
                    compute_layout_walk(rest_consts, rest_addrs, pos + 1, seen_mptrs, seen_poses),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Position map pass: build a List‹G› parallel to all_addrs
  -- ============================================================================

  fn build_pos_map(
    consts: List‹&Constant›,
    addrs: List‹Addr›,
    block_addrs: List‹Addr›,
    block_starts: List‹G›,
    pos: G
  ) -> List‹G› {
    build_pos_map_walk(consts, addrs, block_addrs, block_starts, pos,
                       store(ListNode.Nil), store(ListNode.Nil))
  }

  fn build_pos_map_walk(
    consts: List‹&Constant›,
    addrs: List‹Addr›,
    block_addrs: List‹Addr›,
    block_starts: List‹G›,
    pos: G,
    seen_mptrs: List‹G›,
    seen_poses: List‹G›
  ) -> List‹G› {
    match load(consts) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(&c, rest_consts) =>
        match load(addrs) {
          ListNode.Cons(_, rest_addrs) =>
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.Muts(members) =>
                    let mptr = extract_dedup_mptr(c);
                    let dup = match mptr {
                      0 => 0,
                      _ => is_mptr_seen(mptr, seen_mptrs),
                    };
                    match dup {
                      1 =>
                        let first_pos = first_pos_for_mptr(mptr, seen_mptrs, seen_poses);
                        store(ListNode.Cons(first_pos,
                          build_pos_map_walk(rest_consts, rest_addrs, block_addrs, block_starts, pos, seen_mptrs, seen_poses))),
                      0 =>
                        let size = block_kernel_size(members);
                        let new_seen_m = match mptr {
                          0 => seen_mptrs,
                          _ => store(ListNode.Cons(mptr, seen_mptrs)),
                        };
                        let new_seen_p = match mptr {
                          0 => seen_poses,
                          _ => store(ListNode.Cons(pos, seen_poses)),
                        };
                        store(ListNode.Cons(pos,
                          build_pos_map_walk(rest_consts, rest_addrs, block_addrs, block_starts, pos + size, new_seen_m, new_seen_p))),
                    },
                  ConstantInfo.IPrj(prj) =>
                    match prj {
                      InductiveProj.Mk(idx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(block_info, _, _, _) =>
                            match block_info {
                              ConstantInfo.Muts(members) =>
                                let off = member_offset(members, flatten_u64(idx));
                                store(ListNode.Cons(block_start + off,
                                  build_pos_map_walk(rest_consts, rest_addrs, block_addrs, block_starts, pos, seen_mptrs, seen_poses))),
                            },
                        },
                    },
                  ConstantInfo.CPrj(prj) =>
                    match prj {
                      ConstructorProj.Mk(idx, cidx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(block_info, _, _, _) =>
                            match block_info {
                              ConstantInfo.Muts(members) =>
                                let mem_off = member_offset(members, flatten_u64(idx));
                                store(ListNode.Cons(block_start + mem_off + 1 + flatten_u64(cidx),
                                  build_pos_map_walk(rest_consts, rest_addrs, block_addrs, block_starts, pos, seen_mptrs, seen_poses))),
                            },
                        },
                    },
                  ConstantInfo.RPrj(prj) =>
                    match prj {
                      RecursorProj.Mk(idx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(block_info, _, _, _) =>
                            match block_info {
                              ConstantInfo.Muts(members) =>
                                let off = member_offset(members, flatten_u64(idx));
                                store(ListNode.Cons(block_start + off,
                                  build_pos_map_walk(rest_consts, rest_addrs, block_addrs, block_starts, pos, seen_mptrs, seen_poses))),
                            },
                        },
                    },
                  ConstantInfo.DPrj(prj) =>
                    match prj {
                      DefinitionProj.Mk(idx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(block_info, _, _, _) =>
                            match block_info {
                              ConstantInfo.Muts(members) =>
                                let off = member_offset(members, flatten_u64(idx));
                                store(ListNode.Cons(block_start + off,
                                  build_pos_map_walk(rest_consts, rest_addrs, block_addrs, block_starts, pos, seen_mptrs, seen_poses))),
                            },
                        },
                    },
                  _ =>
                    store(ListNode.Cons(pos,
                      build_pos_map_walk(rest_consts, rest_addrs, block_addrs, block_starts, pos + 1, seen_mptrs, seen_poses))),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Ref index building using position map
  -- ============================================================================

  fn build_ref_idxs_mapped(refs: List‹Addr›, addr_pos_map: &RBTreeMap‹G›,
                           all_addrs: List‹Addr›, pos_map: List‹G›) -> List‹G› {
    match load(refs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(addr, rest) =>
        let pos = lookup_addr_pos(addr, addr_pos_map, all_addrs, pos_map);
        store(ListNode.Cons(pos, build_ref_idxs_mapped(rest, addr_pos_map, all_addrs, pos_map))),
    }
  }

  -- Mirror of Rust kernel canonicalization (`ingress_compiled_names` /
  -- `resolve_all`): IXON can encode the same logical inductive via multiple
  -- wrapper addresses (singleton-Muts vs IPrj-rewrapping vs bundle-Muts).
  -- Aiur expands each wrapper into its own positional slots, so the same
  -- inductive lands at distinct kernel positions; refs traveling different
  -- IXON paths land on different positions and break the `Proj` / `Const`
  -- identity invariants assumed by infer / def_eq.
  --
  -- Dedup key: the `members` `List<MutConst>` Ptr. Aiur `store` content-
  -- dedupes structurally identical lists, so two Muts wrappers with the
  -- same member content (e.g. `[Indc(Nat)]`) share a Ptr regardless of the
  -- outer Constant.Mk wrapper's refs / sharing / univs differences.
  fn extract_muts_members_ptr(c: &Constant) -> G {
    -- Same dedup semantic as extract_dedup_mptr: singleton-Indc Muts only,
    -- keyed on full Constant ptr (so wrappers around different logical
    -- Indcs that happen to share IXON-canonical Indc.Mk content stay
    -- distinct via differing refs).
    match load(c) {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            match is_singleton_indc(members) {
              0 => 0,
              1 => ptr_val(c),
            },
          _ => 0,
        },
    }
  }

  fn find_canon_pos_for_mptr(mptr: G, seen_mptrs: List‹G›,
                              seen_poses: List‹G›, default_pos: G) -> G {
    match load(seen_mptrs) {
      ListNode.Nil => default_pos,
      ListNode.Cons(s, rest_m) =>
        match load(seen_poses) {
          ListNode.Cons(q, rest_q) =>
            match s - mptr {
              0 => q,
              _ => find_canon_pos_for_mptr(mptr, rest_m, rest_q, default_pos),
            },
        },
    }
  }

  fn canonicalize_pos_map_walk(consts: List‹&Constant›, pos_map: List‹G›,
                                seen_mptrs: List‹G›, seen_poses: List‹G›) -> List‹G› {
    match load(consts) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(c, rest_c) =>
        match load(pos_map) {
          ListNode.Cons(p, rest_p) =>
            let mptr = extract_muts_members_ptr(c);
            let canon_pos = match mptr {
              0 => p,
              _ => find_canon_pos_for_mptr(mptr, seen_mptrs, seen_poses, p),
            };
            let new_seen_mptrs = match mptr {
              0 => seen_mptrs,
              _ => store(ListNode.Cons(mptr, seen_mptrs)),
            };
            let new_seen_poses = match mptr {
              0 => seen_poses,
              _ => store(ListNode.Cons(canon_pos, seen_poses)),
            };
            store(ListNode.Cons(canon_pos,
              canonicalize_pos_map_walk(rest_c, rest_p, new_seen_mptrs, new_seen_poses))),
        },
    }
  }

  fn canonicalize_pos_map(consts: List‹&Constant›, pos_map: List‹G›) -> List‹G› {
    canonicalize_pos_map_walk(consts, pos_map, store(ListNode.Nil), store(ListNode.Nil))
  }

  -- Companion to `canonicalize_pos_map`: produces a `canonical_addr_map`
  -- parallel to `all_addrs`. Each entry records the FIRST address that
  -- yielded this Muts content. Used to canonicalize `block_addr` fields
  -- baked into Inductives by Aiur's positional convert step (without
  -- this, two distinct wrapper addrs produce Inductives with structurally
  -- different 10th fields — defeating store-Ptr equality).
  fn find_canon_addr_for_mptr(mptr: G, seen_mptrs: List‹G›,
                               seen_addrs: List‹Addr›,
                               default_addr: Addr) -> Addr {
    match load(seen_mptrs) {
      ListNode.Nil => default_addr,
      ListNode.Cons(s, rest_m) =>
        match load(seen_addrs) {
          ListNode.Cons(a, rest_a) =>
            match s - mptr {
              0 => a,
              _ => find_canon_addr_for_mptr(mptr, rest_m, rest_a, default_addr),
            },
        },
    }
  }

  fn canonicalize_addr_map_walk(addrs: List‹Addr›, consts: List‹&Constant›,
                                 seen_mptrs: List‹G›,
                                 seen_addrs: List‹Addr›) -> List‹Addr› {
    match load(addrs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(addr, rest_a) =>
        match load(consts) {
          ListNode.Cons(c, rest_c) =>
            let mptr = extract_muts_members_ptr(c);
            let canon_addr = match mptr {
              0 => addr,
              _ => find_canon_addr_for_mptr(mptr, seen_mptrs, seen_addrs, addr),
            };
            let new_seen_mptrs = match mptr {
              0 => seen_mptrs,
              _ => store(ListNode.Cons(mptr, seen_mptrs)),
            };
            let new_seen_addrs = match mptr {
              0 => seen_addrs,
              _ => store(ListNode.Cons(canon_addr, seen_addrs)),
            };
            store(ListNode.Cons(canon_addr,
              canonicalize_addr_map_walk(rest_a, rest_c, new_seen_mptrs, new_seen_addrs))),
        },
    }
  }

  fn canonicalize_addr_map(addrs: List‹Addr›, consts: List‹&Constant›) -> List‹Addr› {
    canonicalize_addr_map_walk(addrs, consts, store(ListNode.Nil), store(ListNode.Nil))
  }

  fn lookup_canon_addr(target: Addr, all_addrs: List‹Addr›,
                        canon_addrs: List‹Addr›) -> Addr {
    match load(all_addrs) {
      ListNode.Nil => target,
      ListNode.Cons(addr, rest_a) =>
        match load(canon_addrs) {
          ListNode.Cons(canon, rest_c) =>
            match address_eq(target, addr) {
              1 => canon,
              0 => lookup_canon_addr(target, rest_a, rest_c),
            },
        },
    }
  }

  -- Build kernel positions of each member's Indc within the block expansion.
  -- pos[i] = block_start + sum(member_kernel_size(members[0..i])).
  fn build_recur_idxs(members: List‹MutConst›, block_start: G, _member_idx: G) -> List‹G› {
    build_recur_idxs_walk(members, block_start)
  }

  fn build_recur_idxs_walk(members: List‹MutConst›, cur_pos: G) -> List‹G› {
    match load(members) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(mc, rest) =>
        store(ListNode.Cons(cur_pos,
          build_recur_idxs_walk(rest, cur_pos + member_kernel_size(mc)))),
    }
  }

  fn build_ctor_idxs(num_ctors: G, induct_pos: G, cidx: G) -> List‹G› {
    match num_ctors {
      0 => store(ListNode.Nil),
      _ =>
        store(ListNode.Cons(induct_pos + 1 + cidx,
          build_ctor_idxs(num_ctors - 1, induct_pos, cidx + 1))),
    }
  }

  fn build_rule_ctor_idxs(members: List‹MutConst›, block_start: G, _member_idx: G) -> List‹G› {
    build_rule_ctor_idxs_walk(members, block_start)
  }

  fn build_rule_ctor_idxs_walk(members: List‹MutConst›, cur_pos: G) -> List‹G› {
    match load(members) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(mc, rest) =>
        match mc {
          MutConst.Indc(ind) =>
            match ind {
              Inductive.Mk(_, _, _, _, _, _, _, _, ctors) =>
                let num_ctors = list_length(ctors);
                let this_ctors = build_ctor_idxs(num_ctors, cur_pos, 0);
                let rest_ctors = build_rule_ctor_idxs_walk(rest,
                  cur_pos + 1 + num_ctors);
                list_concat(this_ctors, rest_ctors),
            },
          MutConst.Defn(_) =>
            build_rule_ctor_idxs_walk(rest, cur_pos + 1),
          MutConst.Recr(_) =>
            build_rule_ctor_idxs_walk(rest, cur_pos + 1),
        },
    }
  }

  -- ============================================================================
  -- ConvertInput construction: expand Muts blocks into kernel constants
  -- ============================================================================

  -- Returns 1 if `members` contains at least one MutConst.Indc, else 0.
  fn members_have_indc(members: List‹MutConst›) -> G {
    match load(members) {
      ListNode.Nil => 0,
      ListNode.Cons(mc, rest) =>
        match mc {
          MutConst.Indc(_) => 1,
          _ => members_have_indc(rest),
        },
    }
  }

  -- Deref Expr.Share via the constant's sharing list.
  fn deref_share(e: Expr, sharing: List‹&Expr›) -> Expr {
    match e {
      Expr.Share(idx) => deref_share(load(list_lookup_u64(sharing, idx)), sharing),
      _ => e,
    }
  }

  -- Walk a recursor's typ skipping `n` leading Alls; return body Expr.
  fn peel_n_alls_expr(e: Expr, n: G, sharing: List‹&Expr›) -> Expr {
    match n {
      0 => deref_share(e, sharing),
      _ =>
        match deref_share(e, sharing) {
          Expr.All(_, body_ref) => peel_n_alls_expr(load(body_ref), n - 1, sharing),
          _ => e,
        },
    }
  }

  -- Take an App-spine expression's head.
  fn collect_app_spine_expr_head(e: Expr, sharing: List‹&Expr›) -> Expr {
    match deref_share(e, sharing) {
      Expr.App(f_ref, _) => collect_app_spine_expr_head(load(f_ref), sharing),
      other => other,
    }
  }

  -- Extract the inductive's address from a recursor's typ.
  -- Walks past `n_skip = params + motives + minors + indices` foralls,
  -- then takes the next forall's domain (major's type), peels the App-spine,
  -- and reads the head Ref's address from the recursor's `refs` list.
  -- Returns `[0;32]` if the head isn't a Ref (e.g. mutual self-rec via Rec).
  fn rec_typ_to_inductive_addr(typ: Expr, n_skip: G, refs: List‹Addr›,
                                sharing: List‹&Expr›) -> Addr {
    let after_skip = peel_n_alls_expr(typ, n_skip, sharing);
    match after_skip {
      Expr.All(major_ty_ref, _) =>
        let head = collect_app_spine_expr_head(load(major_ty_ref), sharing);
        match head {
          Expr.Ref(ref_idx_bytes, _) => list_lookup(refs, flatten_u64(ref_idx_bytes)),
          _ => store([0u8; 32]),
        },
      _ => store([0u8; 32]),
    }
  }

  -- For aux-only Recr blocks (Muts containing only Recrs/Defns, e.g. produced
  -- by `compile_aux_block` in src/ix/compile/mutual.rs), the rule_ctor_idxs
  -- must come from the *original* inductive block referenced by the enclosing
  -- Constant's refs, not from `members` (which has no Indc). Resolve the
  -- block by extracting the inductive's address from the recursor's typ
  -- (rather than heuristically matching ctor counts among refs, which fails
  -- when multiple in-scope inductives share the same number of ctors).
  fn build_aux_recr_ctor_idxs(
    recr: Recursor,
    refs: List‹Addr›,
    sharing: List‹&Expr›,
    all_addrs: List‹Addr›,
    block_addrs: List‹Addr›,
    block_starts: List‹G›
  ) -> List‹G› {
    match recr {
      Recursor.Mk(_, _, _, params, indices, motives, minors, &typ, _) =>
        let n_skip = ((flatten_u64(params) + flatten_u64(motives))
                      + flatten_u64(minors)) + flatten_u64(indices);
        let ind_addr = rec_typ_to_inductive_addr(typ, n_skip, refs, sharing);
        let ind_const = load_verified_constant(ind_addr);
        match ind_const {
          Constant.Mk(info, _, _, _) =>
            match info {
              ConstantInfo.IPrj(prj) =>
                match prj {
                  InductiveProj.Mk(member_idx, block_addr) =>
                    let block_const = load_verified_constant(block_addr);
                    match block_const {
                      Constant.Mk(bi, _, _, _) =>
                        match bi {
                          ConstantInfo.Muts(other_members) =>
                            let bs = lookup_block_start(block_addr, block_addrs, block_starts);
                            -- Mutual block: each recursor's rules cover only
                            -- its OWN inductive's ctors. Slice the global
                            -- rule_ctor_idxs to just this member's ctors.
                            extract_member_ctor_idxs(other_members, bs,
                              flatten_u64(member_idx)),
                        },
                    },
                },
            },
        },
    }
  }

  -- Extract kernel ctor positions for member at `target_idx` in `members`.
  fn extract_member_ctor_idxs(members: List‹MutConst›, block_start: G,
                              target_idx: G) -> List‹G› {
    extract_member_ctor_idxs_walk(members, block_start, target_idx, 0)
  }

  fn extract_member_ctor_idxs_walk(members: List‹MutConst›, cur_pos: G,
                                    target_idx: G, idx: G) -> List‹G› {
    match load(members) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(mc, rest) =>
        let mc_size = member_kernel_size(mc);
        match eq_zero(idx - target_idx) {
          1 =>
            match mc {
              MutConst.Indc(ind) =>
                match ind {
                  Inductive.Mk(_, _, _, _, _, _, _, _, ctors) =>
                    build_ctor_idxs(list_length(ctors), cur_pos, 0),
                },
              _ => store(ListNode.Nil),
            },
          0 => extract_member_ctor_idxs_walk(rest, cur_pos + mc_size,
                                              target_idx, idx + 1),
        },
    }
  }

  -- Expand a single MutConst member into ConvertInputs.
  -- For Indc: emits 1 Induct + N Ctors.
  -- For Recr: emits 1 Rec.
  -- For Defn: emits 1 Defn.
  fn expand_member(
    mc: MutConst,
    ctx: ConvertCtx,
    members: List‹MutConst›,
    block_start: G,
    member_idx: G,
    refs: List‹Addr›,
    all_addrs: List‹Addr›,
    block_addrs: List‹Addr›,
    block_starts: List‹G›,
    block_addr: Addr
  ) -> List‹&ConvertInput› {
    match mc {
      MutConst.Indc(ind) =>
        match ind {
          Inductive.Mk(_, _, _, _, _, _, _, _, ctors) =>
            let num_ctors = list_length(ctors);
            let induct_pos = block_start + member_offset(members, member_idx);
            let ctor_idxs = build_ctor_idxs(num_ctors, induct_pos, 0);
            let indc_input = ConvertInput.Mk(ctx, ConvertKind.CKIndc(ind, ctor_idxs, block_addr));
            let ctor_inputs = expand_ctors(ctors, ctx, induct_pos);
            store(ListNode.Cons(store(indc_input), ctor_inputs)),
        },
      MutConst.Recr(recr) =>
        match members_have_indc(members) {
          1 =>
            let rule_ctor_idxs = build_rule_ctor_idxs(members, block_start, 0);
            let input = ConvertInput.Mk(ctx, ConvertKind.CKRecr(recr, rule_ctor_idxs, block_addr));
            store(ListNode.Cons(store(input), store(ListNode.Nil))),
          0 =>
            let sharing = match ctx { ConvertCtx.Mk(s, _, _, _, _) => s, };
            let rule_ctor_idxs =
              build_aux_recr_ctor_idxs(recr, refs, sharing, all_addrs, block_addrs, block_starts);
            let input = ConvertInput.Mk(ctx, ConvertKind.CKRecr(recr, rule_ctor_idxs, block_addr));
            store(ListNode.Cons(store(input), store(ListNode.Nil))),
        },
      MutConst.Defn(defn) =>
        -- Muts-block defs default to Regular(0) (hint=1). Per-member hints
        -- aren't currently plumbed; standalone Defns get their actual hint
        -- via load_constant_hint in build_convert_inputs.
        let input = ConvertInput.Mk(ctx, ConvertKind.CKDefn(defn, 1));
        store(ListNode.Cons(store(input), store(ListNode.Nil))),
    }
  }

  fn expand_ctors(ctors: List‹Constructor›, ctx: ConvertCtx, induct_pos: G) -> List‹&ConvertInput› {
    match load(ctors) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(ctor, rest) =>
        let input = ConvertInput.Mk(ctx, ConvertKind.CKCtor(ctor, induct_pos));
        store(ListNode.Cons(store(input), expand_ctors(rest, ctx, induct_pos))),
    }
  }

  fn expand_members(
    members: List‹MutConst›,
    ctx: ConvertCtx,
    all_members: List‹MutConst›,
    block_start: G,
    member_idx: G,
    refs: List‹Addr›,
    all_addrs: List‹Addr›,
    block_addrs: List‹Addr›,
    block_starts: List‹G›,
    block_addr: Addr
  ) -> List‹&ConvertInput› {
    match load(members) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(mc, rest) =>
        let this = expand_member(mc, ctx, all_members, block_start, member_idx,
          refs, all_addrs, block_addrs, block_starts, block_addr);
        let more = expand_members(rest, ctx, all_members, block_start, member_idx + 1,
          refs, all_addrs, block_addrs, block_starts, block_addr);
        list_concat(this, more),
    }
  }

  -- Build the full List‹&ConvertInput› by walking loaded constants.
  -- Muts blocks are expanded into their members.
  -- Projections are skipped (handled via block expansion).
  -- Standalone constants are converted directly.
  -- Unpack head + tail of an addrs list (parallel walker for build_convert_inputs).
  fn unpack_head_addr(addrs: List‹Addr›) -> (Addr, List‹Addr›) {
    match load(addrs) {
      ListNode.Cons(a, r) => (a, r),
    }
  }

  fn build_convert_inputs(
    consts: List‹&Constant›,
    cur_addrs: List‹Addr›,
    all_addrs: List‹Addr›,
    pos_map: List‹G›,
    canon_addrs: List‹Addr›,
    block_addrs: List‹Addr›,
    block_starts: List‹G›,
    pos: G
  ) -> List‹&ConvertInput› {
    -- Built once here; threaded as the fast-path index for `lookup_addr_pos`.
    let addr_pos_map = store(build_addr_pos_map(all_addrs, pos_map));
    build_convert_inputs_walk(consts, cur_addrs, all_addrs, addr_pos_map, pos_map,
                              canon_addrs, block_addrs, block_starts, pos,
                              store(ListNode.Nil))
  }

  fn build_convert_inputs_walk(
    consts: List‹&Constant›,
    cur_addrs: List‹Addr›,
    all_addrs: List‹Addr›,
    addr_pos_map: &RBTreeMap‹G›,
    pos_map: List‹G›,
    canon_addrs: List‹Addr›,
    block_addrs: List‹Addr›,
    block_starts: List‹G›,
    pos: G,
    seen_mptrs: List‹G›
  ) -> List‹&ConvertInput› {
    match load(consts) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(&c, rest) =>
        match unpack_head_addr(cur_addrs) {
          (head_addr, rest_addrs) =>
            match c {
              Constant.Mk(info, sharing, refs, univs) =>
                match info {
                  ConstantInfo.Muts(members) =>
                    let mptr = extract_dedup_mptr(c);
                    let dup = match mptr {
                      0 => 0,
                      _ => is_mptr_seen(mptr, seen_mptrs),
                    };
                    match dup {
                      1 =>
                        -- Duplicate Muts: skip emission (canonical Muts already
                        -- emitted). Don't advance pos. Refs to this wrapper
                        -- resolve to canonical pos via pos_map dedup.
                        build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map,
                          canon_addrs, block_addrs, block_starts, pos, seen_mptrs),
                      0 =>
                        let new_seen = match mptr {
                          0 => seen_mptrs,
                          _ => store(ListNode.Cons(mptr, seen_mptrs)),
                        };
                        let size = block_kernel_size(members);
                        let canon_block_start = lookup_addr_pos(head_addr, addr_pos_map, all_addrs, pos_map);
                        let canon_addr = lookup_canon_addr(head_addr, all_addrs, canon_addrs);
                        let ref_idxs = build_ref_idxs_mapped(refs, addr_pos_map, all_addrs, pos_map);
                        let lit_blobs = build_lit_blobs(refs, addr_pos_map);
                        let recur_idxs = build_recur_idxs(members, canon_block_start, 0);
                        let ctx = ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs);
                        let expanded = expand_members(members, ctx, members, canon_block_start, 0,
                          refs, all_addrs, block_addrs, block_starts, canon_addr);
                        let more = build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map,
                          canon_addrs, block_addrs, block_starts, pos + size, new_seen);
                        list_concat(expanded, more),
                    },
                  ConstantInfo.IPrj(_) =>
                    build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map, canon_addrs, block_addrs, block_starts, pos, seen_mptrs),
                  ConstantInfo.CPrj(_) =>
                    build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map, canon_addrs, block_addrs, block_starts, pos, seen_mptrs),
                  ConstantInfo.RPrj(_) =>
                    build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map, canon_addrs, block_addrs, block_starts, pos, seen_mptrs),
                  ConstantInfo.DPrj(_) =>
                    build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map, canon_addrs, block_addrs, block_starts, pos, seen_mptrs),
                  ConstantInfo.Defn(defn) =>
                    let ref_idxs = build_ref_idxs_mapped(refs, addr_pos_map, all_addrs, pos_map);
                    let lit_blobs = build_lit_blobs(refs, addr_pos_map);
                    let recur_idxs = store(ListNode.Cons(pos, store(ListNode.Nil)));
                    let ctx = ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs);
                    let hint = #load_constant_hint(head_addr);
                    let input = ConvertInput.Mk(ctx, ConvertKind.CKDefn(defn, hint));
                    store(ListNode.Cons(store(input),
                      build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map, canon_addrs, block_addrs, block_starts, pos + 1, seen_mptrs))),
                  ConstantInfo.Axio(axio) =>
                    let ref_idxs = build_ref_idxs_mapped(refs, addr_pos_map, all_addrs, pos_map);
                    let lit_blobs = build_lit_blobs(refs, addr_pos_map);
                    let ctx = ConvertCtx.Mk(sharing, ref_idxs, store(ListNode.Nil), lit_blobs, univs);
                    let input = ConvertInput.Mk(ctx, ConvertKind.CKAxio(axio));
                    store(ListNode.Cons(store(input),
                      build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map, canon_addrs, block_addrs, block_starts, pos + 1, seen_mptrs))),
                  ConstantInfo.Quot(quot) =>
                    let ref_idxs = build_ref_idxs_mapped(refs, addr_pos_map, all_addrs, pos_map);
                    let lit_blobs = build_lit_blobs(refs, addr_pos_map);
                    let ctx = ConvertCtx.Mk(sharing, ref_idxs, store(ListNode.Nil), lit_blobs, univs);
                    let input = ConvertInput.Mk(ctx, ConvertKind.CKQuot(quot));
                    store(ListNode.Cons(store(input),
                      build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map, canon_addrs, block_addrs, block_starts, pos + 1, seen_mptrs))),
                  ConstantInfo.Recr(recr) =>
                    let ref_idxs = build_ref_idxs_mapped(refs, addr_pos_map, all_addrs, pos_map);
                    let lit_blobs = build_lit_blobs(refs, addr_pos_map);
                    -- Resolve the recursor's inductive via typ-based lookup:
                    -- peel n_skip foralls of `recr.typ` to reach the major's
                    -- type, take its head, lookup `refs[head_ref_idx]`. The
                    -- ctor-count heuristic in `find_matching_block_addr` picks
                    -- the wrong block when multiple in-scope inductives share
                    -- the same ctor count.
                    let rule_ctor_idxs = build_aux_recr_ctor_idxs(
                      recr, refs, sharing, all_addrs, block_addrs, block_starts);
                    let n_skip = match recr {
                      Recursor.Mk(_, _, _, params, indices, motives, minors, _, _) =>
                        ((flatten_u64(params) + flatten_u64(motives))
                          + flatten_u64(minors)) + flatten_u64(indices),
                    };
                    let typ = match recr {
                      Recursor.Mk(_, _, _, _, _, _, _, &typ, _) => typ,
                    };
                    let ind_addr = rec_typ_to_inductive_addr(typ, n_skip, refs, sharing);
                    let ind_const = load_verified_constant(ind_addr);
                    let block_addr = match ind_const {
                      Constant.Mk(info, _, _, _) =>
                        match info {
                          ConstantInfo.IPrj(prj) =>
                            match prj { InductiveProj.Mk(_, ba) => ba, },
                        },
                    };
                    let recur_idxs = store(ListNode.Cons(pos, store(ListNode.Nil)));
                    let ctx = ConvertCtx.Mk(sharing, ref_idxs, recur_idxs, lit_blobs, univs);
                    let input = ConvertInput.Mk(ctx, ConvertKind.CKRecr(recr, rule_ctor_idxs, block_addr));
                    store(ListNode.Cons(store(input),
                      build_convert_inputs_walk(rest, rest_addrs, all_addrs, addr_pos_map, pos_map, canon_addrs, block_addrs, block_starts, pos + 1, seen_mptrs))),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Loading and dependency tracking
  -- ============================================================================

  -- Check if an address is already in a list
  fn address_in_list(addr: Addr, list: List‹Addr›) -> G {
    match load(list) {
      ListNode.Nil => 0,
      ListNode.Cons(a, rest) =>
        let eq = address_eq(addr, a);
        match eq {
          1 => 1,
          0 => address_in_list(addr, rest),
        },
    }
  }

  -- Recursively load constants and their transitive dependencies.
  -- Processes one address at a time from a worklist, deduplicating by
  -- checking the visited set. Blob addresses are detected via io_get_info:
  -- the prover provides len=0 for blobs (which are not serialized constants).
  -- For projection constants (IPrj, CPrj, RPrj, DPrj), also follows the
  -- Muts block's refs so that all dependencies of block members are loaded.
  fn load_with_deps(
    addr: Addr,
    worklist: List‹Addr›,
    visited_addrs: List‹Addr›,
    visited_consts: List‹&Constant›,
    visited_set: RBTreeMap‹G›
  ) -> (List‹Addr›, List‹&Constant›) {
    let already = rbtree_map_lookup_or_default(ptr_val(addr), visited_set, 0);
    match already {
      1 =>
        match load(worklist) {
          ListNode.Nil => (visited_addrs, visited_consts),
          ListNode.Cons(next, rest) =>
            load_with_deps(next, rest, visited_addrs, visited_consts, visited_set),
        },
      _ =>
        -- Check if this address has constant data in IOBuffer.
        -- io_get_info is unconstrained; the prover provides (0, 0) for blob addresses.
        -- Soundness: if the prover lies and skips a real constant, type checking will fail.
        let (_, len) = io_get_info(0, load(addr));
        match len {
          0 =>
            -- Blob address: skip (blob values are loaded on demand in build_lit_blobs)
            match load(worklist) {
              ListNode.Nil => (visited_addrs, visited_consts),
              ListNode.Cons(next, rest) =>
                load_with_deps(next, rest, visited_addrs, visited_consts, visited_set),
            },
          _ =>
            let new_addrs = store(ListNode.Cons(addr, visited_addrs));
            let new_set = rbtree_map_insert(ptr_val(addr), 1, visited_set);
            let constant = load_verified_constant(addr);
            let new_consts = store(ListNode.Cons(store(constant), visited_consts));
            match constant {
              Constant.Mk(info, _, refs, _) =>
                let block_addr = get_proj_block_addr(info);
                match address_eq(block_addr, store([0u8; 32])) {
                  1 =>
                    let combined_refs = list_concat(refs, store(ListNode.Nil));
                    let next_worklist = list_concat(combined_refs, worklist);
                    match load(next_worklist) {
                      ListNode.Nil => (new_addrs, new_consts),
                      ListNode.Cons(next, rest) =>
                        load_with_deps(next, rest, new_addrs, new_consts, new_set),
                    },
                  0 =>
                    let combined_refs = list_concat(
                      refs,
                      store(ListNode.Cons(block_addr, store(ListNode.Nil)))
                    );
                    let next_worklist = list_concat(combined_refs, worklist);
                    match load(next_worklist) {
                      ListNode.Nil => (new_addrs, new_consts),
                      ListNode.Cons(next, rest) =>
                        load_with_deps(next, rest, new_addrs, new_consts, new_set),
                    },
                },
            },
        },
    }
  }

  -- Transitively loads all dependencies of the target constant from IOBuffer,
  -- verifies blake3 hashes then converts to kernel types.
  fn ingress(target_addr: Addr) -> List‹&KConstantInfo› {
    let (all_addrs, all_consts) = load_with_deps(
      target_addr, store(ListNode.Nil), store(ListNode.Nil), store(ListNode.Nil), RBTreeMap.Nil);
    let (block_addrs, block_starts, _total) = compute_layout(all_consts, all_addrs, 0);
    let pos_map_naive = build_pos_map(all_consts, all_addrs, block_addrs, block_starts, 0);
    let pos_map = canonicalize_pos_map(all_consts, pos_map_naive);
    let canon_addrs = canonicalize_addr_map(all_addrs, all_consts);
    let inputs = build_convert_inputs(all_consts, all_addrs, all_addrs, pos_map, canon_addrs, block_addrs, block_starts, 0);
    convert_all(inputs)
  }

  -- Build a List‹Addr› parallel to k_consts: addrs[i] = blake3 address
  -- of the kernel const at position i. Walks (all_addrs, pos_map) and for
  -- each kernel position emits the addr that resolves to it.
  -- Address-keyed dispatch: primitives compared by address, not by
  -- precomputed positional index.
  fn build_addrs_aligned(i: G, total: G,
                         all_addrs: List‹Addr›,
                         all_consts: List‹&Constant›,
                         pos_map: List‹G›) -> List‹Addr› {
    match i - total {
      0 => store(ListNode.Nil),
      _ =>
        let addr = find_best_addr_at_pos(i, all_addrs, all_consts, pos_map);
        store(ListNode.Cons(addr, build_addrs_aligned(i + 1, total, all_addrs, all_consts, pos_map))),
    }
  }

  -- Returns 1 if `c` is a projection constant (IPrj/CPrj/RPrj/DPrj).
  -- Used to prioritize per-member primitive addresses over the parent
  -- Muts block's content-hash when both share the same kernel position.
  fn is_proj_const(c: &Constant) -> G {
    match load(c) {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.IPrj(_) => 1,
          ConstantInfo.CPrj(_) => 1,
          ConstantInfo.RPrj(_) => 1,
          ConstantInfo.DPrj(_) => 1,
          _ => 0,
        },
    }
  }

  -- First pass: find a projection-constant entry whose pos_map = `target`.
  -- Per-member primitive addrs (e.g. `nat_addr`) live on IPrj entries;
  -- the parent Muts block has the BLOCK content-hash, not the member's.
  -- So we prefer the IPrj-derived addr at a shared pos.
  fn find_prj_addr_at_pos(target: G, all_addrs: List‹Addr›,
                           all_consts: List‹&Constant›,
                           pos_map: List‹G›) -> (G, Addr) {
    match load(all_addrs) {
      ListNode.Nil => (0, store([0u8; 32])),
      ListNode.Cons(addr, rest_a) =>
        match load(all_consts) {
          ListNode.Cons(c, rest_c) =>
            match load(pos_map) {
              ListNode.Cons(pos, rest_p) =>
                let pos_match = eq_zero(pos - target);
                let prj = is_proj_const(c);
                match pos_match * prj {
                  1 => (1, addr),
                  _ => find_prj_addr_at_pos(target, rest_a, rest_c, rest_p),
                },
            },
        },
    }
  }

  -- Find the address in all_addrs whose pos_map entry equals `target`.
  -- Returns all-zero `Addr` if not found — happens for kernel
  -- positions that are only reached via within-block peer refs
  -- (Expr.Rec) and never loaded as a standalone ref. Primitive
  -- dispatch via `address_eq` against hardcoded non-zero addresses
  -- treats zero-addr as "no primitive here", falling through.
  fn find_addr_at_pos(target: G, all_addrs: List‹Addr›, pos_map: List‹G›) -> Addr {
    match load(all_addrs) {
      ListNode.Nil => store([0u8; 32]),
      ListNode.Cons(addr, rest_addrs) =>
        match load(pos_map) {
          ListNode.Cons(pos, rest_pos) =>
            match pos - target {
              0 => addr,
              _ => find_addr_at_pos(target, rest_addrs, rest_pos),
            },
        },
    }
  }

  -- Wrapper: prefer Prj-derived addr at shared pos, fall back to any.
  fn find_best_addr_at_pos(target: G, all_addrs: List‹Addr›,
                            all_consts: List‹&Constant›,
                            pos_map: List‹G›) -> Addr {
    match find_prj_addr_at_pos(target, all_addrs, all_consts, pos_map) {
      (1, addr) => addr,
      (0, _) => find_addr_at_pos(target, all_addrs, pos_map),
    }
  }

  -- ============================================================================
  -- Tree-based addr table construction.
  --
  -- Replaces the O(N²) `build_addrs_aligned` (which scanned `all_addrs`
  -- once per kernel position). Builds a pos→Addr RBTreeMap by walking
  -- the input lists twice: non-PRJ pass first, PRJ pass second so PRJ
  -- entries overwrite non-PRJ at shared kernel positions (per the
  -- PRJ-priority semantics in `find_best_addr_at_pos`). Then emits a
  -- position-indexed `List‹Addr›` for downstream compatibility.
  -- O(N log N) build + emit total.
  -- ============================================================================

  fn build_addr_tree_walk(addrs: List‹Addr›,
                          consts: List‹&Constant›,
                          pos_map: List‹G›,
                          want_prj: G,
                          tree: RBTreeMap‹Addr›) -> RBTreeMap‹Addr› {
    match load(addrs) {
      ListNode.Nil => tree,
      ListNode.Cons(addr, rest_a) =>
        match load(consts) {
          ListNode.Cons(c, rest_c) =>
            match load(pos_map) {
              ListNode.Cons(pos, rest_p) =>
                let is_prj = is_proj_const(c);
                match is_prj - want_prj {
                  0 =>
                    let new_tree = rbtree_map_insert(pos, addr, tree);
                    build_addr_tree_walk(rest_a, rest_c, rest_p, want_prj, new_tree),
                  _ =>
                    build_addr_tree_walk(rest_a, rest_c, rest_p, want_prj, tree),
                },
            },
        },
    }
  }

  fn build_addr_tree(all_addrs: List‹Addr›,
                     all_consts: List‹&Constant›,
                     pos_map: List‹G›) -> RBTreeMap‹Addr› {
    let t = build_addr_tree_walk(all_addrs, all_consts, pos_map, 0, RBTreeMap.Nil);
    build_addr_tree_walk(all_addrs, all_consts, pos_map, 1, t)
  }

  -- Apply ctor overrides as tree updates. Each (pos, addr) in
  -- `overrides` replaces the entry at `pos`. O(K log N) for K overrides.
  fn apply_ctor_overrides_tree(overrides: List‹(G, Addr)›,
                               tree: RBTreeMap‹Addr›) -> RBTreeMap‹Addr› {
    match load(overrides) {
      ListNode.Nil => tree,
      ListNode.Cons(p, rest) =>
        match p {
          (pos, addr) =>
            let new_tree = rbtree_map_insert(pos, addr, tree);
            apply_ctor_overrides_tree(rest, new_tree),
        },
    }
  }

  -- Emit the position-indexed `List‹Addr›` from a pos→Addr tree.
  -- Positions absent from the tree map to `zero_addr` (matches the
  -- semantics of `find_best_addr_at_pos` which returned a zero addr
  -- for uncovered positions).
  fn emit_addrs_from_tree(i: G, total: G, tree: RBTreeMap‹Addr›,
                          zero_addr: Addr) -> List‹Addr› {
    match total - i {
      0 => store(ListNode.Nil),
      _ =>
        let addr = rbtree_map_lookup_or_default(i, tree, zero_addr);
        store(ListNode.Cons(addr,
          emit_addrs_from_tree(i + 1, total, tree, zero_addr))),
    }
  }

  -- Returns `(k_consts, addrs)` where `addrs[i]` is the blake3 address of
  -- the kernel const at position `i`. Primitive detection downstream
  -- compares addresses via `address_eq` against hardcoded constants
  -- in `Primitive.lean`.
  -- Build override list (ctor_pos → ctor_addr) by walking every loaded
  -- IPrj. For each, find the inductive's ctor count from the parent
  -- block and synthesize each ctor's CPrj content-hash via in-Aiur
  -- `put_constant` + `blake3`. No IO buffer side channel needed: every
  -- input (idx, block_addr, cidx) is either taken from a `load_verified_*`
  -- result or a deterministic loop counter, so the resulting addresses
  -- are derived from already-trusted data.
  fn build_ctor_overrides(all_consts: List‹&Constant›, all_addrs: List‹Addr›,
                          block_addrs: List‹Addr›, block_starts: List‹G›)
                          -> List‹(G, Addr)› {
    match load(all_consts) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(&c, rest_c) =>
        match load(all_addrs) {
          ListNode.Cons(_, rest_a) =>
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.IPrj(prj) =>
                    match prj {
                      InductiveProj.Mk(idx, block_addr) =>
                        let block_start = lookup_block_start(block_addr, block_addrs, block_starts);
                        let block_const = load_verified_constant(block_addr);
                        match block_const {
                          Constant.Mk(bi, _, _, _) =>
                            match bi {
                              ConstantInfo.Muts(members) =>
                                let mem_off = member_offset(members, flatten_u64(idx));
                                let base_pos = block_start + mem_off + 1;
                                let n_ctors = inductive_ctor_count_at(members, flatten_u64(idx));
                                let new_pairs = build_ctor_pairs_computed(idx, block_addr, base_pos, n_ctors, 0);
                                list_concat(new_pairs,
                                  build_ctor_overrides(rest_c, rest_a, block_addrs, block_starts)),
                              _ =>
                                build_ctor_overrides(rest_c, rest_a, block_addrs, block_starts),
                            },
                        },
                    },
                  _ =>
                    build_ctor_overrides(rest_c, rest_a, block_addrs, block_starts),
                },
            },
        },
    }
  }

  -- Number of constructors of the Inductive at `target_idx` within the
  -- given Muts members. Returns 0 if the indexed member isn't an Inductive.
  fn inductive_ctor_count_at(members: List‹MutConst›, target_idx: G) -> G {
    inductive_ctor_count_walk(members, target_idx, 0)
  }

  fn inductive_ctor_count_walk(members: List‹MutConst›, target_idx: G, i: G) -> G {
    match load(members) {
      ListNode.Nil => 0,
      ListNode.Cons(mc, rest) =>
        match i - target_idx {
          0 =>
            match mc {
              MutConst.Indc(ind) =>
                match ind {
                  Inductive.Mk(_, _, _, _, _, _, _, _, ctors) =>
                    list_length(ctors),
                },
              _ => 0,
            },
          _ => inductive_ctor_count_walk(rest, target_idx, i + 1),
        },
    }
  }

  fn build_ctor_pairs_computed(idx: U64, block: Addr,
                                base_pos: G, n_ctors: G, cidx: G)
                                -> List‹(G, Addr)› {
    match n_ctors - cidx {
      0 => store(ListNode.Nil),
      _ =>
        let addr = cprj_content_addr(idx, cidx, block);
        store(ListNode.Cons((base_pos + cidx, addr),
          build_ctor_pairs_computed(idx, block, base_pos, n_ctors, cidx + 1))),
    }
  }

  -- Compute the CPrj's blake3 content-hash from `(idx, cidx, block)` by
  -- constructing the same `Constant{ info := CPrj{...}, ... }` shape Lean
  -- compile uses, serializing it in-Aiur, and hashing. No external trust
  -- needed — every input is derived from a `load_verified_*` result or a
  -- loop counter.
  fn cprj_content_addr(idx: U64, cidx: G, block: Addr) -> Addr {
    let prj = ConstructorProj.Mk(idx, [u8_from_field_unsafe(cidx), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], block);
    let info = ConstantInfo.CPrj(prj);
    let cnst = Constant.Mk(info, store(ListNode.Nil),
                                  store(ListNode.Nil),
                                  store(ListNode.Nil));
    let bytes = put_constant(cnst, store(ListNode.Nil));
    let h = blake3(bytes);
    store([h[0][0], h[0][1], h[0][2], h[0][3],
     h[1][0], h[1][1], h[1][2], h[1][3],
     h[2][0], h[2][1], h[2][2], h[2][3],
     h[3][0], h[3][1], h[3][2], h[3][3],
     h[4][0], h[4][1], h[4][2], h[4][3],
     h[5][0], h[5][1], h[5][2], h[5][3],
     h[6][0], h[6][1], h[6][2], h[6][3],
     h[7][0], h[7][1], h[7][2], h[7][3]])
  }


  -- Walk addrs at increasing positions; if an override exists for the
  -- current position, replace the entry. Lets us inject ctor addresses
  -- into the per-position address list without restructuring the rest.
  fn apply_ctor_overrides(addrs: List‹Addr›,
                          overrides: List‹(G, Addr)›, pos: G)
                          -> List‹Addr› {
    match load(addrs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(addr, rest) =>
        let new_addr = lookup_override(overrides, pos, addr);
        store(ListNode.Cons(new_addr,
          apply_ctor_overrides(rest, overrides, pos + 1))),
    }
  }

  fn lookup_override(overrides: List‹(G, Addr)›, pos: G,
                     default: Addr) -> Addr {
    match load(overrides) {
      ListNode.Nil => default,
      ListNode.Cons(p, rest) =>
        match p {
          (op, oaddr) =>
            match op - pos {
              0 => oaddr,
              _ => lookup_override(rest, pos, default),
            },
        },
    }
  }

  fn ingress_with_primitives(target_addr: Addr) -> (List‹&KConstantInfo›, List‹Addr›) {
    let (all_addrs, all_consts) = load_with_deps(
      target_addr, store(ListNode.Nil), store(ListNode.Nil), store(ListNode.Nil), RBTreeMap.Nil);
    finish_ingress(all_addrs, all_consts)
  }

  -- Ingress the UNION closure of all env leaves in a single pass. One
  -- `load_with_deps` over leaves[0] as target with the remaining leaves as
  -- the initial worklist loads every leaf + its transitive deps; then the
  -- shared `finish_ingress` pipeline runs ONCE over the union, rather than
  -- being re-run per leaf as CheckEnv previously did.
  fn ingress_env(leaves: List‹Addr›) -> (List‹&KConstantInfo›, List‹Addr›) {
    match load(leaves) {
      ListNode.Nil => synthetic_primitive_entries(),
      ListNode.Cons(first, rest) =>
        let (all_addrs, all_consts) = load_with_deps(
          first, rest, store(ListNode.Nil), store(ListNode.Nil), RBTreeMap.Nil);
        finish_ingress(all_addrs, all_consts),
    }
  }

  -- Shared post-load pipeline: layout, conversion, addr table, primitives.
  fn finish_ingress(all_addrs: List‹Addr›, all_consts: List‹&Constant›)
                    -> (List‹&KConstantInfo›, List‹Addr›) {
    let (block_addrs, block_starts, total) = compute_layout(all_consts, all_addrs, 0);
    let pos_map_naive = build_pos_map(all_consts, all_addrs, block_addrs, block_starts, 0);
    -- Canonicalize duplicate Muts wrappers (same members-Ptr) so refs
    -- converge AND emitted KConstantInfos share content via store dedup.
    let pos_map = canonicalize_pos_map(all_consts, pos_map_naive);
    let canon_addrs = canonicalize_addr_map(all_addrs, all_consts);
    let inputs = build_convert_inputs(all_consts, all_addrs, all_addrs, pos_map, canon_addrs, block_addrs, block_starts, 0);
    let k_consts = convert_all(inputs);
    -- Build the pos→Addr tree via two O(N) passes (non-PRJ then PRJ
    -- overwrites at shared positions). Replaces the prior O(N²)
    -- `build_addrs_aligned` + `find_best_addr_at_pos` linear scans.
    let tree = build_addr_tree(all_addrs, all_consts, pos_map);
    -- Patch ctor positions: parent Inductives don't surface their ctors'
    -- CPrj addresses via Lean's compile (non-aux ctors aren't stored in
    -- env.consts). We surface them via the `[3] ++ ipr_addr` IO-buffer
    -- side channel and inject them as tree updates.
    let overrides = build_ctor_overrides(all_consts, all_addrs, block_addrs, block_starts);
    let tree = apply_ctor_overrides_tree(overrides, tree);
    let zero_addr = store([0u8; 32]);
    let addrs = emit_addrs_from_tree(0, total, tree, zero_addr);
    -- Append synthetic primitive entries with their hardcoded addresses.
    -- The Aiur kernel's index-based `KExprNode.Const` references need a
    -- top position for every primitive that internal expansions
    -- (e.g. `str_lit_to_ctor`) construct. When the target's transitive
    -- closure doesn't load a primitive, the synthetic stub at the end
    -- provides a discoverable position. Each stub is an
    -- `Axiom Sort 0` that type-checks trivially. Real loaded primitives
    -- still appear earlier in `addrs` so `find_addr_idx_safe` returns
    -- their true position; the stub is only consulted when the real
    -- one is absent.
    let (prim_consts, prim_addrs_list) = synthetic_primitive_entries();
    let k_consts = list_concat(k_consts, prim_consts);
    let addrs = list_concat(addrs, prim_addrs_list);
    (k_consts, addrs)
  }

  -- Synthetic primitive entries: every hardcoded `*_addr()` from
  -- `Ix.IxVM.Kernel.Primitive`, paired with a stub `Axiom Sort 0`.
  -- Order doesn't matter since lookup is by address. Mirrors the full
  -- `Primitives<M>` set in `src/ix/kernel/primitive.rs`. When the
  -- target's transitive closure already loads a real primitive, that
  -- entry appears earlier in `addrs` and `find_addr_idx_safe` returns
  -- its true position; the stub is only consulted otherwise.
  fn synthetic_primitive_entries() -> (List‹&KConstantInfo›, List‹Addr›) {
    let addrs = synthetic_primitive_addrs();
    let stub_ty = store(KExprNode.Srt(store(KLevel.Zero)));
    let stub = store(KConstantInfo.Axiom(0, stub_ty, 0));
    let consts = list_repeat_stub(stub, list_addr_length(addrs));
    (consts, addrs)
  }

  fn synthetic_primitive_addrs() -> List‹Addr› {
    store(ListNode.Cons(quot_type_addr(),
    store(ListNode.Cons(quot_ctor_addr(),
    store(ListNode.Cons(quot_lift_addr(),
    store(ListNode.Cons(quot_ind_addr(),
    store(ListNode.Cons(bit_vec_addr(),
    store(ListNode.Cons(bit_vec_to_nat_addr(),
    store(ListNode.Cons(bit_vec_of_nat_addr(),
    store(ListNode.Cons(bit_vec_ult_addr(),
    store(ListNode.Cons(decidable_decide_addr(),
    store(ListNode.Cons(lt_lt_addr(),
    store(ListNode.Cons(bool_type_addr(),
    store(ListNode.Cons(eq_addr(),
    store(ListNode.Cons(eq_refl_addr(),
    store(ListNode.Cons(nat_dec_le_addr(),
    store(ListNode.Cons(nat_dec_eq_addr(),
    store(ListNode.Cons(nat_dec_lt_addr(),
    store(ListNode.Cons(int_dec_eq_addr(),
    store(ListNode.Cons(int_dec_le_addr(),
    store(ListNode.Cons(int_dec_lt_addr(),
    store(ListNode.Cons(int_of_nat_addr(),
    store(ListNode.Cons(int_neg_succ_addr(),
    store(ListNode.Cons(fin_addr(),
    store(ListNode.Cons(decidable_rec_addr(),
    store(ListNode.Cons(decidable_is_true_addr(),
    store(ListNode.Cons(decidable_is_false_addr(),
    store(ListNode.Cons(nat_le_of_ble_eq_true_addr(),
    store(ListNode.Cons(nat_not_le_of_not_ble_eq_true_addr(),
    store(ListNode.Cons(nat_eq_of_beq_eq_true_addr(),
    store(ListNode.Cons(nat_ne_of_beq_eq_false_addr(),
    store(ListNode.Cons(reduce_bool_addr(),
    store(ListNode.Cons(reduce_nat_addr(),
    store(ListNode.Cons(system_platform_num_bits_addr(),
    store(ListNode.Cons(system_platform_get_num_bits_addr(),
    store(ListNode.Cons(subtype_val_addr(),
    store(ListNode.Cons(punit_size_of_1_addr(),
    store(ListNode.Cons(size_of_size_of_addr(),
    store(ListNode.Cons(punit_addr(),
    store(ListNode.Cons(unit_addr(),
    store(ListNode.Cons(nat_addr(),
    store(ListNode.Cons(nat_zero_addr(),
    store(ListNode.Cons(nat_succ_addr(),
    store(ListNode.Cons(nat_pred_addr(),
    store(ListNode.Cons(nat_add_addr(),
    store(ListNode.Cons(nat_sub_addr(),
    store(ListNode.Cons(nat_mul_addr(),
    store(ListNode.Cons(nat_pow_addr(),
    store(ListNode.Cons(nat_gcd_addr(),
    store(ListNode.Cons(nat_mod_addr(),
    store(ListNode.Cons(nat_div_addr(),
    store(ListNode.Cons(nat_land_addr(),
    store(ListNode.Cons(nat_lor_addr(),
    store(ListNode.Cons(nat_xor_addr(),
    store(ListNode.Cons(nat_shift_left_addr(),
    store(ListNode.Cons(nat_shift_right_addr(),
    store(ListNode.Cons(nat_beq_addr(),
    store(ListNode.Cons(nat_ble_addr(),
    store(ListNode.Cons(str_addr(),
    store(ListNode.Cons(string_utf8_byte_size_addr(),
    store(ListNode.Cons(string_back_addr(),
    store(ListNode.Cons(string_legacy_back_addr(),
    store(ListNode.Cons(string_to_byte_array_addr(),
    store(ListNode.Cons(byte_array_empty_addr(),
    store(ListNode.Cons(char_of_nat_addr(),
    store(ListNode.Cons(char_type_addr(),
    store(ListNode.Cons(string_of_list_addr(),
    store(ListNode.Cons(list_nil_addr(),
    store(ListNode.Cons(list_cons_addr(),
    store(ListNode.Cons(bool_true_addr(),
    store(ListNode.Cons(bool_false_addr(),
    store(ListNode.Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  }

  fn list_addr_length(xs: List‹Addr›) -> G {
    match load(xs) {
      ListNode.Nil => 0,
      ListNode.Cons(_, rest) => list_addr_length(rest) + 1,
    }
  }

  fn list_repeat_stub(stub: &KConstantInfo, n: G) -> List‹&KConstantInfo› {
    match n {
      0 => store(ListNode.Nil),
      _ => store(ListNode.Cons(stub, list_repeat_stub(stub, n - 1))),
    }
  }
⟧

end IxVM
