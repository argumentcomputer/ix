module
import Ix.Aiur.Meta
public import Ix.Aiur.Stages.Source

public section

namespace IxVM

def ingress := ⟦
  -- ============================================================================
  -- IxVM IOBuffer interface
  --
  -- The host (Lean `IxVM.ClaimHarness` / Rust `aiur_ixvm_witness`) seeds
  -- blake3-keyed payloads on six channels; the kernel consumes them via
  -- `io_get_info` + `#read_byte_stream`. One value shape per channel.
  --
  --   Tier 1 — control input (one-per-run):
  --     ch 0  claim wire bytes        key = blake3(claim_bytes)        value = claim bytes
  --     ch 1  assumption tree bytes   key = tree.root                  value = tree bytes
  --
  --   Tier 2 — per-const data:
  --     ch 2  constant wire bytes     key = const.addr                 value = const bytes
  --     ch 3  Defn reducibility hint  key = defn.addr                  value = [hint_G]
  --
  --   Tier 3 — per-blob data:
  --     ch 4  presence discriminator  key = addr                       value = [1=const,0=blob,2=absent-primitive]
  --     ch 5  blob raw bytes          key = blob.addr                  value = raw bytes
  --
  -- IOBuffer reads are prover-chosen advice: `io_get_info` yields an
  -- unconstrained (idx, len) and `#read_byte_stream` unconstrained bytes.
  -- A read is only meaningful if something in-circuit PINS it.
  --
  --   ch 0/1/2/5 are pinned by content: `verify_bytes_against(bytes, key)`
  --   forces the bytes to be the unique blake3 preimage of the key (ch 1
  --   equivalently re-folds the merkle root and asserts it equals the key,
  --   and ch 0's key is the public input).
  --
  --   ch 3 (hint) is NOT pinned, and needs no pin: it only orders which
  --   side lazy-delta unfolds first. Delta preserves definitional equality
  --   either way, so every value yields the same verdict — an adversarial
  --   hint costs performance, never soundness.
  --
  --   ch 4 (presence) is NOT pinned either, so it must never be able to
  --   select an UNSOUND outcome. It is locked so that both of its
  --   reachable outcomes are safe: `load_verified_constant` asserts
  --   presence == 1, and `check_reachable` skips only on 0/2. Hence the
  --   prover's choice is between "checked AND loadable" (1) and "neither
  --   checked nor loadable" (0/2) — there is no setting that yields
  --   "usable but unchecked". Value 2 additionally stands for an absent
  --   PRIMITIVE and is honored only for the hardcoded primitive addresses
  --   (`get_ci`), whose content the prover cannot forge; the stub it
  --   substitutes can only stall a reduction, never make a check pass.
  --
  -- LAZY INGRESS: there is no upfront closure enumeration. Constants load,
  -- verify, and convert on first dereference via `get_ci`, memoized per
  -- `CRef`. Mutual blocks load once per block; members convert on demand.
  -- ============================================================================

  -- Load a constant from IOBuffer by address (ch 2), verify blake3,
  -- deserialize.
  fn load_verified_constant(addr: Addr) -> Constant {
    -- Loading constant DATA requires the (unconstrained) presence byte to
    -- say "constant". This locks data-resolution to the check decision:
    -- `check_reachable` skips only on presence 0/2, so anything loaded
    -- here (presence 1) is necessarily also checked. Without the lock a
    -- prover could ship a real constant's bytes on ch 2 while marking it
    -- ch 4 = 0/2 — using its data while its check is skipped. Mirrors the
    -- old positional kernel, where one ch 4 read jointly decided "load as
    -- const" and "add to the check list".
    assert_eq!(load_presence(addr), 1);
    let raw = load(addr);
    let (idx, len) = io_get_info(2, raw);
    let bytes = #read_byte_stream(2, idx, len);
    verify_bytes_against(bytes, raw);
    let (constant, rest) = get_constant(bytes);
    assert_eq!(load(rest), ListNode.Nil);
    constant
  }

  -- 1 iff `addr` is one of the hardcoded kernel primitive addresses. Only
  -- these may be replaced by the synthetic stub axiom when absent: the
  -- prover cannot ship different content at a primitive address (blake3
  -- binds it), so stubbing an absent primitive only ever stalls a
  -- reduction — conservative. Any OTHER address marked absent would be a
  -- real dependency the prover is trying to drop, and hard-fails.
  fn addr_is_prim(addr: Addr) -> G {
    addr_in_prim_list(addr, synthetic_primitive_addrs())
  }

  fn addr_in_prim_list(addr: Addr, xs: List‹Addr›) -> G {
    match load(xs) {
      ListNode.Nil => 0,
      ListNode.Cons(a, rest) =>
        match address_eq(addr, a) {
          1 => 1,
          0 => addr_in_prim_list(addr, rest),
        },
    }
  }

  -- Load a blob from IOBuffer by address (ch 5), verify blake3, return
  -- raw bytes.
  fn load_verified_blob(addr: Addr) -> ByteStream {
    let raw = load(addr);
    let (idx, len) = io_get_info(5, raw);
    let bytes = #read_byte_stream(5, idx, len);
    verify_bytes_against(bytes, raw);
    bytes
  }

  -- ch 4 presence discriminator for `addr`:
  --   1 = constant (ch 2 bytes available)
  --   0 = blob (ch 5 bytes available)
  --   2 = absent primitive (no bytes; use the synthetic stub)
  fn load_presence(addr: Addr) -> G {
    let raw = load(addr);
    let (idx, len) = io_get_info(4, raw);
    let bytes = #read_byte_stream(4, idx, len);
    match load(bytes) {
      ListNode.Cons(b, _) => to_field(b),
    }
  }

  -- Compare two 32-byte addresses for equality.
  --
  -- Cold path: limb 0 already matched, compare the remaining 31 limbs.
  -- Factored into its own function so it forms a separate circuit whose height
  -- is only the (rare) limb-0-match rows; Aiur charges a function's full width
  -- on every one of its rows, so a nested match in `address_eq` would not save
  -- anything — the split must be a function boundary.
  fn address_eq_tail(a: Addr, b: Addr) -> G {
    let [_, a1, a2, a3, a4, a5, a6, a7,
         a8, a9, a10, a11, a12, a13, a14, a15,
         a16, a17, a18, a19, a20, a21, a22, a23,
         a24, a25, a26, a27, a28, a29, a30, a31] = load(a);
    let [_, b1, b2, b3, b4, b5, b6, b7,
         b8, b9, b10, b11, b12, b13, b14, b15,
         b16, b17, b18, b19, b20, b21, b22, b23,
         b24, b25, b26, b27, b28, b29, b30, b31] = load(b);
    match [to_field(a1) - to_field(b1),
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
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] => 1,
      _ => 0,
    }
  }

  -- Limb-0 prefilter: a single differing limb proves inequality, and almost
  -- every comparison (the primitive-dispatch gauntlet in whnf) mismatches at
  -- limb 0. Hot rows reject here at narrow width; only limb-0 matches pay the
  -- wide `address_eq_tail` compare. Identical result to a full 32-limb compare.
  fn address_eq(a: Addr, b: Addr) -> G {
    let av = load(a);
    let bv = load(b);
    match to_field(av[0]) - to_field(bv[0]) {
      0 => address_eq_tail(a, b),
      _ => 0,
    }
  }

  -- Load reducibility hint G for a Defn at `addr` (ch 3). Encoding
  -- mirrors `Lean.ReducibilityHints`:
  --   0           = Opaque
  --   1 + h       = Regular(h)
  --   0xFFFFFFFF  = Abbrev
  -- Caller MUST only invoke this for Defn addrs; the harness only
  -- seeds ch 3 for Defns. A missing key aborts execution (correct).
  fn load_constant_hint(addr: Addr) -> G {
    let raw = load(addr);
    let (idx, len) = io_get_info(3, raw);
    let bytes = #read_byte_stream(3, idx, len);
    match load(bytes) {
      ListNode.Cons(b, _) => to_field(b),
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
  -- Block member layout (flat offsets within a Muts block)
  --
  -- Each Indc member occupies 1 (inductive) + num_ctors consecutive offsets;
  -- Recr and Defn members occupy 1. A member's identity is
  -- `CRef.Member(block_addr, flat_offset)`.
  -- ============================================================================

  fn member_kernel_size(mc: MutConst) -> G {
    match mc {
      MutConst.Indc(ind) =>
        match ind {
          Inductive.Mk(_, _, _, _, _, ctors) =>
            list_length(ctors) + 1,
        },
      MutConst.Recr(_) => 1,
      MutConst.Defn(_) => 1,
    }
  }

  fn block_kernel_size(members: List‹MutConst›) -> G {
    match load(members) {
      ListNode.Nil => 0,
      ListNode.Cons(mc, rest) =>
        member_kernel_size(mc) + block_kernel_size(rest),
    }
  }

  -- Flat offset of member `target_idx` within a block's expansion.
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

  -- Selection of the member (or ctor within a member) at a flat offset.
  -- MCtor carries the ctor, its cidx, and its parent Indc's flat offset.
  enum MemberSel {
    MInd(Inductive),
    MCtor(Constructor, G, G),
    MRecr(Recursor),
    MDefn(Definition)
  }

  fn member_at_offset(members: List‹MutConst›, target: G, base: G) -> MemberSel {
    match load(members) {
      ListNode.Cons(mc, rest) =>
        let sz = member_kernel_size(mc);
        match u32_less_than(target - base, sz) {
          1 =>
            let loc = target - base;
            match mc {
              MutConst.Indc(ind) =>
                match loc {
                  0 => MemberSel.MInd(ind),
                  _ =>
                    match ind {
                      Inductive.Mk(_, _, _, _, _, ctors) =>
                        let ListNode.Cons(ctor, _) =
                          load(list_drop_ctors(ctors, loc - 1));
                        MemberSel.MCtor(ctor, loc - 1, base),
                    },
                },
              MutConst.Recr(r) => MemberSel.MRecr(r),
              MutConst.Defn(d) => MemberSel.MDefn(d),
            },
          0 => member_at_offset(rest, target, base + sz),
        },
    }
  }

  fn list_drop_ctors(xs: List‹Constructor›, n: G) -> List‹Constructor› {
    match n {
      0 => xs,
      _ =>
        match load(xs) {
          ListNode.Cons(_, rest) => list_drop_ctors(rest, n - 1),
        },
    }
  }

  -- ============================================================================
  -- Reference identity
  --
  -- `cref_norm` maps a CRef to canonical coordinates `(owner_id, offset)`:
  --   * members (via Member crefs or Std refs to projection constants)
  --     normalize to (content-ptr of the parsed block Constant, flat offset);
  --   * a Std ref to a bare Muts wrapper denotes its first member (offset 0);
  --   * standalone constants normalize to (content-ptr of their own parsed
  --     Constant, 0).
  --
  -- Owner identity is the Aiur-interned pointer of the parsed `Constant`,
  -- so distinct wrapper ADDRESSES with identical parsed content collapse to
  -- one identity (the lazy replacement of the old `extract_dedup_mptr`
  -- positional canonicalization — mirror of Rust `resolve_all`). Pointer
  -- interning is best-effort: a de-interned witness makes two identical
  -- constants compare UNEQUAL, which only ever fails conservatively.
  -- ============================================================================

  fn const_ptr_id(addr: Addr) -> G {
    ptr_val(store(load_verified_constant(addr)))
  }

  fn cref_norm(cr: CRef) -> (G, G) {
    match load(cr) {
      CRefNode.Member(blk, off) =>
        match address_eq(blk, store([0u8; 32])) {
          -- Aux-order sentinel (Member of the zero block): identity is
          -- (zero cell, ordinal) — no constant to load. All sentinels
          -- share the interned zero-address cell, so equal ordinals
          -- norm-equal and distinct ordinals norm-unequal.
          1 => (ptr_val(blk), off),
          0 => (const_ptr_id(blk), off),
        },
      CRefNode.Std(addr) =>
        match address_eq(addr, store([0u8; 32])) {
          1 =>
            -- Null reference: no identity, never equal to anything real.
            (ptr_val(addr), 0),
          0 => cref_norm_std(addr),
        },
    }
  }

  fn cref_norm_std(addr: Addr) -> (G, G) {
    match load_presence(addr) {
          2 =>
            -- Absent primitive: identity is the address cell itself. Distinct
            -- from every parsed-constant id (different store cell family).
            (ptr_val(addr), 0),
          _ =>
            let c = load_verified_constant(addr);
            match c {
              Constant.Mk(info, _, _, _) =>
                match info {
                  ConstantInfo.Muts(_) => (ptr_val(store(c)), 0),
                  ConstantInfo.IPrj(prj) =>
                    match prj {
                      InductiveProj.Mk(idx, blk) =>
                        (const_ptr_id(blk),
                         member_offset(block_members(blk), flatten_u64(idx))),
                    },
                  ConstantInfo.CPrj(prj) =>
                    match prj {
                      ConstructorProj.Mk(idx, cidx, blk) =>
                        (const_ptr_id(blk),
                         (member_offset(block_members(blk), flatten_u64(idx))
                          + 1) + flatten_u64(cidx)),
                    },
                  ConstantInfo.RPrj(prj) =>
                    match prj {
                      RecursorProj.Mk(idx, blk) =>
                        (const_ptr_id(blk),
                         member_offset(block_members(blk), flatten_u64(idx))),
                    },
                  ConstantInfo.DPrj(prj) =>
                    match prj {
                      DefinitionProj.Mk(idx, blk) =>
                        (const_ptr_id(blk),
                         member_offset(block_members(blk), flatten_u64(idx))),
                    },
                  _ => (ptr_val(store(c)), 0),
                },
            },
    }
  }

  -- Identity compare between constant references, in three tiers:
  --
  --   1. pointer equality        → EQUAL   (ptr eq ⇒ content eq: sound)
  --   2. interned-norm equality  → EQUAL   (content-interned owner ids;
  --                                         unifies duplicate wrappers)
  --   3. canonical-ADDRESS value → decides (blake3 addresses are
  --                                         collision-free, so this
  --                                         verdict is EXACT)
  --
  -- Pointer/interning information only ever produces the EQUAL verdict;
  -- the UNEQUAL verdict comes exclusively from tier 3's value compare.
  -- A de-interned witness can therefore only downgrade tiers 1-2 to the
  -- exact tier 3 — it can never flip a verdict. (Pointer inequality
  -- implies nothing; concluding data inequality from it in the
  -- occurrence/positivity scans would let a malicious witness hide a
  -- recursive occurrence and smuggle an illegal inductive through.)
  fn cref_eq(a: CRef, b: CRef) -> G {
    match ptr_val(a) - ptr_val(b) {
      0 => 1,
      _ =>
        let (oa, fa) = cref_norm(a);
        let (ob, fb) = cref_norm(b);
        let norm_eq = match oa - ob {
          0 => eq_zero(fa - fb),
          _ => 0,
        };
        match norm_eq {
          1 => 1,
          0 => cref_eq_val(a, b),
        },
    }
  }

  -- Tier 3: value-level identity. Std refs are their address bytes;
  -- members their derived projection content address; aux sentinels
  -- pair the zero block with their ordinal; the null ref never equals
  -- anything.
  fn cref_eq_val(a: CRef, b: CRef) -> G {
    match load(a) {
      CRefNode.Member(b1, o1) =>
        match address_eq(b1, store([0u8; 32])) {
          1 =>
            match load(b) {
              CRefNode.Member(b2, o2) =>
                match address_eq(b2, store([0u8; 32])) {
                  1 => eq_zero(o1 - o2),
                  0 => 0,
                },
              CRefNode.Std(_) => 0,
            },
          0 => address_eq(member_prj_addr(b1, o1), cref_val_addr(b)),
        },
      CRefNode.Std(a1) =>
        match address_eq(a1, store([0u8; 32])) {
          1 => 0,
          0 => address_eq(a1, cref_val_addr(b)),
        },
    }
  }

  -- Value address of a reference; the zero address stands for "no value
  -- identity" (sentinels, null) and never equals a real address.
  fn cref_val_addr(cr: CRef) -> Addr {
    match load(cr) {
      CRefNode.Std(a) => a,
      CRefNode.Member(blk, off) =>
        match address_eq(blk, store([0u8; 32])) {
          1 => blk,
          0 => member_prj_addr(blk, off),
        },
    }
  }

  -- Null reference: Std of the zero address. Stands for "no constant"
  -- in search results (mirror of the old 0-position sentinel); get_ci on
  -- it fails, which is the correct outcome for a dereferenced miss.
  fn null_cref() -> CRef {
    store(CRefNode.Std(store([0u8; 32])))
  }

  fn cref_is_null(cr: CRef) -> G {
    match load(cr) {
      CRefNode.Std(a) => address_eq(a, store([0u8; 32])),
      CRefNode.Member(_, _) => 0,
    }
  }

  -- Raw env address of a Std cref; [0;32] for Member crefs (peer-only
  -- members have no env-visible address). Primitive dispatch compares
  -- this against hardcoded primitive addresses.
  fn cref_std_addr(cr: CRef) -> Addr {
    match load(cr) {
      CRefNode.Std(addr) => addr,
      CRefNode.Member(_, _) => store([0u8; 32]),
    }
  }

  -- ============================================================================
  -- Block loading & member conversion
  -- ============================================================================

  fn block_members(blk: Addr) -> List‹MutConst› {
    let c = load_verified_constant(blk);
    match c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) => members,
        },
    }
  }

  -- Per-ref conversion inputs of a block (or standalone) constant:
  -- refs become Std crefs (blob refs get a dead cref + their bytes).
  -- ch 4 discriminates const vs blob per ref address.
  -- Per-ref conversion inputs: every ref gets a `Std` cref; refs the
  -- presence byte marks as blobs (0) additionally get their bytes loaded
  -- into the parallel `lit_blobs` slot for `Expr.Nat`/`Expr.Str`.
  fn build_ref_crefs_and_blobs(refs: List‹Addr›)
                               -> (List‹CRef›, List‹ByteStream›) {
    match load(refs) {
      ListNode.Nil => (store(ListNode.Nil), store(ListNode.Nil)),
      ListNode.Cons(addr, rest) =>
        let (rest_crefs, rest_blobs) = build_ref_crefs_and_blobs(rest);
        match load_presence(addr) {
          0 =>
            let bs = load_verified_blob(addr);
            (store(ListNode.Cons(store(CRefNode.Std(addr)), rest_crefs)),
             store(ListNode.Cons(bs, rest_blobs))),
          _ =>
            (store(ListNode.Cons(store(CRefNode.Std(addr)), rest_crefs)),
             store(ListNode.Cons(store(ListNode.Nil), rest_blobs))),
        },
    }
  }

  -- Member crefs for peer references (Expr.Rec): one per member, at the
  -- member's flat offset.
  fn build_recur_crefs(blk: Addr, members: List‹MutConst›, cur: G) -> List‹CRef› {
    match load(members) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(mc, rest) =>
        store(ListNode.Cons(store(CRefNode.Member(blk, cur)),
          build_recur_crefs(blk, rest, cur + member_kernel_size(mc)))),
    }
  }

  -- Ctor crefs of the Indc member at flat offset `ind_off`: offsets
  -- ind_off+1 .. ind_off+n_ctors.
  fn build_ctor_crefs(blk: Addr, ind_off: G, n_ctors: G, cidx: G) -> List‹CRef› {
    match n_ctors - cidx {
      0 => store(ListNode.Nil),
      _ =>
        store(ListNode.Cons(store(CRefNode.Member(blk, (ind_off + 1) + cidx)),
          build_ctor_crefs(blk, ind_off, n_ctors, cidx + 1))),
    }
  }

  -- All ctor crefs of every Indc member of `blk`, in member order — the
  -- rule_ctor list for recursors of blocks that contain their inductives.
  fn build_rule_ctor_crefs(blk: Addr, members: List‹MutConst›, cur: G) -> List‹CRef› {
    match load(members) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(mc, rest) =>
        match mc {
          MutConst.Indc(ind) =>
            match ind {
              Inductive.Mk(_, _, _, _, _, ctors) =>
                let n = list_length(ctors);
                list_concat(build_ctor_crefs(blk, cur, n, 0),
                  build_rule_ctor_crefs(blk, rest, (cur + 1) + n)),
            },
          _ => build_rule_ctor_crefs(blk, rest, cur + 1),
        },
    }
  }

  -- Ctor crefs of the member at index `member_idx` of `blk` (used to slice
  -- an aux recursor's rules to its own inductive's ctors).
  fn member_ctor_crefs(blk: Addr, member_idx: G) -> List‹CRef› {
    let members = block_members(blk);
    let off = member_offset(members, member_idx);
    match member_at_offset(members, off, 0) {
      MemberSel.MInd(ind) =>
        match ind {
          Inductive.Mk(_, _, _, _, _, ctors) =>
            build_ctor_crefs(blk, off, list_length(ctors), 0),
        },
    }
  }

  -- (member_idx, role, cidx) of the member at flat offset `off`:
  -- role 0 = Indc, 1 = its ctor (cidx set), 2 = Recr, 3 = Defn.
  fn member_coords_at_offset(members: List‹MutConst›, target: G,
                             base: G, midx: G) -> (G, G, G) {
    match load(members) {
      ListNode.Cons(mc, rest) =>
        let sz = member_kernel_size(mc);
        match u32_less_than(target - base, sz) {
          1 =>
            let loc = target - base;
            match mc {
              MutConst.Indc(_) =>
                match loc {
                  0 => (midx, 0, 0),
                  _ => (midx, 1, loc - 1),
                },
              MutConst.Recr(_) => (midx, 2, 0),
              MutConst.Defn(_) => (midx, 3, 0),
            },
          0 => member_coords_at_offset(rest, target, base + sz, midx + 1),
        },
    }
  }

  -- Content address of the projection constant a block member is known by
  -- in the env: serialize the `Constant { XPrj { idx, [cidx,] block } }`
  -- shape Lean compile emits and blake3 it. Memoized per (blk, off).
  -- This is Rust `compare_external_refs`' key for member references — and
  -- unlike the old positional addr table it never degrades to [0;32] for
  -- peer-only members.
  fn member_prj_addr(blk: Addr, off: G) -> Addr {
    let members = block_members(blk);
    match member_coords_at_offset(members, off, 0, 0) {
      (m, role, cidx) =>
        let m_bytes = [u8_from_field_unsafe(m), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8];
        let info = match role {
          0 => ConstantInfo.IPrj(InductiveProj.Mk(m_bytes, blk)),
          1 => ConstantInfo.CPrj(ConstructorProj.Mk(m_bytes,
                 [u8_from_field_unsafe(cidx), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], blk)),
          2 => ConstantInfo.RPrj(RecursorProj.Mk(m_bytes, blk)),
          _ => ConstantInfo.DPrj(DefinitionProj.Mk(m_bytes, blk)),
        };
        let cnst = Constant.Mk(info, store(ListNode.Nil),
                                     store(ListNode.Nil),
                                     store(ListNode.Nil));
        let bytes = put_constant(cnst, store(ListNode.Nil));
        bytes_to_addr(bytes),
    }
  }

  -- Canonical env address of a reference: Std refs are their own address;
  -- member refs use their derived projection content address. The stable
  -- external-ordering key for canonical sorts (mirror of Rust
  -- compare_external_refs, which orders by real env addresses).
  fn cref_canonical_addr(cr: CRef) -> Addr {
    match load(cr) {
      CRefNode.Std(a) => a,
      CRefNode.Member(blk, off) =>
        match address_eq(blk, store([0u8; 32])) {
          -- Aux-order sentinel (Member of the zero block): no env identity;
          -- callers order sentinels via the refinement ctx, never here.
          1 => blk,
          0 => member_prj_addr(blk, off),
        },
    }
  }

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
      Expr.Share(idx) =>
        let ListNode.Cons(e, _) = load(list_drop(sharing, flatten_u64(idx)));
        deref_share(load(e), sharing),
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

  -- For aux-only Recr blocks (Muts with no Indc, e.g. `compile_aux_block`
  -- output) and standalone Recrs, the rule ctor crefs come from the
  -- ORIGINAL inductive block, resolved by peeling the recursor's typ down
  -- to the major premise's head Ref (an IPrj constant), then slicing that
  -- member's ctors. Returns `(rule_ctor_crefs, origin_block_addr)`.
  fn aux_recr_ctor_crefs(recr: Recursor, refs: List‹Addr›,
                         sharing: List‹&Expr›) -> (List‹CRef›, Addr) {
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
                    (member_ctor_crefs(block_addr, flatten_u64(member_idx)),
                     block_addr),
                },
            },
        },
    }
  }

  -- Conversion context of a block's members: built once per block (memoized),
  -- shared by every member conversion.
  fn block_ctx(blk: Addr) -> ConvertCtx {
    let c = load_verified_constant(blk);
    match c {
      Constant.Mk(info, sharing, refs, univs) =>
        match info {
          ConstantInfo.Muts(members) =>
            let (ref_crefs, lit_blobs) = build_ref_crefs_and_blobs(refs);
            let recur_crefs = build_recur_crefs(blk, members, 0);
            ConvertCtx.Mk(sharing, ref_crefs, recur_crefs, lit_blobs, univs),
        },
    }
  }

  -- Convert the member of `blk` at flat offset `off` to a KConstantInfo.
  fn convert_member(blk: Addr, off: G) -> KConstantInfo {
    let ctx = block_ctx(blk);
    let members = block_members(blk);
    match member_at_offset(members, off, 0) {
      MemberSel.MInd(ind) =>
        match ind {
          Inductive.Mk(_, _, _, _, _, ctors) =>
            let ctor_crefs = build_ctor_crefs(blk, off, list_length(ctors), 0);
            convert_inductive(ind, ctx, ctor_crefs, blk),
        },
      MemberSel.MCtor(ctor, _, ind_off) =>
        convert_constructor(ctor, ctx, store(CRefNode.Member(blk, ind_off))),
      MemberSel.MRecr(recr) =>
        match members_have_indc(members) {
          1 =>
            let rule_crefs = build_rule_ctor_crefs(blk, members, 0);
            convert_recursor(recr, ctx, rule_crefs, blk),
          0 =>
            let c = load_verified_constant(blk);
            match c {
              Constant.Mk(_, sharing, refs, _) =>
                let (rule_crefs, _) = aux_recr_ctor_crefs(recr, refs, sharing);
                convert_recursor(recr, ctx, rule_crefs, blk),
            },
        },
      MemberSel.MDefn(defn) =>
        -- Muts-block defs default to Regular(0) (hint=1). Per-member hints
        -- aren't plumbed; standalone Defns get their actual ch 3 hint below.
        convert_definition(defn, ctx, 1),
    }
  }

  -- ============================================================================
  -- get_ci: THE constant resolver.
  --
  -- Loads, blake3-verifies, and converts the constant a CRef denotes.
  -- Memoized per stored cref, so each distinct reference converts once,
  -- on first touch — nothing untouched is ever loaded.
  -- ============================================================================

  fn get_ci(cr: CRef) -> &KConstantInfo {
    match load(cr) {
      CRefNode.Member(blk, off) => store(convert_member(blk, off)),
      CRefNode.Std(addr) =>
        match load_presence(addr) {
          2 =>
            -- Absent marker honored ONLY for hardcoded primitive addresses:
            -- the trivially-typechecking stub stands in for a primitive a
            -- run never materializes (kernel-internal literal expansions
            -- fabricate such refs). A non-primitive marked absent would be
            -- a real dependency the prover is dropping: hard-fail. The stub
            -- can only stall a reduction, never make a check pass.
            assert_eq!(addr_is_prim(addr), 1);
            store(KConstantInfo.Axiom(0,
              store(KExprNode.Srt(store(KLevelNode.Zero))), 0)),
          _ =>
        let c = load_verified_constant(addr);
        match c {
          Constant.Mk(info, sharing, refs, univs) =>
            match info {
              ConstantInfo.Muts(_) => store(convert_member(addr, 0)),
              ConstantInfo.IPrj(prj) =>
                match prj {
                  InductiveProj.Mk(idx, blk) =>
                    store(convert_member(blk,
                      member_offset(block_members(blk), flatten_u64(idx)))),
                },
              ConstantInfo.CPrj(prj) =>
                match prj {
                  ConstructorProj.Mk(idx, cidx, blk) =>
                    store(convert_member(blk,
                      (member_offset(block_members(blk), flatten_u64(idx))
                       + 1) + flatten_u64(cidx))),
                },
              ConstantInfo.RPrj(prj) =>
                match prj {
                  RecursorProj.Mk(idx, blk) =>
                    store(convert_member(blk,
                      member_offset(block_members(blk), flatten_u64(idx)))),
                },
              ConstantInfo.DPrj(prj) =>
                match prj {
                  DefinitionProj.Mk(idx, blk) =>
                    store(convert_member(blk,
                      member_offset(block_members(blk), flatten_u64(idx)))),
                },
              ConstantInfo.Defn(defn) =>
                let (ref_crefs, lit_blobs) = build_ref_crefs_and_blobs(refs);
                let recur_crefs = store(ListNode.Cons(cr, store(ListNode.Nil)));
                let ctx = ConvertCtx.Mk(sharing, ref_crefs, recur_crefs, lit_blobs, univs);
                let hint = #load_constant_hint(addr);
                store(convert_definition(defn, ctx, hint)),
              ConstantInfo.Axio(axio) =>
                let (ref_crefs, lit_blobs) = build_ref_crefs_and_blobs(refs);
                let ctx = ConvertCtx.Mk(sharing, ref_crefs, store(ListNode.Nil), lit_blobs, univs);
                store(convert_axiom(axio, ctx)),
              ConstantInfo.Quot(quot) =>
                let (ref_crefs, lit_blobs) = build_ref_crefs_and_blobs(refs);
                let ctx = ConvertCtx.Mk(sharing, ref_crefs, store(ListNode.Nil), lit_blobs, univs);
                store(convert_quotient(quot, ctx)),
              ConstantInfo.Recr(recr) =>
                let (ref_crefs, lit_blobs) = build_ref_crefs_and_blobs(refs);
                let recur_crefs = store(ListNode.Cons(cr, store(ListNode.Nil)));
                let ctx = ConvertCtx.Mk(sharing, ref_crefs, recur_crefs, lit_blobs, univs);
                let (rule_crefs, block_addr) = aux_recr_ctor_crefs(recr, refs, sharing);
                store(convert_recursor(recr, ctx, rule_crefs, block_addr)),
            },
        },
        },
    }
  }

  -- The wire refs of the constant at `addr`, as the claim layer's recursion
  -- worklist (every constant whose data could influence this constant's
  -- check is a transitive wire ref). Projections contribute their block's
  -- refs too (block members' deps live on the wrapper).
  --
  -- `refs` is used directly — it is already the parsed, deduplicated ref
  -- list of a blake3-verified constant, so obtaining it is free. Deriving
  -- the set by walking the converted body instead was tried and is
  -- catastrophic in Aiur's cost model: memoization keys on the whole
  -- argument tuple, so a per-node set-union creates a fresh memo entry per
  -- intermediate list (and per membership probe), which explodes on shared
  -- expression DAGs — measured 159 GiB (concat) / 82 GiB (dedup-union) on
  -- `Nat.add_comm`, versus ~1.5 s here. Blob refs among `refs` are skipped
  -- by `check_reachable` via the presence byte, whose two outcomes are both
  -- sound (see the channel table at the top of this file).
  fn const_check_deps(addr: Addr) -> List‹Addr› {
    let c = load_verified_constant(addr);
    match c {
      Constant.Mk(info, _, refs, _) =>
        let blk = get_proj_block_addr(info);
        match address_eq(blk, store([0u8; 32])) {
          1 => refs,
          0 =>
            let bc = load_verified_constant(blk);
            match bc {
              Constant.Mk(_, _, block_refs, _) =>
                store(ListNode.Cons(blk, list_concat(refs, block_refs))),
            },
        },
    }
  }

  -- ============================================================================
  -- Synthetic primitive stub addresses (see `get_ci`'s absent-primitive arm).
  -- Mirrors the full `Primitives<M>` set in `src/ix/kernel/primitive.rs`.
  -- The witness ships a ch 4 presence byte for every one of these.
  -- ============================================================================

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
⟧

end IxVM

end
