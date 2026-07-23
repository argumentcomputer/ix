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
  --     ch 4  blob raw bytes          key = blob.addr                  value = raw bytes
  --
  -- Soundness: EVERY channel is blake3-verified content — the bytes read
  -- hash to the key. There is NO unverified discriminator channel. The
  -- kind of an address (constant vs blob) is never declared out-of-band;
  -- it is DERIVED from verified content:
  --   * an address used via `Expr.Ref`/`Expr.Rec` is a constant → read ch 2;
  --   * an address used via `Expr.Nat`/`Expr.Str` is a blob   → read ch 4;
  -- the referencing expression node (itself in a blake3-verified constant)
  -- is the discriminator. A constant is CHECKED iff it appears as a
  -- `Const` in some checked constant's converted body (`check_reachable`
  -- collects those and recurses), so "used as a constant" and "checked"
  -- are the same content-derived set — a prover cannot supply a
  -- constant's data on ch 2 while dodging its check.
  --
  -- ch 3 (reducibility hint) is the sole non-content channel and is
  -- semantically optional: it steers the WHNF unfold heuristic only;
  -- def-eq is sound for any value.
  --
  -- Primitives are always shipped on ch 2 when present in the env, so the
  -- kernel never fabricates a reference to unshipped data — there is no
  -- stub axiom and no "absent" signal.
  --
  -- LAZY INGRESS: there is no upfront closure enumeration. Constants load,
  -- verify, and convert on first dereference via `get_ci`, memoized per
  -- `CRef`. Mutual blocks load once per block; members convert on demand.
  -- ============================================================================

  -- Load a constant from IOBuffer by address (ch 2), verify blake3,
  -- deserialize.
  fn load_verified_constant(addr: Addr) -> Constant {
    let raw = load(addr);
    let (idx, len) = io_get_info(2, raw);
    let bytes = #read_byte_stream(2, idx, len);
    verify_bytes_against(bytes, raw);
    let (constant, rest) = get_constant(bytes);
    assert_eq!(load(rest), ListNode.Nil);
    constant
  }

  -- Load a blob from IOBuffer by address (ch 4), verify blake3, return
  -- raw bytes.
  fn load_verified_blob(addr: Addr) -> ByteStream {
    let raw = load(addr);
    let (idx, len) = io_get_info(4, raw);
    let bytes = #read_byte_stream(4, idx, len);
    verify_bytes_against(bytes, raw);
    bytes
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
  -- One `Std` cref per ref address. A ref that a body uses via
  -- `Expr.Ref`/`Expr.Rec` is dereferenced as a constant (its cref → ch 2);
  -- a ref used via `Expr.Nat`/`Expr.Str` is loaded as a blob on demand
  -- from the same address (ch 4). The expression node — verified content —
  -- decides which; no per-address discriminator is consulted.
  fn build_ref_crefs(refs: List‹Addr›) -> List‹CRef› {
    match load(refs) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(addr, rest) =>
        store(ListNode.Cons(store(CRefNode.Std(addr)), build_ref_crefs(rest))),
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
            let ref_crefs = build_ref_crefs(refs);
            let recur_crefs = build_recur_crefs(blk, members, 0);
            ConvertCtx.Mk(sharing, ref_crefs, recur_crefs, univs),
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
                let ref_crefs = build_ref_crefs(refs);
                let recur_crefs = store(ListNode.Cons(cr, store(ListNode.Nil)));
                let ctx = ConvertCtx.Mk(sharing, ref_crefs, recur_crefs, univs);
                let hint = #load_constant_hint(addr);
                store(convert_definition(defn, ctx, hint)),
              ConstantInfo.Axio(axio) =>
                let ref_crefs = build_ref_crefs(refs);
                let ctx = ConvertCtx.Mk(sharing, ref_crefs, store(ListNode.Nil), univs);
                store(convert_axiom(axio, ctx)),
              ConstantInfo.Quot(quot) =>
                let ref_crefs = build_ref_crefs(refs);
                let ctx = ConvertCtx.Mk(sharing, ref_crefs, store(ListNode.Nil), univs);
                store(convert_quotient(quot, ctx)),
              ConstantInfo.Recr(recr) =>
                let ref_crefs = build_ref_crefs(refs);
                let recur_crefs = store(ListNode.Cons(cr, store(ListNode.Nil)));
                let ctx = ConvertCtx.Mk(sharing, ref_crefs, recur_crefs, univs);
                let (rule_crefs, block_addr) = aux_recr_ctor_crefs(recr, refs, sharing);
                store(convert_recursor(recr, ctx, rule_crefs, block_addr)),
            },
        },
    }
  }

  -- The wire refs of the constant at `addr`, as the claim layer's recursion
  -- worklist (every constant whose data could influence this constant's
  -- check is a transitive wire ref). Projections contribute their block's
  -- refs too (block members' deps live on the wrapper).
  -- The check-recursion set of the constant at `addr`: the external
  -- constant addresses it (or, for a block/projection, its whole block)
  -- DEREFERENCES — i.e. the `Std` addresses of the `Const`/`Proj` nodes in
  -- its converted body. This is content-derived: blob literals convert to
  -- `Lit` (never collected, so a blob address is never recursed into — it
  -- has no ch 2 entry and would hard-fail), and intra-block peers are
  -- `Member` refs (checked with their block, not re-recursed). The claim
  -- layer recurses `check_reachable` over exactly this set, so "a
  -- constant's data is dereferenced" and "that constant is checked" are
  -- the same set — there is no way to supply a constant's ch 2 bytes and
  -- dodge its check.
  -- Every collector below is a DIRECT (non-accumulator) recursion keyed on
  -- its node alone, and combines children with the (itself memoized)
  -- `list_concat`. Aiur memoizes on the argument tuple, so a shared
  -- subexpression's const-set is computed once and reused everywhere it
  -- occurs — an accumulator would thread a unique `acc` through every memo
  -- key and defeat that sharing entirely (same rule as `collect_spine`).
  fn const_check_deps(addr: Addr) -> List‹Addr› {
    let c = load_verified_constant(addr);
    match c {
      Constant.Mk(info, _, _, _) =>
        match info {
          ConstantInfo.Muts(members) =>
            collect_block_const_addrs(addr, block_kernel_size(members), 0),
          _ =>
            let blk = get_proj_block_addr(info);
            match address_eq(blk, store([0u8; 32])) {
              1 =>
                collect_kci_const_addrs(load(get_ci(store(CRefNode.Std(addr))))),
              0 =>
                collect_block_const_addrs(blk,
                                          block_kernel_size(block_members(blk)), 0),
            },
        },
    }
  }

  fn collect_block_const_addrs(blk: Addr, size: G, off: G) -> List‹Addr› {
    match size - off {
      0 => store(ListNode.Nil),
      _ =>
        list_concat(
          collect_kci_const_addrs(load(get_ci(store(CRefNode.Member(blk, off))))),
          collect_block_const_addrs(blk, size, off + 1)),
    }
  }

  fn collect_kci_const_addrs(kci: KConstantInfo) -> List‹Addr› {
    match kci {
      KConstantInfo.Axiom(_, ty, _) => collect_expr_const_addrs(ty),
      KConstantInfo.Defn(_, ty, val, _, _) =>
        list_concat(collect_expr_const_addrs(ty), collect_expr_const_addrs(val)),
      KConstantInfo.Thm(_, ty, val) =>
        list_concat(collect_expr_const_addrs(ty), collect_expr_const_addrs(val)),
      KConstantInfo.Opaque(_, ty, val, _) =>
        list_concat(collect_expr_const_addrs(ty), collect_expr_const_addrs(val)),
      KConstantInfo.Quot(_, ty, _) => collect_expr_const_addrs(ty),
      KConstantInfo.Induct(_, ty, _, _, _, _, _) => collect_expr_const_addrs(ty),
      KConstantInfo.Ctor(_, ty, _, _, _, _, _) => collect_expr_const_addrs(ty),
      KConstantInfo.Rec(_, ty, _, _, _, _, rules, _, _, _) =>
        list_concat(collect_expr_const_addrs(ty), collect_rules_const_addrs(rules)),
    }
  }

  fn collect_rules_const_addrs(rules: List‹KRecRule›) -> List‹Addr› {
    match load(rules) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(r, rest) =>
        match r {
          KRecRule.Mk(ctor_cref, _, rhs) =>
            list_concat(collect_cref_addr(ctor_cref),
              list_concat(collect_expr_const_addrs(rhs),
                          collect_rules_const_addrs(rest))),
        },
    }
  }

  fn collect_cref_addr(cref: CRef) -> List‹Addr› {
    match load(cref) {
      CRefNode.Std(a) =>
        match address_eq(a, store([0u8; 32])) {
          1 => store(ListNode.Nil),
          0 => store(ListNode.Cons(a, store(ListNode.Nil))),
        },
      CRefNode.Member(_, _) => store(ListNode.Nil),
    }
  }

  fn collect_expr_const_addrs(e: KExpr) -> List‹Addr› {
    match load(e) {
      KExprNode.BVar(_) => store(ListNode.Nil),
      KExprNode.Srt(_) => store(ListNode.Nil),
      KExprNode.Lit(_) => store(ListNode.Nil),
      KExprNode.Const(cref, _) => collect_cref_addr(cref),
      KExprNode.App(f, x) =>
        list_concat(collect_expr_const_addrs(f), collect_expr_const_addrs(x)),
      KExprNode.Lam(t, b) =>
        list_concat(collect_expr_const_addrs(t), collect_expr_const_addrs(b)),
      KExprNode.Forall(t, b) =>
        list_concat(collect_expr_const_addrs(t), collect_expr_const_addrs(b)),
      KExprNode.Let(t, v, b) =>
        list_concat(collect_expr_const_addrs(t),
          list_concat(collect_expr_const_addrs(v), collect_expr_const_addrs(b))),
      KExprNode.Proj(cref, _, x) =>
        list_concat(collect_cref_addr(cref), collect_expr_const_addrs(x)),
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
