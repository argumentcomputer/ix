module
public import Ix.Aiur.Meta

/-!
# Verifying-key deserializer (Aiur)

Aiur port of `crates/aiur/src/vk_codec.rs` — reconstructs the verifier's
`System<AiurConfig>` from the bytes the prover places on the IO channel.

Wire format (v3, mirrors `vk_codec.rs` — see its module docs for the full
layout). The multi-stark constraint-IR migration replaced the per-circuit
*symbolic* AIR (`SymbolicExpression` trees + `LookupAir`) with a *compiled*
flat base-field node graph, so this reader parses that compiled form:

* GLOBAL HEADER: 7 × u16 parameters + u16 circuit count.
* PER-CIRCUIT RECORD (no framing prefix; nothing derivable is serialized —
  constraint_count, stage_2_width, num_publics, and lookup_prefix_len are
  all recomputed from the counts below):
    - u16 main_width, u16 preprocessed_width, u32 preprocessed_height,
      u16 max_constraint_degree (combined user + logUp),
      u8 lookup_group_size (k: lookups per chained accumulator step),
      u16 node_count
    - `node_count` tagged nodes (dense v5: u16 children, never sub-trees):
      0 ConstSmall(u16) · 1 ConstBig(u64) · 2 Public(u8) ·
      3 IsFirstRow · 4 IsLastRow · 5 IsTransition ·
      6 Add(u16,u16) · 7 Sub(u16,u16) · 8 Mul(u16,u16) · 9 Neg(u16) ·
      10..15 Var(u16 index) with (source, offset) packed in the tag
      (tag = 10 + 2·source + offset)
    - u16 zero_count, then that many u16 constraint-root NodeIds (USER
      constraints only — the logUp constraints are never compiled)
    - u16 lookup_count, then the compiled lookups (u16 multiplicity NodeId,
      u16 arg count, u16 arg NodeIds) — these drive the verifier's direct
      logUp constraint evaluation (`Verifier.lean`).
* TRAILER: preprocessed commit (`0` = None / `1` + MerkleCap) then one u16
  per circuit for the preprocessed index (`0xFFFF` = None).

The vk stream (IO channel 1) is fetched once as unconstrained advice, then
both hashed and deserialized from that same `ByteStream`. The hash and all
deserializer calls are constrained, so the public `system_digest` binds every
value reconstructed below. Per-node degrees are neither serialized nor needed
(the node sweep just evaluates the graph).

The Fiat-Shamir shape limbs (`observe_shape`): the circuit count then,
per circuit, the seven words constraint_count, max_constraint_degree,
preprocessed_height, preprocessed_width, main_width, stage_2_width,
lookup_group_size (as 8-byte LE limbs).
-/

public section

namespace MultiStark

def systemDeserialize := ⟦
  -- ==========================================================================
  -- Reconstructed `System<AiurConfig>` as Aiur data (compiled form).
  -- ==========================================================================

  -- A compiled constraint node (`multi_stark::circuit::Node`). Children of
  -- Add/Sub/Mul/Neg are NodeIds (indices into the circuit's node vector),
  -- not sub-trees: the graph is flat and topologically ordered (a node's
  -- children always have smaller indices).
  enum SysNode {
    Const(G),            -- native Goldilocks constant (reduced on read)
    Var(G, G, G),        -- source (0 Preprocessed, 1 Main, 2 Stage2), offset (0 current, 1 next), column index
    Public(G),           -- public-input coordinate index
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Add(G, G),           -- child NodeIds
    Sub(G, G),
    Mul(G, G),
    Neg(G)
  }

  -- A compiled circuit: the flat node vector, its length, the constraint-root
  -- NodeIds (`zeros`), and the maximum constraint degree (for the quotient
  -- degree). The lookups are omitted — their constraints are compiled into
  -- `zeros`, so the verifier never needs them.
  -- A compiled lookup: multiplicity node id + argument node ids (all into
  -- the graph's lookup prefix). Drives the direct logUp evaluation.
  enum SysLookup { Mk(G, List‹G›) }
  enum SysCircuit { Mk(List‹SysNode›, G, List‹G›, G, List‹SysLookup›, G) }   -- nodes, node_count, zeros, max_constraint_degree, lookups, lookup_group_size

  -- log_blowup, cap_height, log_final_poly_len, max_log_arity, num_queries,
  -- commit_proof_of_work_bits, query_proof_of_work_bits — the commitment + FRI
  -- parameters the config (and its challenger seed) was built from.
  enum SysParams { Mk(G, G, G, G, G, G, G) }

  -- `Option`s as dedicated non-generic enums (unambiguous constructors).
  enum OptCommit { NoCommit, SomeCommit(MerkleCap) }
  enum OptIdx { NoIdx, SomeIdx(G) }

  -- parameters, transcript limbs, circuits, preprocessed_commit,
  -- preprocessed_indices. The transcript limbs are the u64 words the
  -- challenger observes before any commitment — the 7 parameters (bound via
  -- the challenger seed) followed by the system shape (`observe_shape`: the
  -- circuit count, then 6 metadata words per circuit) — kept as limbs because
  -- the Fiat-Shamir replay needs their little-endian bytes.
  enum Sys { Mk(SysParams, List‹U64›, List‹SysCircuit›, OptCommit, List‹OptIdx›) }

  -- ==========================================================================
  -- Byte primitives over the already materialized vk stream. Each returns
  -- the remaining stream. The `_limb` variants also
  -- return the value's 8-LE-byte u64 limb for the Fiat-Shamir replay.
  -- ==========================================================================

  fn read_vk_u8(s: ByteStream) -> (U8, ByteStream) {
    match load(s) {
      ListNode.Cons(byte, rest) => (byte, rest),
    }
  }

  -- A single byte kept as a raw field value for match dispatch (tags, source,
  -- offset).
  fn read_vk_tag(s: ByteStream) -> (G, ByteStream) {
    let (b, rest) = read_vk_u8(s);
    (to_field(b), rest)
  }

  fn read_vk_u16(s: ByteStream) -> (G, ByteStream) {
    let (b0, s0) = read_vk_u8(s);
    let (b1, s1) = read_vk_u8(s0);
    (to_field(b0) + 0x100 * to_field(b1), s1)
  }

  fn read_vk_u16_limb(s: ByteStream) -> (G, U64, ByteStream) {
    let (b0, s0) = read_vk_u8(s);
    let (b1, s1) = read_vk_u8(s0);
    (to_field(b0) + 0x100 * to_field(b1),
     [b0, b1,
      0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
     s1)
  }

  fn read_vk_u32(s: ByteStream) -> (G, ByteStream) {
    let (b0, s0) = read_vk_u8(s); let (b1, s1) = read_vk_u8(s0);
    let (b2, s2) = read_vk_u8(s1); let (b3, s3) = read_vk_u8(s2);
    (to_field(b0) + 0x100 * to_field(b1) + 0x10000 * to_field(b2) + 0x1000000 * to_field(b3), s3)
  }

  fn read_vk_u32_limb(s: ByteStream) -> (G, U64, ByteStream) {
    let (b0, s0) = read_vk_u8(s); let (b1, s1) = read_vk_u8(s0);
    let (b2, s2) = read_vk_u8(s1); let (b3, s3) = read_vk_u8(s2);
    (to_field(b0) + 0x100 * to_field(b1) + 0x10000 * to_field(b2) + 0x1000000 * to_field(b3),
     [b0, b1, b2, b3,
      0u8, 0u8, 0u8, 0u8],
     s3)
  }

  fn read_vk_u64(s: ByteStream) -> (U64, ByteStream) {
    let (b0, s0) = read_vk_u8(s); let (b1, s1) = read_vk_u8(s0);
    let (b2, s2) = read_vk_u8(s1); let (b3, s3) = read_vk_u8(s2);
    let (b4, s4) = read_vk_u8(s3); let (b5, s5) = read_vk_u8(s4);
    let (b6, s6) = read_vk_u8(s5); let (b7, s7) = read_vk_u8(s6);
    ([b0, b1, b2, b3, b4, b5, b6, b7], s7)
  }

  -- A full (u64) Goldilocks constant, reduced into a native field value so it
  -- can feed the composition arithmetic directly.
  fn read_field(i: ByteStream) -> (G, ByteStream) {
    let (u, j) = read_vk_u64(i);
    (@gl_val(u), j)
  }

  fn read_vk_digest(i: ByteStream) -> (Digest, ByteStream) {
    let (a, j0) = read_vk_u64(i);
    let (b, j1) = read_vk_u64(j0);
    let (c, j2) = read_vk_u64(j1);
    let (d, j3) = read_vk_u64(j2);
    ([a, b, c, d], j3)
  }
  fn read_vk_cap_n(i: ByteStream, n: G) -> (MerkleCap, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = @read_vk_digest(i);
        let (rest, j2) = read_vk_cap_n(j, n - 1);
        (store(ListNode.Cons(store(x), rest)), j2),
    }
  }

  -- ==========================================================================
  -- Node reader. A node is a single tagged record whose children (when any)
  -- are u32 NodeIds — there is no recursion over sub-expressions.
  -- ==========================================================================

  -- Dense (v5) node encoding: u16 child ids and column indices; the Var
  -- (source, offset) pair packed into the tag (10 + 2·source + offset);
  -- small (u16) / big (u64) constant split; u8 public index.
  fn read_node(i: ByteStream) -> (SysNode, ByteStream) {
    let (tag, i1) = read_vk_tag(i);
    match tag {
      0 => let (c, i2) = read_vk_u16(i1); (SysNode.Const(c), i2),
      1 => let (c, i2) = read_field(i1); (SysNode.Const(c), i2),
      2 => let (idx, i2) = read_vk_tag(i1); (SysNode.Public(idx), i2),
      3 => (SysNode.IsFirstRow, i1),
      4 => (SysNode.IsLastRow, i1),
      5 => (SysNode.IsTransition, i1),
      6 =>
        let (a, i2) = read_vk_u16(i1);
        let (b, i3) = read_vk_u16(i2);
        (SysNode.Add(a, b), i3),
      7 =>
        let (a, i2) = read_vk_u16(i1);
        let (b, i3) = read_vk_u16(i2);
        (SysNode.Sub(a, b), i3),
      8 =>
        let (a, i2) = read_vk_u16(i1);
        let (b, i3) = read_vk_u16(i2);
        (SysNode.Mul(a, b), i3),
      9 =>
        let (a, i2) = read_vk_u16(i1);
        (SysNode.Neg(a), i2),
      10 => let (idx, i2) = read_vk_u16(i1); (SysNode.Var(0, 0, idx), i2),
      11 => let (idx, i2) = read_vk_u16(i1); (SysNode.Var(0, 1, idx), i2),
      12 => let (idx, i2) = read_vk_u16(i1); (SysNode.Var(1, 0, idx), i2),
      13 => let (idx, i2) = read_vk_u16(i1); (SysNode.Var(1, 1, idx), i2),
      14 => let (idx, i2) = read_vk_u16(i1); (SysNode.Var(2, 0, idx), i2),
      _ => let (idx, i2) = read_vk_u16(i1); (SysNode.Var(2, 1, idx), i2),
    }
  }

  -- `read_node` is folded in as a TAIL match, with the cons + recursion
  -- continuation duplicated into every arm: exclusive arms share aux/lookup
  -- columns (max, not sum), so the duplication is free and the separate
  -- `read_node` circuit (49 wide) disappears. (An `@read_node` splice is not
  -- possible: its lets + tail match building the multi-variant SysNode trips
  -- the inliner — scratchpad InlineRepro case G3.)
  fn read_nodes_n(i: ByteStream, n: G) -> (List‹SysNode›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (tag, i1) = read_vk_tag(i);
        match tag {
          0 =>
            let (c, i2) = read_vk_u16(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Const(c), rest)), i3),
          1 =>
            let (c, i2) = read_field(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Const(c), rest)), i3),
          2 =>
            let (idx, i2) = read_vk_tag(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Public(idx), rest)), i3),
          3 =>
            let (rest, i3) = read_nodes_n(i1, n - 1);
            (store(ListNode.Cons(SysNode.IsFirstRow, rest)), i3),
          4 =>
            let (rest, i3) = read_nodes_n(i1, n - 1);
            (store(ListNode.Cons(SysNode.IsLastRow, rest)), i3),
          5 =>
            let (rest, i3) = read_nodes_n(i1, n - 1);
            (store(ListNode.Cons(SysNode.IsTransition, rest)), i3),
          6 =>
            let (a, i2) = read_vk_u16(i1);
            let (b, i3) = read_vk_u16(i2);
            let (rest, i4) = read_nodes_n(i3, n - 1);
            (store(ListNode.Cons(SysNode.Add(a, b), rest)), i4),
          7 =>
            let (a, i2) = read_vk_u16(i1);
            let (b, i3) = read_vk_u16(i2);
            let (rest, i4) = read_nodes_n(i3, n - 1);
            (store(ListNode.Cons(SysNode.Sub(a, b), rest)), i4),
          8 =>
            let (a, i2) = read_vk_u16(i1);
            let (b, i3) = read_vk_u16(i2);
            let (rest, i4) = read_nodes_n(i3, n - 1);
            (store(ListNode.Cons(SysNode.Mul(a, b), rest)), i4),
          9 =>
            let (a, i2) = read_vk_u16(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Neg(a), rest)), i3),
          10 =>
            let (idx, i2) = read_vk_u16(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Var(0, 0, idx), rest)), i3),
          11 =>
            let (idx, i2) = read_vk_u16(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Var(0, 1, idx), rest)), i3),
          12 =>
            let (idx, i2) = read_vk_u16(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Var(1, 0, idx), rest)), i3),
          13 =>
            let (idx, i2) = read_vk_u16(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Var(1, 1, idx), rest)), i3),
          14 =>
            let (idx, i2) = read_vk_u16(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Var(2, 0, idx), rest)), i3),
          _ =>
            let (idx, i2) = read_vk_u16(i1);
            let (rest, i3) = read_nodes_n(i2, n - 1);
            (store(ListNode.Cons(SysNode.Var(2, 1, idx), rest)), i3),
        },
    }
  }

  -- A run of u16 NodeIds (constraint roots / lookup argument ids).
  fn read_node_ids_n(i: ByteStream, n: G) -> (List‹G›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (id, i1) = read_vk_u16(i);
        let (rest, i2) = read_node_ids_n(i1, n - 1);
        (store(ListNode.Cons(id, rest)), i2),
    }
  }

  fn read_sys_lookup(i: ByteStream) -> (SysLookup, ByteStream) {
    let (m, i1) = read_vk_u16(i);
    let (ac, i2) = read_vk_u16(i1);
    let (args, i3) = read_node_ids_n(i2, ac);
    (SysLookup.Mk(m, args), i3)
  }
  fn read_sys_lookups_n(i: ByteStream, n: G) -> (List‹SysLookup›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = @read_sys_lookup(i);
        let (rest, j2) = read_sys_lookups_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  -- ⌈n/k⌉ by walking the lookups with a within-group countdown (`rem`,
  -- 0 = a new group starts on the next lookup). No in-circuit division.
  fn lookup_groups_count(n: G, rem: G, k: G) -> G {
    match n {
      0 => 0,
      _ => match rem {
        0 => 1 + lookup_groups_count(n - 1, k - 1, k),
        _ => lookup_groups_count(n - 1, rem - 1, k),
      },
    }
  }

  -- One circuit record: a u32 length prefix then the contiguous record. The
  -- 8-word header, the node stream, the zeros, and the compiled lookups
  -- (which drive the direct logUp evaluation) are all parsed. Besides the
  -- parsed circuit, returns its 7 shape words as u64 limbs, in
  -- `observe_shape` order: constraint_count (user roots + ⌈L/k⌉·D, read
  -- from the header), max_constraint_degree (combined),
  -- preprocessed_height, preprocessed_width, main_width, stage_2_width,
  -- lookup_group_size.
  fn read_sys_circuit(base: ByteStream) -> (SysCircuit, [U64; 7], ByteStream) {
    let (mw, mwl, c1) = read_vk_u16_limb(base);
    let (pw, pwl, c2) = read_vk_u16_limb(c1);
    let (ph, phl, c3) = read_vk_u32_limb(c2);
    let (md, mdl, c4) = read_vk_u16_limb(c3);
    let (k, c4b) = read_vk_tag(c4);
    let (ncount, c5) = read_vk_u16(c4b);
    let (nodes, c6) = read_nodes_n(c5, ncount);
    let (zcount, c7) = read_vk_u16(c6);
    let (zeros, c8) = read_node_ids_n(c7, zcount);
    let (lcount, c9) = read_vk_u16(c8);
    let (lks, c10) = read_sys_lookups_n(c9, lcount);
    -- Derived shape values (not serialized): constraint_count = user roots
    -- + ⌈L/k⌉·D and stage_2_width = max(⌈L/k⌉, 1)·D, their observation
    -- limbs built by byte decomposition (both values are far below 2^32, so
    -- the canonical decomposition IS the little-endian u64 limb).
    -- Grouped chained logUp: one accumulator slot and one constraint per
    -- lookup GROUP (`k` consecutive lookups; the last group may be smaller).
    -- ⌈L/k⌉ groups, +1 iff L = 0 (single pass-through slot). Branch-free so
    -- the record reader stays a single-path body: its lookups group 2 per
    -- stage-2 slot, and — with no internal match — it can @-inline into
    -- `read_sys_circuits_n` (a let-bound match here tripped the inliner).
    let groups = lookup_groups_count(lcount, 0, k);
    let gslots = groups + eq_zero(groups);
    let ccl = @gl_to_bytes(zcount + gslots + gslots);
    let s2wl = @gl_to_bytes(gslots + gslots);
    let kl = @gl_to_bytes(k);
    (SysCircuit.Mk(nodes, ncount, zeros, md, lks, k),
     [ccl, mdl, phl, pwl, mwl, s2wl, kl], c10)
  }
  fn cons_shape7(l: [U64; 7], tail: List‹U64›) -> List‹U64› {
    store(ListNode.Cons(l[0], store(ListNode.Cons(l[1], store(ListNode.Cons(l[2],
    store(ListNode.Cons(l[3], store(ListNode.Cons(l[4], store(ListNode.Cons(l[5],
    store(ListNode.Cons(l[6], tail))))))))))))))
  }
  -- Returns the circuits plus their shape limbs (`observe_shape` order: each
  -- circuit's 7 metadata words; the count limb is consed by `read_system`).
  fn read_sys_circuits_n(i: ByteStream, n: G) -> (List‹SysCircuit›, List‹U64›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), store(ListNode.Nil), i),
      _ =>
        let (x, xl, j) = @read_sys_circuit(i);
        let (rest, lrest, j2) = read_sys_circuits_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), @cons_shape7(xl, lrest), j2),
    }
  }

  -- ==========================================================================
  -- Trailer.
  -- ==========================================================================

  fn read_opt_commit(i: ByteStream) -> (OptCommit, ByteStream) {
    let (tag, j) = read_vk_u8(i);
    match tag {
      0 => (OptCommit.NoCommit, j),
      _ =>
        let (n, j1) = read_vk_u16(j);
        let (c, j2) = read_vk_cap_n(j1, n);
        (OptCommit.SomeCommit(c), j2),
    }
  }
  -- One u16 per circuit; 0xFFFF is the None sentinel.
  fn read_opt_idx_n(i: ByteStream, n: G) -> (List‹OptIdx›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (v, j) = read_vk_u16(i);
        let (rest, j2) = read_opt_idx_n(j, n - 1);
        match v {
          65535 => (store(ListNode.Cons(OptIdx.NoIdx, rest)), j2),
          _ => (store(ListNode.Cons(OptIdx.SomeIdx(v), rest)), j2),
        },
    }
  }

  -- The 7 protocol parameters, both as field values (for the verifier logic)
  -- and as u64 limbs (their LE bytes seed the challenger).
  fn read_sys_params(i: ByteStream) -> (SysParams, List‹U64›, ByteStream) {
    let (p0, l0, j0) = read_vk_u16_limb(i);
    let (p1, l1, j1) = read_vk_u16_limb(j0);
    let (p2, l2, j2) = read_vk_u16_limb(j1);
    let (p3, l3, j3) = read_vk_u16_limb(j2);
    let (p4, l4, j4) = read_vk_u16_limb(j3);
    let (p5, l5, j5) = read_vk_u16_limb(j4);
    let (p6, l6, j6) = read_vk_u16_limb(j5);
    (SysParams.Mk(p0, p1, p2, p3, p4, p5, p6),
     store(ListNode.Cons(l0, store(ListNode.Cons(l1, store(ListNode.Cons(l2,
     store(ListNode.Cons(l3, store(ListNode.Cons(l4, store(ListNode.Cons(l5,
     store(ListNode.Cons(l6, store(ListNode.Nil))))))))))))))),
     j6)
  }

  -- Full `System<AiurConfig>` parsed from the digest-bound byte stream.
  -- Returns the unconsumed suffix; the entrypoint asserts it is empty.
  fn read_system(i: ByteStream) -> (Sys, ByteStream) {
    let (params, plimbs, j) = @read_sys_params(i);
    let (n, nlimb, j1) = read_vk_u16_limb(j);
    let (circuits, climbs, j2) = read_sys_circuits_n(j1, n);
    let (commit, j3) = read_opt_commit(j2);
    let (indices, j4) = read_opt_idx_n(j3, n);
    (Sys.Mk(params,
            list_concat(plimbs, store(ListNode.Cons(nlimb, climbs))),
            circuits, commit, indices),
     j4)
  }
⟧

end MultiStark

end
