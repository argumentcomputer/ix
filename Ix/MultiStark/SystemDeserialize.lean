module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.MultiStark.Deserialize

/-!
# Verifying-key deserializer (Aiur)

Aiur port of `crates/aiur/src/vk_codec.rs` — reconstructs the verifier's
`System<AiurConfig>` from the bytes the prover places on the IO channel.

Wire format (v3, mirrors `vk_codec.rs` — see its module docs for the full
layout). The multi-stark constraint-IR migration replaced the per-circuit
*symbolic* AIR (`SymbolicExpression` trees + `LookupAir`) with a *compiled*
flat base-field node graph, so this reader parses that compiled form:

* GLOBAL HEADER: 7 × u16 parameters + u16 circuit count.
* PER-CIRCUIT RECORD: a `u32 LE len` prefix followed by exactly `len`
  contiguous bytes —
    - 8 × u32: main_width, preprocessed_width, preprocessed_height,
      num_publics, stage_2_width, max_constraint_degree, lookup_prefix_len,
      node_count
    - `node_count` tagged nodes (children are u32 NodeIds, never sub-trees):
      0 Const(u64) · 1 Var(u8 source, u8 offset, u32 index) · 2 Public(u32) ·
      3 IsFirstRow · 4 IsLastRow · 5 IsTransition ·
      6 Add(u32,u32) · 7 Sub(u32,u32) · 8 Mul(u32,u32) · 9 Neg(u32)
    - u32 zero_count, then that many u32 constraint-root NodeIds
    - u32 lookup_count, then the compiled lookups (multiplicity + args as
      NodeIds) — the verifier does NOT need these (the lookup argument's
      constraints are compiled into `zeros`), so the reader SKIPS them via
      the record length prefix.
* TRAILER: preprocessed commit (`0` = None / `1` + MerkleCap) then one u16
  per circuit for the preprocessed index (`0xFFFF` = None).

The vk stream (IO channel 1) is read by byte offset with a single cursor —
a v3 record is a contiguous byte range, so there are no separate segment
cursors. The leaf fetches are unconstrained; the digest binding (`b3_io`
over the whole arena, bound to the public `system_digest`) is what makes
the bytes meaningful. Per-node degrees are neither serialized nor needed
(the node sweep just evaluates the graph).

The Fiat-Shamir shape limbs are unchanged from v2: `observe_shape` still
feeds the challenger the circuit count then, per circuit, the six words
constraint_count, max_constraint_degree, preprocessed_height,
preprocessed_width, main_width, stage_2_width (as 8-byte LE limbs).
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
  enum SysCircuit { Mk(List‹SysNode›, G, List‹G›, G) }   -- nodes, node_count, zeros, max_constraint_degree

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
  -- Indexed byte primitives over the vk stream (IO channel 1). Fixed-size
  -- chunks only; each returns the advanced cursor. The `_limb` variants also
  -- return the value's 8-LE-byte u64 limb for the Fiat-Shamir replay.
  -- ==========================================================================

  fn read_vk_u8(i: G) -> (U8, G) {
    let [b] = io_read(1, i, 1);
    (u8_from_field_unsafe(b), i + 1)
  }

  -- A single byte kept as a raw field value for match dispatch (tags, source,
  -- offset).
  fn read_vk_tag(i: G) -> (G, G) {
    let [b] = io_read(1, i, 1);
    (b, i + 1)
  }

  fn read_vk_u16(i: G) -> (G, G) {
    let [b0, b1] = io_read(1, i, 2);
    (b0 + 0x100 * b1, i + 2)
  }

  fn read_vk_u16_limb(i: G) -> (G, U64, G) {
    let [b0, b1] = io_read(1, i, 2);
    (b0 + 0x100 * b1,
     [u8_from_field_unsafe(b0), u8_from_field_unsafe(b1),
      0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
     i + 2)
  }

  fn read_vk_u32(i: G) -> (G, G) {
    let [b0, b1, b2, b3] = io_read(1, i, 4);
    (b0 + 0x100 * b1 + 0x10000 * b2 + 0x1000000 * b3, i + 4)
  }

  fn read_vk_u32_limb(i: G) -> (G, U64, G) {
    let [b0, b1, b2, b3] = io_read(1, i, 4);
    (b0 + 0x100 * b1 + 0x10000 * b2 + 0x1000000 * b3,
     [u8_from_field_unsafe(b0), u8_from_field_unsafe(b1),
      u8_from_field_unsafe(b2), u8_from_field_unsafe(b3),
      0u8, 0u8, 0u8, 0u8],
     i + 4)
  }

  fn read_vk_u64(i: G) -> (U64, G) {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = io_read(1, i, 8);
    ([u8_from_field_unsafe(b0), u8_from_field_unsafe(b1),
      u8_from_field_unsafe(b2), u8_from_field_unsafe(b3),
      u8_from_field_unsafe(b4), u8_from_field_unsafe(b5),
      u8_from_field_unsafe(b6), u8_from_field_unsafe(b7)], i + 8)
  }

  -- A full (u64) Goldilocks constant, reduced into a native field value so it
  -- can feed the composition arithmetic directly.
  fn read_field(i: G) -> (G, G) {
    let (u, j) = #read_vk_u64(i);
    (gl_val(u), j)
  }

  fn read_vk_digest(i: G) -> (Digest, G) {
    let (a, j0) = #read_vk_u64(i);
    let (b, j1) = #read_vk_u64(j0);
    let (c, j2) = #read_vk_u64(j1);
    let (d, j3) = #read_vk_u64(j2);
    ([a, b, c, d], j3)
  }
  fn read_vk_cap_n(i: G, n: G) -> (MerkleCap, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_vk_digest(i);
        let (rest, j2) = read_vk_cap_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  -- ==========================================================================
  -- Node reader. A node is a single tagged record whose children (when any)
  -- are u32 NodeIds — there is no recursion over sub-expressions.
  -- ==========================================================================

  fn read_node(i: G) -> (SysNode, G) {
    let (tag, i1) = #read_vk_tag(i);
    match tag {
      0 => let (c, i2) = #read_field(i1); (SysNode.Const(c), i2),
      1 =>
        let (s, i2) = #read_vk_tag(i1);
        let (o, i3) = #read_vk_tag(i2);
        let (idx, i4) = #read_vk_u32(i3);
        (SysNode.Var(s, o, idx), i4),
      2 => let (idx, i2) = #read_vk_u32(i1); (SysNode.Public(idx), i2),
      3 => (SysNode.IsFirstRow, i1),
      4 => (SysNode.IsLastRow, i1),
      5 => (SysNode.IsTransition, i1),
      6 =>
        let (a, i2) = #read_vk_u32(i1);
        let (b, i3) = #read_vk_u32(i2);
        (SysNode.Add(a, b), i3),
      7 =>
        let (a, i2) = #read_vk_u32(i1);
        let (b, i3) = #read_vk_u32(i2);
        (SysNode.Sub(a, b), i3),
      8 =>
        let (a, i2) = #read_vk_u32(i1);
        let (b, i3) = #read_vk_u32(i2);
        (SysNode.Mul(a, b), i3),
      _ =>
        let (a, i2) = #read_vk_u32(i1);
        (SysNode.Neg(a), i2),
    }
  }

  fn read_nodes_n(i: G, n: G) -> (List‹SysNode›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (nd, i1) = read_node(i);
        let (rest, i2) = read_nodes_n(i1, n - 1);
        (store(ListNode.Cons(nd, rest)), i2),
    }
  }

  -- A run of u32 NodeIds (the `zeros` constraint roots).
  fn read_node_ids_n(i: G, n: G) -> (List‹G›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (id, i1) = #read_vk_u32(i);
        let (rest, i2) = read_node_ids_n(i1, n - 1);
        (store(ListNode.Cons(id, rest)), i2),
    }
  }

  -- One circuit record: a u32 length prefix then the contiguous record. The
  -- 8-word header, the node stream, and the zeros are parsed; the compiled
  -- lookups (which the verifier does not use) are skipped by jumping to the
  -- record end via the length prefix. Besides the parsed circuit, returns its
  -- 6 shape words as u64 limbs, in `observe_shape` order: constraint_count
  -- (= zero_count), max_constraint_degree, preprocessed_height,
  -- preprocessed_width, main_width, stage_2_width.
  fn read_sys_circuit(base: G) -> (SysCircuit, [U64; 6], G) {
    let (rec_len, r0) = #read_vk_u32(base);
    let (mw, mwl, c1) = #read_vk_u32_limb(r0);
    let (pw, pwl, c2) = #read_vk_u32_limb(c1);
    let (ph, phl, c3) = #read_vk_u32_limb(c2);
    let (np, c4) = #read_vk_u32(c3);
    let (s2w, s2wl, c5) = #read_vk_u32_limb(c4);
    let (md, mdl, c6) = #read_vk_u32_limb(c5);
    let (lpl, c7) = #read_vk_u32(c6);
    let (ncount, c8) = #read_vk_u32(c7);
    let (nodes, c9) = read_nodes_n(c8, ncount);
    let (zcount, zcl, c10) = #read_vk_u32_limb(c9);
    let (zeros, c11) = read_node_ids_n(c10, zcount);
    -- The remaining bytes of the record are the compiled lookups; skip them.
    let rend = r0 + rec_len;
    (SysCircuit.Mk(nodes, ncount, zeros, md),
     [zcl, mdl, phl, pwl, mwl, s2wl], rend)
  }
  fn cons_shape6(l: [U64; 6], tail: List‹U64›) -> List‹U64› {
    store(ListNode.Cons(l[0], store(ListNode.Cons(l[1], store(ListNode.Cons(l[2],
    store(ListNode.Cons(l[3], store(ListNode.Cons(l[4], store(ListNode.Cons(l[5],
    tail))))))))))))
  }
  -- Returns the circuits plus their shape limbs (`observe_shape` order: each
  -- circuit's 6 metadata words; the count limb is consed by `read_system`).
  fn read_sys_circuits_n(i: G, n: G) -> (List‹SysCircuit›, List‹U64›, G) {
    match n {
      0 => (store(ListNode.Nil), store(ListNode.Nil), i),
      _ =>
        let (x, xl, j) = read_sys_circuit(i);
        let (rest, lrest, j2) = read_sys_circuits_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), cons_shape6(xl, lrest), j2),
    }
  }

  -- ==========================================================================
  -- Trailer.
  -- ==========================================================================

  fn read_opt_commit(i: G) -> (OptCommit, G) {
    let (tag, j) = #read_vk_u8(i);
    match tag {
      0 => (OptCommit.NoCommit, j),
      _ =>
        let (n, j1) = #read_vk_u16(j);
        let (c, j2) = read_vk_cap_n(j1, n);
        (OptCommit.SomeCommit(c), j2),
    }
  }
  -- One u16 per circuit; 0xFFFF is the None sentinel.
  fn read_opt_idx_n(i: G, n: G) -> (List‹OptIdx›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (v, j) = #read_vk_u16(i);
        let (rest, j2) = read_opt_idx_n(j, n - 1);
        match v {
          65535 => (store(ListNode.Cons(OptIdx.NoIdx, rest)), j2),
          _ => (store(ListNode.Cons(OptIdx.SomeIdx(v), rest)), j2),
        },
    }
  }

  -- The 7 protocol parameters, both as field values (for the verifier logic)
  -- and as u64 limbs (their LE bytes seed the challenger).
  fn read_sys_params(i: G) -> (SysParams, List‹U64›, G) {
    let (p0, l0, j0) = #read_vk_u16_limb(i);
    let (p1, l1, j1) = #read_vk_u16_limb(j0);
    let (p2, l2, j2) = #read_vk_u16_limb(j1);
    let (p3, l3, j3) = #read_vk_u16_limb(j2);
    let (p4, l4, j4) = #read_vk_u16_limb(j3);
    let (p5, l5, j5) = #read_vk_u16_limb(j4);
    let (p6, l6, j6) = #read_vk_u16_limb(j5);
    (SysParams.Mk(p0, p1, p2, p3, p4, p5, p6),
     store(ListNode.Cons(l0, store(ListNode.Cons(l1, store(ListNode.Cons(l2,
     store(ListNode.Cons(l3, store(ListNode.Cons(l4, store(ListNode.Cons(l5,
     store(ListNode.Cons(l6, store(ListNode.Nil))))))))))))))),
     j6)
  }

  -- Full `System<AiurConfig>`, read from the channel-1 IO arena starting at
  -- byte offset `i`. Returns the end offset; the entrypoint asserts full
  -- consumption.
  fn read_system(i: G) -> (Sys, G) {
    let (params, plimbs, j) = read_sys_params(i);
    let (n, nlimb, j1) = #read_vk_u16_limb(j);
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
