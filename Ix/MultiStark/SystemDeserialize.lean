module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.MultiStark.Deserialize

/-!
# Verifying-key deserializer (Aiur)

Aiur port of `crates/aiur/src/vk_codec.rs` — reconstructs the verifier's
`System<AiurCircuit>` from the bytes the prover places on the IO channel.

Split-streams wire format (v2, mirrors `vk_codec.rs` — see its module docs
for the full layout): a global header (7 × u16 parameters + u16 circuit
count), then one contiguous record per circuit — 5 × u32 segment lengths
followed by the TAGS / IDX / C2 / C8 / META segments — then the trailer
(preprocessed commit + u16 preprocessed indices, `0xFFFF` = None). Every
field class has a single fixed width, so all reads are static-size
`io_read` chunks:

* TAGS : 1 byte per node — low nibble = kind, high nibble = aux
         (Variable: entry kind + 8·rotation; Constant: size class)
* IDX  : u16 per Variable (column index)
* C2   : u16 per small constant; C8 : u64 per large constant
* META : u32 per count / metadata field

`degree_multiple` is not on the wire (and unused by the verifier — the
constraint folder just evaluates the tree), so `SymExpr` no longer carries
it. The vk stream (IO channel 1) is read by byte offset — the readers
thread one cursor per segment; the record header binds the cursors and the
per-record end asserts pin each segment's exact consumption. The leaf
fetches are unconstrained — the digest binding (`b3_io` over the whole
arena) is what makes the bytes meaningful.
-/

public section

namespace MultiStark

def systemDeserialize := ⟦
  -- ==========================================================================
  -- Reconstructed `System<AiurCircuit>` as Aiur data.
  -- ==========================================================================

  -- `SymbolicVariable.entry` (a column reference within the window). The
  -- payload of Preprocessed/Main/Stage2 is the rotation offset (0 or 1).
  enum SysEntry {
    Preprocessed(G),
    Main(G),
    Stage2(G),
    Public,
    Stage2Public,
    Challenge
  }

  -- `SymbolicExpression<G>` — the AIR constraint tree. Children are pointers.
  -- (`degree_multiple` is not materialized: the wire drops it and the
  -- constraint folder never reads it.)
  enum SymExpr {
    Var(SysEntry, G),            -- entry, index
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Const(G),                   -- a native Goldilocks constant (reduced on read)
    Add(&SymExpr, &SymExpr),
    Sub(&SymExpr, &SymExpr),
    Neg(&SymExpr),
    Mul(&SymExpr, &SymExpr)
  }

  enum SysLookup { Mk(SymExpr, List‹SymExpr›) }          -- multiplicity, args

  enum SysConstraints { Mk(List‹SymExpr›, G, G, G) }     -- zeros, sel_start, sel_end, width

  enum SysMemory { Mk(G) }                               -- width

  enum SysAir {
    Function(SysConstraints),
    Memory(SysMemory),
    Bytes1,
    Bytes2
  }

  enum SysLookupAir { Mk(SysAir, List‹SysLookup›) }      -- inner_air, lookups

  -- air, constraint_count, max_constraint_degree, preprocessed_height,
  -- preprocessed_width, stage_1_width, stage_2_width.
  enum SysCircuit { Mk(SysLookupAir, G, G, G, G, G, G) }

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
  -- the Fiat-Shamir replay needs their little-endian bytes. The OBSERVED
  -- values are width-independent, so the narrow wire fields pad to the same
  -- 8-byte limbs v1 produced.
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

  -- A TAGS byte, kept as a raw field value for match dispatch.
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

  -- A large (C8) Goldilocks constant, reduced into a native field value so it
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
  -- Expression reader. Cursors: t = TAGS, x = IDX, a = C2, b = C8. The tag
  -- byte packs kind (low nibble) + aux (high nibble); the match keys are the
  -- whole byte values (kind + 16·aux).
  -- ==========================================================================

  fn read_sym_expr(t: G, x: G, a: G, b: G) -> (SymExpr, G, G, G, G) {
    let (tag, t1) = #read_vk_tag(t);
    match tag {
      -- Var: aux = entry kind + 8·rotation
      0 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Preprocessed(0), i), t1, x1, a, b),
      16 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Main(0), i), t1, x1, a, b),
      32 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Stage2(0), i), t1, x1, a, b),
      48 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Public, i), t1, x1, a, b),
      64 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Stage2Public, i), t1, x1, a, b),
      80 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Challenge, i), t1, x1, a, b),
      128 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Preprocessed(1), i), t1, x1, a, b),
      144 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Main(1), i), t1, x1, a, b),
      160 => let (i, x1) = #read_vk_u16(x); (SymExpr.Var(SysEntry.Stage2(1), i), t1, x1, a, b),
      1 => (SymExpr.IsFirstRow, t1, x, a, b),
      2 => (SymExpr.IsLastRow, t1, x, a, b),
      3 => (SymExpr.IsTransition, t1, x, a, b),
      -- Const: aux = size class (0 -> C2, 1 -> C8)
      4 => let (c, a1) = #read_vk_u16(a); (SymExpr.Const(c), t1, x, a1, b),
      20 => let (c, b1) = #read_field(b); (SymExpr.Const(c), t1, x, a, b1),
      5 =>
        let (l, t2, x2, a2, b2) = read_sym_expr(t1, x, a, b);
        let (r, t3, x3, a3, b3) = read_sym_expr(t2, x2, a2, b2);
        (SymExpr.Add(store(l), store(r)), t3, x3, a3, b3),
      6 =>
        let (l, t2, x2, a2, b2) = read_sym_expr(t1, x, a, b);
        let (r, t3, x3, a3, b3) = read_sym_expr(t2, x2, a2, b2);
        (SymExpr.Sub(store(l), store(r)), t3, x3, a3, b3),
      7 =>
        let (l, t2, x2, a2, b2) = read_sym_expr(t1, x, a, b);
        (SymExpr.Neg(store(l)), t2, x2, a2, b2),
      _ =>
        let (l, t2, x2, a2, b2) = read_sym_expr(t1, x, a, b);
        let (r, t3, x3, a3, b3) = read_sym_expr(t2, x2, a2, b2);
        (SymExpr.Mul(store(l), store(r)), t3, x3, a3, b3),
    }
  }

  fn read_sym_exprs_n(t: G, x: G, a: G, b: G, n: G) -> (List‹SymExpr›, G, G, G, G) {
    match n {
      0 => (store(ListNode.Nil), t, x, a, b),
      _ =>
        let (e, t1, x1, a1, b1) = read_sym_expr(t, x, a, b);
        let (rest, t2, x2, a2, b2) = read_sym_exprs_n(t1, x1, a1, b1, n - 1);
        (store(ListNode.Cons(e, rest)), t2, x2, a2, b2),
    }
  }

  -- ==========================================================================
  -- Circuit readers. Cursor m = META joins for the count/metadata fields.
  -- ==========================================================================

  fn read_sys_lookup(t: G, x: G, a: G, b: G, m: G) -> (SysLookup, G, G, G, G, G) {
    let (mul, t1, x1, a1, b1) = read_sym_expr(t, x, a, b);
    let (na, m1) = #read_vk_u32(m);
    let (args, t2, x2, a2, b2) = read_sym_exprs_n(t1, x1, a1, b1, na);
    (SysLookup.Mk(mul, args), t2, x2, a2, b2, m1)
  }
  fn read_sys_lookups_n(t: G, x: G, a: G, b: G, m: G, n: G) -> (List‹SysLookup›, G, G, G, G, G) {
    match n {
      0 => (store(ListNode.Nil), t, x, a, b, m),
      _ =>
        let (l, t1, x1, a1, b1, m1) = read_sys_lookup(t, x, a, b, m);
        let (rest, t2, x2, a2, b2, m2) = read_sys_lookups_n(t1, x1, a1, b1, m1, n - 1);
        (store(ListNode.Cons(l, rest)), t2, x2, a2, b2, m2),
    }
  }

  fn read_sys_air(t: G, x: G, a: G, b: G, m: G) -> (SysAir, G, G, G, G, G) {
    let (tag, t1) = #read_vk_tag(t);
    match tag {
      0 =>
        let (nz, m1) = #read_vk_u32(m);
        let (zeros, t2, x2, a2, b2) = read_sym_exprs_n(t1, x, a, b, nz);
        let (ss, m2) = #read_vk_u32(m1);
        let (se, m3) = #read_vk_u32(m2);
        let (w, m4) = #read_vk_u32(m3);
        (SysAir.Function(SysConstraints.Mk(zeros, ss, se, w)), t2, x2, a2, b2, m4),
      1 => let (w, m1) = #read_vk_u32(m); (SysAir.Memory(SysMemory.Mk(w)), t1, x, a, b, m1),
      2 => (SysAir.Bytes1, t1, x, a, b, m),
      _ => (SysAir.Bytes2, t1, x, a, b, m),
    }
  }

  -- One circuit record: 5 × u32 segment lengths, then the segments. Besides
  -- the parsed circuit, also returns its 6 metadata words as u64 limbs —
  -- `observe_shape` feeds exactly these bytes into the challenger. The end
  -- asserts pin every segment to exact consumption, binding the header
  -- lengths to the parsed structure.
  fn read_sys_circuit(base: G) -> (SysCircuit, [U64; 6], G) {
    let (lt, h1) = #read_vk_u32(base);
    let (lx, h2) = #read_vk_u32(h1);
    let (la, h3) = #read_vk_u32(h2);
    let (lb, h4) = #read_vk_u32(h3);
    let (lm, h5) = #read_vk_u32(h4);
    let t0 = h5;
    let x0 = t0 + lt;
    let a0 = x0 + lx;
    let b0 = a0 + la;
    let m0 = b0 + lb;
    let rend = m0 + lm;
    let (air, t1, x1, a1, b1, m1) = read_sys_air(t0, x0, a0, b0, m0);
    let (nl, m2) = #read_vk_u32(m1);
    let (lookups, t2, x2, a2, b2, m3) = read_sys_lookups_n(t1, x1, a1, b1, m2, nl);
    let (cc, ccl, m4) = #read_vk_u32_limb(m3);
    let (md, mdl, m5) = #read_vk_u32_limb(m4);
    let (ph, phl, m6) = #read_vk_u32_limb(m5);
    let (pw, pwl, m7) = #read_vk_u32_limb(m6);
    let (w1, w1l, m8) = #read_vk_u32_limb(m7);
    let (w2, w2l, m9) = #read_vk_u32_limb(m8);
    assert_eq!(t2, x0);
    assert_eq!(x2, a0);
    assert_eq!(a2, b0);
    assert_eq!(b2, m0);
    assert_eq!(m9, rend);
    (SysCircuit.Mk(SysLookupAir.Mk(air, lookups), cc, md, ph, pw, w1, w2),
     [ccl, mdl, phl, pwl, w1l, w2l], rend)
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

  -- Full `System<AiurCircuit>`, read from the channel-1 IO arena starting at
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
