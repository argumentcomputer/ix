module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.MultiStark.Deserialize

/-!
# Verifying-key deserializer (Aiur)

Aiur port of `src/aiur/vk_codec.rs::manual_deserialize` — reconstructs the
verifier's `System<AiurCircuit>` from the bytes the prover places on the IO
channel. Same bincode wire format the Rust side validated against serde:

* enum tag       : `u32`, 4 bytes LE
* `Option`       : 1 tag byte (`0` = None, `1` = Some)
* `usize`/`u64`  : 8 bytes LE
* `Vec<T>`       : `u64` length, then elements
* struct         : fields in declaration order
* `Range<usize>` : `start`, `end` (two `u64`)
* `MerkleCap`    : `Vec<[u64; 4]>`
* Goldilocks `G` : raw `u64`, 8 bytes LE (reduced mod p on read)

The vk stream (IO channel 1) is read by byte offset with fixed-size
`io_read` chunks (no materialized byte list; digest binding hashes the
arena directly via `b3_io`). Shares the wire-level types (`Digest`,
`MerkleCap`) and `limb_to_field`/`flatten_u64` with the proof deserializer.
-/

public section

namespace MultiStark

def systemDeserialize := ⟦
  -- ==========================================================================
  -- Reconstructed `System<AiurCircuit>` as Aiur data.
  -- ==========================================================================

  -- `SymbolicVariable.entry` (a column reference within the window).
  enum SysEntry {
    Preprocessed(G),   -- offset
    Main(G),
    Stage2(G),
    Public,
    Stage2Public,
    Challenge
  }

  -- `SymbolicExpression<G>` — the AIR constraint tree. Children are pointers;
  -- the trailing `G` on Add/Sub/Neg/Mul is the cached `degree_multiple`.
  enum SymExpr {
    Var(SysEntry, G),            -- entry, index
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Const(G),                   -- a native Goldilocks constant (reduced on read)
    Add(&SymExpr, &SymExpr, G),
    Sub(&SymExpr, &SymExpr, G),
    Neg(&SymExpr, G),
    Mul(&SymExpr, &SymExpr, G)
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
  -- preprocessed_indices. The transcript limbs are the raw u64 wire words the
  -- challenger observes before any commitment — the 7 parameters (bound via
  -- the challenger seed) followed by the system shape (`observe_shape`: the
  -- circuit count, then 6 metadata words per circuit) — kept as limbs because
  -- the Fiat-Shamir replay needs their little-endian bytes.
  enum Sys { Mk(SysParams, List‹U64›, List‹SysCircuit›, OptCommit, List‹OptIdx›) }

  -- ==========================================================================
  -- Indexed byte primitives over the vk stream (IO channel 1). The vk is
  -- digest-bound via `b3_io` straight from the arena, so no byte list is ever
  -- materialized for it; the readers thread a byte offset and pull fixed-size
  -- chunks. The leaf fetches are unconstrained — the same trust boundary as
  -- the proof readers: the digest binding is what makes the bytes meaningful,
  -- and it reads the arena directly.
  -- ==========================================================================

  fn read_vk_u8(i: G) -> (U8, G) {
    let [b] = io_read(1, i, 1);
    (u8_from_field_unsafe(b), i + 1)
  }

  fn read_vk_u64(i: G) -> (U64, G) {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = io_read(1, i, 8);
    ([u8_from_field_unsafe(b0), u8_from_field_unsafe(b1),
      u8_from_field_unsafe(b2), u8_from_field_unsafe(b3),
      u8_from_field_unsafe(b4), u8_from_field_unsafe(b5),
      u8_from_field_unsafe(b6), u8_from_field_unsafe(b7)], i + 8)
  }

  fn read_vk_count(i: G) -> (G, G) {
    let (val, j) = #read_vk_u64(i);
    (flatten_u64(val), j)
  }

  -- A `u32` enum tag: 4 little-endian bytes folded into a field element.
  fn read_u32(i: G) -> (G, G) {
    let [b0, b1, b2, b3] = io_read(1, i, 4);
    (b0 + 0x100 * b1 + 0x10000 * b2 + 0x1000000 * b3, i + 4)
  }

  -- A raw `u64` Goldilocks constant, reduced into a native field value so it
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
  fn read_vk_cap(i: G) -> (MerkleCap, G) {
    let (n, j) = read_vk_count(i);
    read_vk_cap_n(j, n)
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
  -- Recursive readers (mirror `vk_codec` reader-by-reader).
  -- ==========================================================================

  fn read_sys_entry(i: G) -> (SysEntry, G) {
    let (tag, j) = #read_u32(i);
    match tag {
      0 => let (o, j1) = read_vk_count(j); (SysEntry.Preprocessed(o), j1),
      1 => let (o, j1) = read_vk_count(j); (SysEntry.Main(o), j1),
      2 => let (o, j1) = read_vk_count(j); (SysEntry.Stage2(o), j1),
      3 => (SysEntry.Public, j),
      4 => (SysEntry.Stage2Public, j),
      _ => (SysEntry.Challenge, j),
    }
  }

  fn read_sym_expr(i: G) -> (SymExpr, G) {
    let (tag, j) = #read_u32(i);
    match tag {
      0 =>
        let (e, j1) = read_sys_entry(j);
        let (x, j2) = read_vk_count(j1);
        (SymExpr.Var(e, x), j2),
      1 => (SymExpr.IsFirstRow, j),
      2 => (SymExpr.IsLastRow, j),
      3 => (SymExpr.IsTransition, j),
      4 => let (c, j1) = #read_field(j); (SymExpr.Const(c), j1),
      5 =>
        let (x, j1) = read_sym_expr(j);
        let (y, j2) = read_sym_expr(j1);
        let (d, j3) = read_vk_count(j2);
        (SymExpr.Add(store(x), store(y), d), j3),
      6 =>
        let (x, j1) = read_sym_expr(j);
        let (y, j2) = read_sym_expr(j1);
        let (d, j3) = read_vk_count(j2);
        (SymExpr.Sub(store(x), store(y), d), j3),
      7 =>
        let (x, j1) = read_sym_expr(j);
        let (d, j2) = read_vk_count(j1);
        (SymExpr.Neg(store(x), d), j2),
      _ =>
        let (x, j1) = read_sym_expr(j);
        let (y, j2) = read_sym_expr(j1);
        let (d, j3) = read_vk_count(j2);
        (SymExpr.Mul(store(x), store(y), d), j3),
    }
  }

  fn read_sym_exprs(i: G) -> (List‹SymExpr›, G) {
    let (n, j) = read_vk_count(i);
    read_sym_exprs_n(j, n)
  }
  fn read_sym_exprs_n(i: G, n: G) -> (List‹SymExpr›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_sym_expr(i);
        let (rest, j2) = read_sym_exprs_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_sys_lookup(i: G) -> (SysLookup, G) {
    let (m, j) = read_sym_expr(i);
    let (args, j2) = read_sym_exprs(j);
    (SysLookup.Mk(m, args), j2)
  }
  fn read_sys_lookups(i: G) -> (List‹SysLookup›, G) {
    let (n, j) = read_vk_count(i);
    read_sys_lookups_n(j, n)
  }
  fn read_sys_lookups_n(i: G, n: G) -> (List‹SysLookup›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_sys_lookup(i);
        let (rest, j2) = read_sys_lookups_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  fn read_sys_constraints(i: G) -> (SysConstraints, G) {
    let (zeros, j) = read_sym_exprs(i);
    let (sel_start, j1) = read_vk_count(j);
    let (sel_end, j2) = read_vk_count(j1);
    let (width, j3) = read_vk_count(j2);
    (SysConstraints.Mk(zeros, sel_start, sel_end, width), j3)
  }

  fn read_sys_air(i: G) -> (SysAir, G) {
    let (tag, j) = #read_u32(i);
    match tag {
      0 => let (c, j1) = read_sys_constraints(j); (SysAir.Function(c), j1),
      1 => let (w, j1) = read_vk_count(j); (SysAir.Memory(SysMemory.Mk(w)), j1),
      2 => (SysAir.Bytes1, j),
      _ => (SysAir.Bytes2, j),
    }
  }

  fn read_sys_lookupair(i: G) -> (SysLookupAir, G) {
    let (inner, j) = read_sys_air(i);
    let (lookups, j1) = read_sys_lookups(j);
    (SysLookupAir.Mk(inner, lookups), j1)
  }

  -- Besides the parsed circuit, also returns its 6 metadata words as raw u64
  -- limbs — `observe_shape` feeds exactly these bytes into the challenger.
  fn read_sys_circuit(i: G) -> (SysCircuit, [U64; 6], G) {
    let (air, j) = read_sys_lookupair(i);
    let (cc, j1) = #read_vk_u64(j);
    let (md, j2) = #read_vk_u64(j1);
    let (ph, j3) = #read_vk_u64(j2);
    let (pw, j4) = #read_vk_u64(j3);
    let (w1, j5) = #read_vk_u64(j4);
    let (w2, j6) = #read_vk_u64(j5);
    (SysCircuit.Mk(air, flatten_u64(cc), flatten_u64(md), flatten_u64(ph),
                   flatten_u64(pw), flatten_u64(w1), flatten_u64(w2)),
     [cc, md, ph, pw, w1, w2], j6)
  }
  fn cons_shape6(l: [U64; 6], tail: List‹U64›) -> List‹U64› {
    store(ListNode.Cons(l[0], store(ListNode.Cons(l[1], store(ListNode.Cons(l[2],
    store(ListNode.Cons(l[3], store(ListNode.Cons(l[4], store(ListNode.Cons(l[5],
    tail))))))))))))
  }
  -- Returns the circuits plus their shape limbs (`observe_shape` order: the
  -- raw circuit-count word, then each circuit's 6 metadata words).
  fn read_sys_circuits(i: G) -> (List‹SysCircuit›, List‹U64›, G) {
    let (nl, j) = #read_vk_u64(i);
    let (cs, limbs, j1) = read_sys_circuits_n(j, flatten_u64(nl));
    (cs, store(ListNode.Cons(nl, limbs)), j1)
  }
  fn read_sys_circuits_n(i: G, n: G) -> (List‹SysCircuit›, List‹U64›, G) {
    match n {
      0 => (store(ListNode.Nil), store(ListNode.Nil), i),
      _ =>
        let (x, xl, j) = read_sys_circuit(i);
        let (rest, lrest, j2) = read_sys_circuits_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), cons_shape6(xl, lrest), j2),
    }
  }

  -- `Option` tag is a single byte (bincode special-cases Option).
  fn read_opt_commit(i: G) -> (OptCommit, G) {
    let (tag, j) = #read_vk_u8(i);
    match tag {
      0 => (OptCommit.NoCommit, j),
      _ => let (c, j1) = read_vk_cap(j); (OptCommit.SomeCommit(c), j1),
    }
  }
  fn read_opt_idx(i: G) -> (OptIdx, G) {
    let (tag, j) = #read_vk_u8(i);
    match tag {
      0 => (OptIdx.NoIdx, j),
      _ => let (x, j1) = read_vk_count(j); (OptIdx.SomeIdx(x), j1),
    }
  }
  fn read_opt_idx_list(i: G) -> (List‹OptIdx›, G) {
    let (n, j) = read_vk_count(i);
    read_opt_idx_list_n(j, n)
  }
  fn read_opt_idx_list_n(i: G, n: G) -> (List‹OptIdx›, G) {
    match n {
      0 => (store(ListNode.Nil), i),
      _ =>
        let (x, j) = read_opt_idx(i);
        let (rest, j2) = read_opt_idx_list_n(j, n - 1);
        (store(ListNode.Cons(x, rest)), j2),
    }
  }

  -- The 7 protocol parameters, both as field counts (for the verifier logic)
  -- and as raw u64 limbs (their LE bytes seed the challenger).
  fn read_sys_params(i: G) -> (SysParams, List‹U64›, G) {
    let (l0, j0) = #read_vk_u64(i);
    let (l1, j1) = #read_vk_u64(j0);
    let (l2, j2) = #read_vk_u64(j1);
    let (l3, j3) = #read_vk_u64(j2);
    let (l4, j4) = #read_vk_u64(j3);
    let (l5, j5) = #read_vk_u64(j4);
    let (l6, j6) = #read_vk_u64(j5);
    (SysParams.Mk(flatten_u64(l0), flatten_u64(l1), flatten_u64(l2),
                  flatten_u64(l3), flatten_u64(l4), flatten_u64(l5),
                  flatten_u64(l6)),
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
    let (circuits, climbs, j1) = read_sys_circuits(j);
    let (commit, j2) = read_opt_commit(j1);
    let (indices, j3) = read_opt_idx_list(j2);
    (Sys.Mk(params, list_concat(plimbs, climbs), circuits, commit, indices), j3)
  }
⟧

end MultiStark

end
