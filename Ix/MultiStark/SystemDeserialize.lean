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

Reuses the proof deserializer's byte primitives (`read_u8`, `read_u64`,
`read_count`, `read_merkle_cap`, `limb_to_field`, `Digest`, `MerkleCap`).
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
    Const(G),
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

  enum SysParams { Mk(G, G) }                            -- log_blowup, cap_height

  -- `Option`s as dedicated non-generic enums (unambiguous constructors).
  enum OptCommit { NoCommit, SomeCommit(MerkleCap) }
  enum OptIdx { NoIdx, SomeIdx(G) }

  -- commitment_parameters, circuits, preprocessed_commit, preprocessed_indices.
  enum Sys { Mk(SysParams, List‹SysCircuit›, OptCommit, List‹OptIdx›) }

  -- ==========================================================================
  -- Byte primitives specific to the VK format.
  -- ==========================================================================

  -- A `u32` enum tag: 4 little-endian bytes folded into a field element.
  fn read_u32(stream: ByteStream) -> (G, ByteStream) {
    let (b0, s0) = read_u8(stream);
    let (b1, s1) = read_u8(s0);
    let (b2, s2) = read_u8(s1);
    let (b3, s3) = read_u8(s2);
    (to_field(b0) + 0x100 * to_field(b1) + 0x10000 * to_field(b2)
       + 0x1000000 * to_field(b3), s3)
  }

  -- A raw `u64` Goldilocks value, reduced mod p (for `Constant`).
  fn read_field(stream: ByteStream) -> (G, ByteStream) {
    let (u, s) = read_u64(stream);
    (limb_to_field(u), s)
  }

  -- ==========================================================================
  -- Recursive readers (mirror `vk_codec` reader-by-reader).
  -- ==========================================================================

  fn read_sys_entry(stream: ByteStream) -> (SysEntry, ByteStream) {
    let (tag, s) = read_u32(stream);
    match tag {
      0 => let (o, s1) = read_count(s); (SysEntry.Preprocessed(o), s1),
      1 => let (o, s1) = read_count(s); (SysEntry.Main(o), s1),
      2 => let (o, s1) = read_count(s); (SysEntry.Stage2(o), s1),
      3 => (SysEntry.Public, s),
      4 => (SysEntry.Stage2Public, s),
      _ => (SysEntry.Challenge, s),
    }
  }

  fn read_sym_expr(stream: ByteStream) -> (SymExpr, ByteStream) {
    let (tag, s) = read_u32(stream);
    match tag {
      0 =>
        let (e, s1) = read_sys_entry(s);
        let (i, s2) = read_count(s1);
        (SymExpr.Var(e, i), s2),
      1 => (SymExpr.IsFirstRow, s),
      2 => (SymExpr.IsLastRow, s),
      3 => (SymExpr.IsTransition, s),
      4 => let (c, s1) = read_field(s); (SymExpr.Const(c), s1),
      5 =>
        let (x, s1) = read_sym_expr(s);
        let (y, s2) = read_sym_expr(s1);
        let (d, s3) = read_count(s2);
        (SymExpr.Add(store(x), store(y), d), s3),
      6 =>
        let (x, s1) = read_sym_expr(s);
        let (y, s2) = read_sym_expr(s1);
        let (d, s3) = read_count(s2);
        (SymExpr.Sub(store(x), store(y), d), s3),
      7 =>
        let (x, s1) = read_sym_expr(s);
        let (d, s2) = read_count(s1);
        (SymExpr.Neg(store(x), d), s2),
      _ =>
        let (x, s1) = read_sym_expr(s);
        let (y, s2) = read_sym_expr(s1);
        let (d, s3) = read_count(s2);
        (SymExpr.Mul(store(x), store(y), d), s3),
    }
  }

  fn read_sym_exprs(stream: ByteStream) -> (List‹SymExpr›, ByteStream) {
    let (n, s) = read_count(stream);
    read_sym_exprs_n(s, n)
  }
  fn read_sym_exprs_n(stream: ByteStream, n: G) -> (List‹SymExpr›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_sym_expr(stream);
        let (rest, s2) = read_sym_exprs_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_sys_lookup(stream: ByteStream) -> (SysLookup, ByteStream) {
    let (m, s) = read_sym_expr(stream);
    let (args, s2) = read_sym_exprs(s);
    (SysLookup.Mk(m, args), s2)
  }
  fn read_sys_lookups(stream: ByteStream) -> (List‹SysLookup›, ByteStream) {
    let (n, s) = read_count(stream);
    read_sys_lookups_n(s, n)
  }
  fn read_sys_lookups_n(stream: ByteStream, n: G) -> (List‹SysLookup›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_sys_lookup(stream);
        let (rest, s2) = read_sys_lookups_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_sys_constraints(stream: ByteStream) -> (SysConstraints, ByteStream) {
    let (zeros, s) = read_sym_exprs(stream);
    let (sel_start, s1) = read_count(s);
    let (sel_end, s2) = read_count(s1);
    let (width, s3) = read_count(s2);
    (SysConstraints.Mk(zeros, sel_start, sel_end, width), s3)
  }

  fn read_sys_air(stream: ByteStream) -> (SysAir, ByteStream) {
    let (tag, s) = read_u32(stream);
    match tag {
      0 => let (c, s1) = read_sys_constraints(s); (SysAir.Function(c), s1),
      1 => let (w, s1) = read_count(s); (SysAir.Memory(SysMemory.Mk(w)), s1),
      2 => (SysAir.Bytes1, s),
      _ => (SysAir.Bytes2, s),
    }
  }

  fn read_sys_lookupair(stream: ByteStream) -> (SysLookupAir, ByteStream) {
    let (inner, s) = read_sys_air(stream);
    let (lookups, s1) = read_sys_lookups(s);
    (SysLookupAir.Mk(inner, lookups), s1)
  }

  fn read_sys_circuit(stream: ByteStream) -> (SysCircuit, ByteStream) {
    let (air, s) = read_sys_lookupair(stream);
    let (cc, s1) = read_count(s);
    let (md, s2) = read_count(s1);
    let (ph, s3) = read_count(s2);
    let (pw, s4) = read_count(s3);
    let (w1, s5) = read_count(s4);
    let (w2, s6) = read_count(s5);
    (SysCircuit.Mk(air, cc, md, ph, pw, w1, w2), s6)
  }
  fn read_sys_circuits(stream: ByteStream) -> (List‹SysCircuit›, ByteStream) {
    let (n, s) = read_count(stream);
    read_sys_circuits_n(s, n)
  }
  fn read_sys_circuits_n(stream: ByteStream, n: G) -> (List‹SysCircuit›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_sys_circuit(stream);
        let (rest, s2) = read_sys_circuits_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  -- `Option` tag is a single byte (bincode special-cases Option).
  fn read_opt_commit(stream: ByteStream) -> (OptCommit, ByteStream) {
    let (tag, s) = read_u8(stream);
    match tag {
      0 => (OptCommit.NoCommit, s),
      _ => let (c, s1) = read_merkle_cap(s); (OptCommit.SomeCommit(c), s1),
    }
  }
  fn read_opt_idx(stream: ByteStream) -> (OptIdx, ByteStream) {
    let (tag, s) = read_u8(stream);
    match tag {
      0 => (OptIdx.NoIdx, s),
      _ => let (i, s1) = read_count(s); (OptIdx.SomeIdx(i), s1),
    }
  }
  fn read_opt_idx_list(stream: ByteStream) -> (List‹OptIdx›, ByteStream) {
    let (n, s) = read_count(stream);
    read_opt_idx_list_n(s, n)
  }
  fn read_opt_idx_list_n(stream: ByteStream, n: G) -> (List‹OptIdx›, ByteStream) {
    match n {
      0 => (store(ListNode.Nil), stream),
      _ =>
        let (x, s) = read_opt_idx(stream);
        let (rest, s2) = read_opt_idx_list_n(s, n - 1);
        (store(ListNode.Cons(x, rest)), s2),
    }
  }

  fn read_sys_params(stream: ByteStream) -> (SysParams, ByteStream) {
    let (log_blowup, s) = read_count(stream);
    let (cap_height, s1) = read_count(s);
    (SysParams.Mk(log_blowup, cap_height), s1)
  }

  -- Full `System<AiurCircuit>`.
  fn read_system(stream: ByteStream) -> (Sys, ByteStream) {
    let (params, s) = read_sys_params(stream);
    let (circuits, s1) = read_sys_circuits(s);
    let (commit, s2) = read_opt_commit(s1);
    let (indices, s3) = read_opt_idx_list(s2);
    (Sys.Mk(params, circuits, commit, indices), s3)
  }
⟧

end MultiStark

end
