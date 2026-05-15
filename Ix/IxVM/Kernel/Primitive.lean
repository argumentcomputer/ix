module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes

set_option maxRecDepth 8192

public section

namespace IxVM

/-! ## Nat / String primitives

Mirror: `src/ix/kernel/primitive.rs` (PrimAddrs struct + canonical
addresses) and `src/ix/kernel/whnf.rs:500-700` (Nat-on-literals
short-circuit dispatch).

`KLimbs = List<U64>` little-endian (`KernelTypes.lean:28`). Rust
counterpart is `num_bigint::BigUint`. Klimbs ops here mirror BigUint
semantics on bounded inputs.
-/

set_option maxRecDepth 16384 in
def primitive := ⟦
  -- ============================================================================
  -- PrimIdxs: positional kernel const indices for dispatchable primitives.
  --
  -- Mirror: src/ix/kernel/primitive.rs::PrimAddrs (canonical addresses).
  -- The Aiur kernel uses positional Const(idx) so we resolve addresses to
  -- positions at ingress time. Slots:
  --   0: nat
  --   1: nat_zero
  --   2: nat_succ
  --   3: nat_pred
  --   4: nat_add
  --   5: nat_sub
  --   6: nat_mul
  --   7: nat_beq
  --   8: nat_ble
  --   9: str
  -- A slot value of `0 - 1` (max G) means "primitive not present in the
  -- current kernel const list".
  -- ============================================================================

  -- Canonical Anon-mode blake3 addresses (mirror of primitive.rs PrimAddrs).
  fn quot_type_addr() -> [G; 32] {
    [0xab, 0x68, 0x2c, 0x17, 0x78, 0xa1, 0x7b, 0xbe,
     0xae, 0x40, 0x32, 0x97, 0x4d, 0xf3, 0x64, 0x47,
     0xce, 0x8b, 0xfc, 0xab, 0x67, 0x64, 0xa3, 0x6d,
     0x37, 0x85, 0x66, 0xe3, 0xad, 0x63, 0xca, 0xb8]
  }

  fn quot_ctor_addr() -> [G; 32] {
    [0x88, 0x26, 0x66, 0x77, 0xfe, 0xe7, 0x74, 0xd1,
     0x09, 0x86, 0x7e, 0x4b, 0x22, 0x40, 0x28, 0x1a,
     0xa2, 0xee, 0x12, 0xd9, 0x79, 0x20, 0xc1, 0x17,
     0x1c, 0xf5, 0xc1, 0xf6, 0xc8, 0x7d, 0xec, 0xf6]
  }

  fn quot_lift_addr() -> [G; 32] {
    [0xaa, 0x57, 0xe8, 0xc3, 0xf4, 0xf9, 0xe1, 0xcf,
     0x6b, 0x02, 0xa0, 0x38, 0xac, 0x15, 0x81, 0x98,
     0xc3, 0xaf, 0x4b, 0x28, 0xd6, 0x1c, 0xea, 0x79,
     0x95, 0xbf, 0x5c, 0xa7, 0xc7, 0xb8, 0x2c, 0x29]
  }

  fn quot_ind_addr() -> [G; 32] {
    [0x12, 0x49, 0x84, 0xbc, 0xb9, 0x52, 0x08, 0xa0,
     0xf3, 0x0b, 0xb6, 0x9d, 0x67, 0x36, 0xd3, 0xd5,
     0x94, 0x04, 0xe1, 0x15, 0xe2, 0x20, 0x20, 0x43,
     0xfd, 0xa3, 0xd3, 0x4e, 0x01, 0xb0, 0xad, 0x16]
  }

  fn bit_vec_addr() -> [G; 32] {
    [0xcf, 0x55, 0x11, 0x5c, 0x75, 0x34, 0x3f, 0x82,
     0x4f, 0xdd, 0x93, 0x21, 0x78, 0xb0, 0xcb, 0xc7,
     0x5a, 0x86, 0xe5, 0x05, 0x2d, 0xe9, 0x3d, 0xb9,
     0x8f, 0x05, 0xb3, 0x78, 0x85, 0xff, 0xb0, 0x9b]
  }

  fn bit_vec_to_nat_addr() -> [G; 32] {
    [0x78, 0x34, 0x86, 0x5c, 0x1c, 0x6c, 0xd9, 0x63,
     0xb9, 0x36, 0x5c, 0xb0, 0x65, 0x00, 0x62, 0x38,
     0x80, 0xde, 0x4d, 0x99, 0x30, 0x34, 0x3e, 0x96,
     0xe1, 0x9e, 0x62, 0xa0, 0x26, 0xe7, 0xca, 0xce]
  }

  fn bit_vec_of_nat_addr() -> [G; 32] {
    [0xa0, 0x8a, 0xcf, 0x4c, 0xed, 0xb4, 0xc0, 0x5e,
     0xdd, 0xb5, 0x5b, 0xff, 0x36, 0x6c, 0xd9, 0x52,
     0xd5, 0xb7, 0xb8, 0x86, 0x02, 0xc3, 0xfc, 0x6d,
     0x87, 0x5e, 0x8e, 0xa7, 0x32, 0xa3, 0xc2, 0xf4]
  }

  fn bit_vec_ult_addr() -> [G; 32] {
    [0x6a, 0x3f, 0x26, 0x2c, 0x2f, 0x4a, 0x2c, 0x51,
     0x7a, 0x61, 0x6f, 0xba, 0xe5, 0x4a, 0x31, 0xec,
     0xcb, 0x85, 0x99, 0x8a, 0xd9, 0xc1, 0xf9, 0x3b,
     0xe8, 0xcc, 0x59, 0x0d, 0x97, 0x11, 0x7c, 0x04]
  }

  fn decidable_decide_addr() -> [G; 32] {
    [0x6d, 0xda, 0xae, 0xd2, 0x63, 0x74, 0x0b, 0x5d,
     0x5d, 0x67, 0xe6, 0xc1, 0x2e, 0xcf, 0xad, 0xb2,
     0x4a, 0xd8, 0x86, 0x7d, 0x4a, 0x09, 0xfe, 0x78,
     0x4b, 0x59, 0xda, 0xc7, 0xf7, 0x27, 0x54, 0xab]
  }

  fn lt_lt_addr() -> [G; 32] {
    [0x01, 0xd8, 0x71, 0xbc, 0xdf, 0xb2, 0xe7, 0x69,
     0xe1, 0xac, 0xa0, 0x0e, 0x7a, 0x3b, 0x3a, 0x21,
     0xa8, 0xd9, 0x02, 0xcc, 0x27, 0x37, 0x07, 0xc8,
     0x92, 0xeb, 0x86, 0x7b, 0x7f, 0xc7, 0x8a, 0xe2]
  }

  fn bool_type_addr() -> [G; 32] {
    [0x64, 0x05, 0xa4, 0x55, 0xba, 0x70, 0xc2, 0xb2,
     0x17, 0x9c, 0x79, 0x66, 0xc6, 0xf6, 0x10, 0xbf,
     0x34, 0x17, 0xbd, 0x0f, 0x3d, 0xd2, 0xba, 0x7a,
     0x52, 0x25, 0x33, 0xc2, 0xcd, 0x9e, 0x1d, 0x0b]
  }

  fn eq_addr() -> [G; 32] {
    [0x9c, 0x0a, 0xf2, 0xa3, 0x93, 0xcb, 0x5c, 0x08,
     0x35, 0xe4, 0x4e, 0x60, 0xe4, 0xc3, 0xe6, 0x8e,
     0xeb, 0x26, 0x6f, 0xd1, 0x6a, 0xff, 0xad, 0x32,
     0x16, 0x09, 0x6a, 0x35, 0xfe, 0x91, 0xb9, 0xc1]
  }

  fn eq_refl_addr() -> [G; 32] {
    [0x1e, 0x25, 0x11, 0x98, 0xf3, 0x06, 0x25, 0x62,
     0x8e, 0x2e, 0xb0, 0x98, 0x3f, 0x7b, 0xe9, 0xef,
     0xe8, 0xd7, 0x19, 0xa1, 0x04, 0xa8, 0x61, 0xf2,
     0xbe, 0xf2, 0xf4, 0x7e, 0xab, 0xee, 0xd4, 0xf9]
  }

  fn nat_dec_le_addr() -> [G; 32] {
    [0xe0, 0x8c, 0x51, 0x41, 0xc4, 0x4b, 0x27, 0x65,
     0x39, 0x57, 0xae, 0x00, 0xa9, 0x26, 0xa2, 0xdd,
     0x68, 0xdc, 0xd7, 0x77, 0x9c, 0x4f, 0xdf, 0x85,
     0x0e, 0x66, 0x8f, 0xdc, 0x92, 0xb4, 0x08, 0xde]
  }

  fn nat_dec_eq_addr() -> [G; 32] {
    [0x38, 0x32, 0x3f, 0xd9, 0xe1, 0x7e, 0x9d, 0x1f,
     0x17, 0x53, 0x6d, 0xbb, 0x7f, 0x19, 0x6b, 0x94,
     0xb5, 0xba, 0x19, 0xe4, 0xbf, 0x62, 0x5d, 0x9e,
     0x7c, 0x60, 0x7c, 0x47, 0x36, 0x5c, 0x15, 0xad]
  }

  fn nat_dec_lt_addr() -> [G; 32] {
    [0xf4, 0x45, 0x08, 0x4f, 0x68, 0x05, 0xfa, 0xf9,
     0xbe, 0x62, 0xaa, 0x32, 0x84, 0x15, 0x65, 0x13,
     0x43, 0xc9, 0x8f, 0xfe, 0x52, 0xdb, 0x15, 0x9d,
     0xfb, 0x1b, 0x9a, 0x14, 0xcb, 0x28, 0xcf, 0x23]
  }

  fn int_dec_eq_addr() -> [G; 32] {
    [0x42, 0xd9, 0xb7, 0xa9, 0x4a, 0xef, 0xc7, 0x7a,
     0x66, 0x16, 0x93, 0x6b, 0xe3, 0x12, 0x64, 0xea,
     0xf8, 0xbe, 0xd7, 0xbd, 0x80, 0xf5, 0xd3, 0x49,
     0x67, 0xfc, 0x42, 0xaf, 0xaf, 0x29, 0xa7, 0xfd]
  }

  fn int_dec_le_addr() -> [G; 32] {
    [0xee, 0x03, 0x70, 0xe4, 0x26, 0xa4, 0x00, 0xc8,
     0xb1, 0x67, 0x82, 0xfa, 0xbf, 0xa0, 0xe4, 0x3f,
     0xf8, 0x7e, 0xca, 0xc1, 0xa0, 0xc1, 0xc7, 0x65,
     0xcc, 0x51, 0x79, 0xfc, 0x42, 0x3a, 0xb1, 0xbd]
  }

  fn int_dec_lt_addr() -> [G; 32] {
    [0x15, 0x07, 0x0e, 0x92, 0x02, 0x04, 0x27, 0x23,
     0x69, 0xf0, 0xf2, 0xe8, 0x0f, 0xf3, 0xf5, 0x03,
     0x5c, 0x05, 0xb3, 0x9e, 0xfa, 0x71, 0x4e, 0xc8,
     0xe6, 0xbb, 0xfc, 0xe9, 0x95, 0x06, 0x37, 0xaf]
  }

  fn int_of_nat_addr() -> [G; 32] {
    [0x46, 0xb5, 0xeb, 0x67, 0x68, 0xc1, 0xf4, 0x95,
     0x87, 0xd6, 0x53, 0xc1, 0x2e, 0x37, 0x33, 0x89,
     0x12, 0x15, 0x33, 0x86, 0x83, 0x2f, 0x0f, 0xd0,
     0xe4, 0x72, 0x48, 0x4e, 0x26, 0x32, 0x26, 0x32]
  }

  fn int_neg_succ_addr() -> [G; 32] {
    [0x25, 0xbb, 0xcd, 0x75, 0x6b, 0x52, 0xeb, 0x78,
     0xbc, 0xe1, 0x70, 0x41, 0x0d, 0xef, 0xa4, 0xc1,
     0x5b, 0x23, 0x8d, 0xed, 0xef, 0x5f, 0x7b, 0x89,
     0x69, 0x16, 0x21, 0xdc, 0xbe, 0x91, 0x97, 0x80]
  }

  -- Address constants below registered in Rust primitive.rs but not wired
  -- into any Aiur dispatch path. Commented out per "no unused code".
  -- Restore + plug if a reduction/canonicalization tier needs them.
  /-
  fn int_addr() -> [G; 32] {
    [0xe7, 0xdc, 0x2d, 0x5a, 0x2e, 0x15, 0x3e, 0x1a,
     0xb0, 0xc7, 0x87, 0x97, 0xbc, 0xbf, 0xd5, 0x3a,
     0x2c, 0x01, 0xff, 0x40, 0x91, 0x88, 0x77, 0xcf,
     0xad, 0x8a, 0xde, 0x8c, 0x41, 0x69, 0xa4, 0x3a]
  }

  fn int_add_addr() -> [G; 32] {
    [0xd8, 0xe6, 0xcd, 0xc9, 0x88, 0xd4, 0x28, 0x8e,
     0x48, 0xcc, 0x60, 0x92, 0x73, 0x0b, 0xc5, 0x38,
     0x71, 0x76, 0xcf, 0xf6, 0x59, 0x24, 0x71, 0xa3,
     0x28, 0xcc, 0x43, 0x54, 0xf1, 0x87, 0x84, 0x12]
  }

  fn int_sub_addr() -> [G; 32] {
    [0x93, 0xb2, 0xd1, 0x2d, 0x77, 0x97, 0xfd, 0x62,
     0xc2, 0x0b, 0xec, 0x25, 0x53, 0x36, 0xc1, 0xe9,
     0x1c, 0xa1, 0xce, 0xf7, 0xa6, 0x95, 0x10, 0x71,
     0x29, 0x6f, 0xc1, 0xab, 0x5b, 0xd1, 0xd8, 0xc8]
  }

  fn int_mul_addr() -> [G; 32] {
    [0x9a, 0xd6, 0xee, 0x18, 0xef, 0x6d, 0x7d, 0x74,
     0xbb, 0xe4, 0x49, 0xab, 0x61, 0xaa, 0x31, 0xf8,
     0x4a, 0x0e, 0x78, 0x95, 0x1e, 0x95, 0x60, 0xd2,
     0x8f, 0xd8, 0x2e, 0x0c, 0x3b, 0x07, 0x1d, 0x01]
  }

  fn int_neg_addr() -> [G; 32] {
    [0x8c, 0x3f, 0x64, 0xe6, 0xb5, 0xba, 0xaa, 0xa1,
     0x25, 0xf0, 0x63, 0x7d, 0x7a, 0x82, 0x4d, 0xf6,
     0x27, 0xdb, 0xed, 0xe0, 0x11, 0x59, 0x68, 0xf3,
     0xc8, 0x0c, 0x55, 0xe0, 0x22, 0x55, 0x44, 0x62]
  }

  fn int_emod_addr() -> [G; 32] {
    [0x7c, 0xdb, 0x11, 0x27, 0x25, 0xd3, 0xa4, 0xf5,
     0x42, 0xbf, 0xb0, 0xcd, 0x30, 0x92, 0x68, 0x64,
     0x1b, 0xd8, 0x9d, 0xdc, 0x98, 0x90, 0xc7, 0x22,
     0x1e, 0xd0, 0x1f, 0x99, 0xb6, 0xa0, 0x0b, 0x63]
  }

  fn int_ediv_addr() -> [G; 32] {
    [0xba, 0x19, 0x4c, 0x0a, 0x36, 0x74, 0xe6, 0x7b,
     0x99, 0x68, 0xd0, 0xa6, 0x5c, 0xdd, 0xa3, 0xa4,
     0xdd, 0xb9, 0xdc, 0xdc, 0xe4, 0x8a, 0xd6, 0xc6,
     0x2e, 0x91, 0xd4, 0x78, 0xa1, 0x0a, 0x3d, 0xdd]
  }

  fn int_bmod_addr() -> [G; 32] {
    [0xc8, 0x43, 0x1b, 0x7a, 0xdb, 0x91, 0x89, 0x67,
     0xaa, 0x05, 0xba, 0x6f, 0xd8, 0x29, 0x7f, 0x33,
     0xe9, 0x7d, 0x67, 0x00, 0x3e, 0x41, 0x38, 0x02,
     0x1d, 0x91, 0x2e, 0xa9, 0x2c, 0xc1, 0x88, 0x7f]
  }

  fn int_bdiv_addr() -> [G; 32] {
    [0xab, 0x72, 0x47, 0x72, 0x54, 0xd1, 0xca, 0x47,
     0x38, 0x12, 0x3a, 0xd6, 0x12, 0xea, 0xe4, 0xdf,
     0xb9, 0x12, 0x6e, 0xf7, 0x83, 0x10, 0xed, 0x7d,
     0x2e, 0xbd, 0xe8, 0x10, 0x09, 0x63, 0xbf, 0xb1]
  }

  fn int_nat_abs_addr() -> [G; 32] {
    [0x60, 0x66, 0x2e, 0x33, 0x22, 0x4f, 0x55, 0xbe,
     0x9e, 0x36, 0x76, 0x83, 0x37, 0x8c, 0x7b, 0xf6,
     0x09, 0x3c, 0x12, 0x5c, 0x04, 0xff, 0x7c, 0x4e,
     0x3e, 0xca, 0x37, 0x01, 0x12, 0xe1, 0xc5, 0x62]
  }

  fn int_pow_addr() -> [G; 32] {
    [0x0d, 0xfe, 0x8f, 0x22, 0xbd, 0x6c, 0xb6, 0x7d,
     0x53, 0x8a, 0x2f, 0x01, 0x8f, 0x0e, 0x40, 0x6f,
     0xc0, 0xb5, 0xd7, 0x30, 0xca, 0xa6, 0x3e, 0x1a,
     0x79, 0x8d, 0xfa, 0x9a, 0xd7, 0x8b, 0xab, 0x07]
  }

  fn bool_no_confusion_addr() -> [G; 32] {
    [0x47, 0x3b, 0x2c, 0x94, 0x8d, 0xdb, 0xce, 0x4d,
     0xdb, 0x4b, 0x36, 0x9e, 0x5c, 0xf6, 0x19, 0x9f,
     0xf1, 0x85, 0xb6, 0x4e, 0x9f, 0xbb, 0x1e, 0x90,
     0x90, 0x1d, 0x74, 0x6d, 0xe5, 0x51, 0x90, 0xef]
  }

  fn char_mk_addr() -> [G; 32] {
    [0xe6, 0x22, 0x38, 0xc5, 0x4b, 0x91, 0x39, 0x5c,
     0x2c, 0x06, 0x19, 0x2c, 0xfc, 0xcb, 0x5e, 0x80,
     0xfc, 0xe4, 0x1e, 0xd1, 0x1d, 0x1b, 0xf6, 0xdb,
     0x14, 0x2d, 0x2c, 0x39, 0xd7, 0xc8, 0x1a, 0x20]
  }

  fn nat_bitwise_addr() -> [G; 32] {
    [0xf2, 0x1d, 0x74, 0x7a, 0xca, 0x3e, 0x08, 0xf5,
     0x29, 0x00, 0x93, 0xbf, 0x8f, 0x40, 0x20, 0x83,
     0x8d, 0x8e, 0x17, 0x42, 0xa7, 0x8b, 0x3e, 0x1f,
     0x48, 0xd8, 0x3e, 0xf1, 0x59, 0x39, 0x5e, 0x6a]
  }

  fn nat_rec_addr() -> [G; 32] {
    [0x6e, 0x85, 0x5f, 0x04, 0x48, 0x5d, 0xf8, 0xd9,
     0x77, 0x67, 0xf8, 0xaa, 0x89, 0xf2, 0x23, 0xbc,
     0xac, 0x97, 0x7e, 0x2a, 0x15, 0x5c, 0x45, 0xc6,
     0x6d, 0x6e, 0x09, 0x4e, 0xc3, 0x16, 0x31, 0x94]
  }

  fn nat_cases_on_addr() -> [G; 32] {
    [0x9a, 0x6b, 0x32, 0xaf, 0x19, 0x4f, 0xdf, 0x0b,
     0x44, 0x76, 0x33, 0x07, 0x7d, 0x9f, 0xa8, 0x9c,
     0x24, 0x9d, 0x6d, 0x7d, 0xf2, 0x43, 0xd3, 0x00,
     0xb8, 0x9d, 0xd9, 0xb1, 0x4d, 0x92, 0xbb, 0x03]
  }

  fn list_addr() -> [G; 32] {
    [0xab, 0xed, 0x9f, 0xf1, 0xab, 0xa4, 0x63, 0x4a,
     0xbc, 0x0b, 0xd3, 0xaf, 0x76, 0xca, 0x54, 0x42,
     0x85, 0xa3, 0x2d, 0xcf, 0xe4, 0x3d, 0xc2, 0x7b,
     0x12, 0x9a, 0xea, 0x88, 0x67, 0x45, 0x76, 0x20]
  }

  fn string_addr() -> [G; 32] {
    [0xcb, 0x1b, 0xca, 0x7f, 0xc5, 0xdb, 0xb1, 0xbd,
     0xfb, 0xf6, 0x31, 0x9d, 0xf8, 0x9d, 0xa9, 0xfd,
     0xa3, 0xa6, 0x79, 0xd2, 0x25, 0x54, 0xb8, 0xa9,
     0xd5, 0xdd, 0x46, 0x63, 0xc0, 0xa9, 0x73, 0x12]
  }

  fn string_mk_addr() -> [G; 32] {
    [0x63, 0xd9, 0x5a, 0x0f, 0xd6, 0xa1, 0x14, 0x43,
     0x48, 0xd0, 0xf2, 0x0e, 0x20, 0xcc, 0x5c, 0x3a,
     0xf6, 0x1a, 0xc9, 0x55, 0x92, 0x3f, 0x45, 0xf4,
     0x2a, 0x78, 0x2d, 0xe9, 0x33, 0xaa, 0xd5, 0x94]
  }

  fn of_nat_of_nat_addr() -> [G; 32] {
    [0x8f, 0xdc, 0x86, 0x9f, 0x7b, 0x7a, 0xa2, 0xb7,
     0xb5, 0x92, 0x9b, 0xa2, 0x42, 0xed, 0x89, 0x9c,
     0xe2, 0xd7, 0xc5, 0xd4, 0x2d, 0xf1, 0xd4, 0xe2,
     0x39, 0x36, 0x90, 0xcf, 0xa8, 0x5e, 0x94, 0xd2]
  }

  fn eager_reduce_addr() -> [G; 32] {
    -- Aiur is permanently eager (no fvars, no fuel); this address is
    -- registered for parity with Rust but never matched.
    [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  }

  fn pprod_addr() -> [G; 32] {
    [0x6e, 0x99, 0xb0, 0x86, 0x70, 0x0f, 0x29, 0x01,
     0x80, 0x4a, 0x10, 0x7c, 0xad, 0x5e, 0xf0, 0xfe,
     0x87, 0x80, 0x77, 0xb1, 0x72, 0x3f, 0x4b, 0x82,
     0x46, 0x15, 0xdd, 0x02, 0x1d, 0x4d, 0x51, 0x57]
  }

  fn pprod_mk_addr() -> [G; 32] {
    [0x00, 0xdd, 0xf2, 0x6e, 0xfd, 0x5f, 0x7e, 0x5e,
     0xee, 0x55, 0x61, 0xc2, 0x46, 0x7b, 0x16, 0xac,
     0x85, 0x6e, 0xfc, 0xb3, 0xa1, 0x22, 0x65, 0x44,
     0x48, 0x76, 0x45, 0xdd, 0x46, 0x20, 0x85, 0x96]
  }
  -/

  fn fin_addr() -> [G; 32] {
    [0x27, 0x2a, 0xa9, 0xe1, 0x6c, 0x03, 0xe9, 0xad,
     0x73, 0x37, 0xe7, 0x06, 0xd7, 0x3e, 0xfd, 0x14,
     0xcc, 0xf1, 0xda, 0x10, 0xe2, 0xf8, 0x36, 0x7d,
     0xd3, 0x43, 0x74, 0xb6, 0x0e, 0x15, 0x56, 0xfa]
  }

  fn decidable_rec_addr() -> [G; 32] {
    [0xf3, 0x23, 0xa5, 0x49, 0xad, 0x4d, 0xf6, 0xb2,
     0xf3, 0x28, 0x99, 0x23, 0x7a, 0x28, 0x11, 0x36,
     0xf3, 0x4d, 0x43, 0x1e, 0xd7, 0x2b, 0x33, 0x85,
     0x7c, 0x08, 0x5e, 0x6c, 0x4d, 0x85, 0x27, 0x38]
  }

  fn decidable_is_true_addr() -> [G; 32] {
    [0x3a, 0xe2, 0xc7, 0x1d, 0xa2, 0xbf, 0x34, 0x17,
     0x9a, 0x5a, 0x88, 0x08, 0x85, 0x7c, 0x34, 0xa3,
     0xb7, 0x66, 0x2f, 0xf5, 0x65, 0x4d, 0x8c, 0x24,
     0x7c, 0x43, 0xe8, 0x5a, 0x7c, 0xde, 0x49, 0x3f]
  }

  fn decidable_is_false_addr() -> [G; 32] {
    [0x10, 0xac, 0x5f, 0x48, 0x79, 0x8b, 0x3f, 0xf0,
     0x1b, 0x0f, 0x74, 0xc0, 0xb5, 0x44, 0xd2, 0x27,
     0x96, 0xc9, 0x77, 0x5f, 0x6d, 0x43, 0xd3, 0x28,
     0x31, 0x6b, 0xbb, 0x3a, 0xa1, 0x63, 0x89, 0x99]
  }

  fn nat_le_of_ble_eq_true_addr() -> [G; 32] {
    [0x7e, 0x5d, 0x1f, 0x11, 0x18, 0xa8, 0x9f, 0x77,
     0xf8, 0x9d, 0x46, 0x9a, 0x27, 0x73, 0x1a, 0x75,
     0x4d, 0xe3, 0x36, 0xa0, 0x5e, 0x33, 0xf3, 0x83,
     0x05, 0x6b, 0xc9, 0x2b, 0x36, 0x94, 0x78, 0x12]
  }

  fn nat_not_le_of_not_ble_eq_true_addr() -> [G; 32] {
    [0xc1, 0xe2, 0x3b, 0x8d, 0xaf, 0xb3, 0x77, 0x8b,
     0x99, 0x63, 0x12, 0x06, 0x8a, 0x2b, 0xec, 0x3d,
     0xcb, 0xcc, 0x72, 0x13, 0x2e, 0xfb, 0xf4, 0x3c,
     0x23, 0x5e, 0x57, 0x30, 0x84, 0x66, 0x82, 0x41]
  }

  fn nat_eq_of_beq_eq_true_addr() -> [G; 32] {
    [0xb9, 0xac, 0xc8, 0x1f, 0x28, 0x01, 0xaf, 0x89,
     0xb9, 0x5e, 0x09, 0x62, 0xaa, 0x9d, 0x73, 0x90,
     0xa3, 0xac, 0xfe, 0x8f, 0xb7, 0x60, 0x55, 0x9a,
     0x81, 0x1a, 0x82, 0xed, 0x74, 0x43, 0xdb, 0xb5]
  }

  fn nat_ne_of_beq_eq_false_addr() -> [G; 32] {
    [0x24, 0x87, 0x79, 0x88, 0x41, 0x09, 0xee, 0xd0,
     0x06, 0x00, 0xa0, 0xbd, 0x96, 0x8f, 0x74, 0x0d,
     0xb7, 0xf3, 0xd9, 0x24, 0xfb, 0x2b, 0x17, 0x06,
     0xab, 0x55, 0x2e, 0x78, 0x76, 0x06, 0x28, 0x55]
  }

  fn reduce_bool_addr() -> [G; 32] {
    [0x6e, 0x45, 0x3a, 0x7c, 0xed, 0xaf, 0xe2, 0xed,
     0xbb, 0xc1, 0xf0, 0x50, 0x34, 0x42, 0xbe, 0x49,
     0x9e, 0x4c, 0xbf, 0x18, 0xa6, 0xc0, 0x0d, 0xc9,
     0x9f, 0x39, 0x03, 0xee, 0x7f, 0x05, 0xdb, 0xaf]
  }

  fn reduce_nat_addr() -> [G; 32] {
    [0x54, 0x19, 0x18, 0x7f, 0xbf, 0x67, 0xef, 0x1c,
     0x4f, 0xf9, 0xab, 0x0b, 0xe1, 0xb0, 0x1d, 0x46,
     0x31, 0xa2, 0x70, 0x64, 0x7f, 0xfe, 0x43, 0x4b,
     0xf7, 0xe1, 0xf7, 0x88, 0xb3, 0xc8, 0x1d, 0xd4]
  }

  fn system_platform_num_bits_addr() -> [G; 32] {
    [0xd4, 0x83, 0x96, 0x64, 0x38, 0xad, 0x47, 0xce,
     0x41, 0x55, 0xb3, 0x48, 0x58, 0x19, 0xa3, 0x77,
     0xe2, 0x26, 0x05, 0xb5, 0x9a, 0x1a, 0xaf, 0xd0,
     0xb6, 0x81, 0xcb, 0x38, 0xac, 0xa8, 0x31, 0x07]
  }

  fn system_platform_get_num_bits_addr() -> [G; 32] {
    [0xad, 0x44, 0xc9, 0x04, 0x49, 0xfa, 0xf8, 0x6f,
     0x63, 0xc1, 0x70, 0xf0, 0x92, 0xe2, 0x24, 0x9b,
     0xcc, 0xab, 0x1e, 0x74, 0x1c, 0x1f, 0xe1, 0x0d,
     0xf8, 0x4c, 0x95, 0xb4, 0x4b, 0x38, 0x43, 0x71]
  }

  fn subtype_val_addr() -> [G; 32] {
    [0xad, 0x58, 0xc3, 0x65, 0x60, 0x44, 0xd7, 0xfa,
     0xef, 0x69, 0x76, 0x37, 0xf5, 0x16, 0xd7, 0x26,
     0x74, 0xd3, 0x5b, 0x18, 0x66, 0x3c, 0xb2, 0x63,
     0xf7, 0xcc, 0xca, 0x8c, 0xdd, 0x2e, 0x6f, 0x00]
  }

  fn punit_size_of_1_addr() -> [G; 32] {
    [0x8c, 0x2c, 0xbf, 0xe3, 0x28, 0x91, 0x0b, 0xfe,
     0x7f, 0xeb, 0x60, 0x07, 0x2b, 0x46, 0xf7, 0x48,
     0x76, 0x92, 0xcb, 0x37, 0x59, 0x96, 0x81, 0xb1,
     0x37, 0xa3, 0x1d, 0xd9, 0x9e, 0x70, 0x8f, 0x03]
  }

  fn size_of_size_of_addr() -> [G; 32] {
    [0x71, 0x05, 0xea, 0xf4, 0xc5, 0x2c, 0xe3, 0xa1,
     0x93, 0x72, 0xa8, 0x7f, 0xac, 0x57, 0xa8, 0xf9,
     0x59, 0x8a, 0x24, 0x63, 0x34, 0xce, 0x6e, 0xff,
     0xae, 0xe3, 0xe4, 0x8e, 0x7e, 0x6d, 0x3a, 0xad]
  }

  fn punit_addr() -> [G; 32] {
    [0x16, 0xa2, 0xdc, 0x76, 0xa2, 0xcf, 0xcc, 0x94,
     0x40, 0xf4, 0x43, 0xc6, 0x66, 0x53, 0x6f, 0x2f,
     0xa9, 0x9c, 0x02, 0x50, 0xb6, 0x42, 0xfd, 0x39,
     0x71, 0xfb, 0xad, 0x25, 0xd5, 0x31, 0x26, 0x2a]
  }

  fn unit_addr() -> [G; 32] {
    [0x21, 0x1b, 0xf5, 0xed, 0x2f, 0x4c, 0x51, 0xd4,
     0x57, 0x50, 0xe7, 0x5b, 0x89, 0x1f, 0xa2, 0x67,
     0xdb, 0x4d, 0x4e, 0x6f, 0x46, 0xc2, 0x07, 0x92,
     0x82, 0xfa, 0x2b, 0xe3, 0xe8, 0x87, 0x81, 0xa1]
  }

  fn nat_addr() -> [G; 32] {
    [0xfc, 0x0e, 0x1e, 0x91, 0x2f, 0x2d, 0x7f, 0x12,
     0x04, 0x9a, 0x5b, 0x31, 0x5d, 0x76, 0xee, 0xc2,
     0x95, 0x62, 0xe3, 0x4d, 0xc3, 0x9e, 0xbc, 0xa2,
     0x52, 0x87, 0xae, 0x58, 0x80, 0x7d, 0xb1, 0x37]
  }

  fn nat_zero_addr() -> [G; 32] {
    [0xfa, 0xc8, 0x2f, 0x0d, 0x25, 0x55, 0xd6, 0xa6,
     0x3e, 0x1b, 0x8a, 0x1f, 0xe8, 0xd8, 0x6b, 0xd2,
     0x93, 0x19, 0x7f, 0x39, 0xc3, 0x96, 0xfd, 0xc2,
     0x3c, 0x12, 0x75, 0xc6, 0x0f, 0x18, 0x2b, 0x37]
  }

  fn nat_succ_addr() -> [G; 32] {
    [0x71, 0x90, 0xce, 0x56, 0xf6, 0xa2, 0xa8, 0x47,
     0xb9, 0x44, 0xa3, 0x55, 0xe3, 0xec, 0x59, 0x5a,
     0x40, 0x36, 0xfb, 0x07, 0xe3, 0xc3, 0xdb, 0x9d,
     0x90, 0x64, 0xfc, 0x04, 0x1b, 0xe7, 0x2b, 0x64]
  }

  fn nat_pred_addr() -> [G; 32] {
    [0x6b, 0x59, 0xcf, 0x44, 0x97, 0x81, 0xf0, 0x7b,
     0x04, 0x20, 0x7d, 0x66, 0x59, 0x78, 0xb5, 0xc5,
     0xef, 0x96, 0x88, 0xaf, 0xa7, 0x44, 0x85, 0x90,
     0xa6, 0x8f, 0x7d, 0xa7, 0xff, 0x88, 0xc5, 0x16]
  }

  fn nat_add_addr() -> [G; 32] {
    [0xf9, 0x41, 0x92, 0x05, 0x8e, 0x41, 0xbc, 0x29,
     0xe8, 0x89, 0x24, 0xd8, 0x57, 0xa6, 0xbd, 0x33,
     0xf8, 0xb3, 0xe0, 0xa9, 0x0f, 0x87, 0x86, 0x82,
     0x82, 0x70, 0xd1, 0xcc, 0x1d, 0xd0, 0xad, 0xc6]
  }

  fn nat_sub_addr() -> [G; 32] {
    [0xfa, 0x98, 0xda, 0xbf, 0x44, 0xd2, 0xa6, 0x30,
     0x7b, 0x49, 0x0a, 0xc9, 0xe8, 0x11, 0x43, 0x3e,
     0xfc, 0x2f, 0x95, 0x89, 0x96, 0xc6, 0x7b, 0xe1,
     0x39, 0x8c, 0xb4, 0xd1, 0xb2, 0x64, 0xcf, 0x39]
  }

  fn nat_mul_addr() -> [G; 32] {
    [0x9b, 0x5c, 0x57, 0xea, 0x1c, 0xf2, 0xfb, 0x1d,
     0xe6, 0x7e, 0xe5, 0xbe, 0xc1, 0x5e, 0x36, 0x0d,
     0x20, 0xa9, 0x63, 0x59, 0x90, 0x27, 0x30, 0x14,
     0xe6, 0x78, 0x51, 0xe0, 0x49, 0xff, 0x36, 0x19]
  }

  fn nat_pow_addr() -> [G; 32] {
    [0xd0, 0x15, 0x98, 0x7b, 0xb1, 0x0d, 0xd2, 0x28,
     0x63, 0xdd, 0xc4, 0x11, 0x60, 0xd2, 0x7d, 0xd3,
     0xd1, 0xea, 0x74, 0xf7, 0x54, 0xfb, 0x24, 0x12,
     0x43, 0x24, 0x36, 0xf3, 0xea, 0x5b, 0x50, 0x71]
  }

  fn nat_gcd_addr() -> [G; 32] {
    [0xee, 0x8b, 0xa9, 0x21, 0x6b, 0x3f, 0xc8, 0x1e,
     0x79, 0x68, 0x58, 0x6b, 0x43, 0xce, 0xbe, 0xa1,
     0x5d, 0x0e, 0x14, 0x3d, 0x5d, 0x4b, 0x1f, 0xde,
     0x1b, 0xd3, 0x01, 0xa7, 0x40, 0x93, 0xf6, 0x06]
  }

  fn nat_mod_addr() -> [G; 32] {
    [0x8e, 0xf8, 0xb2, 0x8b, 0x4e, 0x9e, 0x0a, 0x59,
     0xf3, 0x82, 0x2e, 0x24, 0x3e, 0x71, 0x29, 0x9f,
     0x06, 0xbb, 0x6e, 0x7a, 0xfd, 0xb6, 0xcd, 0xd9,
     0x79, 0x76, 0xfb, 0x29, 0x0b, 0x66, 0x7b, 0xb4]
  }

  fn nat_div_addr() -> [G; 32] {
    [0xfa, 0x58, 0x37, 0x94, 0xc8, 0xef, 0x36, 0x8e,
     0xff, 0x68, 0x81, 0xe8, 0x16, 0xa4, 0xe8, 0x89,
     0xf9, 0x50, 0x61, 0x11, 0x6c, 0xe4, 0x9b, 0x15,
     0x40, 0x56, 0xd3, 0x8f, 0xce, 0x4b, 0x7f, 0x52]
  }

  fn nat_land_addr() -> [G; 32] {
    [0xa0, 0xdb, 0x90, 0xe6, 0x8e, 0xe3, 0xb7, 0xa1,
     0x66, 0xe3, 0x5f, 0x61, 0x9b, 0xd7, 0xb0, 0x2c,
     0x08, 0x96, 0xef, 0xd6, 0x0e, 0xb4, 0x69, 0x14,
     0xff, 0x3e, 0x4f, 0xb8, 0x12, 0x52, 0xfb, 0x94]
  }

  fn nat_lor_addr() -> [G; 32] {
    [0xd1, 0x44, 0x19, 0xaa, 0xa4, 0x7a, 0x03, 0xbf,
     0x9a, 0x46, 0x93, 0x8b, 0xf7, 0x2e, 0x40, 0xf9,
     0x6c, 0xab, 0x85, 0x3f, 0x9c, 0xc5, 0x86, 0x98,
     0x79, 0xe7, 0x69, 0x9f, 0x45, 0x17, 0x17, 0x73]
  }

  fn nat_xor_addr() -> [G; 32] {
    [0xae, 0x68, 0xfd, 0x41, 0x6e, 0xcb, 0x9c, 0xe2,
     0x06, 0x12, 0x27, 0x2d, 0x43, 0xc2, 0xf8, 0x6e,
     0xaf, 0x21, 0xd9, 0x54, 0x7f, 0x56, 0x59, 0x68,
     0x39, 0x1e, 0x9e, 0x12, 0xe3, 0x93, 0x72, 0xdc]
  }

  fn nat_shift_left_addr() -> [G; 32] {
    [0xf6, 0x06, 0xb7, 0xc2, 0x31, 0x80, 0xa2, 0x0a,
     0xce, 0x60, 0xfe, 0x24, 0xd5, 0x2b, 0xc0, 0xea,
     0x38, 0x54, 0x69, 0x8d, 0x2d, 0x14, 0xda, 0x05,
     0xc4, 0x83, 0x7a, 0x97, 0xe1, 0xab, 0x44, 0x69]
  }

  fn nat_shift_right_addr() -> [G; 32] {
    [0xd8, 0x60, 0xb5, 0x60, 0x15, 0x6d, 0xa6, 0x8e,
     0x80, 0x1c, 0x8b, 0xd5, 0x1d, 0x89, 0x2e, 0x55,
     0x7f, 0xbe, 0x35, 0x26, 0xd7, 0xd1, 0x98, 0x69,
     0x6f, 0xfb, 0x4d, 0x55, 0x1a, 0xe0, 0x4b, 0xb7]
  }

  fn nat_beq_addr() -> [G; 32] {
    [0xe8, 0xb7, 0x14, 0x9d, 0x8a, 0x7d, 0x12, 0x41,
     0x4b, 0x06, 0x25, 0x2f, 0x31, 0x8d, 0x40, 0x82,
     0x04, 0x72, 0x3c, 0xa4, 0xc0, 0x2f, 0x3a, 0x38,
     0xed, 0xfa, 0x37, 0x79, 0x24, 0x48, 0xc0, 0xda]
  }

  fn nat_ble_addr() -> [G; 32] {
    [0x22, 0x75, 0x08, 0x0a, 0x89, 0xc3, 0x27, 0x90,
     0x4e, 0x3a, 0xd1, 0x27, 0xba, 0x44, 0x37, 0x0a,
     0x7c, 0x6c, 0x1b, 0xef, 0x3a, 0xa7, 0x47, 0x92,
     0x07, 0x9f, 0x8f, 0x31, 0x59, 0x63, 0x69, 0x57]
  }

  fn str_addr() -> [G; 32] {
    [0xcb, 0x1b, 0xca, 0x7f, 0xc5, 0xdb, 0xb1, 0xbd,
     0xfb, 0xf6, 0x31, 0x9d, 0xf8, 0x9d, 0xa9, 0xfd,
     0xa3, 0xa6, 0x79, 0xd2, 0x25, 0x54, 0xb8, 0xa9,
     0xd5, 0xdd, 0x46, 0x63, 0xc0, 0xa9, 0x73, 0x12]
  }

  fn string_utf8_byte_size_addr() -> [G; 32] {
    [0x11, 0xea, 0x14, 0x32, 0x56, 0x2b, 0x11, 0x32,
     0x85, 0x3f, 0x17, 0x3f, 0xda, 0x9a, 0xdd, 0x59,
     0x1b, 0x06, 0x06, 0xa8, 0xde, 0xe3, 0x6b, 0x00,
     0xf7, 0x1b, 0xec, 0x29, 0x67, 0xfb, 0x64, 0x47]
  }

  fn string_back_addr() -> [G; 32] {
    [0x11, 0xba, 0xba, 0x55, 0xcb, 0xdf, 0x36, 0x49,
     0xfc, 0x1b, 0x69, 0x6c, 0x2e, 0x77, 0x56, 0x96,
     0xe9, 0x95, 0xc3, 0x8e, 0xf3, 0x13, 0xcf, 0x27,
     0x65, 0x53, 0xe1, 0x89, 0x8d, 0xa4, 0x5e, 0x0f]
  }

  fn string_legacy_back_addr() -> [G; 32] {
    [0x99, 0x8c, 0x3e, 0x64, 0x0c, 0x8b, 0x3a, 0x35,
     0xc6, 0x27, 0x20, 0x0d, 0xcd, 0x69, 0x4f, 0x67,
     0xf8, 0xb1, 0xd4, 0x1e, 0x68, 0x76, 0x0c, 0x90,
     0xe3, 0x61, 0xda, 0x24, 0x73, 0x4d, 0x39, 0xbc]
  }

  fn string_to_byte_array_addr() -> [G; 32] {
    [0x65, 0xf6, 0x44, 0x28, 0x6b, 0xc4, 0x94, 0x64,
     0xcc, 0x7a, 0x36, 0xb7, 0xd7, 0x95, 0x2f, 0x85,
     0x43, 0xab, 0x67, 0x56, 0x4c, 0xd5, 0x09, 0xee,
     0x87, 0x8a, 0x95, 0x37, 0x56, 0x09, 0x06, 0x9b]
  }

  fn byte_array_empty_addr() -> [G; 32] {
    [0xd9, 0x74, 0x17, 0xc4, 0x92, 0x06, 0xc6, 0x1f,
     0xe2, 0x8c, 0xbb, 0x7a, 0x0b, 0x60, 0x95, 0xf7,
     0x22, 0xcd, 0xfb, 0xc2, 0x13, 0xe0, 0x34, 0xaa,
     0x59, 0xde, 0x51, 0xb9, 0x21, 0x8a, 0xf0, 0x74]
  }

  fn char_of_nat_addr() -> [G; 32] {
    [0x7a, 0x57, 0x54, 0x38, 0x6b, 0x30, 0xbb, 0x86,
     0xf0, 0xb6, 0xf7, 0x0f, 0xd3, 0x68, 0xbb, 0x50,
     0xe6, 0x03, 0x27, 0x3a, 0x50, 0xad, 0x79, 0xd8,
     0xc1, 0x7f, 0xc3, 0xcb, 0x59, 0xf8, 0x0f, 0xac]
  }

  fn char_type_addr() -> [G; 32] {
    [0x38, 0xaa, 0x12, 0x05, 0x9f, 0xad, 0x3a, 0xfa,
     0x1e, 0x1e, 0x87, 0x40, 0xdc, 0x94, 0x70, 0xa4,
     0x7c, 0x26, 0x98, 0x63, 0x50, 0xf6, 0xcb, 0x3b,
     0xea, 0x1f, 0xae, 0x12, 0x76, 0xd7, 0xb5, 0xf1]
  }

  fn string_of_list_addr() -> [G; 32] {
    [0x63, 0xd9, 0x5a, 0x0f, 0xd6, 0xa1, 0x14, 0x43,
     0x48, 0xd0, 0xf2, 0x0e, 0x20, 0xcc, 0x5c, 0x3a,
     0xf6, 0x1a, 0xc9, 0x55, 0x92, 0x3f, 0x45, 0xf4,
     0x2a, 0x78, 0x2d, 0xe9, 0x33, 0xaa, 0xd5, 0x94]
  }

  fn list_nil_addr() -> [G; 32] {
    [0x0e, 0xbe, 0x34, 0x5d, 0xc4, 0x69, 0x17, 0xc8,
     0x24, 0xb6, 0xc3, 0xf6, 0xc4, 0x2b, 0x10, 0x1f,
     0x2a, 0xc8, 0xc0, 0xe2, 0xc9, 0x9f, 0x03, 0x3a,
     0x0e, 0xe3, 0xc6, 0x0a, 0xcb, 0x9c, 0xd8, 0x4d]
  }

  fn list_cons_addr() -> [G; 32] {
    [0xf7, 0x98, 0x42, 0xf1, 0x02, 0x06, 0x59, 0x89,
     0x29, 0xe6, 0xba, 0x60, 0xce, 0x3e, 0xba, 0xa0,
     0x0d, 0x11, 0xf2, 0x01, 0xc9, 0x9e, 0x80, 0x28,
     0x5f, 0x46, 0xcc, 0x0e, 0x90, 0x93, 0x28, 0x32]
  }

  fn bool_true_addr() -> [G; 32] {
    [0x42, 0x0d, 0xea, 0xd2, 0x16, 0x8a, 0xbd, 0x16,
     0xa7, 0x05, 0x0e, 0xdf, 0xd8, 0xe1, 0x7d, 0x45,
     0x15, 0x52, 0x37, 0xd3, 0x11, 0x87, 0x82, 0xd0,
     0xe6, 0x8b, 0x6d, 0xe8, 0x77, 0x42, 0xcb, 0x8d]
  }

  fn bool_false_addr() -> [G; 32] {
    [0xc1, 0x27, 0xf8, 0x9f, 0x92, 0xe0, 0x48, 0x1f,
     0x7a, 0x3e, 0x06, 0x31, 0xc5, 0x61, 0x5f, 0xe7,
     0xf6, 0xcb, 0xbf, 0x43, 0x9d, 0x5f, 0xd7, 0xeb,
     0xa4, 0x00, 0xfb, 0x06, 0x03, 0xae, 0xdf, 0x2f]
  }

  -- Mirror: BigUint::succ. Increment a KLimbs by 1; ripple carry.
  fn klimbs_succ(n: KLimbs) -> KLimbs {
    match load(n) {
      ListNode.Nil =>
        store(ListNode.Cons([1, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil))),
      ListNode.Cons(limb, rest) =>
        let pair = u64_add(limb, [1, 0, 0, 0, 0, 0, 0, 0]);
        match pair {
          (sum, carry) =>
            match carry {
              0 => store(ListNode.Cons(sum, rest)),
              _ => store(ListNode.Cons(sum, klimbs_succ(rest))),
            },
        },
    }
  }

  -- Mirror: BigUint::add. Limb-wise add with ripple carry.
  -- KLimbs are little-endian; head = least significant.
  -- Asymmetric lengths handled by terminating on shorter list and
  -- propagating carry into the longer.
  fn klimbs_add_carry(a: KLimbs, b: KLimbs, carry: G) -> KLimbs {
    match load(a) {
      ListNode.Nil =>
        match carry {
          0 => b,
          _ => klimbs_succ(b),
        },
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil =>
            match carry {
              0 => a,
              _ => klimbs_succ(a),
            },
          ListNode.Cons(lb, rb) =>
            let pair1 = u64_add(la, lb);
            match pair1 {
              (sum1, carry1) =>
                let pair2 = u64_add(sum1, [carry, 0, 0, 0, 0, 0, 0, 0]);
                match pair2 {
                  (sum2, carry2) =>
                    let total_carry = g_or(carry1, carry2);
                    store(ListNode.Cons(sum2, klimbs_add_carry(ra, rb, total_carry))),
                },
            },
        },
    }
  }

  fn klimbs_add(a: KLimbs, b: KLimbs) -> KLimbs {
    klimbs_add_carry(a, b, 0)
  }

  -- Mirror: byte-wise u64_sub with explicit final borrow.
  fn u64_sub_with_borrow(a: U64, b: U64) -> (U64, G) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let (r0, br1) = u8_sub(a0, b0);
    let (t1, u_t1) = u8_sub(a1, b1);
    let (r1, u_r1) = u8_sub(t1, br1);
    let br2 = g_or(u_t1, u_r1);
    let (t2, u_t2) = u8_sub(a2, b2);
    let (r2, u_r2) = u8_sub(t2, br2);
    let br3 = g_or(u_t2, u_r2);
    let (t3, u_t3) = u8_sub(a3, b3);
    let (r3, u_r3) = u8_sub(t3, br3);
    let br4 = g_or(u_t3, u_r3);
    let (t4, u_t4) = u8_sub(a4, b4);
    let (r4, u_r4) = u8_sub(t4, br4);
    let br5 = g_or(u_t4, u_r4);
    let (t5, u_t5) = u8_sub(a5, b5);
    let (r5, u_r5) = u8_sub(t5, br5);
    let br6 = g_or(u_t5, u_r5);
    let (t6, u_t6) = u8_sub(a6, b6);
    let (r6, u_r6) = u8_sub(t6, br6);
    let br7 = g_or(u_t6, u_r6);
    let (t7, u_t7) = u8_sub(a7, b7);
    let (r7, u_r7) = u8_sub(t7, br7);
    let final_borrow = g_or(u_t7, u_r7);
    ([r0, r1, r2, r3, r4, r5, r6, r7], final_borrow)
  }

  -- Mirror: BigUint::sub with saturating-at-zero (Lean Nat.sub semantics).
  -- a - b clamped to 0 when b > a.
  --
  -- Walk both lists in parallel limb-by-limb with borrow ripple. If the
  -- final borrow is 1 OR `b` has more limbs than `a`, return 0 (Nil).
  -- Otherwise normalize trailing zero limbs.
  fn klimbs_sub_borrow(a: KLimbs, b: KLimbs, borrow: G) -> (KLimbs, G) {
    match load(a) {
      ListNode.Nil =>
        match load(b) {
          ListNode.Nil =>
            -- 0 - 0 - borrow: borrow=1 → underflow.
            (store(ListNode.Nil), borrow),
          ListNode.Cons(_, _) =>
            -- 0 - non-empty: definite underflow (b > 0 + carries).
            (store(ListNode.Nil), 1),
        },
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil =>
            -- a - 0 - borrow: subtract borrow from la, propagate.
            match borrow {
              0 => (a, 0),
              _ =>
                let pair = u64_sub_with_borrow(la, [1, 0, 0, 0, 0, 0, 0, 0]);
                match pair {
                  (diff, br) =>
                    let pair2 = klimbs_sub_borrow(ra, store(ListNode.Nil), br);
                    match pair2 {
                      (rest_res, br2) =>
                        (store(ListNode.Cons(diff, rest_res)), br2),
                    },
                },
            },
          ListNode.Cons(lb, rb) =>
            let pair1 = u64_sub_with_borrow(la, lb);
            match pair1 {
              (sum1, br1) =>
                let pair2 = u64_sub_with_borrow(sum1, [borrow, 0, 0, 0, 0, 0, 0, 0]);
                match pair2 {
                  (sum2, br2) =>
                    let total = g_or(br1, br2);
                    let rec_pair = klimbs_sub_borrow(ra, rb, total);
                    match rec_pair {
                      (rest_res, br_final) =>
                        (store(ListNode.Cons(sum2, rest_res)), br_final),
                    },
                },
            },
        },
    }
  }

  -- Strip trailing zero limbs (canonicalize `[k, 0, 0]` → `[k]`).
  fn klimbs_normalize(n: KLimbs) -> KLimbs {
    match load(n) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(limb, rest) =>
        let normalized_rest = klimbs_normalize(rest);
        match load(normalized_rest) {
          ListNode.Nil =>
            match u64_is_zero(limb) {
              1 => store(ListNode.Nil),
              0 => store(ListNode.Cons(limb, store(ListNode.Nil))),
            },
          _ => store(ListNode.Cons(limb, normalized_rest)),
        },
    }
  }

  fn klimbs_sub(a: KLimbs, b: KLimbs) -> KLimbs {
    let pair = klimbs_sub_borrow(a, b, 0);
    match pair {
      (result, borrow) =>
        match borrow {
          1 => store(ListNode.Nil),
          0 => klimbs_normalize(result),
        },
    }
  }

  -- Mirror: Nat.le. Returns 1 if a ≤ b, 0 otherwise.
  -- Uses saturating sub: a ≤ b iff (a - b) saturates to 0.
  fn klimbs_le(a: KLimbs, b: KLimbs) -> G {
    let diff = klimbs_sub(a, b);
    match load(diff) {
      ListNode.Nil => 1,
      _ => 0,
    }
  }

  -- Mirror: Nat.pred. Saturating decrement; pred(0) = 0.
  fn klimbs_dec(a: KLimbs) -> KLimbs {
    let one = store(ListNode.Cons([1, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil)));
    klimbs_sub(a, one)
  }

  -- Returns (remainder, quotient): remainder = x mod 256, quotient = x / 256.
  -- `u64_mul` feeds this only small column sums (sums of bytes, < ~4096),
  -- so the repeated subtraction terminates in a handful of steps.
  fn divmod_256(x: G, q: G) -> (G, G) {
    match u32_less_than(x, 256) {
      1 => (x, q),
      0 => divmod_256(x - 256, q + 1),
    }
  }

  -- u64×u64 → (lo: U64, hi: U64) via byte schoolbook. Each byte×byte
  -- product is split into (low, high) bytes by the `u8_mul` gadget, so
  -- every column is a sum of bytes (not products) and `divmod_256` only
  -- carry-propagates small values.
  fn u64_mul(a: U64, b: U64) -> (U64, U64) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let (l00, h00) = u8_mul(a0, b0);
    let (l01, h01) = u8_mul(a0, b1);
    let (l02, h02) = u8_mul(a0, b2);
    let (l03, h03) = u8_mul(a0, b3);
    let (l04, h04) = u8_mul(a0, b4);
    let (l05, h05) = u8_mul(a0, b5);
    let (l06, h06) = u8_mul(a0, b6);
    let (l07, h07) = u8_mul(a0, b7);
    let (l10, h10) = u8_mul(a1, b0);
    let (l11, h11) = u8_mul(a1, b1);
    let (l12, h12) = u8_mul(a1, b2);
    let (l13, h13) = u8_mul(a1, b3);
    let (l14, h14) = u8_mul(a1, b4);
    let (l15, h15) = u8_mul(a1, b5);
    let (l16, h16) = u8_mul(a1, b6);
    let (l17, h17) = u8_mul(a1, b7);
    let (l20, h20) = u8_mul(a2, b0);
    let (l21, h21) = u8_mul(a2, b1);
    let (l22, h22) = u8_mul(a2, b2);
    let (l23, h23) = u8_mul(a2, b3);
    let (l24, h24) = u8_mul(a2, b4);
    let (l25, h25) = u8_mul(a2, b5);
    let (l26, h26) = u8_mul(a2, b6);
    let (l27, h27) = u8_mul(a2, b7);
    let (l30, h30) = u8_mul(a3, b0);
    let (l31, h31) = u8_mul(a3, b1);
    let (l32, h32) = u8_mul(a3, b2);
    let (l33, h33) = u8_mul(a3, b3);
    let (l34, h34) = u8_mul(a3, b4);
    let (l35, h35) = u8_mul(a3, b5);
    let (l36, h36) = u8_mul(a3, b6);
    let (l37, h37) = u8_mul(a3, b7);
    let (l40, h40) = u8_mul(a4, b0);
    let (l41, h41) = u8_mul(a4, b1);
    let (l42, h42) = u8_mul(a4, b2);
    let (l43, h43) = u8_mul(a4, b3);
    let (l44, h44) = u8_mul(a4, b4);
    let (l45, h45) = u8_mul(a4, b5);
    let (l46, h46) = u8_mul(a4, b6);
    let (l47, h47) = u8_mul(a4, b7);
    let (l50, h50) = u8_mul(a5, b0);
    let (l51, h51) = u8_mul(a5, b1);
    let (l52, h52) = u8_mul(a5, b2);
    let (l53, h53) = u8_mul(a5, b3);
    let (l54, h54) = u8_mul(a5, b4);
    let (l55, h55) = u8_mul(a5, b5);
    let (l56, h56) = u8_mul(a5, b6);
    let (l57, h57) = u8_mul(a5, b7);
    let (l60, h60) = u8_mul(a6, b0);
    let (l61, h61) = u8_mul(a6, b1);
    let (l62, h62) = u8_mul(a6, b2);
    let (l63, h63) = u8_mul(a6, b3);
    let (l64, h64) = u8_mul(a6, b4);
    let (l65, h65) = u8_mul(a6, b5);
    let (l66, h66) = u8_mul(a6, b6);
    let (l67, h67) = u8_mul(a6, b7);
    let (l70, h70) = u8_mul(a7, b0);
    let (l71, h71) = u8_mul(a7, b1);
    let (l72, h72) = u8_mul(a7, b2);
    let (l73, h73) = u8_mul(a7, b3);
    let (l74, h74) = u8_mul(a7, b4);
    let (l75, h75) = u8_mul(a7, b5);
    let (l76, h76) = u8_mul(a7, b6);
    let (l77, h77) = u8_mul(a7, b7);
    -- Column k gathers low bytes of products with i+j=k and high bytes
    -- of products with i+j=k-1.
    let col0 = l00;
    let col1 = l01 + l10 + h00;
    let col2 = l02 + l11 + l20 + h01 + h10;
    let col3 = l03 + l12 + l21 + l30 + h02 + h11 + h20;
    let col4 = l04 + l13 + l22 + l31 + l40 + h03 + h12 + h21 + h30;
    let col5 = l05 + l14 + l23 + l32 + l41 + l50 + h04 + h13 + h22 + h31 + h40;
    let col6 = l06 + l15 + l24 + l33 + l42 + l51 + l60 + h05 + h14 + h23 + h32 + h41 + h50;
    let col7 = l07 + l16 + l25 + l34 + l43 + l52 + l61 + l70 + h06 + h15 + h24 + h33 + h42 + h51 + h60;
    let col8 = l17 + l26 + l35 + l44 + l53 + l62 + l71 + h07 + h16 + h25 + h34 + h43 + h52 + h61 + h70;
    let col9 = l27 + l36 + l45 + l54 + l63 + l72 + h17 + h26 + h35 + h44 + h53 + h62 + h71;
    let col10 = l37 + l46 + l55 + l64 + l73 + h27 + h36 + h45 + h54 + h63 + h72;
    let col11 = l47 + l56 + l65 + l74 + h37 + h46 + h55 + h64 + h73;
    let col12 = l57 + l66 + l75 + h47 + h56 + h65 + h74;
    let col13 = l67 + l76 + h57 + h66 + h75;
    let col14 = l77 + h67 + h76;
    let col15 = h77;
    match divmod_256(col0, 0) {
      (r0, c1) =>
        match divmod_256(col1 + c1, 0) {
          (r1, c2) =>
            match divmod_256(col2 + c2, 0) {
              (r2, c3) =>
                match divmod_256(col3 + c3, 0) {
                  (r3, c4) =>
                    match divmod_256(col4 + c4, 0) {
                      (r4, c5) =>
                        match divmod_256(col5 + c5, 0) {
                          (r5, c6) =>
                            match divmod_256(col6 + c6, 0) {
                              (r6, c7) =>
                                match divmod_256(col7 + c7, 0) {
                                  (r7, c8) =>
                                    match divmod_256(col8 + c8, 0) {
                                      (r8, c9) =>
                                        match divmod_256(col9 + c9, 0) {
                                          (r9, c10) =>
                                            match divmod_256(col10 + c10, 0) {
                                              (r10, c11) =>
                                                match divmod_256(col11 + c11, 0) {
                                                  (r11, c12) =>
                                                    match divmod_256(col12 + c12, 0) {
                                                      (r12, c13) =>
                                                        match divmod_256(col13 + c13, 0) {
                                                          (r13, c14) =>
                                                            match divmod_256(col14 + c14, 0) {
                                                              (r14, c15) =>
                                                                match divmod_256(col15 + c15, 0) {
                                                                  (r15, _) =>
                                                                    ([r0, r1, r2, r3, r4, r5, r6, r7],
                                                                     [r8, r9, r10, r11, r12, r13, r14, r15]),
                                                                },
                                                            },
                                                        },
                                                    },
                                                },
                                            },
                                        },
                                    },
                                },
                            },
                        },
                    },
                },
            },
        },
    }
  }

  -- Mirror: BigUint::mul. Limb-wise schoolbook multiply.
  fn klimbs_mul(a: KLimbs, b: KLimbs) -> KLimbs {
    klimbs_mul_outer(a, b, store(ListNode.Nil), 0)
  }

  fn klimbs_mul_outer(a: KLimbs, b: KLimbs, acc: KLimbs, shift: G) -> KLimbs {
    match load(a) {
      ListNode.Nil => acc,
      ListNode.Cons(a_limb, rest) =>
        let prod = klimbs_mul_single(a_limb, b, [0, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil));
        let shifted = klimbs_shl_limbs(prod, shift);
        let new_acc = klimbs_add(acc, shifted);
        klimbs_mul_outer(rest, b, new_acc, shift + 1),
    }
  }

  fn klimbs_mul_single(a_limb: U64, b: KLimbs, carry: U64, acc: KLimbs) -> KLimbs {
    match load(b) {
      ListNode.Nil =>
        match u64_is_zero(carry) {
          1 => acc,
          0 => list_snoc(acc, carry),
        },
      ListNode.Cons(b_limb, rest) =>
        match u64_mul(a_limb, b_limb) {
          (lo, hi) =>
            match u64_add(lo, carry) {
              (sum, carry_out) =>
                match u64_add(hi, [carry_out, 0, 0, 0, 0, 0, 0, 0]) {
                  (new_carry, _) =>
                    let new_acc = list_snoc(acc, sum);
                    klimbs_mul_single(a_limb, rest, new_carry, new_acc),
                },
            },
        },
    }
  }

  fn klimbs_shl_limbs(x: KLimbs, shift: G) -> KLimbs {
    match shift {
      0 => x,
      _ =>
        let prepended = store(ListNode.Cons([0, 0, 0, 0, 0, 0, 0, 0], x));
        klimbs_shl_limbs(prepended, shift - 1),
    }
  }

  fn klimbs_is_zero(x: KLimbs) -> G {
    match load(klimbs_normalize(x)) {
      ListNode.Nil => 1,
      _ => 0,
    }
  }

  -- Mirror: BigUint::div_mod via repeated subtraction. Returns (quotient,
  -- remainder). For divisor 0, follows Lean Nat semantics: a / 0 = 0,
  -- a % 0 = a.
  fn klimbs_div_mod(a: KLimbs, b: KLimbs) -> (KLimbs, KLimbs) {
    match klimbs_is_zero(b) {
      1 => (store(ListNode.Nil), a),
      0 => klimbs_div_mod_go(a, b, store(ListNode.Nil)),
    }
  }

  fn klimbs_div_mod_go(a: KLimbs, b: KLimbs, q: KLimbs) -> (KLimbs, KLimbs) {
    match klimbs_le(b, a) {
      0 => (q, a),
      1 => klimbs_div_mod_go(klimbs_sub(a, b), b, klimbs_succ(q)),
    }
  }

  fn klimbs_div(a: KLimbs, b: KLimbs) -> KLimbs {
    match klimbs_div_mod(a, b) { (q, _) => q, }
  }

  fn klimbs_mod(a: KLimbs, b: KLimbs) -> KLimbs {
    match klimbs_div_mod(a, b) { (_, r) => r, }
  }

  fn klimbs_gcd(a: KLimbs, b: KLimbs) -> KLimbs {
    match klimbs_is_zero(b) {
      1 => a,
      0 => klimbs_gcd(b, klimbs_mod(a, b)),
    }
  }

  fn klimbs_pow(base: KLimbs, exp: KLimbs) -> KLimbs {
    match klimbs_is_zero(exp) {
      1 => store(ListNode.Cons([1, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil))),
      0 => klimbs_mul(base, klimbs_pow(base, klimbs_dec(exp))),
    }
  }

  -- Byte-wise AND on two U64 limbs.
  fn u64_and(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [u8_and(a0, b0), u8_and(a1, b1), u8_and(a2, b2), u8_and(a3, b3),
     u8_and(a4, b4), u8_and(a5, b5), u8_and(a6, b6), u8_and(a7, b7)]
  }

  fn u64_or(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [u8_or(a0, b0), u8_or(a1, b1), u8_or(a2, b2), u8_or(a3, b3),
     u8_or(a4, b4), u8_or(a5, b5), u8_or(a6, b6), u8_or(a7, b7)]
  }

  fn u64_xor_kbits(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [u8_xor(a0, b0), u8_xor(a1, b1), u8_xor(a2, b2), u8_xor(a3, b3),
     u8_xor(a4, b4), u8_xor(a5, b5), u8_xor(a6, b6), u8_xor(a7, b7)]
  }

  -- Mirror: BigUint::bitand. Walks parallel limbs; result length = min(len(a), len(b)).
  fn klimbs_land(a: KLimbs, b: KLimbs) -> KLimbs {
    match load(a) {
      ListNode.Nil => store(ListNode.Nil),
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => store(ListNode.Nil),
          ListNode.Cons(lb, rb) =>
            store(ListNode.Cons(u64_and(la, lb), klimbs_land(ra, rb))),
        },
    }
  }

  -- Mirror: BigUint::bitor. Result length = max(len(a), len(b)); shorter is zero-padded.
  fn klimbs_lor(a: KLimbs, b: KLimbs) -> KLimbs {
    match load(a) {
      ListNode.Nil => b,
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => a,
          ListNode.Cons(lb, rb) =>
            store(ListNode.Cons(u64_or(la, lb), klimbs_lor(ra, rb))),
        },
    }
  }

  -- Mirror: BigUint::bitxor. Result length = max(len(a), len(b)); zero-padded shorter.
  fn klimbs_xor_op(a: KLimbs, b: KLimbs) -> KLimbs {
    match load(a) {
      ListNode.Nil => b,
      ListNode.Cons(la, ra) =>
        match load(b) {
          ListNode.Nil => a,
          ListNode.Cons(lb, rb) =>
            store(ListNode.Cons(u64_xor_kbits(la, lb), klimbs_xor_op(ra, rb))),
        },
    }
  }

  -- Shift left by n bits via repeated multiplication by 2.
  fn klimbs_shl(a: KLimbs, n: KLimbs) -> KLimbs {
    let two = store(ListNode.Cons([2, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil)));
    klimbs_mul(a, klimbs_pow(two, n))
  }

  -- Shift right by n bits via integer division by 2^n.
  fn klimbs_shr(a: KLimbs, n: KLimbs) -> KLimbs {
    let two = store(ListNode.Cons([2, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil)));
    klimbs_div(a, klimbs_pow(two, n))
  }

  -- ============================================================================
  -- Lit(Nat) extraction + dispatch
  -- ============================================================================

  -- Find target's positional idx in addrs. Returns (1, idx) if found,
  -- (0, _) if not. Used by Nat literal coercion in iota.
  fn find_addr_idx_safe(target: [G; 32], addrs: List‹[G; 32]›, i: G) -> (G, G) {
    match load(addrs) {
      ListNode.Nil => (0, 0),
      ListNode.Cons(a, rest) =>
        match address_eq(target, a) {
          1 => (1, i),
          0 => find_addr_idx_safe(target, rest, i + 1),
        },
    }
  }

  -- Convert a KLimbs n into a chain `App(Const(succ), App(Const(succ),
  -- ... Const(zero)))` for n calls of succ. Used by nat-literal-to-ctor
  -- coercion in iota.
  fn klimbs_to_ctor_form(n: KLimbs, zero_idx: G, succ_idx: G) -> KExpr {
    match load(n) {
      ListNode.Nil =>
        store(KExprNode.Const(zero_idx, store(ListNode.Nil))),
      ListNode.Cons(_, _) =>
        let dec = klimbs_dec(n);
        let pred = klimbs_to_ctor_form(dec, zero_idx, succ_idx);
        let succ_const = store(KExprNode.Const(succ_idx, store(ListNode.Nil)));
        store(KExprNode.App(succ_const, pred)),
    }
  }

  -- If `e` is `Lit(Nat(klimbs))` and addrs contains both Nat.zero and
  -- Nat.succ, expand to ctor chain. Else return `e` unchanged. Mirror:
  -- src/ix/kernel/whnf.rs:929-946 nat_to_constructor.
  fn nat_lit_to_ctor_or_self(e: KExpr, addrs: List‹[G; 32]›) -> KExpr {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(klimbs) =>
            let z = find_addr_idx_safe(nat_zero_addr(), addrs, 0);
            let s = find_addr_idx_safe(nat_succ_addr(), addrs, 0);
            match z {
              (1, zero_idx) =>
                match s {
                  (1, succ_idx) => klimbs_to_ctor_form(klimbs, zero_idx, succ_idx),
                  _ => e,
                },
              _ => e,
            },
          _ => e,
        },
      _ => e,
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs::extract_nat_value. Accepts:
  --   * `Lit(Nat klimbs)` → klimbs
  --   * `Const(Nat.zero)` → 0
  --   * `App(Const(Nat.succ), x)` → 1 + extract(x)
  fn try_extract_nat(e: KExpr, addrs: List‹[G; 32]›) -> (G, KLimbs) {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(limbs) => (1, limbs),
          _ => (0, store(ListNode.Nil)),
        },
      KExprNode.Const(idx, _) =>
        let const_addr = list_lookup(addrs, idx);
        match address_eq(const_addr, nat_zero_addr()) {
          1 => (1, store(ListNode.Nil)),
          0 => (0, store(ListNode.Nil)),
        },
      KExprNode.App(f, a) =>
        match load(f) {
          KExprNode.Const(idx, _) =>
            let head_addr_ = list_lookup(addrs, idx);
            match address_eq(head_addr_, nat_succ_addr()) {
              1 =>
                match try_extract_nat(a, addrs) {
                  (1, pred_limbs) => (1, klimbs_succ(pred_limbs)),
                  _ => (0, store(ListNode.Nil)),
                },
              0 => (0, store(ListNode.Nil)),
            },
          _ => (0, store(ListNode.Nil)),
        },
      _ => (0, store(ListNode.Nil)),
    }
  }

  -- Wrap a KLimbs in `Lit(Nat(...))`.
  fn mk_nat_lit(n: KLimbs) -> KExpr {
    store(KExprNode.Lit(KLiteral.Nat(n)))
  }

  -- Mirror: src/ix/kernel/whnf.rs:500-700 Nat-on-literals dispatch.
  -- Address-keyed (no positional prims): given the head Const's blake3
  -- address and the unreduced spine, fold a Nat primitive op when both
  -- required args are literals. Returns (1, reduced) on hit, (0, _) on miss.
  fn try_nat_dispatch(head_addr: [G; 32], spine: List‹KExpr›,
                      types: List‹KExpr›, top: List‹&KConstantInfo›,
                      addrs: List‹[G; 32]›) -> (G, KExpr) {
    let spine_len = list_length(spine);
    let is_pred = address_eq(head_addr, nat_pred_addr());
    let is_succ = address_eq(head_addr, nat_succ_addr());
    match is_succ {
      1 =>
        -- Mirror: whnf.rs:1789-1822 try_reduce_nat_succ_iter. Single arg;
        -- whnf, fold to Lit(n+1) on hit.
        match u32_less_than(spine_len, 1) {
          1 => (0, store(KExprNode.BVar(0))),
          0 =>
            let a0_w = whnf(list_lookup(spine, 0), types, top, addrs);
            match try_extract_nat(a0_w, addrs) {
              (1, na) =>
                let post = list_drop(spine, 1);
                (1, apply_spine(mk_nat_lit(klimbs_succ(na)), post)),
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
      0 =>
        match is_pred {
          1 =>
            match u32_less_than(spine_len, 1) {
              1 => (0, store(KExprNode.BVar(0))),
              0 =>
                let a0_w = whnf(list_lookup(spine, 0), types, top, addrs);
                match try_extract_nat(a0_w, addrs) {
                  (1, na) =>
                    let post = list_drop(spine, 1);
                    (1, apply_spine(mk_nat_lit(klimbs_dec(na)), post)),
                  _ => (0, store(KExprNode.BVar(0))),
                },
            },
          0 =>
            -- Binary ops: require 2 args.
            match u32_less_than(spine_len, 2) {
              1 => (0, store(KExprNode.BVar(0))),
              0 =>
                let a0_w = whnf(list_lookup(spine, 0), types, top, addrs);
                let a1_w = whnf(list_lookup(spine, 1), types, top, addrs);
                let pa = try_extract_nat(a0_w, addrs);
                let pb = try_extract_nat(a1_w, addrs);
                match pa {
                  (1, na) =>
                    match pb {
                      (1, nb) =>
                        match try_nat_binop_addr(head_addr, na, nb, addrs) {
                          (1, result) =>
                            let post = list_drop(spine, 2);
                            (1, apply_spine(result, post)),
                          (0, _) => (0, store(KExprNode.BVar(0))),
                        },
                      _ => (0, store(KExprNode.BVar(0))),
                    },
                  _ => (0, store(KExprNode.BVar(0))),
                },
            },
        },
    }
  }

  -- Dispatch a Nat binary op by head address. Bool result for beq/ble
  -- wraps via Bool.true / Bool.false ctors (mk_bool).
  fn try_nat_binop_addr(head_addr: [G; 32], a: KLimbs, b: KLimbs,
                        addrs: List‹[G; 32]›) -> (G, KExpr) {
    match address_eq(head_addr, nat_add_addr()) {
      1 => (1, mk_nat_lit(klimbs_normalize(klimbs_add(a, b)))),
      0 =>
        match address_eq(head_addr, nat_sub_addr()) {
          1 => (1, mk_nat_lit(klimbs_normalize(klimbs_sub(a, b)))),
          0 =>
            match address_eq(head_addr, nat_mul_addr()) {
              1 => (1, mk_nat_lit(klimbs_normalize(klimbs_mul(a, b)))),
              0 =>
                match address_eq(head_addr, nat_div_addr()) {
                  1 => (1, mk_nat_lit(klimbs_normalize(klimbs_div(a, b)))),
                  0 =>
                    match address_eq(head_addr, nat_mod_addr()) {
                      1 => (1, mk_nat_lit(klimbs_normalize(klimbs_mod(a, b)))),
                      0 =>
                        match address_eq(head_addr, nat_gcd_addr()) {
                          1 => (1, mk_nat_lit(klimbs_normalize(klimbs_gcd(a, b)))),
                          0 =>
                            match address_eq(head_addr, nat_pow_addr()) {
                              1 => (1, mk_nat_lit(klimbs_normalize(klimbs_pow(a, b)))),
                              0 =>
                                match address_eq(head_addr, nat_land_addr()) {
                                  1 => (1, mk_nat_lit(klimbs_normalize(klimbs_land(a, b)))),
                                  0 =>
                                    match address_eq(head_addr, nat_lor_addr()) {
                                      1 => (1, mk_nat_lit(klimbs_normalize(klimbs_lor(a, b)))),
                                      0 =>
                                        match address_eq(head_addr, nat_xor_addr()) {
                                          1 => (1, mk_nat_lit(klimbs_normalize(klimbs_xor_op(a, b)))),
                                          0 =>
                                            match address_eq(head_addr, nat_shift_left_addr()) {
                                              1 => (1, mk_nat_lit(klimbs_normalize(klimbs_shl(a, b)))),
                                              0 =>
                                                match address_eq(head_addr, nat_shift_right_addr()) {
                                                  1 => (1, mk_nat_lit(klimbs_normalize(klimbs_shr(a, b)))),
                                                  0 =>
                                            match address_eq(head_addr, nat_beq_addr()) {
                                              1 => (1, mk_bool(klimbs_eq(a, b), addrs)),
                                              0 =>
                                                match address_eq(head_addr, nat_ble_addr()) {
                                                  1 => (1, mk_bool(klimbs_le(a, b), addrs)),
                                                  0 => (0, store(KExprNode.BVar(0))),
                                                },
                                            },
                                        },
                                    },
                                },
                            },
                        },
                    },
                },
            },
        },
        },
        },
    }
  }

  -- Encode a boolean as `Const(Bool.true)` / `Const(Bool.false)` when
  -- those ctors are present in addrs. Falls back to `Lit(Nat(0|1))`
  -- when not (e.g., kernel const list lacks Bool — should not happen
  -- in practice for typed beq/ble dispatch).
  fn mk_bool(g: G, addrs: List‹[G; 32]›) -> KExpr {
    let target = match g {
      0 => bool_false_addr(),
      _ => bool_true_addr(),
    };
    let pair = find_addr_idx_safe(target, addrs, 0);
    match pair {
      (1, idx) => store(KExprNode.Const(idx, store(ListNode.Nil))),
      (0, _) =>
        match g {
          0 => store(KExprNode.Lit(KLiteral.Nat(store(ListNode.Nil)))),
          _ =>
            store(KExprNode.Lit(KLiteral.Nat(
              store(ListNode.Cons([1, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil)))))),
        },
    }
  }

  -- Single-limb KLimbs to G value (low 4 bytes). Used for bitvec width
  -- where width ≤ 2^24 fits in 24 bits. Returns 0 for empty KLimbs.
  fn klimbs_lo_g(n: KLimbs) -> G {
    match load(n) {
      ListNode.Nil => 0,
      ListNode.Cons(limb, _) =>
        let [b0, b1, b2, b3, _, _, _, _] = limb;
        b0 + 256*b1 + 65536*b2 + 16777216*b3,
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:2546-2579 fn try_reduce_bitvec_to_nat.
  -- `BitVec.toNat width (BitVec.ofNat width' n)` → `Lit(Nat (n mod 2^width))`.
  -- Width must be ≤ 2^24 to bound klimbs_pow cost.
  fn try_reduce_bit_vec_to_nat(spine: List‹KExpr›, types: List‹KExpr›,
                                top: List‹&KConstantInfo›,
                                addrs: List‹[G; 32]›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let width_e = list_lookup(spine, 0);
        let val_e = list_lookup(spine, 1);
        let val_w = whnf(val_e, types, top, addrs);
        -- Mirror: src/ix/kernel/whnf.rs:2581-2602 bitvec_of_nat_args.
        -- Accepts both `BitVec.ofNat(W, N)` and `OfNat.ofNat(BitVec W, N)`.
        let pair = bitvec_of_nat_args(val_w, addrs);
        match pair {
          (0, _, _) => (0, store(KExprNode.BVar(0))),
          (1, val_width, n_e) =>
            let n_w = whnf(n_e, types, top, addrs);
            let np = try_extract_nat(n_w, addrs);
            match np {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, n_klimbs) =>
                let width_w = whnf(val_width, types, top, addrs);
                let wp = try_extract_nat(width_w, addrs);
                match wp {
                  (0, _) => (0, store(KExprNode.BVar(0))),
                  (1, w_klimbs) =>
                    let two = store(ListNode.Cons([2, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil)));
                    let modulus = klimbs_pow(two, w_klimbs);
                    let result = klimbs_mod(n_klimbs, modulus);
                    (1, mk_nat_lit(result)),
                },
            },
        },
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:2581-2602 fn bitvec_of_nat_args.
  -- Returns (1, width_e, n_e) if `e` is `BitVec.ofNat W N` or
  -- `OfNat.ofNat (BitVec W) N _inst`. Else (0, _, _).
  fn bitvec_of_nat_args(e: KExpr, addrs: List‹[G; 32]›) -> (G, KExpr, KExpr) {
    match collect_spine_simple(e) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(idx, _) =>
            let head_addr = list_lookup(addrs, idx);
            match address_eq(head_addr, bit_vec_of_nat_addr()) {
              1 =>
                match list_length(args) - 2 {
                  0 => (1, list_lookup(args, 0), list_lookup(args, 1)),
                  _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                },
              0 =>
                let of_nat_addr = [0x8f, 0xdc, 0x86, 0x9f, 0x7b, 0x7a, 0xa2, 0xb7,
                                   0xb5, 0x92, 0x9b, 0xa2, 0x42, 0xed, 0x89, 0x9c,
                                   0xe2, 0xd7, 0xc5, 0xd4, 0x2d, 0xf1, 0xd4, 0xe2,
                                   0x39, 0x36, 0x90, 0xcf, 0xa8, 0x5e, 0x94, 0xd2];
                match address_eq(head_addr, of_nat_addr) {
                  0 => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                  1 =>
                    match u32_less_than(list_length(args), 2) {
                      1 => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                      0 =>
                        let ty_arg = list_lookup(args, 0);
                        match collect_spine_simple(ty_arg) {
                          (ty_head, ty_args) =>
                            match load(ty_head) {
                              KExprNode.Const(ty_idx, _) =>
                                let ty_addr = list_lookup(addrs, ty_idx);
                                match address_eq(ty_addr, bit_vec_addr()) {
                                  0 => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                                  1 =>
                                    match list_length(ty_args) - 1 {
                                      0 => (1, list_lookup(ty_args, 0), list_lookup(args, 1)),
                                      _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                                    },
                                },
                              _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                            },
                        },
                    },
                },
            },
          _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
        },
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:2465-2506 fn try_reduce_bitvec_ult.
  -- `BitVec.ult width lhs rhs` → `Bool.true/false`. Both sides converted
  -- to nat via bit_vec_to_nat, then compared with `<` (= Nat.ble (lhs+1) rhs).
  fn try_reduce_bit_vec_ult(spine: List‹KExpr›, types: List‹KExpr›,
                             top: List‹&KConstantInfo›,
                             addrs: List‹[G; 32]›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 3) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let width_e = list_lookup(spine, 0);
        let lhs_e = list_lookup(spine, 1);
        let rhs_e = list_lookup(spine, 2);
        -- Build BitVec.toNat width lhs / rhs and reduce.
        let lhs_pair = bv_to_nat_via(width_e, lhs_e, types, top, addrs);
        let rhs_pair = bv_to_nat_via(width_e, rhs_e, types, top, addrs);
        match lhs_pair {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, lhs_n) =>
            match rhs_pair {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, rhs_n) =>
                -- lhs < rhs iff klimbs_le(lhs+1, rhs) iff !klimbs_le(rhs, lhs)
                let r = 1 - klimbs_le(rhs_n, lhs_n);
                (1, mk_bool(r, addrs)),
            },
        },
    }
  }

  -- Helper: invoke bit_vec_to_nat reduction on (width, val) pair, return
  -- extracted nat KLimbs. Returns (1, klimbs) or (0, _).
  fn bv_to_nat_via(width_e: KExpr, val_e: KExpr, types: List‹KExpr›,
                    top: List‹&KConstantInfo›,
                    addrs: List‹[G; 32]›) -> (G, KLimbs) {
    let spine = store(ListNode.Cons(width_e,
      store(ListNode.Cons(val_e, store(ListNode.Nil)))));
    let r = try_reduce_bit_vec_to_nat(spine, types, top, addrs);
    match r {
      (0, _) => (0, store(ListNode.Nil)),
      (1, lit_e) =>
        match load(lit_e) {
          KExprNode.Lit(lit) =>
            match lit {
              KLiteral.Nat(klimbs) => (1, klimbs),
              _ => (0, store(ListNode.Nil)),
            },
          _ => (0, store(ListNode.Nil)),
        },
    }
  }

  -- Top-level bitvec dispatch: routes head_addr to the right reduction.
  fn try_bitvec_dispatch(head_addr: [G; 32], spine: List‹KExpr›,
                          types: List‹KExpr›,
                          top: List‹&KConstantInfo›,
                          addrs: List‹[G; 32]›) -> (G, KExpr) {
    match address_eq(head_addr, bit_vec_to_nat_addr()) {
      1 => try_reduce_bit_vec_to_nat(spine, types, top, addrs),
      0 =>
        match address_eq(head_addr, bit_vec_ult_addr()) {
          1 => try_reduce_bit_vec_ult(spine, types, top, addrs),
          0 =>
            -- decide (LT.lt BitVec width a b) → bitvec_ult.
            -- Mirror: src/ix/kernel/whnf.rs:2455-2460.
            match address_eq(head_addr, decidable_decide_addr()) {
              1 => try_reduce_decide_bitvec_lt(spine, types, top, addrs),
              0 => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  -- `decide (LT.lt BitVec a b) inst` → if LT.lt's type arg is BitVec, reduce
  -- via bit_vec_ult. Mirror: src/ix/kernel/whnf.rs:2508-2529 fn try_reduce_bitvec_lt_prop.
  fn try_reduce_decide_bitvec_lt(spine: List‹KExpr›, types: List‹KExpr›,
                                  top: List‹&KConstantInfo›,
                                  addrs: List‹[G; 32]›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let prop = list_lookup(spine, 0);
        match collect_spine_simple(prop) {
          (lt_head, lt_args) =>
            match load(lt_head) {
              KExprNode.Const(lt_idx, _) =>
                let lt_addr = list_lookup(addrs, lt_idx);
                match address_eq(lt_addr, lt_lt_addr()) {
                  0 => (0, store(KExprNode.BVar(0))),
                  1 =>
                    match u32_less_than(list_length(lt_args), 4) {
                      1 => (0, store(KExprNode.BVar(0))),
                      0 =>
                        let ty_arg = list_lookup(lt_args, 0);
                        match collect_spine_simple(ty_arg) {
                          (ty_head, ty_args) =>
                            match load(ty_head) {
                              KExprNode.Const(ty_idx, _) =>
                                let ty_addr = list_lookup(addrs, ty_idx);
                                match address_eq(ty_addr, bit_vec_addr()) {
                                  0 => (0, store(KExprNode.BVar(0))),
                                  1 =>
                                    match u32_less_than(list_length(ty_args), 1) {
                                      1 => (0, store(KExprNode.BVar(0))),
                                      0 =>
                                        let width = list_lookup(ty_args, 0);
                                        let lhs = list_lookup(lt_args, 2);
                                        let rhs = list_lookup(lt_args, 3);
                                        let inner_spine = store(ListNode.Cons(width,
                                          store(ListNode.Cons(lhs,
                                            store(ListNode.Cons(rhs, store(ListNode.Nil)))))));
                                        try_reduce_bit_vec_ult(inner_spine, types, top, addrs),
                                    },
                                },
                              _ => (0, store(KExprNode.BVar(0))),
                            },
                        },
                    },
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:2637-2755 fn try_reduce_native.
  -- Handles compiler-emitted Nat/Bool reductions:
  --   • `Lean.reduceBool c` / `Lean.reduceNat c`: unfold + accept ctor/lit.
  --   • `System.Platform.numBits` (no args) → `Lit(Nat 64)`.
  --   • `Subtype.val (System.Platform.getNumBits ())` → `Lit(Nat 64)`.
  --   • `SizeOf.sizeOf Unit/PUnit ...` → `Lit(Nat 1)`.
  --   • `PUnit.SizeOf.1 ...` → `Lit(Nat 1)`.
  fn try_reduce_native(head_addr: [G; 32], spine: List‹KExpr›,
                       types: List‹KExpr›,
                       top: List‹&KConstantInfo›,
                       addrs: List‹[G; 32]›) -> (G, KExpr) {
    -- Nullary System.Platform.numBits
    match address_eq(head_addr, system_platform_num_bits_addr()) {
      1 => (1, mk_nat_literal_64()),
      0 =>
        -- subtype_val (... getNumBits ()): 3 args, args[2] is `getNumBits ()`.
        match address_eq(head_addr, subtype_val_addr()) {
          1 => try_reduce_subtype_val(spine, addrs),
          0 =>
            -- size_of_size_of Unit/PUnit ...: 3 args, first is type.
            match address_eq(head_addr, size_of_size_of_addr()) {
              1 => try_reduce_size_of_unit(spine, addrs),
              0 =>
                -- PUnit's stored sizeOf instance.
                match address_eq(head_addr, punit_size_of_1_addr()) {
                  1 => (1, mk_nat_one()),
                  0 =>
                    let is_rb = address_eq(head_addr, reduce_bool_addr());
                    let is_rn = address_eq(head_addr, reduce_nat_addr());
                    match is_rb + is_rn {
                      0 => (0, store(KExprNode.BVar(0))),
                      _ =>
                        match u32_less_than(list_length(spine), 1) {
                          1 => (0, store(KExprNode.BVar(0))),
                          0 =>
                            let arg = list_lookup(spine, 0);
                            let result = whnf(arg, types, top, addrs);
                            match is_rb {
                              1 => check_native_bool(result, addrs),
                              0 => check_native_nat(result),
                            },
                        },
                    },
                },
            },
        },
    }
  }

  fn mk_nat_literal_64() -> KExpr {
    let limbs = store(ListNode.Cons([64, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil)));
    store(KExprNode.Lit(KLiteral.Nat(limbs)))
  }

  fn mk_nat_one() -> KExpr {
    let limbs = store(ListNode.Cons([1, 0, 0, 0, 0, 0, 0, 0], store(ListNode.Nil)));
    store(KExprNode.Lit(KLiteral.Nat(limbs)))
  }

  -- Subtype.val A P (System.Platform.getNumBits ()) → 64.
  -- Spine: [A, P, val_arg]. If val_arg's spine head = getNumBits, return 64.
  fn try_reduce_subtype_val(spine: List‹KExpr›,
                            addrs: List‹[G; 32]›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 3) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let val_arg = list_lookup(spine, 2);
        match collect_spine_simple(val_arg) {
          (head, _) =>
            match load(head) {
              KExprNode.Const(idx, _) =>
                let head_addr = list_lookup(addrs, idx);
                match address_eq(head_addr, system_platform_get_num_bits_addr()) {
                  1 => (1, mk_nat_literal_64()),
                  0 => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  -- size_of_size_of Unit/PUnit ... → 1. First arg is the type.
  fn try_reduce_size_of_unit(spine: List‹KExpr›,
                             addrs: List‹[G; 32]›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 1) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let ty_arg = list_lookup(spine, 0);
        match collect_spine_simple(ty_arg) {
          (head, _) =>
            match load(head) {
              KExprNode.Const(idx, _) =>
                let head_addr = list_lookup(addrs, idx);
                let is_unit = address_eq(head_addr, unit_addr());
                let is_punit = address_eq(head_addr, punit_addr());
                match is_unit + is_punit {
                  0 => (0, store(KExprNode.BVar(0))),
                  _ => (1, mk_nat_one()),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  -- For reduce_bool: result must be Const(bool_true|bool_false).
  fn check_native_bool(e: KExpr, addrs: List‹[G; 32]›) -> (G, KExpr) {
    match load(e) {
      KExprNode.Const(idx, _) =>
        let head_addr = list_lookup(addrs, idx);
        let is_t = address_eq(head_addr, bool_true_addr());
        let is_f = address_eq(head_addr, bool_false_addr());
        match is_t + is_f {
          0 => (0, store(KExprNode.BVar(0))),
          _ => (1, e),
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- For reduce_nat: result must be Lit(Nat).
  fn check_native_nat(e: KExpr) -> (G, KExpr) {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(_) => (1, e),
          _ => (0, store(KExprNode.BVar(0))),
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:2173-2329 fn try_reduce_decidable.
  -- Handles `Nat.decLe`/`decEq`/`decLt`. Constructs `Decidable.isTrue/isFalse`
  -- proof terms with `Eq.refl Bool Bool.true/false` witnesses.
  --
  -- For decLt: rewrites to `decLe (n+1) m` and recurses through whnf.
  -- For decLe / decEq: extracts n, m as Nat lits; computes verdict; builds
  -- proof term using compiler-emitted helper fns.
  --
  -- Prop extraction: invokes `k_infer` on the call expression's spine head
  -- + spine to recover the `Decidable prop` type. `prop` is the type's
  -- first arg. Requires `types` to be the local context so k_infer is
  -- valid under binders.
  fn try_reduce_decidable(head_addr: [G; 32], head_idx: G,
                          head_lvls: List‹&KLevel›,
                          spine: List‹KExpr›,
                          types: List‹KExpr›,
                          top: List‹&KConstantInfo›,
                          addrs: List‹[G; 32]›) -> (G, KExpr) {
    let is_dec_le = address_eq(head_addr, nat_dec_le_addr());
    let is_dec_eq = address_eq(head_addr, nat_dec_eq_addr());
    let is_dec_lt = address_eq(head_addr, nat_dec_lt_addr());
    let is_int_dec_le = address_eq(head_addr, int_dec_le_addr());
    let is_int_dec_eq = address_eq(head_addr, int_dec_eq_addr());
    let is_int_dec_lt = address_eq(head_addr, int_dec_lt_addr());
    match is_int_dec_le + is_int_dec_eq + is_int_dec_lt {
      1 => try_normalize_int_decidable(head_idx, head_lvls, spine, types, top, addrs),
      _ =>
        match is_dec_le + is_dec_eq + is_dec_lt {
          0 => (0, store(KExprNode.BVar(0))),
          _ =>
            match u32_less_than(list_length(spine), 2) {
              1 => (0, store(KExprNode.BVar(0))),
              0 => decidable_dispatch(is_dec_le, is_dec_eq, is_dec_lt, head_idx, head_lvls,
                                       spine, types, top, addrs),
            },
        },
    }
  }

  -- Try-match `App(Const(int_of_nat | int_neg_succ), Lit(Nat _))`. Returns
  -- `(found, sign, limbs)` where sign=0 for nonneg (Int.ofNat), 1 for
  -- Int.negSucc. Mirror: src/ix/kernel/whnf.rs::extract_int_lit.
  fn try_extract_int(e: KExpr, addrs: List‹[G; 32]›) -> (G, G, KLimbs) {
    match load(e) {
      KExprNode.App(f, a) =>
        match load(f) {
          KExprNode.Const(idx, _) =>
            let head_addr = list_lookup(addrs, idx);
            let is_ofnat = address_eq(head_addr, int_of_nat_addr());
            let is_negsucc = address_eq(head_addr, int_neg_succ_addr());
            match is_ofnat + is_negsucc {
              0 => (0, 0, store(ListNode.Nil)),
              _ =>
                match load(a) {
                  KExprNode.Lit(lit) =>
                    match lit {
                      KLiteral.Nat(limbs) => (1, is_negsucc, limbs),
                      _ => (0, 0, store(ListNode.Nil)),
                    },
                  _ => (0, 0, store(ListNode.Nil)),
                },
            },
          _ => (0, 0, store(ListNode.Nil)),
        },
      _ => (0, 0, store(ListNode.Nil)),
    }
  }

  -- Build canonical `App(Const(int_of_nat | int_neg_succ), Lit(Nat n))`.
  fn intern_int_lit(sign: G, limbs: KLimbs, addrs: List‹[G; 32]›) -> (G, KExpr) {
    let target = match sign {
      0 => int_of_nat_addr(),
      _ => int_neg_succ_addr(),
    };
    match find_addr_idx_safe(target, addrs, 0) {
      (1, idx) =>
        let head = store(KExprNode.Const(idx, store(ListNode.Nil)));
        (1, store(KExprNode.App(head, mk_nat_lit(limbs)))),
      (0, _) => (0, store(KExprNode.BVar(0))),
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:2331-2370 fn try_normalize_int_decidable.
  -- For Int.decEq/decLe/decLt: whnf both args, extract Int literals,
  -- rebuild canonical form `App(Const(int_dec_*), int_of_nat n, int_neg_succ k, ...)`.
  -- Bails if both args already canonical (no normalization needed).
  fn try_normalize_int_decidable(head_idx: G, head_lvls: List‹&KLevel›,
                                  spine: List‹KExpr›, types: List‹KExpr›,
                                  top: List‹&KConstantInfo›,
                                  addrs: List‹[G; 32]›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let a0 = list_lookup(spine, 0);
        let a1 = list_lookup(spine, 1);
        match try_extract_int(a0, addrs) {
          (1, _, _) =>
            match try_extract_int(a1, addrs) {
              -- Both already canonical Int lits — no normalization needed.
              (1, _, _) => (0, store(KExprNode.BVar(0))),
              _ => normalize_int_dec_rebuild(head_idx, head_lvls, spine, a0, a1, types, top, addrs),
            },
          _ => normalize_int_dec_rebuild(head_idx, head_lvls, spine, a0, a1, types, top, addrs),
        },
    }
  }

  fn normalize_int_dec_rebuild(head_idx: G, head_lvls: List‹&KLevel›,
                                spine: List‹KExpr›, a0: KExpr, a1: KExpr,
                                types: List‹KExpr›, top: List‹&KConstantInfo›,
                                addrs: List‹[G; 32]›) -> (G, KExpr) {
    let wa = whnf(a0, types, top, addrs);
    let wb = whnf(a1, types, top, addrs);
    match try_extract_int(wa, addrs) {
      (1, sa, na) =>
        match try_extract_int(wb, addrs) {
          (1, sb, nb) =>
            match intern_int_lit(sa, na, addrs) {
              (1, a_e) =>
                match intern_int_lit(sb, nb, addrs) {
                  (1, b_e) =>
                    let head = store(KExprNode.Const(head_idx, head_lvls));
                    let r1 = store(KExprNode.App(head, a_e));
                    let r2 = store(KExprNode.App(r1, b_e));
                    let post = list_drop(spine, 2);
                    (1, apply_spine(r2, post)),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  fn decidable_dispatch(is_dec_le: G, is_dec_eq: G, is_dec_lt: G,
                         head_idx: G, head_lvls: List‹&KLevel›,
                         spine: List‹KExpr›, types: List‹KExpr›,
                         top: List‹&KConstantInfo›,
                         addrs: List‹[G; 32]›) -> (G, KExpr) {
    -- decLt n m → decLe (n+1) m: rewrite spine.
    match is_dec_lt {
      1 =>
        let n_e = list_lookup(spine, 0);
        let m_e = list_lookup(spine, 1);
        let n_w = whnf(n_e, types, top, addrs);
        let np = try_extract_nat(n_w, addrs);
        match np {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, n_klimbs) =>
            let succ_n = klimbs_succ(n_klimbs);
            let succ_n_lit = mk_nat_lit(succ_n);
            let dec_le_const = store(KExprNode.Const(0, store(ListNode.Nil)));
            -- Find dec_le_idx via address.
            let pair = find_addr_idx_safe(nat_dec_le_addr(), addrs, 0);
            match pair {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, dec_le_idx) =>
                let head = store(KExprNode.Const(dec_le_idx, store(ListNode.Nil)));
                let app1 = store(KExprNode.App(head, succ_n_lit));
                let app2 = store(KExprNode.App(app1, m_e));
                let post = list_drop(spine, 2);
                let result = apply_spine(app2, post);
                (1, result),
            },
        },
      0 =>
        decidable_dispatch_le_eq(is_dec_le, is_dec_eq, head_idx, head_lvls,
                                 spine, types, top, addrs),
    }
  }

  fn decidable_dispatch_le_eq(is_dec_le: G, is_dec_eq: G,
                              head_idx: G, head_lvls: List‹&KLevel›,
                              spine: List‹KExpr›, types: List‹KExpr›,
                              top: List‹&KConstantInfo›,
                              addrs: List‹[G; 32]›) -> (G, KExpr) {
    let n_e = list_lookup(spine, 0);
    let m_e = list_lookup(spine, 1);
    let n_w = whnf(n_e, types, top, addrs);
    let m_w = whnf(m_e, types, top, addrs);
    let np = try_extract_nat(n_w, addrs);
    let mp = try_extract_nat(m_w, addrs);
    match np {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, n_kl) =>
        match mp {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, m_kl) =>
            let verdict = match is_dec_le {
              1 => klimbs_le(n_kl, m_kl),
              0 => klimbs_eq(n_kl, m_kl),
            };
            decidable_build_proof(is_dec_le, is_dec_eq, verdict, n_e, m_e,
                                  head_idx, head_lvls, spine, types, top, addrs),
        },
    }
  }

  -- Build Decidable.isTrue/isFalse proof term. Prop slot recovered via
  -- k_infer over the original call expression in `decidable_finish`.
  fn decidable_build_proof(is_dec_le: G, is_dec_eq: G, verdict: G,
                           n_e: KExpr, m_e: KExpr,
                           head_idx: G, head_lvls: List‹&KLevel›,
                           spine: List‹KExpr›,
                           types: List‹KExpr›,
                           top: List‹&KConstantInfo›,
                           addrs: List‹[G; 32]›) -> (G, KExpr) {
    -- Build `Eq.refl.{1} Bool Bool.true_or_false`.
    let eq_refl_pair = find_addr_idx_safe(eq_refl_addr(), addrs, 0);
    match eq_refl_pair {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, eq_refl_idx) =>
        let bool_pair = find_addr_idx_safe(bool_type_addr(), addrs, 0);
        match bool_pair {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, bool_idx) =>
            let bool_lit_pair = match verdict {
              1 => find_addr_idx_safe(bool_true_addr(), addrs, 0),
              0 => find_addr_idx_safe(bool_false_addr(), addrs, 0),
            };
            match bool_lit_pair {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, bool_lit_idx) =>
                let one_lvl = store(KLevel.Succ(store(KLevel.Zero)));
                let lvls = store(ListNode.Cons(one_lvl, store(ListNode.Nil)));
                let eq_refl_const = store(KExprNode.Const(eq_refl_idx, lvls));
                let bool_const = store(KExprNode.Const(bool_idx, store(ListNode.Nil)));
                let bool_lit_const = store(KExprNode.Const(bool_lit_idx, store(ListNode.Nil)));
                let r1 = store(KExprNode.App(eq_refl_const, bool_const));
                let refl_proof = store(KExprNode.App(r1, bool_lit_const));
                -- proof_fn: nat_le_of_ble_eq_true / nat_eq_of_beq_eq_true /
                -- nat_ne_of_beq_eq_false based on (is_dec_le, verdict).
                let proof_fn_addr = match is_dec_le {
                  1 =>
                    match verdict {
                      1 => nat_le_of_ble_eq_true_addr(),
                      0 => nat_not_le_of_not_ble_eq_true_addr(),
                    },
                  0 =>
                    match verdict {
                      1 => nat_eq_of_beq_eq_true_addr(),
                      0 => nat_ne_of_beq_eq_false_addr(),
                    },
                };
                let proof_fn_pair = find_addr_idx_safe(proof_fn_addr, addrs, 0);
                match proof_fn_pair {
                  (0, _) => (0, store(KExprNode.BVar(0))),
                  (1, proof_fn_idx) =>
                    -- Bail decLe-false: needs Bool.noConfusion proof not yet
                    -- exposed. Mirror Rust whnf.rs:2317-2322.
                    let bail = is_dec_le * (1 - verdict);
                    match bail {
                      1 => (0, store(KExprNode.BVar(0))),
                      0 =>
                        let proof_const = store(KExprNode.Const(proof_fn_idx, store(ListNode.Nil)));
                        let p1 = store(KExprNode.App(proof_const, n_e));
                        let p2 = store(KExprNode.App(p1, m_e));
                        let proof = store(KExprNode.App(p2, refl_proof));
                        decidable_finish(verdict, proof, head_idx, head_lvls,
                                          spine, types, top, addrs),
                    },
                },
            },
        },
    }
  }

  fn decidable_finish(verdict: G, proof: KExpr, head_idx: G,
                       head_lvls: List‹&KLevel›, spine: List‹KExpr›,
                       types: List‹KExpr›, top: List‹&KConstantInfo›,
                       addrs: List‹[G; 32]›) -> (G, KExpr) {
    let dec_addr = match verdict {
      1 => decidable_is_true_addr(),
      0 => decidable_is_false_addr(),
    };
    let dec_pair = find_addr_idx_safe(dec_addr, addrs, 0);
    match dec_pair {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, dec_idx) =>
        -- Reconstruct head Const + first 2 spine args, k_infer to get
        -- `Decidable prop`, extract prop. Mirrors Rust producing the
        -- elaborator-shaped `Decidable.isTrue (n ≤ m) ...` form.
        let head_const = store(KExprNode.Const(head_idx, head_lvls));
        let two_args = list_take(spine, 2);
        let call_expr = apply_spine(head_const, two_args);
        let call_ty = k_infer(call_expr, types, top, addrs);
        let call_ty_w = whnf(call_ty, types, top, addrs);
        match collect_spine(call_ty_w) {
          (_, dec_args) =>
            -- Guard against malformed inferred type. Rust returns
            -- `Ok(None)` when the spine is empty; Aiur bails to (0, _)
            -- so caller falls through to delta unfolding.
            match u32_less_than(list_length(dec_args), 1) {
              1 => (0, store(KExprNode.BVar(0))),
              0 =>
                let prop = list_lookup(dec_args, 0);
                let dec_const = store(KExprNode.Const(dec_idx, store(ListNode.Nil)));
                let r1 = store(KExprNode.App(dec_const, prop));
                let r2 = store(KExprNode.App(r1, proof));
                let post = list_drop(spine, 2);
                (1, apply_spine(r2, post)),
            },
        },
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:2755-2807 fn try_reduce_string +
  -- char_of_nat_expr.
  --
  -- Dispatches on `String.utf8ByteSize`, `String.back`, `String.legacy_back`,
  -- `String.toByteArray`. All require a single Lit(Str) arg.
  fn try_str_dispatch(head_addr: [G; 32], spine: List‹KExpr›,
                      addrs: List‹[G; 32]›) -> (G, KExpr) {
    let spine_len = list_length(spine);
    let lt1 = u32_less_than(spine_len, 1);
    match lt1 {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let a0 = list_lookup(spine, 0);
        match load(a0) {
          KExprNode.Lit(lit) =>
            match lit {
              KLiteral.Str(bs) =>
                match address_eq(head_addr, string_utf8_byte_size_addr()) {
                  1 =>
                    let len = list_length_u64(bs);
                    let limbs = store(ListNode.Cons(len, store(ListNode.Nil)));
                    (1, store(KExprNode.Lit(KLiteral.Nat(limbs)))),
                  0 =>
                    match address_eq(head_addr, string_to_byte_array_addr()) {
                      1 => try_str_to_byte_array(bs, addrs),
                      0 =>
                        let is_back = address_eq(head_addr, string_back_addr());
                        let is_legacy = address_eq(head_addr, string_legacy_back_addr());
                        match is_back + is_legacy {
                          0 => (0, store(KExprNode.BVar(0))),
                          _ => try_str_back(bs, addrs),
                        },
                    },
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- Empty Lit(Str) → Const(byte_array_empty). Non-empty: defer.
  fn try_str_to_byte_array(bs: ByteStream, addrs: List‹[G; 32]›) -> (G, KExpr) {
    match load(bs) {
      ListNode.Nil =>
        match find_addr_idx_safe(byte_array_empty_addr(), addrs, 0) {
          (1, idx) => (1, store(KExprNode.Const(idx, store(ListNode.Nil)))),
          (0, _) => (0, store(KExprNode.BVar(0))),
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- String.back/legacy_back over Lit(Str(s)) →
  -- App(Const(char_of_nat), Lit(Nat(last_codepoint))). Empty → 65 ('A').
  fn try_str_back(bs: ByteStream, addrs: List‹[G; 32]›) -> (G, KExpr) {
    match find_addr_idx_safe(char_of_nat_addr(), addrs, 0) {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, idx) =>
        let cp = utf8_last_codepoint(bs);
        let cp_limbs = klimbs_from_g(cp);
        let cp_lit = store(KExprNode.Lit(KLiteral.Nat(cp_limbs)));
        let con = store(KExprNode.Const(idx, store(ListNode.Nil)));
        (1, store(KExprNode.App(con, cp_lit))),
    }
  }

  -- Convert G value (≤ 2^32) into single-limb KLimbs via byte decomp.
  fn klimbs_from_g(x: G) -> KLimbs {
    match divmod_256(x, 0) {
      (b0, q1) =>
        match divmod_256(q1, 0) {
          (b1, q2) =>
            match divmod_256(q2, 0) {
              (b2, q3) =>
                match divmod_256(q3, 0) {
                  (b3, _q4) =>
                    store(ListNode.Cons([b0, b1, b2, b3, 0, 0, 0, 0],
                                        store(ListNode.Nil))),
                },
            },
        },
    }
  }

  -- Walk byte stream forward decoding UTF-8 codepoints; return last.
  -- Empty → 65 ('A') per Rust default.
  fn utf8_last_codepoint(bs: ByteStream) -> G {
    utf8_last_go(bs, 65)
  }

  fn utf8_last_go(bs: ByteStream, prev: G) -> G {
    match load(bs) {
      ListNode.Nil => prev,
      ListNode.Cons(b0, rest) =>
        match utf8_decode_one(b0, rest) {
          (cp, remaining) => utf8_last_go(remaining, cp),
        },
    }
  }

  -- Decode one UTF-8 codepoint. Honors length prefix bits:
  -- 0xxxxxxx → 1 byte; 110xxxxx 10xxxxxx → 2; 1110xxxx 10*2 → 3;
  -- 11110xxx 10*3 → 4 bytes.
  fn utf8_decode_one(b0: G, rest: ByteStream) -> (G, ByteStream) {
    match u8_less_than(b0, 128) {
      1 => (b0, rest),
      0 =>
        match u8_less_than(b0, 224) {
          1 =>
            match load(rest) {
              ListNode.Cons(b1, r1) =>
                let cp = (b0 - 192) * 64 + (b1 - 128);
                (cp, r1),
            },
          0 =>
            match u8_less_than(b0, 240) {
              1 =>
                match load(rest) {
                  ListNode.Cons(b1, r1) =>
                    match load(r1) {
                      ListNode.Cons(b2, r2) =>
                        let cp = (b0 - 224) * 4096 + (b1 - 128) * 64 + (b2 - 128);
                        (cp, r2),
                    },
                },
              0 =>
                match load(rest) {
                  ListNode.Cons(b1, r1) =>
                    match load(r1) {
                      ListNode.Cons(b2, r2) =>
                        match load(r2) {
                          ListNode.Cons(b3, r3) =>
                            let cp = (b0 - 240) * 262144 + (b1 - 128) * 4096
                                    + (b2 - 128) * 64 + (b3 - 128);
                            (cp, r3),
                        },
                    },
                },
            },
        },
    }
  }

  -- Mirror: src/ix/kernel/def_eq.rs:1025-1060 fn str_lit_to_constructor.
  -- Expand a Lit(Str(bs)) to ctor form
  -- `String.ofList (List.cons.{0} Char (Char.ofNat c) (... List.nil.{0} Char))`.
  -- Returns (1, expanded) when all required ctor addrs in `addrs`, else (0, _).
  fn str_lit_to_ctor(bs: ByteStream, addrs: List‹[G; 32]›) -> (G, KExpr) {
    match find_addr_idx_safe(list_nil_addr(), addrs, 0) {
      (0, _) => (0, store(KExprNode.BVar(0))),
      (1, nil_idx) =>
        match find_addr_idx_safe(list_cons_addr(), addrs, 0) {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, cons_idx) =>
            match find_addr_idx_safe(char_type_addr(), addrs, 0) {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, char_idx) =>
                match find_addr_idx_safe(char_of_nat_addr(), addrs, 0) {
                  (0, _) => (0, store(KExprNode.BVar(0))),
                  (1, con_idx) =>
                    match find_addr_idx_safe(string_of_list_addr(), addrs, 0) {
                      (0, _) => (0, store(KExprNode.BVar(0))),
                      (1, str_idx) =>
                        let zero_lvl = store(KLevel.Zero);
                        let ulvls = store(ListNode.Cons(zero_lvl, store(ListNode.Nil)));
                        let nil_const = store(KExprNode.Const(nil_idx, ulvls));
                        let cons_const = store(KExprNode.Const(cons_idx, ulvls));
                        let char_const = store(KExprNode.Const(char_idx, store(ListNode.Nil)));
                        let con_const = store(KExprNode.Const(con_idx, store(ListNode.Nil)));
                        let str_const = store(KExprNode.Const(str_idx, store(ListNode.Nil)));
                        let nil_app = store(KExprNode.App(nil_const, char_const));
                        let cons_partial = store(KExprNode.App(cons_const, char_const));
                        let list_expr = build_char_list(bs, nil_app, cons_partial, con_const);
                        (1, store(KExprNode.App(str_const, list_expr))),
                    },
                },
            },
        },
    }
  }

  fn build_char_list(bs: ByteStream, nil_app: KExpr,
                     cons_partial: KExpr, con_const: KExpr) -> KExpr {
    match load(bs) {
      ListNode.Nil => nil_app,
      ListNode.Cons(b0, rest) =>
        match utf8_decode_one(b0, rest) {
          (cp, remaining) =>
            let cp_limbs = klimbs_from_g(cp);
            let cp_lit = store(KExprNode.Lit(KLiteral.Nat(cp_limbs)));
            let char_val = store(KExprNode.App(con_const, cp_lit));
            let with_head = store(KExprNode.App(cons_partial, char_val));
            let tail = build_char_list(remaining, nil_app, cons_partial, con_const);
            store(KExprNode.App(with_head, tail)),
        },
    }
  }

  -- If `e` is `Lit(Str(bs))` and addrs has required ctors, expand to ctor form.
  -- Else return `e` unchanged. Used pre-iota.
  fn str_lit_to_ctor_or_self(e: KExpr, addrs: List‹[G; 32]›) -> KExpr {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Str(bs) =>
            match str_lit_to_ctor(bs, addrs) {
              (1, expanded) => expanded,
              (0, _) => e,
            },
          _ => e,
        },
      _ => e,
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:1531-1585 try_reduce_projection_definition
  -- + projection_definition_info.
  --
  -- Recognizes Defn-kind constants whose body is `λ x_1 ... x_n → Prj S i (BVar k)`
  -- and shortcuts the unfolding to a direct `Prj S i args[arity-1-k]`. Pure
  -- performance: standard delta+beta still produces same result.
  fn try_reduce_projection_definition(head_idx: G, spine: List‹KExpr›,
                                       top: List‹&KConstantInfo›) -> (G, KExpr) {
    match load(list_lookup(top, head_idx)) {
      KConstantInfo.Defn(_, _, value, _, _) =>
        match projection_definition_info(value, 0) {
          (1, arity, struct_idx, field, struct_arg_idx) =>
            match u32_less_than(list_length(spine), arity) {
              1 => (0, store(KExprNode.BVar(0))),
              0 =>
                let target_arg = list_lookup(spine, struct_arg_idx);
                let proj_expr = store(KExprNode.Proj(struct_idx, field, target_arg));
                let post = list_drop(spine, arity);
                (1, apply_spine(proj_expr, post)),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:1441-1500 try_reduce_fin_val_decidable_rec
  -- + project_decidable_fin_val_minor.
  --
  -- Pushes `Fin.val` projection inside `Decidable.rec` minors when the
  -- structure type is Fin and field 0. Allows iota to fire once major is
  -- a concrete `Decidable.isTrue/isFalse`.
  fn try_reduce_fin_val_decidable_rec(tidx: G, field: G, head: KExpr,
                                       args: List‹KExpr›,
                                       addrs: List‹[G; 32]›) -> (G, KExpr) {
    let tidx_addr = list_lookup(addrs, tidx);
    match address_eq(tidx_addr, fin_addr()) {
      0 => (0, store(KExprNode.BVar(0))),
      1 =>
        match field {
          0 =>
            match load(head) {
              KExprNode.Const(rec_idx, rec_us) =>
                let rec_addr_ = list_lookup(addrs, rec_idx);
                match address_eq(rec_addr_, decidable_rec_addr()) {
                  0 => (0, store(KExprNode.BVar(0))),
                  1 =>
                    match u32_less_than(list_length(args), 5) {
                      1 => (0, store(KExprNode.BVar(0))),
                      0 =>
                        let a0 = list_lookup(args, 0);
                        let a1 = list_lookup(args, 1);
                        let a2 = list_lookup(args, 2);
                        let a3 = list_lookup(args, 3);
                        let a4 = list_lookup(args, 4);
                        match load(a1) {
                          KExprNode.Lam(motive_dom, _) =>
                            -- Inline project_decidable_fin_val_minor twice.
                            match load(a2) {
                              KExprNode.Lam(fdom, fbody) =>
                                let fproj = store(KExprNode.Proj(tidx, field, fbody));
                                let false_minor = store(KExprNode.Lam(fdom, fproj));
                                match load(a3) {
                                  KExprNode.Lam(tdom, tbody) =>
                                    let tproj = store(KExprNode.Proj(tidx, field, tbody));
                                    let true_minor = store(KExprNode.Lam(tdom, tproj));
                                    match find_addr_idx_safe(nat_addr(), addrs, 0) {
                                      (1, nat_idx) =>
                                        let nat_ty = store(KExprNode.Const(nat_idx, store(ListNode.Nil)));
                                        let new_motive = store(KExprNode.Lam(motive_dom, nat_ty));
                                        let head_const = store(KExprNode.Const(rec_idx, rec_us));
                                        let r1 = store(KExprNode.App(head_const, a0));
                                        let r2 = store(KExprNode.App(r1, new_motive));
                                        let r3 = store(KExprNode.App(r2, false_minor));
                                        let r4 = store(KExprNode.App(r3, true_minor));
                                        let r5 = store(KExprNode.App(r4, a4));
                                        let post = list_drop(args, 5);
                                        (1, apply_spine(r5, post)),
                                      (0, _) => (0, store(KExprNode.BVar(0))),
                                    },
                                  _ => (0, store(KExprNode.BVar(0))),
                                },
                              _ => (0, store(KExprNode.BVar(0))),
                            },
                          _ => (0, store(KExprNode.BVar(0))),
                        },
                    },
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- Returns (found, arity, struct_idx, field, struct_arg_idx). Walks Lam
  -- bindings counting arity; expects body to be `Prj S i (BVar k)` with
  -- `k < arity`. struct_arg_idx = (arity - 1) - k.
  fn projection_definition_info(val: KExpr, arity: G) -> (G, G, G, G, G) {
    match load(val) {
      KExprNode.Lam(_, body) =>
        projection_definition_info(body, arity + 1),
      KExprNode.Proj(struct_idx, field, projected) =>
        match load(projected) {
          KExprNode.BVar(i) =>
            match u32_less_than(i, arity) {
              1 => (1, arity, struct_idx, field, (arity - 1) - i),
              _ => (0, 0, 0, 0, 0),
            },
          _ => (0, 0, 0, 0, 0),
        },
      _ => (0, 0, 0, 0, 0),
    }
  }
⟧

end IxVM

end
