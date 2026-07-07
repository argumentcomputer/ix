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
  fn quot_type_addr() -> Addr {
    store([0xabu8, 0x68u8, 0x2cu8, 0x17u8, 0x78u8, 0xa1u8, 0x7bu8, 0xbeu8,
     0xaeu8, 0x40u8, 0x32u8, 0x97u8, 0x4du8, 0xf3u8, 0x64u8, 0x47u8,
     0xceu8, 0x8bu8, 0xfcu8, 0xabu8, 0x67u8, 0x64u8, 0xa3u8, 0x6du8,
     0x37u8, 0x85u8, 0x66u8, 0xe3u8, 0xadu8, 0x63u8, 0xcau8, 0xb8u8])
  }

  fn quot_ctor_addr() -> Addr {
    store([0x88u8, 0x26u8, 0x66u8, 0x77u8, 0xfeu8, 0xe7u8, 0x74u8, 0xd1u8,
     0x09u8, 0x86u8, 0x7eu8, 0x4bu8, 0x22u8, 0x40u8, 0x28u8, 0x1au8,
     0xa2u8, 0xeeu8, 0x12u8, 0xd9u8, 0x79u8, 0x20u8, 0xc1u8, 0x17u8,
     0x1cu8, 0xf5u8, 0xc1u8, 0xf6u8, 0xc8u8, 0x7du8, 0xecu8, 0xf6u8])
  }

  fn quot_lift_addr() -> Addr {
    store([0x8du8, 0xc4u8, 0xa9u8, 0x75u8, 0x27u8, 0x81u8, 0x2fu8, 0x8bu8,
     0x78u8, 0x17u8, 0xb7u8, 0x7cu8, 0xd0u8, 0x79u8, 0xacu8, 0xe6u8,
     0x14u8, 0x50u8, 0xaau8, 0x01u8, 0x85u8, 0xacu8, 0x58u8, 0x85u8,
     0x66u8, 0x1eu8, 0xc2u8, 0xacu8, 0xbau8, 0x8bu8, 0x7bu8, 0xd0u8])
  }

  fn quot_ind_addr() -> Addr {
    store([0x12u8, 0x49u8, 0x84u8, 0xbcu8, 0xb9u8, 0x52u8, 0x08u8, 0xa0u8,
     0xf3u8, 0x0bu8, 0xb6u8, 0x9du8, 0x67u8, 0x36u8, 0xd3u8, 0xd5u8,
     0x94u8, 0x04u8, 0xe1u8, 0x15u8, 0xe2u8, 0x20u8, 0x20u8, 0x43u8,
     0xfdu8, 0xa3u8, 0xd3u8, 0x4eu8, 0x01u8, 0xb0u8, 0xadu8, 0x16u8])
  }

  fn bit_vec_addr() -> Addr {
    store([0x69u8, 0x8du8, 0xd5u8, 0x93u8, 0xabu8, 0xfbu8, 0x63u8, 0xdbu8,
     0x36u8, 0x2au8, 0xaeu8, 0xf5u8, 0x7eu8, 0x70u8, 0xa7u8, 0x93u8,
     0x04u8, 0x4fu8, 0xb6u8, 0x57u8, 0x25u8, 0x72u8, 0x91u8, 0xeeu8,
     0x2cu8, 0x3eu8, 0x99u8, 0x7cu8, 0xaau8, 0x42u8, 0x3eu8, 0xaeu8])
  }

  fn bit_vec_to_nat_addr() -> Addr {
    store([0x77u8, 0xa0u8, 0x25u8, 0xc1u8, 0x9fu8, 0x8bu8, 0xe1u8, 0x31u8,
     0xfbu8, 0x9du8, 0x5bu8, 0x0bu8, 0xecu8, 0x49u8, 0x48u8, 0x17u8,
     0xa2u8, 0x65u8, 0x38u8, 0xb9u8, 0xa5u8, 0x50u8, 0xabu8, 0xbbu8,
     0xceu8, 0xc8u8, 0x09u8, 0x9fu8, 0xaeu8, 0x9du8, 0xe4u8, 0xe4u8])
  }

  fn bit_vec_of_nat_addr() -> Addr {
    store([0x90u8, 0xcau8, 0x81u8, 0x30u8, 0x73u8, 0x5cu8, 0x8du8, 0x9au8,
     0x34u8, 0x00u8, 0x5au8, 0x89u8, 0x43u8, 0xb5u8, 0x9fu8, 0xe1u8,
     0xdfu8, 0x18u8, 0x2eu8, 0x08u8, 0xa9u8, 0xf2u8, 0xbfu8, 0xc7u8,
     0xdcu8, 0x83u8, 0x23u8, 0x22u8, 0x96u8, 0x59u8, 0xa5u8, 0x74u8])
  }

  fn bit_vec_ult_addr() -> Addr {
    store([0x9fu8, 0xd8u8, 0xe7u8, 0x45u8, 0x9au8, 0x1du8, 0x2du8, 0xeeu8,
     0xf0u8, 0x0au8, 0x49u8, 0x92u8, 0xa5u8, 0x04u8, 0x19u8, 0xbau8,
     0xc6u8, 0x6cu8, 0x03u8, 0x08u8, 0x2bu8, 0x58u8, 0xadu8, 0xe0u8,
     0x74u8, 0x22u8, 0x89u8, 0x6fu8, 0x13u8, 0x03u8, 0x3du8, 0x74u8])
  }

  fn decidable_decide_addr() -> Addr {
    store([0xc5u8, 0xf7u8, 0xb1u8, 0x96u8, 0x63u8, 0xe4u8, 0x49u8, 0x9eu8,
     0x70u8, 0xe1u8, 0xb2u8, 0x64u8, 0x51u8, 0x62u8, 0xc5u8, 0xbeu8,
     0x15u8, 0xfau8, 0x86u8, 0x0fu8, 0x4fu8, 0x81u8, 0x57u8, 0xe3u8,
     0x31u8, 0xaeu8, 0x54u8, 0x6cu8, 0x6fu8, 0x73u8, 0x37u8, 0x23u8])
  }

  fn lt_lt_addr() -> Addr {
    store([0xcau8, 0xcau8, 0xeau8, 0x97u8, 0xf4u8, 0xcdu8, 0xbau8, 0x0au8,
     0x4au8, 0x0au8, 0xf7u8, 0x10u8, 0x05u8, 0xd0u8, 0x51u8, 0x7du8,
     0x18u8, 0x18u8, 0xabu8, 0x26u8, 0x23u8, 0xbdu8, 0x2eu8, 0xa7u8,
     0xfau8, 0x8cu8, 0x63u8, 0x7au8, 0x0eu8, 0x3du8, 0x33u8, 0x12u8])
  }

  fn bool_type_addr() -> Addr {
    store([0xe6u8, 0xebu8, 0xa3u8, 0xc8u8, 0xb4u8, 0xd1u8, 0x9fu8, 0x6au8,
     0x10u8, 0x76u8, 0xb3u8, 0x9fu8, 0xa8u8, 0x9au8, 0xecu8, 0x61u8,
     0xdcu8, 0xcbu8, 0xb9u8, 0x60u8, 0xf8u8, 0x3du8, 0x9au8, 0x62u8,
     0xe6u8, 0xacu8, 0xf3u8, 0x5au8, 0x69u8, 0xc9u8, 0xa0u8, 0xa4u8])
  }

  fn eq_addr() -> Addr {
    store([0x03u8, 0x6bu8, 0x63u8, 0xd5u8, 0xccu8, 0x09u8, 0x61u8, 0xe9u8,
     0x20u8, 0xdeu8, 0xe5u8, 0x0eu8, 0x73u8, 0x64u8, 0xecu8, 0x0du8,
     0xd3u8, 0xf9u8, 0xc3u8, 0x8au8, 0x9cu8, 0xacu8, 0xe4u8, 0x0eu8,
     0x51u8, 0x3bu8, 0x38u8, 0x35u8, 0xdeu8, 0xc8u8, 0xe0u8, 0xc9u8])
  }

  fn eq_refl_addr() -> Addr {
    store([0x6cu8, 0x9bu8, 0xd6u8, 0x0eu8, 0x1eu8, 0xaeu8, 0x93u8, 0x8eu8,
     0x56u8, 0x26u8, 0xcau8, 0x23u8, 0x7du8, 0xbcu8, 0xa7u8, 0xfdu8,
     0x95u8, 0x0fu8, 0x2eu8, 0x99u8, 0xe2u8, 0x34u8, 0xa9u8, 0x9cu8,
     0x23u8, 0xcfu8, 0xdcu8, 0x29u8, 0x4cu8, 0xa7u8, 0xadu8, 0xceu8])
  }

  fn nat_dec_le_addr() -> Addr {
    store([0xecu8, 0x1fu8, 0x60u8, 0xc1u8, 0xa2u8, 0x8du8, 0x48u8, 0xbcu8,
     0x98u8, 0xfeu8, 0x3eu8, 0xf7u8, 0x2du8, 0x25u8, 0x51u8, 0x32u8,
     0x73u8, 0x5au8, 0x50u8, 0x3cu8, 0xc3u8, 0x6eu8, 0x3fu8, 0xf0u8,
     0xf2u8, 0x2eu8, 0x3du8, 0x48u8, 0x6eu8, 0x26u8, 0x6eu8, 0xbeu8])
  }

  fn nat_dec_eq_addr() -> Addr {
    store([0xb4u8, 0xb2u8, 0x6cu8, 0x2eu8, 0x29u8, 0x93u8, 0x1cu8, 0x06u8,
     0xe8u8, 0x85u8, 0x91u8, 0x46u8, 0x13u8, 0xfau8, 0xffu8, 0x58u8,
     0x56u8, 0x13u8, 0x8eu8, 0x5cu8, 0xb0u8, 0x96u8, 0x20u8, 0xddu8,
     0xb6u8, 0x92u8, 0x1au8, 0x34u8, 0x2du8, 0xedu8, 0x89u8, 0x57u8])
  }

  fn nat_dec_lt_addr() -> Addr {
    store([0xc0u8, 0x13u8, 0xc1u8, 0x53u8, 0xebu8, 0xf0u8, 0x20u8, 0x28u8,
     0xaeu8, 0xd2u8, 0x64u8, 0x33u8, 0x3cu8, 0x1eu8, 0x4cu8, 0x85u8,
     0x01u8, 0x7du8, 0x0bu8, 0x87u8, 0x02u8, 0x5du8, 0x75u8, 0x96u8,
     0xa9u8, 0x69u8, 0x71u8, 0xbbu8, 0x2bu8, 0x67u8, 0x92u8, 0x1du8])
  }

  fn int_dec_eq_addr() -> Addr {
    store([0x83u8, 0xfdu8, 0xe3u8, 0x8fu8, 0xaau8, 0x11u8, 0x64u8, 0x64u8,
     0x8eu8, 0x42u8, 0x27u8, 0x97u8, 0x5au8, 0xbfu8, 0x2eu8, 0x8cu8,
     0x26u8, 0x0du8, 0x7du8, 0x4eu8, 0xf1u8, 0xc9u8, 0x26u8, 0x76u8,
     0x21u8, 0x4fu8, 0xfeu8, 0x58u8, 0x26u8, 0xc2u8, 0x07u8, 0x5du8])
  }

  fn int_dec_le_addr() -> Addr {
    store([0x38u8, 0xd6u8, 0x0fu8, 0xfau8, 0x07u8, 0xb5u8, 0x06u8, 0x78u8,
     0xd0u8, 0xc3u8, 0xbfu8, 0x0cu8, 0x06u8, 0xf8u8, 0x6cu8, 0xd7u8,
     0x96u8, 0x7bu8, 0x35u8, 0xe8u8, 0x7au8, 0xb0u8, 0x71u8, 0xbcu8,
     0x55u8, 0x89u8, 0x9fu8, 0xcbu8, 0xaeu8, 0xd4u8, 0x74u8, 0x4fu8])
  }

  fn int_dec_lt_addr() -> Addr {
    store([0x55u8, 0x68u8, 0xe7u8, 0x99u8, 0x19u8, 0x8du8, 0xadu8, 0x9fu8,
     0xabu8, 0x0eu8, 0x78u8, 0x4bu8, 0x7au8, 0x4cu8, 0x58u8, 0x11u8,
     0x2bu8, 0xfcu8, 0x26u8, 0x88u8, 0xaeu8, 0xceu8, 0xbeu8, 0x3cu8,
     0x2cu8, 0x65u8, 0x63u8, 0x30u8, 0x42u8, 0x10u8, 0xf9u8, 0x56u8])
  }

  fn int_of_nat_addr() -> Addr {
    store([0x09u8, 0xbcu8, 0x25u8, 0x31u8, 0x47u8, 0xc3u8, 0x6cu8, 0xe2u8,
     0x2cu8, 0x8eu8, 0x0cu8, 0xcdu8, 0x43u8, 0xc7u8, 0x9bu8, 0x2cu8,
     0xdau8, 0xe2u8, 0x20u8, 0x6eu8, 0x0du8, 0xddu8, 0x16u8, 0x8fu8,
     0xcau8, 0x36u8, 0x09u8, 0xb2u8, 0xa5u8, 0x84u8, 0xd3u8, 0xdcu8])
  }

  fn int_neg_succ_addr() -> Addr {
    store([0x26u8, 0x7cu8, 0x0au8, 0x9cu8, 0x92u8, 0xe7u8, 0x56u8, 0x38u8,
     0xfcu8, 0x73u8, 0xedu8, 0x52u8, 0xa9u8, 0xf9u8, 0xc8u8, 0x16u8,
     0x47u8, 0xeeu8, 0xecu8, 0xeeu8, 0xffu8, 0x21u8, 0x44u8, 0xc1u8,
     0xf9u8, 0x7eu8, 0x65u8, 0xe2u8, 0xafu8, 0xf1u8, 0x49u8, 0xf1u8])
  }

  -- Address constants below registered in Rust primitive.rs but not wired
  -- into any Aiur dispatch path. Commented out per "no unused code".
  -- Restore + plug if a reduction/canonicalization tier needs them.
  /-
  fn int_addr() -> Addr {
    store([0xa5u8, 0xcau8, 0x2eu8, 0x1du8, 0x5cu8, 0xebu8, 0x8du8, 0x43u8,
     0x36u8, 0x7bu8, 0xc3u8, 0x4du8, 0x69u8, 0xa5u8, 0x0cu8, 0x16u8,
     0x50u8, 0xa2u8, 0x5du8, 0xc1u8, 0x07u8, 0x80u8, 0xaau8, 0x0cu8,
     0x37u8, 0x8cu8, 0xdfu8, 0xa9u8, 0x31u8, 0xffu8, 0x04u8, 0x24u8])
  }

  fn int_add_addr() -> Addr {
    store([0xcau8, 0x99u8, 0x08u8, 0x4cu8, 0x9du8, 0x2fu8, 0xcbu8, 0x4cu8,
     0x5du8, 0xd1u8, 0x39u8, 0xaeu8, 0xcau8, 0xf1u8, 0x59u8, 0xebu8,
     0xd0u8, 0x49u8, 0x92u8, 0xd7u8, 0x62u8, 0x30u8, 0xcbu8, 0x93u8,
     0x0fu8, 0x41u8, 0xb8u8, 0x60u8, 0x74u8, 0x68u8, 0x48u8, 0x17u8])
  }

  fn int_sub_addr() -> Addr {
    store([0xd3u8, 0x14u8, 0x12u8, 0x31u8, 0x80u8, 0x0eu8, 0x01u8, 0x2eu8,
     0x8du8, 0xb7u8, 0xc2u8, 0x40u8, 0xf7u8, 0x94u8, 0xe4u8, 0x92u8,
     0x9bu8, 0xfdu8, 0x15u8, 0x6bu8, 0x38u8, 0x45u8, 0xe2u8, 0x2fu8,
     0x1cu8, 0xf3u8, 0x1du8, 0x3fu8, 0xe3u8, 0x9au8, 0xecu8, 0xd9u8])
  }

  fn int_mul_addr() -> Addr {
    store([0x48u8, 0x20u8, 0x64u8, 0xe3u8, 0x56u8, 0x34u8, 0xa9u8, 0x5cu8,
     0x0fu8, 0x25u8, 0x2du8, 0xe7u8, 0x3du8, 0x68u8, 0x7cu8, 0x24u8,
     0x76u8, 0x4eu8, 0xa4u8, 0xfau8, 0x7du8, 0xfdu8, 0x14u8, 0xcfu8,
     0x7au8, 0xf8u8, 0xaau8, 0x75u8, 0x31u8, 0xf1u8, 0x7au8, 0x5cu8])
  }

  fn int_neg_addr() -> Addr {
    store([0xf6u8, 0x1cu8, 0x7du8, 0x3fu8, 0xceu8, 0x59u8, 0x54u8, 0x30u8,
     0xf8u8, 0x6fu8, 0x0cu8, 0xd5u8, 0x2du8, 0xa5u8, 0xbcu8, 0xb0u8,
     0x0bu8, 0xf9u8, 0x10u8, 0xedu8, 0xd8u8, 0x5eu8, 0x14u8, 0xdcu8,
     0x04u8, 0x02u8, 0x13u8, 0x0fu8, 0xccu8, 0xe3u8, 0x4eu8, 0xbdu8])
  }

  fn int_emod_addr() -> Addr {
    store([0x25u8, 0xc2u8, 0x67u8, 0xefu8, 0x44u8, 0xf1u8, 0x50u8, 0x07u8,
     0xf2u8, 0xd2u8, 0xe0u8, 0x81u8, 0x9bu8, 0xe6u8, 0xfbu8, 0x64u8,
     0x90u8, 0x2cu8, 0x33u8, 0xa7u8, 0xd2u8, 0x7au8, 0x6fu8, 0x2cu8,
     0x9du8, 0x61u8, 0x26u8, 0x38u8, 0x98u8, 0x95u8, 0x38u8, 0x04u8])
  }

  fn int_ediv_addr() -> Addr {
    store([0x49u8, 0xb3u8, 0x4du8, 0xcbu8, 0xffu8, 0x1eu8, 0x60u8, 0x53u8,
     0x28u8, 0x25u8, 0xffu8, 0x5au8, 0xf4u8, 0x77u8, 0xebu8, 0x5du8,
     0xe9u8, 0x81u8, 0x0eu8, 0xe3u8, 0x8eu8, 0x0fu8, 0x7au8, 0x32u8,
     0x01u8, 0x4du8, 0x54u8, 0xc8u8, 0xc1u8, 0xa3u8, 0xa3u8, 0xc5u8])
  }

  fn int_bmod_addr() -> Addr {
    store([0x6au8, 0x6au8, 0xdfu8, 0x0eu8, 0x95u8, 0xb3u8, 0xa4u8, 0xceu8,
     0x18u8, 0x33u8, 0x0eu8, 0xe2u8, 0x21u8, 0x05u8, 0x71u8, 0x2eu8,
     0x9au8, 0x64u8, 0x0eu8, 0xe4u8, 0x31u8, 0x1bu8, 0x5du8, 0xd1u8,
     0x02u8, 0x2au8, 0x8eu8, 0x0au8, 0x30u8, 0xcbu8, 0xa0u8, 0xafu8])
  }

  fn int_bdiv_addr() -> Addr {
    store([0xa4u8, 0xf1u8, 0xd7u8, 0xa3u8, 0xfeu8, 0x5bu8, 0x6bu8, 0x2eu8,
     0xf9u8, 0x52u8, 0x2fu8, 0xa5u8, 0x37u8, 0xf1u8, 0xe6u8, 0x22u8,
     0xfbu8, 0xb8u8, 0x17u8, 0x6fu8, 0x9fu8, 0xb3u8, 0x35u8, 0x8cu8,
     0x56u8, 0xceu8, 0xbeu8, 0x1au8, 0x37u8, 0x9bu8, 0x61u8, 0x84u8])
  }

  fn int_nat_abs_addr() -> Addr {
    store([0x83u8, 0xe3u8, 0xceu8, 0x8au8, 0x74u8, 0x75u8, 0x20u8, 0xccu8,
     0x24u8, 0x8au8, 0x0du8, 0xacu8, 0xf9u8, 0xbdu8, 0x13u8, 0x69u8,
     0x46u8, 0x7eu8, 0x49u8, 0x07u8, 0xe8u8, 0xaau8, 0xaau8, 0x43u8,
     0x3eu8, 0x1bu8, 0x43u8, 0x8eu8, 0x1cu8, 0xadu8, 0x7cu8, 0xa4u8])
  }

  fn int_pow_addr() -> Addr {
    store([0x73u8, 0xecu8, 0xccu8, 0xfeu8, 0xabu8, 0x8au8, 0x63u8, 0xa3u8,
     0xa0u8, 0xfau8, 0xf8u8, 0xd7u8, 0x1du8, 0xc7u8, 0x79u8, 0x95u8,
     0xbdu8, 0xa8u8, 0x34u8, 0x18u8, 0xb1u8, 0x3cu8, 0xd3u8, 0x99u8,
     0xb1u8, 0xfau8, 0x57u8, 0x1bu8, 0x50u8, 0xb4u8, 0x57u8, 0x5eu8])
  }

  fn bool_no_confusion_addr() -> Addr {
    store([0xcdu8, 0x98u8, 0x3au8, 0x82u8, 0x6cu8, 0x1eu8, 0x20u8, 0xc4u8,
     0x57u8, 0x0au8, 0xfcu8, 0xa2u8, 0x44u8, 0x91u8, 0x6cu8, 0x79u8,
     0xe2u8, 0x0eu8, 0x81u8, 0x6fu8, 0x61u8, 0x8fu8, 0xfdu8, 0xdau8,
     0x38u8, 0xbeu8, 0x8au8, 0x79u8, 0x07u8, 0x92u8, 0x74u8, 0xceu8])
  }

  fn char_mk_addr() -> Addr {
    store([0x97u8, 0xafu8, 0xa5u8, 0xadu8, 0x3du8, 0x86u8, 0x89u8, 0x5eu8,
     0x6du8, 0x15u8, 0x50u8, 0x19u8, 0xb6u8, 0x6cu8, 0x25u8, 0x6cu8,
     0xd1u8, 0xaau8, 0x86u8, 0x2bu8, 0x4eu8, 0x3cu8, 0x89u8, 0xd8u8,
     0xc6u8, 0x58u8, 0x0bu8, 0x61u8, 0x93u8, 0x9eu8, 0xe5u8, 0x41u8])
  }

  fn nat_bitwise_addr() -> Addr {
    store([0xd2u8, 0x07u8, 0x5eu8, 0x32u8, 0x3bu8, 0xedu8, 0x82u8, 0xf2u8,
     0x3eu8, 0xafu8, 0x75u8, 0xebu8, 0xc0u8, 0xfau8, 0xe4u8, 0xceu8,
     0xb8u8, 0x07u8, 0x94u8, 0x24u8, 0x0cu8, 0x04u8, 0x6bu8, 0x90u8,
     0xc5u8, 0x1au8, 0x94u8, 0xd0u8, 0x7fu8, 0x5eu8, 0x88u8, 0x5fu8])
  }

  fn nat_rec_addr() -> Addr {
    store([0xb9u8, 0x75u8, 0x15u8, 0x2fu8, 0x3fu8, 0x0cu8, 0xd9u8, 0x03u8,
     0x94u8, 0x33u8, 0xc6u8, 0x8fu8, 0x5au8, 0x5eu8, 0x54u8, 0x55u8,
     0xf5u8, 0xcbu8, 0x5du8, 0x91u8, 0x70u8, 0x78u8, 0xbau8, 0xedu8,
     0x01u8, 0x18u8, 0xb5u8, 0x90u8, 0x67u8, 0xa7u8, 0x4eu8, 0xa7u8])
  }

  fn nat_cases_on_addr() -> Addr {
    store([0x19u8, 0x17u8, 0x84u8, 0x1du8, 0x20u8, 0x85u8, 0x79u8, 0x6du8,
     0xd7u8, 0xbau8, 0x34u8, 0x6du8, 0xe9u8, 0x3au8, 0x57u8, 0x95u8,
     0x71u8, 0xb5u8, 0x64u8, 0x1cu8, 0x33u8, 0xfcu8, 0x40u8, 0x04u8,
     0x08u8, 0xecu8, 0x55u8, 0xb5u8, 0x77u8, 0x8au8, 0x9au8, 0x51u8])
  }

  fn list_addr() -> Addr {
    store([0x14u8, 0x4eu8, 0x20u8, 0x7au8, 0x88u8, 0xd1u8, 0xdfu8, 0xbdu8,
     0xe2u8, 0x2au8, 0x1bu8, 0x40u8, 0x68u8, 0x90u8, 0x33u8, 0xb3u8,
     0xa6u8, 0x5au8, 0x65u8, 0x2cu8, 0x8fu8, 0x75u8, 0x00u8, 0xb9u8,
     0xbeu8, 0x3cu8, 0xb7u8, 0xf6u8, 0x63u8, 0x66u8, 0xe0u8, 0xfeu8])
  }

  fn string_addr() -> Addr {
    store([0x7au8, 0xb2u8, 0xd5u8, 0x2au8, 0xc5u8, 0x2fu8, 0xd1u8, 0xf5u8,
     0x18u8, 0x09u8, 0xb7u8, 0x18u8, 0xe5u8, 0x3cu8, 0xd0u8, 0x58u8,
     0xacu8, 0x4bu8, 0x50u8, 0xd6u8, 0x51u8, 0x50u8, 0xe7u8, 0x8au8,
     0xe6u8, 0x19u8, 0x13u8, 0x9cu8, 0xcfu8, 0x13u8, 0xc8u8, 0xfdu8])
  }

  fn string_mk_addr() -> Addr {
    store([0x96u8, 0x71u8, 0xfdu8, 0x4fu8, 0xcfu8, 0xbcu8, 0x06u8, 0x1cu8,
     0x93u8, 0xc2u8, 0x82u8, 0x48u8, 0x64u8, 0xcfu8, 0x03u8, 0x12u8,
     0x4fu8, 0xfeu8, 0xe7u8, 0xccu8, 0x22u8, 0x30u8, 0x8du8, 0xe1u8,
     0x2au8, 0x7cu8, 0x82u8, 0x64u8, 0x73u8, 0xe4u8, 0x99u8, 0x06u8])
  }

  fn of_nat_of_nat_addr() -> Addr {
    store([0x5au8, 0x72u8, 0x92u8, 0xadu8, 0x75u8, 0x6eu8, 0xe1u8, 0xf2u8,
     0xdfu8, 0x4bu8, 0x92u8, 0xf1u8, 0x8au8, 0x27u8, 0x57u8, 0x4au8,
     0x47u8, 0xcbu8, 0xbcu8, 0xf7u8, 0x09u8, 0x4fu8, 0x98u8, 0xabu8,
     0x28u8, 0x65u8, 0xf9u8, 0x2eu8, 0xb2u8, 0x23u8, 0x42u8, 0xd7u8])
  }

  fn eager_reduce_addr() -> Addr {
    -- Aiur is permanently eager (no fvars, no fuel); this address is
    -- registered for parity with Rust but never matched.
    store([0x00u8; 32])
  }

  fn pprod_addr() -> Addr {
    store([0x81u8, 0xa4u8, 0x22u8, 0xa4u8, 0x2bu8, 0x2cu8, 0xb6u8, 0x56u8,
     0xb9u8, 0xa4u8, 0x7eu8, 0x61u8, 0xa4u8, 0x42u8, 0x2fu8, 0x89u8,
     0xcdu8, 0xb0u8, 0xa0u8, 0xc1u8, 0x66u8, 0x03u8, 0x5du8, 0x47u8,
     0xbfu8, 0x5eu8, 0x2cu8, 0x2au8, 0xf0u8, 0x21u8, 0x75u8, 0xfau8])
  }

  fn pprod_mk_addr() -> Addr {
    store([0xc9u8, 0xc5u8, 0x84u8, 0xdau8, 0x78u8, 0x2cu8, 0xdcu8, 0x45u8,
     0x33u8, 0x06u8, 0xbeu8, 0x9au8, 0x64u8, 0x32u8, 0x44u8, 0xfau8,
     0x0bu8, 0xcbu8, 0xfcu8, 0x3bu8, 0x5du8, 0xbcu8, 0xbau8, 0xfeu8,
     0x3fu8, 0x6bu8, 0x9du8, 0x65u8, 0xdfu8, 0x03u8, 0x1fu8, 0xedu8])
  }
  -/

  fn fin_addr() -> Addr {
    store([0x74u8, 0x59u8, 0x36u8, 0xfcu8, 0xb9u8, 0xd8u8, 0x6cu8, 0x44u8,
     0x57u8, 0xf0u8, 0xfdu8, 0x1eu8, 0x53u8, 0x7eu8, 0x67u8, 0x07u8,
     0x7fu8, 0x46u8, 0xf7u8, 0x84u8, 0x11u8, 0x08u8, 0x41u8, 0x9du8,
     0xacu8, 0x79u8, 0x84u8, 0x00u8, 0x8bu8, 0x56u8, 0x5bu8, 0x97u8])
  }

  fn decidable_rec_addr() -> Addr {
    store([0xabu8, 0x37u8, 0x76u8, 0x98u8, 0x57u8, 0x43u8, 0xafu8, 0x13u8,
     0xa9u8, 0xcbu8, 0x1au8, 0x7du8, 0x2fu8, 0x84u8, 0x96u8, 0x99u8,
     0x78u8, 0x92u8, 0xe1u8, 0x79u8, 0x83u8, 0xd1u8, 0x4bu8, 0xe5u8,
     0x27u8, 0x0au8, 0x71u8, 0x65u8, 0x70u8, 0xb3u8, 0x57u8, 0x19u8])
  }

  fn decidable_is_true_addr() -> Addr {
    store([0x0fu8, 0x9eu8, 0xe8u8, 0xd9u8, 0x03u8, 0x3du8, 0x8fu8, 0x7bu8,
     0x85u8, 0x2fu8, 0x5bu8, 0x71u8, 0x52u8, 0xfdu8, 0x12u8, 0x4fu8,
     0x7du8, 0x41u8, 0x19u8, 0x30u8, 0xc9u8, 0x92u8, 0xe0u8, 0xf4u8,
     0x57u8, 0xf8u8, 0x10u8, 0x4bu8, 0x60u8, 0xa9u8, 0x83u8, 0x81u8])
  }

  fn decidable_is_false_addr() -> Addr {
    store([0x04u8, 0x71u8, 0xe4u8, 0x71u8, 0x58u8, 0xb2u8, 0xaeu8, 0x18u8,
     0xd3u8, 0xc0u8, 0x8du8, 0xd5u8, 0xc7u8, 0x7au8, 0xaeu8, 0x23u8,
     0xe6u8, 0x2du8, 0x7bu8, 0xbcu8, 0x1eu8, 0x61u8, 0x11u8, 0x6bu8,
     0xc2u8, 0x81u8, 0x3bu8, 0x13u8, 0x06u8, 0xbcu8, 0x57u8, 0x95u8])
  }

  fn nat_le_of_ble_eq_true_addr() -> Addr {
    store([0x21u8, 0xe0u8, 0xe0u8, 0x78u8, 0x3bu8, 0x76u8, 0x17u8, 0xb0u8,
     0xccu8, 0x4eu8, 0xffu8, 0x4du8, 0x1fu8, 0xabu8, 0x7cu8, 0xffu8,
     0xefu8, 0xe0u8, 0x1cu8, 0xd4u8, 0x3du8, 0xa7u8, 0x7eu8, 0x2fu8,
     0x98u8, 0xd1u8, 0x50u8, 0x94u8, 0xa0u8, 0xd8u8, 0xf0u8, 0x86u8])
  }

  fn nat_not_le_of_not_ble_eq_true_addr() -> Addr {
    store([0x01u8, 0x83u8, 0x59u8, 0x5bu8, 0x83u8, 0x7bu8, 0x9bu8, 0x84u8,
     0xdau8, 0x5fu8, 0x00u8, 0x4bu8, 0x8au8, 0xc4u8, 0xa4u8, 0xbbu8,
     0xd3u8, 0xbcu8, 0x06u8, 0x28u8, 0xb9u8, 0x9cu8, 0x8du8, 0x55u8,
     0x0eu8, 0xb3u8, 0x51u8, 0xf7u8, 0x4cu8, 0xe1u8, 0x6du8, 0x48u8])
  }

  fn nat_eq_of_beq_eq_true_addr() -> Addr {
    store([0x9cu8, 0xe6u8, 0xe3u8, 0x22u8, 0xf1u8, 0x94u8, 0x81u8, 0xf2u8,
     0x1cu8, 0xf4u8, 0xc4u8, 0x8fu8, 0x88u8, 0x78u8, 0x98u8, 0x76u8,
     0xb6u8, 0x9bu8, 0x8au8, 0x9bu8, 0x15u8, 0x20u8, 0x43u8, 0x9cu8,
     0x10u8, 0x1du8, 0x98u8, 0x3fu8, 0x96u8, 0xeau8, 0x60u8, 0xb7u8])
  }

  fn nat_ne_of_beq_eq_false_addr() -> Addr {
    store([0x3cu8, 0xf5u8, 0x4du8, 0x33u8, 0x38u8, 0x21u8, 0xddu8, 0x37u8,
     0x68u8, 0x3au8, 0x0bu8, 0xf3u8, 0x87u8, 0x39u8, 0xe6u8, 0x87u8,
     0x61u8, 0x0au8, 0x19u8, 0x91u8, 0x75u8, 0x92u8, 0x20u8, 0xb7u8,
     0x7eu8, 0xdeu8, 0xc3u8, 0x38u8, 0xbau8, 0x3cu8, 0xfbu8, 0xc8u8])
  }

  fn reduce_bool_addr() -> Addr {
    store([0x1cu8, 0x17u8, 0x00u8, 0x98u8, 0xe2u8, 0x31u8, 0x43u8, 0xfdu8,
     0x8fu8, 0xd6u8, 0x17u8, 0x2cu8, 0xefu8, 0xd2u8, 0xecu8, 0xeeu8,
     0x30u8, 0x50u8, 0x72u8, 0xd2u8, 0x99u8, 0x11u8, 0x13u8, 0xcfu8,
     0xc4u8, 0xd5u8, 0x28u8, 0x40u8, 0xa5u8, 0xa9u8, 0xfau8, 0x78u8])
  }

  fn reduce_nat_addr() -> Addr {
    store([0x16u8, 0x85u8, 0x30u8, 0x76u8, 0xb0u8, 0xd9u8, 0x6du8, 0x35u8,
     0x6du8, 0x85u8, 0x48u8, 0x5cu8, 0x56u8, 0xf3u8, 0x39u8, 0x80u8,
     0x14u8, 0xb6u8, 0xa0u8, 0xf2u8, 0xeeu8, 0x72u8, 0xabu8, 0x16u8,
     0x28u8, 0x4au8, 0x38u8, 0x1du8, 0x9cu8, 0x28u8, 0xe5u8, 0x60u8])
  }

  fn system_platform_num_bits_addr() -> Addr {
    store([0xcfu8, 0x86u8, 0x26u8, 0x35u8, 0x21u8, 0xd3u8, 0x45u8, 0xc3u8,
     0x90u8, 0x76u8, 0x47u8, 0x3eu8, 0xcdu8, 0xb9u8, 0xf6u8, 0xfdu8,
     0x41u8, 0x1bu8, 0x5bu8, 0x50u8, 0x3bu8, 0xceu8, 0x83u8, 0xe2u8,
     0x31u8, 0x8bu8, 0xa3u8, 0xfbu8, 0x6fu8, 0x23u8, 0x76u8, 0xd8u8])
  }

  fn system_platform_get_num_bits_addr() -> Addr {
    store([0xf5u8, 0xd2u8, 0x56u8, 0xc1u8, 0xddu8, 0x79u8, 0x4du8, 0x02u8,
     0xcfu8, 0xdfu8, 0x17u8, 0x62u8, 0xc9u8, 0xe4u8, 0x1bu8, 0x13u8,
     0xabu8, 0xe5u8, 0xbdu8, 0xddu8, 0xe1u8, 0x2du8, 0x92u8, 0x9du8,
     0x02u8, 0xadu8, 0xa3u8, 0x7eu8, 0x4fu8, 0x40u8, 0xe8u8, 0x5fu8])
  }

  fn subtype_val_addr() -> Addr {
    store([0x0bu8, 0x59u8, 0x58u8, 0xa3u8, 0xc8u8, 0x22u8, 0xc9u8, 0x9eu8,
     0x86u8, 0x43u8, 0xa2u8, 0x7fu8, 0x0bu8, 0x92u8, 0x8du8, 0xfbu8,
     0x82u8, 0xc4u8, 0x54u8, 0x47u8, 0xbeu8, 0xe0u8, 0x35u8, 0x3cu8,
     0x20u8, 0x0au8, 0xd1u8, 0xb7u8, 0xd0u8, 0xe4u8, 0x60u8, 0x92u8])
  }

  fn punit_size_of_1_addr() -> Addr {
    store([0x7bu8, 0xd8u8, 0xe1u8, 0x9fu8, 0x47u8, 0xf6u8, 0xeau8, 0xe6u8,
     0x20u8, 0xa5u8, 0xc3u8, 0x9fu8, 0x24u8, 0x3cu8, 0xe4u8, 0x15u8,
     0xddu8, 0x6au8, 0x77u8, 0xf0u8, 0x95u8, 0x90u8, 0xf4u8, 0xc2u8,
     0x27u8, 0xceu8, 0xf3u8, 0x63u8, 0x00u8, 0x7fu8, 0x40u8, 0x12u8])
  }

  fn size_of_size_of_addr() -> Addr {
    store([0x38u8, 0x97u8, 0x15u8, 0xf9u8, 0x1eu8, 0x66u8, 0x68u8, 0x3du8,
     0xc7u8, 0x10u8, 0x8cu8, 0xcdu8, 0x85u8, 0x3eu8, 0xfcu8, 0xe9u8,
     0x29u8, 0x49u8, 0x51u8, 0x2fu8, 0xa6u8, 0x59u8, 0xadu8, 0x3cu8,
     0x19u8, 0x02u8, 0xe7u8, 0x54u8, 0x69u8, 0x29u8, 0x19u8, 0xcdu8])
  }

  fn punit_addr() -> Addr {
    store([0x2du8, 0xfcu8, 0x16u8, 0xafu8, 0x01u8, 0xb8u8, 0x2bu8, 0x3bu8,
     0x91u8, 0xc2u8, 0xffu8, 0x70u8, 0x44u8, 0x09u8, 0xd7u8, 0x62u8,
     0x36u8, 0xa8u8, 0x3fu8, 0x95u8, 0x6cu8, 0x0cu8, 0x6eu8, 0x66u8,
     0x59u8, 0xa6u8, 0x4fu8, 0xe2u8, 0x1du8, 0x76u8, 0x69u8, 0x5bu8])
  }

  fn unit_addr() -> Addr {
    store([0x92u8, 0x32u8, 0x49u8, 0x86u8, 0x67u8, 0xf7u8, 0x65u8, 0xf4u8,
     0x37u8, 0xdeu8, 0xdau8, 0xacu8, 0x82u8, 0x8eu8, 0x55u8, 0x5fu8,
     0x6cu8, 0xc6u8, 0x7au8, 0x20u8, 0xe6u8, 0xdbu8, 0x28u8, 0xf6u8,
     0x14u8, 0xfdu8, 0xf3u8, 0xc2u8, 0x62u8, 0x71u8, 0x0fu8, 0xebu8])
  }

  fn nat_addr() -> Addr {
    store([0x39u8, 0x8au8, 0x77u8, 0x06u8, 0xcfu8, 0x13u8, 0xf2u8, 0x23u8,
     0x99u8, 0x2du8, 0x17u8, 0x3du8, 0xceu8, 0x07u8, 0x94u8, 0x68u8,
     0x57u8, 0x24u8, 0x0fu8, 0x49u8, 0xafu8, 0xccu8, 0x74u8, 0x37u8,
     0x23u8, 0xe8u8, 0x39u8, 0xf8u8, 0xf3u8, 0xf2u8, 0xb6u8, 0x31u8])
  }

  fn nat_zero_addr() -> Addr {
    store([0xd3u8, 0x97u8, 0x37u8, 0x01u8, 0x57u8, 0xfbu8, 0x9au8, 0xe2u8,
     0xc6u8, 0xe1u8, 0xedu8, 0xa7u8, 0x9fu8, 0xebu8, 0x10u8, 0xbfu8,
     0x49u8, 0x74u8, 0x01u8, 0x74u8, 0x1au8, 0xbau8, 0x78u8, 0x8fu8,
     0xabu8, 0x72u8, 0x6cu8, 0xfau8, 0x4cu8, 0x46u8, 0x7du8, 0xb6u8])
  }

  fn nat_succ_addr() -> Addr {
    store([0xdeu8, 0xf5u8, 0x2du8, 0x1du8, 0xadu8, 0x5fu8, 0x10u8, 0xcfu8,
     0x98u8, 0x93u8, 0xc9u8, 0x45u8, 0xe1u8, 0x69u8, 0x71u8, 0x8du8,
     0x62u8, 0xb1u8, 0x5eu8, 0x2du8, 0xd2u8, 0xc9u8, 0x06u8, 0x6eu8,
     0x59u8, 0x7bu8, 0x9du8, 0x45u8, 0x70u8, 0xbau8, 0x05u8, 0x6eu8])
  }

  fn nat_pred_addr() -> Addr {
    store([0x91u8, 0x4fu8, 0x9cu8, 0x01u8, 0x88u8, 0x48u8, 0x53u8, 0x65u8,
     0x2eu8, 0x92u8, 0x24u8, 0xdcu8, 0x51u8, 0x1fu8, 0x86u8, 0x7du8,
     0x54u8, 0x08u8, 0x51u8, 0x7fu8, 0x3bu8, 0xebu8, 0x31u8, 0x92u8,
     0xfcu8, 0x44u8, 0x77u8, 0xe0u8, 0xe9u8, 0x59u8, 0x4cu8, 0x88u8])
  }

  fn nat_add_addr() -> Addr {
    store([0xd6u8, 0xf6u8, 0x2au8, 0x97u8, 0x79u8, 0x10u8, 0x8fu8, 0x9fu8,
     0xb6u8, 0xb6u8, 0x6bu8, 0x31u8, 0xccu8, 0x94u8, 0xc3u8, 0xd8u8,
     0x4cu8, 0xa7u8, 0x2du8, 0x8bu8, 0xeau8, 0x18u8, 0x5eu8, 0x13u8,
     0x13u8, 0x7cu8, 0x50u8, 0xc7u8, 0xefu8, 0x84u8, 0xc9u8, 0x69u8])
  }

  fn nat_sub_addr() -> Addr {
    store([0xfdu8, 0xbdu8, 0x5fu8, 0xefu8, 0x40u8, 0x14u8, 0x9cu8, 0x85u8,
     0x33u8, 0x3cu8, 0x6fu8, 0x3cu8, 0xceu8, 0xbbu8, 0x4bu8, 0xe7u8,
     0x41u8, 0x27u8, 0x0du8, 0x20u8, 0x66u8, 0x33u8, 0x6cu8, 0xb2u8,
     0xeeu8, 0xf8u8, 0x76u8, 0x23u8, 0x74u8, 0x4bu8, 0x72u8, 0xb0u8])
  }

  fn nat_mul_addr() -> Addr {
    store([0x66u8, 0x49u8, 0x66u8, 0x56u8, 0x07u8, 0xb0u8, 0x75u8, 0x0cu8,
     0x2cu8, 0xa7u8, 0x3fu8, 0x45u8, 0xdeu8, 0x60u8, 0x0fu8, 0x21u8,
     0xcbu8, 0x67u8, 0x03u8, 0x98u8, 0x50u8, 0x48u8, 0x65u8, 0xbbu8,
     0x97u8, 0x97u8, 0x24u8, 0x38u8, 0x01u8, 0x4fu8, 0x96u8, 0xd9u8])
  }

  fn nat_pow_addr() -> Addr {
    store([0x33u8, 0xc6u8, 0x04u8, 0x45u8, 0x1du8, 0x01u8, 0xcbu8, 0x19u8,
     0xa4u8, 0x33u8, 0x66u8, 0x82u8, 0x46u8, 0xb9u8, 0x8fu8, 0x6eu8,
     0x87u8, 0x4bu8, 0xd6u8, 0x30u8, 0xb7u8, 0x8au8, 0x79u8, 0x1du8,
     0x7au8, 0x37u8, 0x3au8, 0x97u8, 0x98u8, 0x49u8, 0xa1u8, 0xcfu8])
  }

  fn nat_gcd_addr() -> Addr {
    store([0x3bu8, 0xe4u8, 0x83u8, 0x57u8, 0xaeu8, 0x17u8, 0xf7u8, 0x4du8,
     0x4du8, 0xf2u8, 0x7du8, 0x69u8, 0x7au8, 0xedu8, 0x3fu8, 0x47u8,
     0xc1u8, 0x30u8, 0x79u8, 0x41u8, 0xf4u8, 0x1au8, 0xffu8, 0xcfu8,
     0x74u8, 0xdau8, 0x5fu8, 0x66u8, 0xd5u8, 0x11u8, 0xa7u8, 0x97u8])
  }

  fn nat_mod_addr() -> Addr {
    store([0x51u8, 0x79u8, 0x63u8, 0x8bu8, 0x82u8, 0xccu8, 0x83u8, 0x37u8,
     0x91u8, 0x4au8, 0x7bu8, 0xcau8, 0xadu8, 0x85u8, 0x8cu8, 0x85u8,
     0x88u8, 0x88u8, 0x44u8, 0xe9u8, 0xa2u8, 0x92u8, 0x43u8, 0x0cu8,
     0xacu8, 0x51u8, 0xe5u8, 0xeau8, 0xdcu8, 0x41u8, 0xa1u8, 0xafu8])
  }

  fn nat_div_addr() -> Addr {
    store([0x89u8, 0xdeu8, 0xcau8, 0x86u8, 0xddu8, 0x8fu8, 0x00u8, 0x66u8,
     0xa5u8, 0x06u8, 0x4fu8, 0xdbu8, 0x19u8, 0xa2u8, 0xc6u8, 0x89u8,
     0x7au8, 0x3au8, 0x98u8, 0x67u8, 0xcau8, 0xadu8, 0xc0u8, 0x4fu8,
     0x77u8, 0x8du8, 0x5cu8, 0x5cu8, 0xd0u8, 0x22u8, 0x53u8, 0x62u8])
  }

  fn nat_land_addr() -> Addr {
    store([0x81u8, 0x8au8, 0xbbu8, 0x33u8, 0x11u8, 0x50u8, 0x40u8, 0x0du8,
     0x10u8, 0xb3u8, 0x4fu8, 0xaeu8, 0x4du8, 0xfbu8, 0x94u8, 0x26u8,
     0x74u8, 0x1cu8, 0x46u8, 0x07u8, 0xbau8, 0xeeu8, 0xd8u8, 0xd9u8,
     0x62u8, 0x71u8, 0xbau8, 0x16u8, 0x59u8, 0x05u8, 0x8eu8, 0xf8u8])
  }

  fn nat_lor_addr() -> Addr {
    store([0x9bu8, 0x76u8, 0xf3u8, 0x2bu8, 0xbbu8, 0x1du8, 0xbdu8, 0xf4u8,
     0xffu8, 0x68u8, 0xe0u8, 0x22u8, 0x12u8, 0x25u8, 0x01u8, 0x5du8,
     0xf0u8, 0xcau8, 0x2du8, 0x2au8, 0x60u8, 0x23u8, 0xc1u8, 0xa8u8,
     0x13u8, 0x06u8, 0xd4u8, 0x02u8, 0x0du8, 0x4eu8, 0xf3u8, 0x97u8])
  }

  fn nat_xor_addr() -> Addr {
    store([0x97u8, 0xe3u8, 0x25u8, 0xa9u8, 0x6au8, 0x6au8, 0x18u8, 0x27u8,
     0x19u8, 0x4eu8, 0xebu8, 0x7du8, 0x2au8, 0xa0u8, 0xd9u8, 0x19u8,
     0x21u8, 0x07u8, 0x3au8, 0xefu8, 0x9cu8, 0x2du8, 0x33u8, 0x3cu8,
     0x24u8, 0x61u8, 0x3eu8, 0x9au8, 0xc9u8, 0x56u8, 0xedu8, 0x29u8])
  }

  fn nat_shift_left_addr() -> Addr {
    store([0xdcu8, 0x81u8, 0xe4u8, 0x1cu8, 0xadu8, 0x11u8, 0x90u8, 0x37u8,
     0x7du8, 0xbeu8, 0x60u8, 0x4bu8, 0xfcu8, 0x3au8, 0xfeu8, 0x65u8,
     0x8au8, 0x41u8, 0x3bu8, 0x9au8, 0x2du8, 0xcfu8, 0xbcu8, 0xabu8,
     0x79u8, 0xfau8, 0xd7u8, 0xb7u8, 0xa5u8, 0xcdu8, 0xd9u8, 0x54u8])
  }

  fn nat_shift_right_addr() -> Addr {
    store([0x6du8, 0xb4u8, 0x93u8, 0x04u8, 0xbfu8, 0x0fu8, 0x5au8, 0xcbu8,
     0xfdu8, 0x1du8, 0x9du8, 0x9au8, 0x0cu8, 0x1bu8, 0x7au8, 0xe2u8,
     0x0eu8, 0xf9u8, 0x9du8, 0x07u8, 0x37u8, 0x88u8, 0x70u8, 0x56u8,
     0x12u8, 0x9fu8, 0x5bu8, 0x5cu8, 0xb5u8, 0xa9u8, 0xbau8, 0x8au8])
  }

  fn nat_beq_addr() -> Addr {
    store([0xa3u8, 0x4au8, 0xb2u8, 0xdau8, 0xbau8, 0x34u8, 0x83u8, 0x9eu8,
     0x85u8, 0x1fu8, 0xa3u8, 0x67u8, 0x51u8, 0x24u8, 0x56u8, 0x6fu8,
     0x9fu8, 0x4du8, 0xcdu8, 0xe5u8, 0x97u8, 0x34u8, 0x9eu8, 0xcdu8,
     0x54u8, 0xaeu8, 0x32u8, 0xf8u8, 0x42u8, 0x4eu8, 0x44u8, 0xb8u8])
  }

  fn nat_ble_addr() -> Addr {
    store([0xdeu8, 0x0bu8, 0xefu8, 0xa8u8, 0x4fu8, 0xaau8, 0x22u8, 0xd1u8,
     0x39u8, 0x43u8, 0x79u8, 0xa0u8, 0xbau8, 0x67u8, 0x29u8, 0x6eu8,
     0x11u8, 0x66u8, 0x60u8, 0xf7u8, 0x81u8, 0xb4u8, 0xebu8, 0x63u8,
     0x9du8, 0xbbu8, 0xabu8, 0xa2u8, 0x00u8, 0xefu8, 0x2bu8, 0xf8u8])
  }

  fn str_addr() -> Addr {
    store([0x7au8, 0xb2u8, 0xd5u8, 0x2au8, 0xc5u8, 0x2fu8, 0xd1u8, 0xf5u8,
     0x18u8, 0x09u8, 0xb7u8, 0x18u8, 0xe5u8, 0x3cu8, 0xd0u8, 0x58u8,
     0xacu8, 0x4bu8, 0x50u8, 0xd6u8, 0x51u8, 0x50u8, 0xe7u8, 0x8au8,
     0xe6u8, 0x19u8, 0x13u8, 0x9cu8, 0xcfu8, 0x13u8, 0xc8u8, 0xfdu8])
  }

  fn string_utf8_byte_size_addr() -> Addr {
    store([0xdeu8, 0xf4u8, 0x43u8, 0x3du8, 0x95u8, 0x47u8, 0xb5u8, 0x31u8,
     0x75u8, 0xe2u8, 0x4au8, 0x3au8, 0xc1u8, 0x82u8, 0xc8u8, 0x8bu8,
     0x07u8, 0x2au8, 0xf0u8, 0xd4u8, 0xadu8, 0x33u8, 0xfdu8, 0x04u8,
     0xecu8, 0x4cu8, 0xf2u8, 0xbau8, 0x3du8, 0x95u8, 0xeau8, 0x93u8])
  }

  fn string_back_addr() -> Addr {
    store([0xe9u8, 0x5cu8, 0x8du8, 0x87u8, 0x6eu8, 0x7cu8, 0xcfu8, 0x78u8,
     0x04u8, 0x18u8, 0x61u8, 0x5eu8, 0x33u8, 0xb7u8, 0x47u8, 0xa2u8,
     0x45u8, 0xd9u8, 0x4fu8, 0xacu8, 0xd7u8, 0x56u8, 0x7fu8, 0xecu8,
     0xbeu8, 0x7au8, 0xe7u8, 0x3au8, 0x5au8, 0xc0u8, 0x92u8, 0x06u8])
  }

  fn string_legacy_back_addr() -> Addr {
    store([0x6bu8, 0xb6u8, 0x16u8, 0x2au8, 0xacu8, 0x7du8, 0x6au8, 0x01u8,
     0xb6u8, 0xecu8, 0x05u8, 0x58u8, 0x06u8, 0x64u8, 0xe8u8, 0xa7u8,
     0xf0u8, 0xd4u8, 0xb0u8, 0xecu8, 0x1fu8, 0xc5u8, 0xafu8, 0xaau8,
     0xe6u8, 0x60u8, 0x18u8, 0xe9u8, 0xa1u8, 0x93u8, 0x6du8, 0xacu8])
  }

  fn string_to_byte_array_addr() -> Addr {
    store([0xedu8, 0x43u8, 0xc7u8, 0x7eu8, 0x55u8, 0x55u8, 0x93u8, 0xb6u8,
     0xcdu8, 0x0du8, 0x4bu8, 0xfbu8, 0xc4u8, 0x27u8, 0x3bu8, 0xa1u8,
     0x22u8, 0xe1u8, 0xc0u8, 0xcdu8, 0xf1u8, 0x09u8, 0x05u8, 0x71u8,
     0x61u8, 0x2au8, 0x95u8, 0x2fu8, 0x94u8, 0x1eu8, 0xadu8, 0xb1u8])
  }

  fn byte_array_empty_addr() -> Addr {
    store([0x7cu8, 0xfbu8, 0xa8u8, 0xfau8, 0x95u8, 0x84u8, 0x7cu8, 0x21u8,
     0x3au8, 0xa4u8, 0x06u8, 0x61u8, 0x10u8, 0xbau8, 0x01u8, 0xa9u8,
     0x7fu8, 0xb5u8, 0x97u8, 0xdau8, 0xf2u8, 0x9fu8, 0x5cu8, 0x07u8,
     0xf7u8, 0x23u8, 0x66u8, 0x07u8, 0x2fu8, 0x25u8, 0x07u8, 0x44u8])
  }

  fn char_of_nat_addr() -> Addr {
    store([0x1au8, 0x4cu8, 0x66u8, 0xf7u8, 0x67u8, 0x60u8, 0xf5u8, 0xefu8,
     0x38u8, 0x6du8, 0xe0u8, 0x89u8, 0x68u8, 0x2au8, 0x55u8, 0xb7u8,
     0x52u8, 0x13u8, 0x1eu8, 0x14u8, 0xa0u8, 0x85u8, 0x57u8, 0xc4u8,
     0x46u8, 0x5eu8, 0xd1u8, 0x7fu8, 0xe0u8, 0xc4u8, 0xdcu8, 0x86u8])
  }

  fn char_type_addr() -> Addr {
    store([0x29u8, 0xddu8, 0x2du8, 0x19u8, 0x86u8, 0xa5u8, 0x25u8, 0xbdu8,
     0xdeu8, 0x49u8, 0xb4u8, 0xadu8, 0x2du8, 0xefu8, 0xc3u8, 0x49u8,
     0xceu8, 0xc7u8, 0x1du8, 0x04u8, 0x84u8, 0xcdu8, 0x13u8, 0xf2u8,
     0xdau8, 0x92u8, 0xf1u8, 0xfcu8, 0xe8u8, 0x9au8, 0x4cu8, 0x79u8])
  }

  fn string_of_list_addr() -> Addr {
    store([0x96u8, 0x71u8, 0xfdu8, 0x4fu8, 0xcfu8, 0xbcu8, 0x06u8, 0x1cu8,
     0x93u8, 0xc2u8, 0x82u8, 0x48u8, 0x64u8, 0xcfu8, 0x03u8, 0x12u8,
     0x4fu8, 0xfeu8, 0xe7u8, 0xccu8, 0x22u8, 0x30u8, 0x8du8, 0xe1u8,
     0x2au8, 0x7cu8, 0x82u8, 0x64u8, 0x73u8, 0xe4u8, 0x99u8, 0x06u8])
  }

  fn list_nil_addr() -> Addr {
    store([0x25u8, 0x8au8, 0x73u8, 0x64u8, 0xb8u8, 0x7cu8, 0x99u8, 0xfeu8,
     0x9fu8, 0x83u8, 0xe0u8, 0x5eu8, 0x0du8, 0x05u8, 0xc9u8, 0x35u8,
     0x60u8, 0x9au8, 0x0du8, 0xc5u8, 0xdfu8, 0x8du8, 0x77u8, 0x93u8,
     0x91u8, 0x30u8, 0xefu8, 0xe5u8, 0xe0u8, 0xefu8, 0xcau8, 0x3eu8])
  }

  fn list_cons_addr() -> Addr {
    store([0x77u8, 0xd5u8, 0x19u8, 0x25u8, 0x9eu8, 0xc9u8, 0xfau8, 0x48u8,
     0x9du8, 0xbeu8, 0x0eu8, 0x3du8, 0xc0u8, 0xb9u8, 0x35u8, 0x2au8,
     0xefu8, 0x34u8, 0x9cu8, 0xcdu8, 0xaau8, 0x73u8, 0xeau8, 0x58u8,
     0xb0u8, 0x8bu8, 0xb0u8, 0xbcu8, 0x68u8, 0x35u8, 0x02u8, 0xa0u8])
  }

  fn bool_true_addr() -> Addr {
    store([0xa2u8, 0x9au8, 0x63u8, 0x61u8, 0x76u8, 0xcfu8, 0x11u8, 0x35u8,
     0xd0u8, 0x77u8, 0xebu8, 0x07u8, 0x47u8, 0x98u8, 0xf9u8, 0x00u8,
     0x7cu8, 0x78u8, 0xe7u8, 0x80u8, 0x13u8, 0x83u8, 0xe9u8, 0xcfu8,
     0xf3u8, 0x63u8, 0xbau8, 0xe5u8, 0xedu8, 0xf0u8, 0x57u8, 0x62u8])
  }

  fn bool_false_addr() -> Addr {
    store([0xddu8, 0xa1u8, 0x2bu8, 0xcbu8, 0x33u8, 0x07u8, 0x27u8, 0xf6u8,
     0xdfu8, 0xb8u8, 0x16u8, 0xbcu8, 0x97u8, 0x52u8, 0xaau8, 0xbdu8,
     0x05u8, 0x20u8, 0xe6u8, 0x51u8, 0x5bu8, 0x79u8, 0xfcu8, 0x8au8,
     0x5au8, 0x9eu8, 0x71u8, 0x38u8, 0x66u8, 0xf4u8, 0xc6u8, 0x3eu8])
  }

  -- Mirror: BigUint::succ. Increment a KLimbs by 1; ripple carry.
  fn klimbs_succ(n: KLimbs) -> KLimbs {
    match load(n) {
      ListNode.Nil =>
        store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil))),
      ListNode.Cons(limb, rest) =>
        let pair = u64_add(limb, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
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
                let pair2 = u64_add(sum1, [u8_from_field_unsafe(carry), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
                match pair2 {
                  (sum2, carry2) =>
                    -- carry1, carry2 mutually exclusive: carry1=1 ⇒ sum1 ≤
                    -- 2^64-2 ⇒ sum1 + carry_in ≤ 2^64-1 ⇒ carry2=0.
                    let total_carry = to_field(carry1) + to_field(carry2);
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
  -- Per-byte: u_t = borrow(a_i - b_i); u_r = borrow((a_i + 256 - b_i) - br_in).
  -- u_t = 1 ⇒ a_i + 256 - b_i ≥ 1 ⇒ subtracting br_in ∈ {0,1} cannot underflow
  -- ⇒ u_r = 0. So `u_t` and `u_r` are mutually-exclusive 0/1 values; field `+`
  -- substitutes for `g_or` (which charges +1 aux +1 lookup per call). See
  -- [[reference_aiur_carry_add]].
  fn u64_sub_with_borrow(a: U64, b: U64) -> (U64, G) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let (r0, br1) = u8_sub(a0, b0);
    let (t1, u_t1) = u8_sub(a1, b1);
    let (r1, u_r1) = u8_sub(t1, br1);
    let br2 = to_field(u_t1) + to_field(u_r1);
    let (t2, u_t2) = u8_sub(a2, b2);
    let (r2, u_r2) = u8_sub(t2, u8_from_field_unsafe(br2));
    let br3 = to_field(u_t2) + to_field(u_r2);
    let (t3, u_t3) = u8_sub(a3, b3);
    let (r3, u_r3) = u8_sub(t3, u8_from_field_unsafe(br3));
    let br4 = to_field(u_t3) + to_field(u_r3);
    let (t4, u_t4) = u8_sub(a4, b4);
    let (r4, u_r4) = u8_sub(t4, u8_from_field_unsafe(br4));
    let br5 = to_field(u_t4) + to_field(u_r4);
    let (t5, u_t5) = u8_sub(a5, b5);
    let (r5, u_r5) = u8_sub(t5, u8_from_field_unsafe(br5));
    let br6 = to_field(u_t5) + to_field(u_r5);
    let (t6, u_t6) = u8_sub(a6, b6);
    let (r6, u_r6) = u8_sub(t6, u8_from_field_unsafe(br6));
    let br7 = to_field(u_t6) + to_field(u_r6);
    let (t7, u_t7) = u8_sub(a7, b7);
    let (r7, u_r7) = u8_sub(t7, u8_from_field_unsafe(br7));
    let final_borrow = to_field(u_t7) + to_field(u_r7);
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
                let pair = u64_sub_with_borrow(la, [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
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
                let pair2 = u64_sub_with_borrow(sum1, [u8_from_field_unsafe(borrow), 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]);
                match pair2 {
                  (sum2, br2) =>
                    -- br1, br2 mutually exclusive: br1=1 ⇒ sum1 ≥ 1 ⇒
                    -- sum1 - borrow ≥ 0 ⇒ br2=0.
                    let total = br1 + br2;
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
    let one = store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    klimbs_sub(a, one)
  }

  -- Returns (remainder, quotient): remainder = x mod 256, quotient = x / 256.
  -- Repeated subtraction. Only ever invoked from the `#split_carry` /
  -- `#split_u32` unconstrained witness generators, so the O(x/256)
  -- iteration cost is off-circuit (untraced).
  fn divmod_256(x: G, q: G) -> (G, G) {
    match u32_less_than(x, 256) {
      1 => (x, q),
      0 => divmod_256(x - 256, q + 1),
    }
  }

  -- Unconstrained witness generator: split `x` into its low byte `limb`
  -- and the two bytes (clo, chi) of `x div 256`. Always invoked as
  -- `#split_carry(...)`; the result is prover-provided and MUST be pinned
  -- by the caller with u8 range checks + a reconstruction assert. The
  -- division here is off-circuit (untraced), so its cost is irrelevant.
  fn split_carry(x: G) -> (G, G, G) {
    match divmod_256(x, 0) {
      (limb, quot) =>
        match divmod_256(quot, 0) {
          (clo, chi) => (limb, clo, chi),
        },
    }
  }

  -- u64×u64 → (lo: U64, hi: U64) via byte schoolbook. Faithful port of the
  -- `MulWitness`/`Product` reference: column k is the raw field sum
  -- Σ_{i+j=k} a[i]*b[j]; each column accumulator `out` is decomposed by a
  -- prover-provided (unconstrained) split into result byte + 16-bit carry,
  -- then pinned by three u8 range checks (`u8_xor(_, 0)`) and the
  -- reconstruction assert `out == limb + 256·clo + 65536·chi`. No `u8_mul`
  -- gadget and no constrained division. Column accumulators are < 2^19, so
  -- the decomposition into (limb, clo, chi) ∈ [0,256)³ is unique → sound.
  fn u64_mul(a: U64, b: U64) -> (U64, U64) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    let col0 = (to_field(a0) * to_field(b0));
    let col1 = (to_field(a0) * to_field(b1)) + (to_field(a1) * to_field(b0));
    let col2 = (to_field(a0) * to_field(b2)) + (to_field(a1) * to_field(b1)) + (to_field(a2) * to_field(b0));
    let col3 = (to_field(a0) * to_field(b3)) + (to_field(a1) * to_field(b2)) + (to_field(a2) * to_field(b1)) + (to_field(a3) * to_field(b0));
    let col4 = (to_field(a0) * to_field(b4)) + (to_field(a1) * to_field(b3)) + (to_field(a2) * to_field(b2)) + (to_field(a3) * to_field(b1)) + (to_field(a4) * to_field(b0));
    let col5 = (to_field(a0) * to_field(b5)) + (to_field(a1) * to_field(b4)) + (to_field(a2) * to_field(b3)) + (to_field(a3) * to_field(b2)) + (to_field(a4) * to_field(b1)) + (to_field(a5) * to_field(b0));
    let col6 = (to_field(a0) * to_field(b6)) + (to_field(a1) * to_field(b5)) + (to_field(a2) * to_field(b4)) + (to_field(a3) * to_field(b3)) + (to_field(a4) * to_field(b2)) + (to_field(a5) * to_field(b1)) + (to_field(a6) * to_field(b0));
    let col7 = (to_field(a0) * to_field(b7)) + (to_field(a1) * to_field(b6)) + (to_field(a2) * to_field(b5)) + (to_field(a3) * to_field(b4)) + (to_field(a4) * to_field(b3)) + (to_field(a5) * to_field(b2)) + (to_field(a6) * to_field(b1)) + (to_field(a7) * to_field(b0));
    let col8 = (to_field(a1) * to_field(b7)) + (to_field(a2) * to_field(b6)) + (to_field(a3) * to_field(b5)) + (to_field(a4) * to_field(b4)) + (to_field(a5) * to_field(b3)) + (to_field(a6) * to_field(b2)) + (to_field(a7) * to_field(b1));
    let col9 = (to_field(a2) * to_field(b7)) + (to_field(a3) * to_field(b6)) + (to_field(a4) * to_field(b5)) + (to_field(a5) * to_field(b4)) + (to_field(a6) * to_field(b3)) + (to_field(a7) * to_field(b2));
    let col10 = (to_field(a3) * to_field(b7)) + (to_field(a4) * to_field(b6)) + (to_field(a5) * to_field(b5)) + (to_field(a6) * to_field(b4)) + (to_field(a7) * to_field(b3));
    let col11 = (to_field(a4) * to_field(b7)) + (to_field(a5) * to_field(b6)) + (to_field(a6) * to_field(b5)) + (to_field(a7) * to_field(b4));
    let col12 = (to_field(a5) * to_field(b7)) + (to_field(a6) * to_field(b6)) + (to_field(a7) * to_field(b5));
    let col13 = (to_field(a6) * to_field(b7)) + (to_field(a7) * to_field(b6));
    let col14 = (to_field(a7) * to_field(b7));
    match #split_carry(col0) {
      (rl0, rc0, rh0) =>
        let r0 = u8_xor(u8_from_field_unsafe(rl0), 0u8);
        let lo0 = u8_xor(u8_from_field_unsafe(rc0), 0u8);
        let hi0 = u8_xor(u8_from_field_unsafe(rh0), 0u8);
        assert_eq!(col0, to_field(r0) + (256 * to_field(lo0)) + (65536 * to_field(hi0)));
        let out1 = col1 + to_field(lo0) + (256 * to_field(hi0));
        match #split_carry(out1) {
          (rl1, rc1, rh1) =>
            let r1 = u8_xor(u8_from_field_unsafe(rl1), 0u8);
            let lo1 = u8_xor(u8_from_field_unsafe(rc1), 0u8);
            let hi1 = u8_xor(u8_from_field_unsafe(rh1), 0u8);
            assert_eq!(out1, to_field(r1) + (256 * to_field(lo1)) + (65536 * to_field(hi1)));
            let out2 = col2 + to_field(lo1) + (256 * to_field(hi1));
            match #split_carry(out2) {
              (rl2, rc2, rh2) =>
                let r2 = u8_xor(u8_from_field_unsafe(rl2), 0u8);
                let lo2 = u8_xor(u8_from_field_unsafe(rc2), 0u8);
                let hi2 = u8_xor(u8_from_field_unsafe(rh2), 0u8);
                assert_eq!(out2, to_field(r2) + (256 * to_field(lo2)) + (65536 * to_field(hi2)));
                let out3 = col3 + to_field(lo2) + (256 * to_field(hi2));
                match #split_carry(out3) {
                  (rl3, rc3, rh3) =>
                    let r3 = u8_xor(u8_from_field_unsafe(rl3), 0u8);
                    let lo3 = u8_xor(u8_from_field_unsafe(rc3), 0u8);
                    let hi3 = u8_xor(u8_from_field_unsafe(rh3), 0u8);
                    assert_eq!(out3, to_field(r3) + (256 * to_field(lo3)) + (65536 * to_field(hi3)));
                    let out4 = col4 + to_field(lo3) + (256 * to_field(hi3));
                    match #split_carry(out4) {
                      (rl4, rc4, rh4) =>
                        let r4 = u8_xor(u8_from_field_unsafe(rl4), 0u8);
                        let lo4 = u8_xor(u8_from_field_unsafe(rc4), 0u8);
                        let hi4 = u8_xor(u8_from_field_unsafe(rh4), 0u8);
                        assert_eq!(out4, to_field(r4) + (256 * to_field(lo4)) + (65536 * to_field(hi4)));
                        let out5 = col5 + to_field(lo4) + (256 * to_field(hi4));
                        match #split_carry(out5) {
                          (rl5, rc5, rh5) =>
                            let r5 = u8_xor(u8_from_field_unsafe(rl5), 0u8);
                            let lo5 = u8_xor(u8_from_field_unsafe(rc5), 0u8);
                            let hi5 = u8_xor(u8_from_field_unsafe(rh5), 0u8);
                            assert_eq!(out5, to_field(r5) + (256 * to_field(lo5)) + (65536 * to_field(hi5)));
                            let out6 = col6 + to_field(lo5) + (256 * to_field(hi5));
                            match #split_carry(out6) {
                              (rl6, rc6, rh6) =>
                                let r6 = u8_xor(u8_from_field_unsafe(rl6), 0u8);
                                let lo6 = u8_xor(u8_from_field_unsafe(rc6), 0u8);
                                let hi6 = u8_xor(u8_from_field_unsafe(rh6), 0u8);
                                assert_eq!(out6, to_field(r6) + (256 * to_field(lo6)) + (65536 * to_field(hi6)));
                                let out7 = col7 + to_field(lo6) + (256 * to_field(hi6));
                                match #split_carry(out7) {
                                  (rl7, rc7, rh7) =>
                                    let r7 = u8_xor(u8_from_field_unsafe(rl7), 0u8);
                                    let lo7 = u8_xor(u8_from_field_unsafe(rc7), 0u8);
                                    let hi7 = u8_xor(u8_from_field_unsafe(rh7), 0u8);
                                    assert_eq!(out7, to_field(r7) + (256 * to_field(lo7)) + (65536 * to_field(hi7)));
                                    let out8 = col8 + to_field(lo7) + (256 * to_field(hi7));
                                    match #split_carry(out8) {
                                      (rl8, rc8, rh8) =>
                                        let r8 = u8_xor(u8_from_field_unsafe(rl8), 0u8);
                                        let lo8 = u8_xor(u8_from_field_unsafe(rc8), 0u8);
                                        let hi8 = u8_xor(u8_from_field_unsafe(rh8), 0u8);
                                        assert_eq!(out8, to_field(r8) + (256 * to_field(lo8)) + (65536 * to_field(hi8)));
                                        let out9 = col9 + to_field(lo8) + (256 * to_field(hi8));
                                        match #split_carry(out9) {
                                          (rl9, rc9, rh9) =>
                                            let r9 = u8_xor(u8_from_field_unsafe(rl9), 0u8);
                                            let lo9 = u8_xor(u8_from_field_unsafe(rc9), 0u8);
                                            let hi9 = u8_xor(u8_from_field_unsafe(rh9), 0u8);
                                            assert_eq!(out9, to_field(r9) + (256 * to_field(lo9)) + (65536 * to_field(hi9)));
                                            let out10 = col10 + to_field(lo9) + (256 * to_field(hi9));
                                            match #split_carry(out10) {
                                              (rl10, rc10, rh10) =>
                                                let r10 = u8_xor(u8_from_field_unsafe(rl10), 0u8);
                                                let lo10 = u8_xor(u8_from_field_unsafe(rc10), 0u8);
                                                let hi10 = u8_xor(u8_from_field_unsafe(rh10), 0u8);
                                                assert_eq!(out10, to_field(r10) + (256 * to_field(lo10)) + (65536 * to_field(hi10)));
                                                let out11 = col11 + to_field(lo10) + (256 * to_field(hi10));
                                                match #split_carry(out11) {
                                                  (rl11, rc11, rh11) =>
                                                    let r11 = u8_xor(u8_from_field_unsafe(rl11), 0u8);
                                                    let lo11 = u8_xor(u8_from_field_unsafe(rc11), 0u8);
                                                    let hi11 = u8_xor(u8_from_field_unsafe(rh11), 0u8);
                                                    assert_eq!(out11, to_field(r11) + (256 * to_field(lo11)) + (65536 * to_field(hi11)));
                                                    let out12 = col12 + to_field(lo11) + (256 * to_field(hi11));
                                                    match #split_carry(out12) {
                                                      (rl12, rc12, rh12) =>
                                                        let r12 = u8_xor(u8_from_field_unsafe(rl12), 0u8);
                                                        let lo12 = u8_xor(u8_from_field_unsafe(rc12), 0u8);
                                                        let hi12 = u8_xor(u8_from_field_unsafe(rh12), 0u8);
                                                        assert_eq!(out12, to_field(r12) + (256 * to_field(lo12)) + (65536 * to_field(hi12)));
                                                        let out13 = col13 + to_field(lo12) + (256 * to_field(hi12));
                                                        match #split_carry(out13) {
                                                          (rl13, rc13, rh13) =>
                                                            let r13 = u8_xor(u8_from_field_unsafe(rl13), 0u8);
                                                            let lo13 = u8_xor(u8_from_field_unsafe(rc13), 0u8);
                                                            let hi13 = u8_xor(u8_from_field_unsafe(rh13), 0u8);
                                                            assert_eq!(out13, to_field(r13) + (256 * to_field(lo13)) + (65536 * to_field(hi13)));
                                                            let out14 = col14 + to_field(lo13) + (256 * to_field(hi13));
                                                            match #split_carry(out14) {
                                                              (rl14, rc14, rh14) =>
                                                                let r14 = u8_xor(u8_from_field_unsafe(rl14), 0u8);
                                                                let lo14 = u8_xor(u8_from_field_unsafe(rc14), 0u8);
                                                                let hi14 = u8_xor(u8_from_field_unsafe(rh14), 0u8);
                                                                assert_eq!(out14, to_field(r14) + (256 * to_field(lo14)) + (65536 * to_field(hi14)));
                                                                let r15 = u8_from_field_unsafe(to_field(lo14) + (256 * to_field(hi14)));
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
        let prod = klimbs_mul_single(a_limb, b, [0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil));
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
                match u64_add(hi, [carry_out, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]) {
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
        let prepended = store(ListNode.Cons([0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], x));
        klimbs_shl_limbs(prepended, shift - 1),
    }
  }

  fn klimbs_is_zero(x: KLimbs) -> G {
    match load(klimbs_normalize(x)) {
      ListNode.Nil => 1,
      _ => 0,
    }
  }

  -- Unconstrained Aiur op `unconstrained_big_uint_div_mod(a, b) -> (q, r)`
  -- pushes prover-supplied (q, r) into the trace map; no constraints emitted
  -- by the op itself. Caller verifies `q*b + r == a` (under normalize) and
  -- `r < b` when `b != 0`. For `b == 0` the op returns `(0, a)`; only the
  -- `q*b + r == a` equality is required (which holds: `0*0 + a == a`).
  --
  -- Soundness on the prover-supplied bytes: every limb byte flows through
  -- u8_mul inside `klimbs_mul(q, b)` and u8_add inside `klimbs_add(qb, r)`,
  -- both of which push to the u8_range_check channel
  -- (src/aiur/gadgets/bytes2.rs), so a byte > 255 fails the gadget's range
  -- check. Trailing junk limbs that mul doesn't touch are caught by the
  -- post-normalize equality below.
  fn klimbs_div_mod(a: KLimbs, b: KLimbs) -> (KLimbs, KLimbs) {
    let (q, r) = unconstrained_big_uint_div_mod(a, b);
    let qb = klimbs_mul(q, b);
    let lhs = klimbs_normalize(klimbs_add(qb, r));
    let rhs = klimbs_normalize(a);
    assert_eq!(lhs, rhs);
    match klimbs_is_zero(b) {
      1 => (q, r),
      0 =>
        -- r < b iff (r + 1) ≤ b. One klimbs_le on klimbs_succ(r); cheapest
        -- of the sound variants empirically (vs `le(r,b)∧¬eq(r,b)` or
        -- `¬le(b,r)`).
        assert_eq!(klimbs_le(klimbs_succ(r), b), 1);
        (q, r),
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

  -- Binary exponentiation. Replaces the old O(exp) recursive
  -- `klimbs_mul(base, klimbs_pow(base, klimbs_dec(exp)))` body, which
  -- created one per-fn memo row per exponent step and OOM'd for
  -- non-trivial exponents. Recursion depth is `log2(exp)` — for
  -- `exp = 2^32` that's 32 memo entries instead of 4 billion.
  --
  -- Both `klimbs_div2` (= `klimbs_div(exp, 2)`) and `klimbs_is_odd`
  -- (= `klimbs_mod(exp, 2) != 0`) route through `klimbs_div_mod`, which
  -- is itself native (unconstrained_big_uint_div_mod) — so the
  -- division per step is O(1) work.
  fn klimbs_pow(base: KLimbs, exp: KLimbs) -> KLimbs {
    match klimbs_is_zero(exp) {
      1 => store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil))),
      0 =>
        let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
        let (half, r) = klimbs_div_mod(exp, two);
        let sq = klimbs_pow(klimbs_normalize(klimbs_mul(base, base)), klimbs_normalize(half));
        match klimbs_is_zero(r) {
          1 => sq,
          0 => klimbs_mul(base, sq),
        },
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
    let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    klimbs_mul(a, klimbs_pow(two, n))
  }

  -- Shift right by n bits via integer division by 2^n.
  fn klimbs_shr(a: KLimbs, n: KLimbs) -> KLimbs {
    let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    klimbs_div(a, klimbs_pow(two, n))
  }

  -- ============================================================================
  -- Lit(Nat) extraction + dispatch
  -- ============================================================================

  -- Find target's positional idx in addrs. Returns (1, idx) if found,
  -- (0, _) if not. Used by Nat literal coercion in iota.
  fn find_addr_idx_safe(target: Addr, addrs: List‹Addr›, i: G) -> (G, G) {
    match load(addrs) {
      ListNode.Nil => (0, 0),
      ListNode.Cons(a, rest) =>
        match address_eq(target, a) {
          1 => (1, i),
          0 => find_addr_idx_safe(target, rest, i + 1),
        },
    }
  }

  -- Single-step Nat-literal → ctor coercion. Mirrors Rust
  -- `nat_to_constructor` (src/ix/kernel/whnf.rs:1664-1687):
  --   0   → `Const(Nat.zero)`
  --   n+1 → `App(Const(Nat.succ), Lit(Nat(n-1)))`
  -- The predecessor stays a `Lit`; the iota that asked for this expansion
  -- only needs to see the head ctor. Subsequent matches re-trigger
  -- expansion as needed. The previous body unfolded recursively into
  -- `Nat.succ^n(Nat.zero)`, which OOM'd for large literals (the original
  -- driver: per-step `klimbs_dec` memo growth, 4M+ entries seen on
  -- `Init.Data.String.Decode.0.ByteArray.utf8DecodeChar?.assemble₂._proof_1`
  -- before allocation failure).
  fn klimbs_to_ctor_form(n: KLimbs, zero_idx: G, succ_idx: G) -> KExpr {
    match load(n) {
      ListNode.Nil =>
        store(KExprNode.Const(zero_idx, store(ListNode.Nil))),
      ListNode.Cons(_, _) =>
        let pred = mk_nat_lit(klimbs_normalize(klimbs_dec(n)));
        let succ_const = store(KExprNode.Const(succ_idx, store(ListNode.Nil)));
        store(KExprNode.App(succ_const, pred)),
    }
  }

  -- If `e` is `Lit(Nat(klimbs))` and addrs contains both Nat.zero and
  -- Nat.succ, expand to ctor chain. Else return `e` unchanged. Mirror:
  -- src/ix/kernel/whnf.rs:929-946 nat_to_constructor.
  fn nat_lit_to_ctor_or_self(e: KExpr, addrs: List‹Addr›) -> KExpr {
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
  fn try_extract_nat(e: KExpr, addrs: List‹Addr›) -> (G, KLimbs) {
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
      KExprNode.App(f, a) => try_extract_nat_app(f, a, addrs),
      _ => (0, store(ListNode.Nil)),
    }
  }

  -- Cold-extracted App arm: list_lookup + address_eq + recursive
  -- try_extract_nat + klimbs_succ is the widest arm; pulling it out lets
  -- `try_extract_nat`'s main width drop to the leaf-arm width.
  fn try_extract_nat_app(f: KExpr, a: KExpr, addrs: List‹Addr›) -> (G, KLimbs) {
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
    }
  }

  -- Wrap a KLimbs in `Lit(Nat(...))`.
  fn mk_nat_lit(n: KLimbs) -> KExpr {
    store(KExprNode.Lit(KLiteral.Nat(n)))
  }

  -- 1 iff `head_addr` is one of the head-dispatched primitive ops checked by
  -- `try_nat_dispatch` / `try_str_dispatch` / `try_bitvec_dispatch` /
  -- `try_reduce_native` / `try_reduce_decidable`. These addresses are mutually
  -- exclusive (a const has one content address), so the sum is 0 or 1.
  -- Memoized on `head_addr` (a content pointer): computed once per distinct
  -- const, vs the per-whnf gauntlet of 5 `try_*` calls. Lets `whnf_const_head`
  -- skip the gauntlet for the common non-primitive head. MUST stay in sync
  -- with the `address_eq(head_addr, …)` checks in those functions — a
  -- differential `assert` guards that during development.
  fn prim_any_addr(head_addr: Addr) -> G {
    address_eq(head_addr, nat_add_addr())
    + address_eq(head_addr, nat_sub_addr())
    + address_eq(head_addr, nat_mul_addr())
    + address_eq(head_addr, nat_div_addr())
    + address_eq(head_addr, nat_mod_addr())
    + address_eq(head_addr, nat_pow_addr())
    + address_eq(head_addr, nat_gcd_addr())
    + address_eq(head_addr, nat_land_addr())
    + address_eq(head_addr, nat_lor_addr())
    + address_eq(head_addr, nat_xor_addr())
    + address_eq(head_addr, nat_shift_left_addr())
    + address_eq(head_addr, nat_shift_right_addr())
    + address_eq(head_addr, nat_succ_addr())
    + address_eq(head_addr, nat_pred_addr())
    + address_eq(head_addr, nat_beq_addr())
    + address_eq(head_addr, nat_ble_addr())
    + address_eq(head_addr, nat_dec_eq_addr())
    + address_eq(head_addr, nat_dec_le_addr())
    + address_eq(head_addr, nat_dec_lt_addr())
    + address_eq(head_addr, bool_true_addr())
    + address_eq(head_addr, bool_false_addr())
    + address_eq(head_addr, int_of_nat_addr())
    + address_eq(head_addr, int_neg_succ_addr())
    + address_eq(head_addr, int_dec_eq_addr())
    + address_eq(head_addr, int_dec_le_addr())
    + address_eq(head_addr, int_dec_lt_addr())
    + address_eq(head_addr, bit_vec_of_nat_addr())
    + address_eq(head_addr, bit_vec_to_nat_addr())
    + address_eq(head_addr, bit_vec_ult_addr())
    + address_eq(head_addr, decidable_decide_addr())
    + address_eq(head_addr, reduce_bool_addr())
    + address_eq(head_addr, reduce_nat_addr())
    + address_eq(head_addr, size_of_size_of_addr())
    + address_eq(head_addr, string_back_addr())
    + address_eq(head_addr, string_legacy_back_addr())
    + address_eq(head_addr, string_to_byte_array_addr())
    + address_eq(head_addr, subtype_val_addr())
    + address_eq(head_addr, system_platform_get_num_bits_addr())
    + address_eq(head_addr, system_platform_num_bits_addr())
    + address_eq(head_addr, punit_addr())
    + address_eq(head_addr, punit_size_of_1_addr())
    + address_eq(head_addr, unit_addr())
    + address_eq(head_addr, string_utf8_byte_size_addr())
  }

  -- Mirror: src/ix/kernel/whnf.rs:500-700 Nat-on-literals dispatch.
  -- Address-keyed (no positional prims): given the head Const's blake3
  -- address and the unreduced spine, fold a Nat primitive op when both
  -- required args are literals. Returns (1, reduced) on hit, (0, _) on miss.
  fn try_nat_dispatch(head_addr: Addr, spine: List‹KExpr›,
                      types: List‹KExpr›, top: List‹&KConstantInfo›,
                      addrs: List‹Addr›) -> (G, KExpr) {
    let spine_len = list_length(spine);
    let is_pred = address_eq(head_addr, nat_pred_addr());
    let is_succ = address_eq(head_addr, nat_succ_addr());
    match is_succ {
      1 =>
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
          0 => try_nat_binop_dispatch(head_addr, spine, spine_len, types, top, addrs),
        },
    }
  }

  -- Cold-extracted binop arm (mirror [[reference_aiur_hot_cold_split]]).
  -- Binop dispatch is the widest arm of `try_nat_dispatch` (2× whnf + 2×
  -- try_extract_nat + try_nat_binop_addr + apply_spine), so it pays
  -- max-arm-width on every Nat.succ/Nat.pred row when inlined. Factored
  -- here so its width only charges the rows that actually dispatch a
  -- binop.
  fn try_nat_binop_dispatch(head_addr: Addr, spine: List‹KExpr›, spine_len: G,
                             types: List‹KExpr›, top: List‹&KConstantInfo›,
                             addrs: List‹Addr›) -> (G, KExpr) {
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
    }
  }

  -- Dispatch a Nat binary op by head address. Bool result for beq/ble
  -- wraps via Bool.true / Bool.false ctors (mk_bool).
  fn try_nat_binop_addr(head_addr: Addr, a: KLimbs, b: KLimbs,
                        addrs: List‹Addr›) -> (G, KExpr) {
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
  fn mk_bool(g: G, addrs: List‹Addr›) -> KExpr {
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
              store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)))))),
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
        to_field(b0) + 256*to_field(b1) + 65536*to_field(b2) + 16777216*to_field(b3),
    }
  }

  -- Mirror: src/ix/kernel/whnf.rs:2546-2579 fn try_reduce_bitvec_to_nat.
  -- `BitVec.toNat width (BitVec.ofNat width' n)` → `Lit(Nat (n mod 2^width))`.
  -- Width must be ≤ 2^24 to bound klimbs_pow cost.
  fn try_reduce_bit_vec_to_nat(spine: List‹KExpr›, types: List‹KExpr›,
                                top: List‹&KConstantInfo›,
                                addrs: List‹Addr›) -> (G, KExpr) {
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
                    let two = store(ListNode.Cons([2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
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
  fn bitvec_of_nat_args(e: KExpr, addrs: List‹Addr›) -> (G, KExpr, KExpr) {
    match collect_spine(e) {
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
                let of_nat_addr = store([0x8fu8, 0xdcu8, 0x86u8, 0x9fu8, 0x7bu8, 0x7au8, 0xa2u8, 0xb7u8,
                                   0xb5u8, 0x92u8, 0x9bu8, 0xa2u8, 0x42u8, 0xedu8, 0x89u8, 0x9cu8,
                                   0xe2u8, 0xd7u8, 0xc5u8, 0xd4u8, 0x2du8, 0xf1u8, 0xd4u8, 0xe2u8,
                                   0x39u8, 0x36u8, 0x90u8, 0xcfu8, 0xa8u8, 0x5eu8, 0x94u8, 0xd2u8]);
                match address_eq(head_addr, of_nat_addr) {
                  0 => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                  1 =>
                    match u32_less_than(list_length(args), 2) {
                      1 => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                      0 =>
                        let ty_arg = list_lookup(args, 0);
                        match collect_spine(ty_arg) {
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
                             addrs: List‹Addr›) -> (G, KExpr) {
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
                    addrs: List‹Addr›) -> (G, KLimbs) {
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
  fn try_bitvec_dispatch(head_addr: Addr, spine: List‹KExpr›,
                          types: List‹KExpr›,
                          top: List‹&KConstantInfo›,
                          addrs: List‹Addr›) -> (G, KExpr) {
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
                                  addrs: List‹Addr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let prop = list_lookup(spine, 0);
        match collect_spine(prop) {
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
                        match collect_spine(ty_arg) {
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
  fn try_reduce_native(head_addr: Addr, spine: List‹KExpr›,
                       types: List‹KExpr›,
                       top: List‹&KConstantInfo›,
                       addrs: List‹Addr›) -> (G, KExpr) {
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
    let limbs = store(ListNode.Cons([64u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    store(KExprNode.Lit(KLiteral.Nat(limbs)))
  }

  fn mk_nat_one() -> KExpr {
    let limbs = store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    store(KExprNode.Lit(KLiteral.Nat(limbs)))
  }

  -- Subtype.val A P (System.Platform.getNumBits ()) → 64.
  -- Spine: [A, P, val_arg]. If val_arg's spine head = getNumBits, return 64.
  fn try_reduce_subtype_val(spine: List‹KExpr›,
                            addrs: List‹Addr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 3) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let val_arg = list_lookup(spine, 2);
        match collect_spine(val_arg) {
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
                             addrs: List‹Addr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 1) {
      1 => (0, store(KExprNode.BVar(0))),
      0 =>
        let ty_arg = list_lookup(spine, 0);
        match collect_spine(ty_arg) {
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
  fn check_native_bool(e: KExpr, addrs: List‹Addr›) -> (G, KExpr) {
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
  fn try_reduce_decidable(head_addr: Addr, head_idx: G,
                          head_lvls: List‹KLevel›,
                          spine: List‹KExpr›,
                          types: List‹KExpr›,
                          top: List‹&KConstantInfo›,
                          addrs: List‹Addr›) -> (G, KExpr) {
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
  fn try_extract_int(e: KExpr, addrs: List‹Addr›) -> (G, G, KLimbs) {
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
  fn intern_int_lit(sign: G, limbs: KLimbs, addrs: List‹Addr›) -> (G, KExpr) {
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
  fn try_normalize_int_decidable(head_idx: G, head_lvls: List‹KLevel›,
                                  spine: List‹KExpr›, types: List‹KExpr›,
                                  top: List‹&KConstantInfo›,
                                  addrs: List‹Addr›) -> (G, KExpr) {
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

  fn normalize_int_dec_rebuild(head_idx: G, head_lvls: List‹KLevel›,
                                spine: List‹KExpr›, a0: KExpr, a1: KExpr,
                                types: List‹KExpr›, top: List‹&KConstantInfo›,
                                addrs: List‹Addr›) -> (G, KExpr) {
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
                         head_idx: G, head_lvls: List‹KLevel›,
                         spine: List‹KExpr›, types: List‹KExpr›,
                         top: List‹&KConstantInfo›,
                         addrs: List‹Addr›) -> (G, KExpr) {
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
                              head_idx: G, head_lvls: List‹KLevel›,
                              spine: List‹KExpr›, types: List‹KExpr›,
                              top: List‹&KConstantInfo›,
                              addrs: List‹Addr›) -> (G, KExpr) {
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
                           head_idx: G, head_lvls: List‹KLevel›,
                           spine: List‹KExpr›,
                           types: List‹KExpr›,
                           top: List‹&KConstantInfo›,
                           addrs: List‹Addr›) -> (G, KExpr) {
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
                let one_lvl = store(KLevelNode.Succ(store(KLevelNode.Zero)));
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
                       head_lvls: List‹KLevel›, spine: List‹KExpr›,
                       types: List‹KExpr›, top: List‹&KConstantInfo›,
                       addrs: List‹Addr›) -> (G, KExpr) {
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
  fn try_str_dispatch(head_addr: Addr, spine: List‹KExpr›,
                      addrs: List‹Addr›) -> (G, KExpr) {
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
  fn try_str_to_byte_array(bs: ByteStream, addrs: List‹Addr›) -> (G, KExpr) {
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
  fn try_str_back(bs: ByteStream, addrs: List‹Addr›) -> (G, KExpr) {
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

  -- Unconstrained witness generator: split `x` (< 2^32) into 4
  -- little-endian bytes. Always invoked as `#split_u32(...)`; the result
  -- is prover-provided and MUST be pinned by the caller with u8 range
  -- checks + a reconstruction assert. Division is off-circuit (untraced).
  fn split_u32(x: G) -> (G, G, G, G) {
    match divmod_256(x, 0) {
      (b0, q1) =>
        match divmod_256(q1, 0) {
          (b1, q2) =>
            match divmod_256(q2, 0) {
              (b2, q3) =>
                match divmod_256(q3, 0) {
                  (b3, _) => (b0, b1, b2, b3),
                },
            },
        },
    }
  }

  -- Convert G value (< 2^32) into single-limb KLimbs. The 4-byte
  -- decomposition is a prover-provided (unconstrained) witness, pinned by
  -- four u8 range checks + the reconstruction assert. `x >= 2^32` is
  -- rejected (assert fails) rather than silently truncated.
  fn klimbs_from_g(x: G) -> KLimbs {
    match #split_u32(x) {
      (rb0, rb1, rb2, rb3) =>
        let b0 = u8_xor(u8_from_field_unsafe(rb0), 0u8);
        let b1 = u8_xor(u8_from_field_unsafe(rb1), 0u8);
        let b2 = u8_xor(u8_from_field_unsafe(rb2), 0u8);
        let b3 = u8_xor(u8_from_field_unsafe(rb3), 0u8);
        assert_eq!(x, to_field(b0) + (256 * to_field(b1)) + (65536 * to_field(b2)) + (16777216 * to_field(b3)));
        store(ListNode.Cons([b0, b1, b2, b3, 0u8, 0u8, 0u8, 0u8],
                            store(ListNode.Nil))),
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
  fn utf8_decode_one(b0: U8, rest: ByteStream) -> (G, ByteStream) {
    match u8_less_than(b0, 128u8) {
      1 => (to_field(b0), rest),
      0 =>
        match u8_less_than(b0, 224u8) {
          1 =>
            match load(rest) {
              ListNode.Cons(b1, r1) =>
                let cp = (to_field(b0) - 192) * 64 + (to_field(b1) - 128);
                (cp, r1),
            },
          0 =>
            match u8_less_than(b0, 240u8) {
              1 =>
                match load(rest) {
                  ListNode.Cons(b1, r1) =>
                    match load(r1) {
                      ListNode.Cons(b2, r2) =>
                        let cp = (to_field(b0) - 224) * 4096 + (to_field(b1) - 128) * 64 + (to_field(b2) - 128);
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
                            let cp = (to_field(b0) - 240) * 262144 + (to_field(b1) - 128) * 4096
                                    + (to_field(b2) - 128) * 64 + (to_field(b3) - 128);
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
  fn str_lit_to_ctor(bs: ByteStream, addrs: List‹Addr›) -> (G, KExpr) {
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
                        let zero_lvl = store(KLevelNode.Zero);
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
  fn str_lit_to_ctor_or_self(e: KExpr, addrs: List‹Addr›) -> KExpr {
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
                                       addrs: List‹Addr›) -> (G, KExpr) {
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
