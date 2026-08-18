module
public import Ix.Aiur.Meta
public import Ix.IxVM.KernelTypes
public import Ix.IxVM.Kernel.Klimbs

set_option maxRecDepth 8192

public section

namespace IxVM

/-! ## Nat primitive dispatch

Nat/Str/BitVec/decidable/native reduction, mirroring
crates/kernel/src/primitive.rs. Recognizes Const-headed applications of
Nat.succ / Nat.pred / Nat.add / Nat.sub / Nat.mul / Nat.div / Nat.mod /
Nat.pow / Nat.gcd / Nat.land / Nat.lor / Nat.xor / Nat.shl / Nat.shr /
Nat.beq / Nat.ble on Nat literals (or on Nat.zero / App(Nat.succ, ...)
ctor chains) and reduces them to a Nat or Bool literal via the
`klimbs_*` bignum ops.

Recognition is by address: each primitive is identified by the 32-byte
blake3 of its Ixon serialization, hardcoded below and read straight out
of `Const(addr, _)`. Those literals are the kernel's entire notion of
"this constant IS Nat.add", so a single wrong byte silently disables a
primitive or misapplies one — `Tests/Ix/Kernel/PrimAddrs.lean` guards
every one of them against the canonical table.

Beyond literal-on-literal folding, the dispatch also produces "stuck
compact forms" for symbolic bases (`Nat.add x 3`, `x / n`): reducing
those to successor towers or unfolding the division algorithm is what
makes naive Nat reduction explode, so they are kept in offset form and
compared structurally instead.
-/

set_option maxRecDepth 16384 in
def natPrim := ⟦
  -- ============================================================================
  -- Primitive canonical addresses. Guarded by Tests/Ix/Kernel/PrimAddrs.lean.
  -- ============================================================================
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
    store([0xe1u8, 0xeeu8, 0x4cu8, 0x78u8, 0xa3u8, 0x90u8, 0x64u8, 0x64u8,
     0xfau8, 0x8cu8, 0x17u8, 0xecu8, 0x2eu8, 0xd0u8, 0xc0u8, 0xbfu8,
     0x66u8, 0xdbu8, 0x3bu8, 0x41u8, 0x2du8, 0x9bu8, 0x1cu8, 0x5fu8,
     0x31u8, 0xfbu8, 0xa7u8, 0xbbu8, 0x97u8, 0x4au8, 0x93u8, 0xe5u8])
  }

  fn nat_sub_addr() -> Addr {
    store([0xbfu8, 0x05u8, 0x8eu8, 0xe4u8, 0x46u8, 0x52u8, 0x7au8, 0xf6u8,
     0xecu8, 0x74u8, 0x92u8, 0x23u8, 0x75u8, 0x2du8, 0x07u8, 0xe6u8,
     0xd7u8, 0xc2u8, 0xdfu8, 0x8du8, 0xc0u8, 0xa0u8, 0x77u8, 0x8du8,
     0x93u8, 0x4fu8, 0x88u8, 0x5au8, 0xe8u8, 0x26u8, 0x7du8, 0x57u8])
  }

  fn nat_mul_addr() -> Addr {
    store([0xc2u8, 0xfeu8, 0x5eu8, 0xdau8, 0x1eu8, 0x55u8, 0x92u8, 0x36u8,
     0xbfu8, 0xc2u8, 0xa7u8, 0xa4u8, 0x7du8, 0xb0u8, 0xcau8, 0x6cu8,
     0xf7u8, 0x82u8, 0xf7u8, 0xb6u8, 0x9bu8, 0xddu8, 0x96u8, 0x32u8,
     0x37u8, 0xd0u8, 0x88u8, 0x9fu8, 0xbfu8, 0x9au8, 0x4bu8, 0x07u8])
  }

  fn nat_pow_addr() -> Addr {
    store([0x0au8, 0xecu8, 0x92u8, 0x31u8, 0x3eu8, 0x59u8, 0x8du8, 0x5fu8,
     0xcbu8, 0x5du8, 0xcfu8, 0x0bu8, 0x80u8, 0x39u8, 0x9cu8, 0x69u8,
     0xebu8, 0xf6u8, 0xa4u8, 0x3bu8, 0x9eu8, 0xe9u8, 0x7au8, 0x3eu8,
     0x56u8, 0x14u8, 0x36u8, 0xb9u8, 0xf2u8, 0xb9u8, 0x54u8, 0x80u8])
  }

  fn nat_gcd_addr() -> Addr {
    store([0x59u8, 0xe4u8, 0x7du8, 0x71u8, 0xd7u8, 0x3cu8, 0x54u8, 0x4eu8,
     0xe1u8, 0xa4u8, 0xedu8, 0xf0u8, 0x7eu8, 0x9fu8, 0xffu8, 0xf5u8,
     0x42u8, 0xcbu8, 0x75u8, 0x7eu8, 0x73u8, 0x96u8, 0x51u8, 0xa9u8,
     0xcdu8, 0x45u8, 0x3au8, 0xf0u8, 0x3du8, 0x3du8, 0xceu8, 0x42u8])
  }

  fn nat_mod_addr() -> Addr {
    store([0x2cu8, 0x9du8, 0x2du8, 0x3eu8, 0x7eu8, 0x97u8, 0x4bu8, 0x43u8,
     0xcau8, 0x3du8, 0x21u8, 0x2fu8, 0x32u8, 0x70u8, 0x71u8, 0x87u8,
     0x38u8, 0x21u8, 0x25u8, 0xb1u8, 0x27u8, 0x27u8, 0x58u8, 0xf6u8,
     0x9cu8, 0x4bu8, 0x47u8, 0xe9u8, 0x6du8, 0x9au8, 0xabu8, 0xcfu8])
  }

  fn nat_div_addr() -> Addr {
    store([0x2fu8, 0x12u8, 0xf3u8, 0x22u8, 0x94u8, 0xb7u8, 0xd1u8, 0x16u8,
     0x8au8, 0xdau8, 0x18u8, 0x09u8, 0xc9u8, 0xb8u8, 0xb2u8, 0x56u8,
     0x38u8, 0x24u8, 0xe9u8, 0xc2u8, 0x87u8, 0x9bu8, 0xf8u8, 0xd3u8,
     0xbbu8, 0x9bu8, 0x5cu8, 0x03u8, 0xd7u8, 0xabu8, 0x71u8, 0x31u8])
  }

  fn nat_land_addr() -> Addr {
    store([0x83u8, 0x3cu8, 0x5bu8, 0x2eu8, 0x3cu8, 0x07u8, 0x7eu8, 0xb6u8,
     0xb3u8, 0xc0u8, 0xe4u8, 0xd8u8, 0x48u8, 0xcfu8, 0x54u8, 0x08u8,
     0x24u8, 0x0cu8, 0x7du8, 0x3cu8, 0xffu8, 0x8cu8, 0x40u8, 0x63u8,
     0x5cu8, 0x6eu8, 0x3bu8, 0xf9u8, 0x46u8, 0x63u8, 0x0eu8, 0x34u8])
  }

  fn nat_lor_addr() -> Addr {
    store([0x72u8, 0x32u8, 0x09u8, 0x5au8, 0xeau8, 0x9au8, 0x5fu8, 0x79u8,
     0xccu8, 0x0fu8, 0x2bu8, 0x0au8, 0xd8u8, 0x48u8, 0xdbu8, 0xf1u8,
     0x90u8, 0x4au8, 0x63u8, 0x0fu8, 0x1eu8, 0xf8u8, 0x6fu8, 0x24u8,
     0x4fu8, 0x8au8, 0x42u8, 0xb8u8, 0x47u8, 0xafu8, 0xabu8, 0x9au8])
  }

  fn nat_xor_addr() -> Addr {
    store([0xc3u8, 0xb0u8, 0x0bu8, 0x51u8, 0x4bu8, 0x9fu8, 0x26u8, 0xdcu8,
     0x1eu8, 0xdfu8, 0x10u8, 0xc7u8, 0xd6u8, 0xf6u8, 0x9fu8, 0x45u8,
     0x5eu8, 0xf8u8, 0xedu8, 0x0cu8, 0x51u8, 0xb0u8, 0xa6u8, 0x66u8,
     0xe3u8, 0x42u8, 0x7fu8, 0xb4u8, 0x4du8, 0x3au8, 0x04u8, 0xf0u8])
  }

  fn nat_shift_left_addr() -> Addr {
    store([0x6eu8, 0x70u8, 0xcdu8, 0x9du8, 0x17u8, 0x08u8, 0xb8u8, 0xf0u8,
     0x0bu8, 0xe4u8, 0x60u8, 0x65u8, 0x5cu8, 0xa4u8, 0x7au8, 0x41u8,
     0x9du8, 0xc6u8, 0x01u8, 0xf9u8, 0xc0u8, 0x55u8, 0x8eu8, 0x7au8,
     0xc2u8, 0x12u8, 0xb8u8, 0x0eu8, 0xe6u8, 0xffu8, 0x09u8, 0x78u8])
  }

  fn nat_shift_right_addr() -> Addr {
    store([0xd8u8, 0xddu8, 0xecu8, 0x67u8, 0xd3u8, 0x2eu8, 0xebu8, 0x1fu8,
     0x2bu8, 0x0du8, 0x54u8, 0x03u8, 0x72u8, 0xedu8, 0x74u8, 0x52u8,
     0x20u8, 0xfdu8, 0xb1u8, 0xe4u8, 0xe2u8, 0xb2u8, 0xf5u8, 0x4bu8,
     0xadu8, 0xdeu8, 0x60u8, 0xb6u8, 0x67u8, 0x34u8, 0xf9u8, 0xf3u8])
  }

  fn nat_beq_addr() -> Addr {
    store([0xcau8, 0x30u8, 0x22u8, 0xa3u8, 0xc8u8, 0x35u8, 0x9bu8, 0x0cu8,
     0x43u8, 0x5eu8, 0xb4u8, 0xbbu8, 0x8eu8, 0x8eu8, 0xacu8, 0x0au8,
     0xa0u8, 0x85u8, 0xd1u8, 0xdau8, 0x10u8, 0xf2u8, 0x59u8, 0x28u8,
     0x70u8, 0x25u8, 0x22u8, 0x98u8, 0x61u8, 0x11u8, 0x20u8, 0x70u8])
  }

  fn nat_ble_addr() -> Addr {
    store([0xcau8, 0x4bu8, 0x39u8, 0x8bu8, 0x20u8, 0x80u8, 0xbeu8, 0xccu8,
     0xccu8, 0xf3u8, 0xa3u8, 0x12u8, 0x1eu8, 0x84u8, 0x8bu8, 0xd1u8,
     0x97u8, 0x78u8, 0x47u8, 0x66u8, 0x8cu8, 0x18u8, 0xa6u8, 0x44u8,
     0x7bu8, 0x0eu8, 0xdcu8, 0x5fu8, 0x56u8, 0x1bu8, 0x1cu8, 0xbcu8])
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

  -- Native primitives ()
  fn system_platform_num_bits_addr() -> Addr {
    store([0xa9u8, 0x16u8, 0x24u8, 0x44u8, 0x53u8, 0x93u8, 0xa6u8, 0x74u8,
     0xfau8, 0x0fu8, 0x9eu8, 0x9fu8, 0x9au8, 0x52u8, 0xf4u8, 0x1bu8,
     0x93u8, 0xb1u8, 0x04u8, 0x87u8, 0x01u8, 0x80u8, 0x46u8, 0xcbu8,
     0xc1u8, 0x26u8, 0x5au8, 0x24u8, 0x55u8, 0xbcu8, 0xfau8, 0xecu8])
  }

  fn punit_size_of_1_addr() -> Addr {
    store([0x7bu8, 0xd8u8, 0xe1u8, 0x9fu8, 0x47u8, 0xf6u8, 0xeau8, 0xe6u8,
     0x20u8, 0xa5u8, 0xc3u8, 0x9fu8, 0x24u8, 0x3cu8, 0xe4u8, 0x15u8,
     0xddu8, 0x6au8, 0x77u8, 0xf0u8, 0x95u8, 0x90u8, 0xf4u8, 0xc2u8,
     0x27u8, 0xceu8, 0xf3u8, 0x63u8, 0x00u8, 0x7fu8, 0x40u8, 0x12u8])
  }

  -- Compiler-emitted native reduction primitives.
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

  fn subtype_val_addr() -> Addr {
    store([0x0cu8, 0x70u8, 0x72u8, 0xa9u8, 0x27u8, 0xb1u8, 0xc4u8, 0x6eu8,
     0xfcu8, 0x94u8, 0x98u8, 0xe7u8, 0x49u8, 0xb8u8, 0x32u8, 0x0bu8,
     0x74u8, 0xd8u8, 0x99u8, 0x4eu8, 0xc2u8, 0x80u8, 0x60u8, 0x16u8,
     0x28u8, 0xbfu8, 0xaeu8, 0xe1u8, 0xadu8, 0xe3u8, 0x6cu8, 0x71u8])
  }

  fn system_platform_get_num_bits_addr() -> Addr {
    store([0x66u8, 0xf2u8, 0x9bu8, 0xe6u8, 0xe0u8, 0x0au8, 0xc8u8, 0x35u8,
     0x63u8, 0x8au8, 0x28u8, 0x14u8, 0x98u8, 0x8fu8, 0x9cu8, 0xf1u8,
     0x65u8, 0x47u8, 0xbeu8, 0xbbu8, 0x07u8, 0x63u8, 0x52u8, 0x7cu8,
     0x11u8, 0x9bu8, 0xcau8, 0x51u8, 0xd7u8, 0xb0u8, 0xbdu8, 0xd5u8])
  }

  fn size_of_size_of_addr() -> Addr {
    store([0xa3u8, 0x43u8, 0xa6u8, 0x51u8, 0xbfu8, 0xf4u8, 0x08u8, 0xc3u8,
     0xa2u8, 0x9fu8, 0xf2u8, 0x7bu8, 0x2bu8, 0x62u8, 0xe3u8, 0x4bu8,
     0x54u8, 0xb2u8, 0xabu8, 0x38u8, 0x1cu8, 0xf6u8, 0xf3u8, 0xadu8,
     0x87u8, 0xc5u8, 0x40u8, 0xc9u8, 0x77u8, 0xdcu8, 0x3cu8, 0x4au8])
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

  fn is_native_prim_addr(a: Addr) -> G {
    match address_eq(a, system_platform_num_bits_addr()) {
      1 => 1,
      _ =>
      match address_eq(a, punit_size_of_1_addr()) {
        1 => 1,
        _ =>
        match address_eq(a, reduce_bool_addr()) {
          1 => 1,
          _ =>
          match address_eq(a, reduce_nat_addr()) {
            1 => 1,
            _ =>
            match address_eq(a, subtype_val_addr()) {
              1 => 1,
              _ =>
              match address_eq(a, size_of_size_of_addr()) {
                1 => 1,
                _ => 0,
              },
            },
          },
        },
      },
    }
  }

  fn mk_nat_literal_64() -> KExpr {
    let limbs = store(ListNode.Cons(
      [64u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    store(KExprNode.Lit(KLiteral.Nat(limbs)))
  }

  fn mk_nat_one() -> KExpr {
    let limbs = store(ListNode.Cons(
      [1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], store(ListNode.Nil)));
    store(KExprNode.Lit(KLiteral.Nat(limbs)))
  }

  -- Native reduce dispatch.
  --   numBits (nullary)      → Lit(Nat 64)
  --   PUnit.SizeOf.1 (nul)   → Lit(Nat 1)
  --   Lean.reduceBool arg    → whnf arg; accept Const(Bool.true|Bool.false)
  --   Lean.reduceNat arg     → whnf arg; accept Lit(Nat _)
  fn try_native_dispatch(head_addr: Addr, spine: List‹KExpr›,
                             types: List‹KExpr›) -> (G, KExpr) {
    match address_eq(head_addr, system_platform_num_bits_addr()) {
      1 => (1, mk_nat_literal_64()),
      _ =>
      match address_eq(head_addr, punit_size_of_1_addr()) {
        1 => (1, mk_nat_one()),
        _ =>
        match address_eq(head_addr, subtype_val_addr()) {
          1 => try_reduce_subtype_val(spine),
          _ =>
          match address_eq(head_addr, size_of_size_of_addr()) {
            1 => try_reduce_size_of_unit(spine),
            _ =>
              let is_rb = address_eq(head_addr, reduce_bool_addr());
              let is_rn = address_eq(head_addr, reduce_nat_addr());
              match is_rb + is_rn {
                0 => (0, store(KExprNode.BVar(0))),
                _ =>
                  match u32_less_than(list_length(spine), 1) {
                    1 => (0, store(KExprNode.BVar(0))),
                    _ =>
                      let arg = list_lookup(spine, 0);
                      let result = whnf(arg, types);
                      match is_rb {
                        1 => check_native_bool(result),
                        _ => check_native_nat(result),
                      },
                  },
              },
          },
        },
      },
    }
  }

  -- Subtype.val A P (System.Platform.getNumBits ()) → 64.
  -- Spine: [A, P, val_arg]. val_arg's spine head must = getNumBits.
  fn try_reduce_subtype_val(spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 3) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        match collect_spine(list_lookup(spine, 2)) {
          (head, _) =>
            match load(head) {
              KExprNode.Const(caddr, _) =>
                match address_eq(caddr, system_platform_get_num_bits_addr()) {
                  1 => (1, mk_nat_literal_64()),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  -- SizeOf.sizeOf.{u} Unit/PUnit ... → 1. First arg = type.
  fn try_reduce_size_of_unit(spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 1) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        match collect_spine(list_lookup(spine, 0)) {
          (head, _) =>
            match load(head) {
              KExprNode.Const(caddr, _) =>
                match address_eq(caddr, unit_addr()) {
                  1 => (1, mk_nat_one()),
                  _ =>
                    match address_eq(caddr, punit_addr()) {
                      1 => (1, mk_nat_one()),
                      _ => (0, store(KExprNode.BVar(0))),
                    },
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  fn check_native_bool(e: KExpr) -> (G, KExpr) {
    match load(e) {
      KExprNode.Const(caddr, _) =>
        let is_t = address_eq(caddr, bool_true_addr());
        let is_f = address_eq(caddr, bool_false_addr());
        match is_t + is_f {
          0 => (0, store(KExprNode.BVar(0))),
          _ => (1, e),
        },
      _ => (0, store(KExprNode.BVar(0))),
    }
  }

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

  -- BitVec primitives ()
  fn bit_vec_to_nat_addr() -> Addr {
    store([0xe3u8, 0x2au8, 0xb4u8, 0xe7u8, 0x72u8, 0x0du8, 0x34u8, 0x42u8,
     0xa2u8, 0x66u8, 0xb3u8, 0x7cu8, 0x97u8, 0xa2u8, 0x72u8, 0x18u8,
     0xe6u8, 0x82u8, 0x39u8, 0x31u8, 0x83u8, 0x11u8, 0xf8u8, 0xe4u8,
     0xb0u8, 0x46u8, 0xa6u8, 0xbdu8, 0xdeu8, 0x52u8, 0x03u8, 0x74u8])
  }

  fn bit_vec_of_nat_addr() -> Addr {
    store([0x3bu8, 0x33u8, 0x4cu8, 0x94u8, 0xddu8, 0x56u8, 0xd8u8, 0x0bu8,
     0xebu8, 0x4eu8, 0xffu8, 0x5du8, 0x82u8, 0x5fu8, 0x67u8, 0xf6u8,
     0xf1u8, 0xacu8, 0x4eu8, 0x14u8, 0x04u8, 0x03u8, 0x69u8, 0x9eu8,
     0x3du8, 0xafu8, 0xf5u8, 0x2au8, 0x00u8, 0xbdu8, 0xbfu8, 0x6eu8])
  }

  fn bit_vec_addr() -> Addr {
    store([0x67u8, 0xf4u8, 0x74u8, 0xb8u8, 0xc3u8, 0x30u8, 0x2bu8, 0x04u8,
     0x41u8, 0x7fu8, 0x72u8, 0x1fu8, 0xf3u8, 0xe8u8, 0x8cu8, 0xe6u8,
     0xf1u8, 0x6au8, 0x7du8, 0xfcu8, 0xb3u8, 0xbau8, 0xe9u8, 0x93u8,
     0x68u8, 0x08u8, 0x5du8, 0x1cu8, 0x5eu8, 0x87u8, 0x2bu8, 0xa4u8])
  }

  fn bit_vec_ult_addr() -> Addr {
    store([0x4fu8, 0x9du8, 0x4eu8, 0x0cu8, 0x70u8, 0xe1u8, 0x6cu8, 0x78u8,
     0xe0u8, 0xedu8, 0xa3u8, 0x8eu8, 0x2du8, 0x6du8, 0x94u8, 0xccu8,
     0xd1u8, 0x25u8, 0x98u8, 0x75u8, 0x5eu8, 0x0eu8, 0x72u8, 0x00u8,
     0xa9u8, 0x23u8, 0x9du8, 0xa9u8, 0x2bu8, 0x90u8, 0x57u8, 0xccu8])
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

  fn is_bitvec_prim_addr(a: Addr) -> G {
    match address_eq(a, bit_vec_to_nat_addr()) {
      1 => 1,
      _ =>
      match address_eq(a, bit_vec_ult_addr()) {
        1 => 1,
        _ =>
        match address_eq(a, decidable_decide_addr()) {
          1 => 1,
          _ => 0,
        },
      },
    }
  }

  -- Bool value (0/1) → Const(Bool.false/Bool.true).
  fn mk_bool(g: G) -> KExpr {
    match g {
      0 => store(KExprNode.Const(bool_false_addr(), store(ListNode.Nil))),
      _ => store(KExprNode.Const(bool_true_addr(), store(ListNode.Nil))),
    }
  }

  -- Compute BitVec.toNat internally: given (width_e, val_e), returns
  -- (1, N mod 2^W) as KLimbs. (0, _) on miss.
  fn bv_to_nat_via(width_e: KExpr, val_e: KExpr) -> (G, KLimbs) {
    match bitvec_of_nat_args_direct(val_e) {
      (0, _, _) => (0, store(ListNode.Nil)),
      (1, val_width, n_e) =>
        match try_extract_nat(n_e) {
          (0, _) => (0, store(ListNode.Nil)),
          (1, n_kl) =>
            match try_extract_nat(val_width) {
              (0, _) => (0, store(ListNode.Nil)),
              (1, w_kl) =>
                let two = store(ListNode.Cons(
                  [2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                  store(ListNode.Nil)));
                let modulus = klimbs_pow(two, w_kl);
                (1, klimbs_normalize(klimbs_mod(n_kl, modulus))),
            },
        },
    }
  }

  -- BitVec.ult width lhs rhs → mk_bool(lhs_nat < rhs_nat)
  fn try_reduce_bit_vec_ult(spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 3) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let width_e = list_lookup(spine, 0);
        let lhs_e = list_lookup(spine, 1);
        let rhs_e = list_lookup(spine, 2);
        match bv_to_nat_via(width_e, lhs_e) {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, lhs_n) =>
            match bv_to_nat_via(width_e, rhs_e) {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, rhs_n) =>
                -- lhs < rhs iff !(rhs ≤ lhs)
                let r = 1 - klimbs_le(rhs_n, lhs_n);
                (1, mk_bool(r)),
            },
        },
    }
  }

  -- decide (LT.lt BitVec width lhs rhs) inst → bit_vec_ult.
  fn try_reduce_decide_bitvec_lt(spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let prop = list_lookup(spine, 0);
        match collect_spine(prop) {
          (lt_head, lt_args) =>
            match load(lt_head) {
              KExprNode.Const(lt_caddr, _) =>
                match address_eq(lt_caddr, lt_lt_addr()) {
                  0 => (0, store(KExprNode.BVar(0))),
                  _ =>
                    match u32_less_than(list_length(lt_args), 4) {
                      1 => (0, store(KExprNode.BVar(0))),
                      _ =>
                        let ty_arg = list_lookup(lt_args, 0);
                        match collect_spine(ty_arg) {
                          (ty_head, ty_args) =>
                            match load(ty_head) {
                              KExprNode.Const(ty_caddr, _) =>
                                match address_eq(ty_caddr, bit_vec_addr()) {
                                  0 => (0, store(KExprNode.BVar(0))),
                                  _ =>
                                    match u32_less_than(list_length(ty_args), 1) {
                                      1 => (0, store(KExprNode.BVar(0))),
                                      _ =>
                                        let width = list_lookup(ty_args, 0);
                                        let lhs = list_lookup(lt_args, 2);
                                        let rhs = list_lookup(lt_args, 3);
                                        let inner = store(ListNode.Cons(width,
                                          store(ListNode.Cons(lhs,
                                            store(ListNode.Cons(rhs,
                                              store(ListNode.Nil)))))));
                                        try_reduce_bit_vec_ult(inner),
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

  -- Extract (width, value) from `BitVec.ofNat W N` shape. Returns
  -- (1, W, N) or (0, _, _). Direct form only: the `OfNat.ofNat`-wrapped
  -- form is not recognized here, so a wrapped literal stays stuck rather
  -- than folding.
  fn bitvec_of_nat_args_direct(e: KExpr) -> (G, KExpr, KExpr) {
    match collect_spine(e) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(caddr, _) =>
            match address_eq(caddr, bit_vec_of_nat_addr()) {
              1 =>
                match list_length(args) - 2 {
                  0 => (1, list_lookup(args, 0), list_lookup(args, 1)),
                  _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0)), store(KExprNode.BVar(0))),
        },
    }
  }

  -- BitVec.toNat / BitVec.ult / decide(BitVec.lt) dispatch.
  -- toNat + ult prep spine (whnf inner (W, N) args first). decide
  -- inspects prop head shape — no pre-whnf (avoid cascading Defn
  -- unfolds on arbitrary Prop args).
  fn try_bitvec_dispatch(head_addr: Addr, spine: List‹KExpr›,
                              types: List‹KExpr›) -> (G, KExpr) {
    match address_eq(head_addr, bit_vec_to_nat_addr()) {
      1 =>
        match u32_less_than(list_length(spine), 2) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let spine_p = bitvec_prep_spine(spine, types);
            let width_e = list_lookup(spine_p, 0);
            let val_e = list_lookup(spine_p, 1);
            match bv_to_nat_via(width_e, val_e) {
              (0, _) => (0, store(KExprNode.BVar(0))),
              (1, kl) => (1, mk_nat_lit(kl)),
            },
        },
      _ =>
        match address_eq(head_addr, bit_vec_ult_addr()) {
          1 =>
            let spine_p = bitvec_prep_spine_ult(spine, types);
            try_reduce_bit_vec_ult(spine_p),
          _ =>
            match address_eq(head_addr, decidable_decide_addr()) {
              1 => try_reduce_decide_bitvec_lt(spine),
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  -- BitVec.ult prep: whnf [width, lhs, rhs] and recursively whnf each
  -- BitVec.ofNat inner args, mirror bitvec_prep_spine (toNat) shape.
  fn bitvec_prep_spine_ult(spine: List‹KExpr›, types: List‹KExpr›)
                                -> List‹KExpr› {
    let sw = whnf_spine(spine, types);
    match load(sw) {
      ListNode.Nil => sw,
      ListNode.Cons(width_e, r1) =>
        match load(r1) {
          ListNode.Nil => sw,
          ListNode.Cons(lhs_e, r2) =>
            match load(r2) {
              ListNode.Nil => sw,
              ListNode.Cons(rhs_e, tail) =>
                let lhs_p = np_whnf_inner_bv(lhs_e, types);
                let rhs_p = np_whnf_inner_bv(rhs_e, types);
                store(ListNode.Cons(width_e,
                  store(ListNode.Cons(lhs_p,
                    store(ListNode.Cons(rhs_p, tail)))))),
            },
        },
    }
  }

  -- If e = App*(head, args), whnf each arg once.
  fn np_whnf_inner_bv(e: KExpr, types: List‹KExpr›) -> KExpr {
    match collect_spine(e) {
      (h, a) => apply_spine(h, whnf_spine(a, types)),
    }
  }

  -- String primitives ()
  fn string_utf8_byte_size_addr() -> Addr {
    store([0x51u8, 0x86u8, 0xd9u8, 0x1eu8, 0xf8u8, 0x89u8, 0x2eu8, 0x48u8,
     0xebu8, 0x02u8, 0x91u8, 0x8bu8, 0x09u8, 0x26u8, 0xe9u8, 0x76u8,
     0x7cu8, 0x6du8, 0x4bu8, 0x9bu8, 0x08u8, 0x14u8, 0x06u8, 0x4au8,
     0x44u8, 0x9au8, 0x5au8, 0xfeu8, 0x8au8, 0x9eu8, 0x5au8, 0x6eu8])
  }

  -- Native string-value fast paths (mirror crates/kernel/src/primitive.rs
  -- `string_append` / `string_dec_eq`): literal append and literal
  -- decidable equality reduce natively in whnf, keeping evaluator-grade
  -- string values out of the structural ByteArray/UTF-8 model.
  fn string_append_addr() -> Addr {
    store([0xffu8, 0x45u8, 0x95u8, 0x54u8, 0xdfu8, 0xdcu8, 0x34u8, 0xd1u8,
     0x59u8, 0x02u8, 0x70u8, 0x38u8, 0x17u8, 0x45u8, 0x71u8, 0xb7u8,
     0x70u8, 0x46u8, 0x4du8, 0x52u8, 0x83u8, 0x4cu8, 0x1du8, 0xbcu8,
     0x64u8, 0x36u8, 0x46u8, 0x7fu8, 0xa8u8, 0x1du8, 0x03u8, 0x9eu8])
  }

  fn string_of_list_addr() -> Addr {
    store([0x0fu8, 0x02u8, 0x50u8, 0xd7u8, 0x71u8, 0x37u8, 0x04u8, 0x43u8,
     0x90u8, 0x73u8, 0xbau8, 0xbdu8, 0x51u8, 0x1bu8, 0x77u8, 0xa9u8,
     0xeeu8, 0xeau8, 0xe5u8, 0xadu8, 0xbdu8, 0x50u8, 0xffu8, 0x57u8,
     0x4du8, 0x80u8, 0x1fu8, 0xfbu8, 0x55u8, 0x81u8, 0x28u8, 0xd9u8])
  }

  fn char_of_nat_addr() -> Addr {
    store([0x09u8, 0xeeu8, 0xb4u8, 0x16u8, 0xc8u8, 0x40u8, 0x76u8, 0x66u8,
     0x64u8, 0x57u8, 0x41u8, 0x7fu8, 0x4bu8, 0x7cu8, 0xe3u8, 0xd1u8,
     0xbfu8, 0x34u8, 0x97u8, 0x7du8, 0x3fu8, 0x56u8, 0xddu8, 0x25u8,
     0x62u8, 0xc0u8, 0x01u8, 0x4au8, 0x51u8, 0xcbu8, 0x8du8, 0x34u8])
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

  fn char_type_addr() -> Addr {
    store([0x20u8, 0x3bu8, 0x76u8, 0xc5u8, 0xb4u8, 0xf5u8, 0xcau8, 0x06u8,
     0x15u8, 0x63u8, 0x31u8, 0x40u8, 0x57u8, 0xa9u8, 0x43u8, 0xbcu8,
     0x43u8, 0x80u8, 0x88u8, 0x5eu8, 0x73u8, 0xd0u8, 0xefu8, 0xafu8,
     0x14u8, 0x64u8, 0x45u8, 0x98u8, 0xc2u8, 0xfau8, 0x6eu8, 0xeeu8])
  }

  fn string_back_addr() -> Addr {
    store([0x54u8, 0x8bu8, 0xbfu8, 0x22u8, 0xbau8, 0x30u8, 0x5fu8, 0x8eu8,
     0x36u8, 0x3eu8, 0xdfu8, 0x99u8, 0x07u8, 0xd0u8, 0xc2u8, 0xc4u8,
     0x54u8, 0xadu8, 0xd4u8, 0x16u8, 0xddu8, 0xbfu8, 0x25u8, 0xb3u8,
     0x8cu8, 0x76u8, 0xd0u8, 0x06u8, 0x3au8, 0xd2u8, 0x1du8, 0x65u8])
  }

  fn string_legacy_back_addr() -> Addr {
    store([0xefu8, 0x4eu8, 0x74u8, 0xe4u8, 0x4eu8, 0x3bu8, 0xb9u8, 0xfau8,
     0x5eu8, 0x54u8, 0x88u8, 0xa4u8, 0x6cu8, 0x5bu8, 0x4du8, 0x61u8,
     0xfbu8, 0xfdu8, 0x70u8, 0x1eu8, 0x36u8, 0x79u8, 0xc5u8, 0xbfu8,
     0xb4u8, 0x15u8, 0x4cu8, 0x87u8, 0x47u8, 0xceu8, 0xfdu8, 0xc9u8])
  }

  fn string_to_byte_array_addr() -> Addr {
    store([0x87u8, 0x09u8, 0xf5u8, 0x70u8, 0xa8u8, 0x19u8, 0x32u8, 0x52u8,
     0x18u8, 0x2au8, 0x9eu8, 0xcdu8, 0x71u8, 0x3fu8, 0x89u8, 0x0eu8,
     0x75u8, 0xd3u8, 0xbfu8, 0xb5u8, 0xa2u8, 0x7fu8, 0x5bu8, 0x91u8,
     0x81u8, 0xccu8, 0xabu8, 0xe0u8, 0x65u8, 0x4au8, 0x0cu8, 0x29u8])
  }

  fn byte_array_empty_addr() -> Addr {
    store([0x0du8, 0x23u8, 0x63u8, 0xd6u8, 0x03u8, 0x5cu8, 0xc7u8, 0xc0u8,
     0x33u8, 0x1fu8, 0xffu8, 0x5cu8, 0xa1u8, 0xdeu8, 0x7bu8, 0x40u8,
     0x91u8, 0x25u8, 0x1bu8, 0x50u8, 0x4du8, 0x44u8, 0xeeu8, 0xb2u8,
     0x85u8, 0x09u8, 0x93u8, 0xbdu8, 0x0du8, 0xddu8, 0xe2u8, 0x22u8])
  }

  fn string_dec_eq_addr() -> Addr {
    store([0x14u8, 0xcfu8, 0x51u8, 0x9bu8, 0x05u8, 0xc3u8, 0x03u8, 0x84u8,
     0xfdu8, 0x4cu8, 0xb2u8, 0xe2u8, 0x71u8, 0xb0u8, 0x89u8, 0x6fu8,
     0xe2u8, 0x3eu8, 0x74u8, 0xc9u8, 0x95u8, 0x01u8, 0x0du8, 0x42u8,
     0xebu8, 0x1fu8, 0xfcu8, 0xe1u8, 0x49u8, 0x27u8, 0xe5u8, 0x6bu8])
  }

  fn string_type_addr() -> Addr {
    store([0xfdu8, 0x53u8, 0xe8u8, 0xdcu8, 0xe8u8, 0x2du8, 0x56u8, 0x8bu8,
     0x56u8, 0xe9u8, 0xb1u8, 0x6cu8, 0x39u8, 0x0bu8, 0x56u8, 0x93u8,
     0xc1u8, 0x37u8, 0xb4u8, 0xe5u8, 0x4du8, 0x12u8, 0xacu8, 0x09u8,
     0xaau8, 0x55u8, 0x98u8, 0x63u8, 0x95u8, 0x4bu8, 0x65u8, 0x87u8])
  }

  -- Address is a string primitive.
  fn is_str_prim_addr(a: Addr) -> G {
    match address_eq(a, string_utf8_byte_size_addr()) {
      1 => 1,
      _ =>
      match address_eq(a, string_append_addr()) {
        1 => 1,
        _ =>
        match address_eq(a, string_of_list_addr()) {
          1 => 1,
          _ =>
          match address_eq(a, string_back_addr()) {
            1 => 1,
            _ =>
            match address_eq(a, string_legacy_back_addr()) {
              1 => 1,
              _ =>
              match address_eq(a, string_to_byte_array_addr()) {
                1 => 1,
                _ =>
                match address_eq(a, string_dec_eq_addr()) {
                  1 => 1,
                  _ => 0,
                },
              },
            },
          },
        },
      },
    }
  }


  -- String primitive dispatch. Handles:
  -- - String.utf8ByteSize (Lit(Str))          -> Lit(Nat len)
  -- - String.append (Lit(Str), Lit(Str))      -> Lit(Str concat)
  -- - String.ofList / String.mk (char-list)   -> Lit(Str) via UTF-8 fold
  -- Caller pre-whnfs spine's outermost args; the ofList arm recursively
  -- whnfs Cons tails to reach further literal-ctor nodes.
  fn try_str_dispatch(head_addr: Addr, spine: List‹KExpr›,
                          types: List‹KExpr›) -> (G, KExpr) {
    let spine_len = list_length(spine);
    match address_eq(head_addr, string_of_list_addr()) {
      1 =>
        match spine_len {
          1 =>
            match walk_char_list_bytes(list_lookup(spine, 0), types) {
              (1, bs) => (1, store(KExprNode.Lit(KLiteral.Str(bs)))),
              (0, _) => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
      _ =>
    match address_eq(head_addr, string_utf8_byte_size_addr()) {
      1 =>
        match u32_less_than(spine_len, 1) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let a0 = list_lookup(spine, 0);
            match load(a0) {
              KExprNode.Lit(lit) =>
                match lit {
                  KLiteral.Str(bs) =>
                    -- The length must be a CANONICAL `KLimbs`, because
                    -- `klimbs_eq` — behind `Nat.beq`/`Nat.decEq`/
                    -- `literal_eq` — compares limbs without normalizing.
                    -- `klimbs_from_g` range-checks and pins its byte
                    -- decomposition (so a length >= 256 lands in the right
                    -- limb instead of an out-of-range digit), and
                    -- `klimbs_normalize` strips the all-zero limb so the
                    -- empty string yields the canonical zero rather than
                    -- `[[0;8]]`.
                    let limbs =
                      klimbs_normalize(klimbs_from_g(list_length(bs)));
                    (1, store(KExprNode.Lit(KLiteral.Nat(limbs)))),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
      _ =>
    match address_eq(head_addr, string_back_addr()) {
      1 => try_str_back(spine),
      _ =>
    match address_eq(head_addr, string_legacy_back_addr()) {
      1 => try_str_back(spine),
      _ =>
    match address_eq(head_addr, string_to_byte_array_addr()) {
      1 => try_str_to_byte_array(spine),
      _ =>
    match address_eq(head_addr, string_dec_eq_addr()) {
      1 => try_str_dec_eq(head_addr, spine, types),
      _ =>
        match address_eq(head_addr, string_append_addr()) {
          1 =>
            match u32_less_than(spine_len, 2) {
              1 => (0, store(KExprNode.BVar(0))),
              _ =>
                let a0 = list_lookup(spine, 0);
                let a1 = list_lookup(spine, 1);
                match load(a0) {
                  KExprNode.Lit(la) =>
                    match la {
                      KLiteral.Str(sa) =>
                        match load(a1) {
                          KExprNode.Lit(lb) =>
                            match lb {
                              KLiteral.Str(sb) =>
                                let joined = list_concat(sa, sb);
                                (1, store(KExprNode.Lit(KLiteral.Str(joined)))),
                              _ => (0, store(KExprNode.BVar(0))),
                            },
                          _ => (0, store(KExprNode.BVar(0))),
                        },
                      _ => (0, store(KExprNode.BVar(0))),
                    },
                  _ => (0, store(KExprNode.BVar(0))),
                },
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    },
    },
    },
    },
    },
    }
  }

  -- String.back / legacy_back over Lit(Str(bs)) →
  -- App(Const(char_of_nat), Lit(Nat last_cp)). Empty bs → 65 ('A').
  fn try_str_back(spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 1) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        match load(list_lookup(spine, 0)) {
          KExprNode.Lit(lit) =>
            match lit {
              KLiteral.Str(bs) =>
                let cp = utf8_last_codepoint(bs);
                let cp_limbs = klimbs_from_g(cp);
                let cp_lit = store(KExprNode.Lit(KLiteral.Nat(cp_limbs)));
                let con = store(KExprNode.Const(char_of_nat_addr(),
                                                 store(ListNode.Nil)));
                (1, store(KExprNode.App(con, cp_lit))),
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- String.toByteArray on Lit(Str "")  →  Const(byte_array_empty).
  -- Non-empty bails to structural (caller falls back to Defn unfold).
  fn try_str_to_byte_array(spine: List‹KExpr›) -> (G, KExpr) {
    match u32_less_than(list_length(spine), 1) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        match load(list_lookup(spine, 0)) {
          KExprNode.Lit(lit) =>
            match lit {
              KLiteral.Str(bs) =>
                match load(bs) {
                  ListNode.Nil =>
                    (1, store(KExprNode.Const(byte_array_empty_addr(),
                                                store(ListNode.Nil)))),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (0, store(KExprNode.BVar(0))),
        },
    }
  }

  -- Walk byte stream forward decoding UTF-8; return last codepoint.
  -- Empty → 65 ('A') per Rust default.
  -- Validate an entire byte stream as UTF-8, aborting on the first
  -- malformed scalar. `utf8_decode_one` already rejects out-of-range
  -- continuation bytes, stray continuations as leaders, and overlong
  -- forms, so walking the stream with it is exactly the reference
  -- kernels' `String::from_utf8` check at ingress.
  --
  -- Needed at Str-literal CONVERSION, not just during string reduction:
  -- `KLiteral.Str` is typed `String` by `k_infer_lit` without inspecting
  -- the bytes, so a literal that is never decoded would otherwise
  -- typecheck as a `String` that no Lean `String` corresponds to.
  fn utf8_validate(bs: ByteStream) {
    match load(bs) {
      ListNode.Nil => (),
      ListNode.Cons(b0, rest) =>
        match utf8_decode_one(b0, rest) {
          (_, remaining) => utf8_validate(remaining),
        },
    }
  }

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
  -- A UTF-8 continuation byte is `10xxxxxx`, i.e. in [0x80, 0xC0). Only
  -- that range decodes to a 6-bit payload; matching the two valid-range
  -- outcomes makes any other byte fall off the match and abort (the
  -- kernel's reject). Both bounds are load-bearing for soundness, not
  -- conformance nicety: a byte < 0x80 makes `to_field(b) - 128` wrap to a
  -- ~2^64 field element, and a byte >= 0xC0 makes the payload spill into
  -- [64,128), so e.g. `[0xC0, 0xC0]` would decode to codepoint 64 and
  -- alias the valid char `'@'`.
  fn utf8_cont(b: U8) -> G {
    match u8_less_than(b, 128u8) {
      0 =>
        match u8_less_than(b, 192u8) {
          1 => to_field(b) - 128,
        },
    }
  }

  -- Decode one UTF-8 scalar, validating just enough to be INJECTIVE: no
  -- two distinct byte sequences may decode to the same codepoint, or the
  -- expanded `String.ofList` forms alias and def_eq accepts a false string
  -- equality. That requires (a) continuation bytes in range (`utf8_cont`),
  -- and (b) the per-length overlong minimum, so a codepoint that has a
  -- shorter valid encoding cannot also be produced by a longer one. The
  -- reference kernels validate the whole blob as UTF-8 at ingress; this is
  -- the same rejection, done per scalar. Surrogates and codepoints beyond
  -- 0x10FFFF are NOT rejected here: they produce unique codepoints that no
  -- valid char reaches, so they cannot alias, and the downstream
  -- `Char.ofNat` scalar guard leaves them stuck rather than folding them
  -- into a valid char.
  fn utf8_decode_one(b0: U8, rest: ByteStream) -> (G, ByteStream) {
    match u8_less_than(b0, 128u8) {
      1 => (to_field(b0), rest),
      _ =>
        -- Reject stray continuation bytes [0x80, 0xC2) as leaders: [0x80,
        -- 0xC0) are continuations, and 0xC0/0xC1 only ever encode overlong
        -- two-byte forms. Valid multi-byte leaders are >= 0xC2.
        match u8_less_than(b0, 194u8) {
          0 =>
            match u8_less_than(b0, 224u8) {
              1 =>
                match load(rest) {
                  ListNode.Cons(b1, r1) =>
                    -- Two-byte cp is >= 0x80 for every leader >= 0xC2, so
                    -- no overlong is reachable once the leader is gated.
                    let cp = (to_field(b0) - 192) * 64 + utf8_cont(b1);
                    (cp, r1),
                },
              _ =>
                match u8_less_than(b0, 240u8) {
                  1 =>
                    match load(rest) {
                      ListNode.Cons(b1, r1) =>
                        match load(r1) {
                          ListNode.Cons(b2, r2) =>
                            let cp = (to_field(b0) - 224) * 4096
                                   + utf8_cont(b1) * 64
                                   + utf8_cont(b2);
                            -- Overlong: a real three-byte scalar is
                            -- >= 0x800. Reject anything below (e.g.
                            -- [0xE0,0x80,0x80] -> 0, which would alias
                            -- the one-byte NUL).
                            match u32_less_than(cp, 2048) {
                              0 => (cp, r2),
                            },
                        },
                    },
                  _ =>
                    match load(rest) {
                      ListNode.Cons(b1, r1) =>
                        match load(r1) {
                          ListNode.Cons(b2, r2) =>
                            match load(r2) {
                              ListNode.Cons(b3, r3) =>
                                let cp = (to_field(b0) - 240) * 262144
                                       + utf8_cont(b1) * 4096
                                       + utf8_cont(b2) * 64
                                       + utf8_cont(b3);
                                -- Overlong: a real four-byte scalar is
                                -- >= 0x10000.
                                match u32_less_than(cp, 65536) {
                                  0 => (cp, r3),
                                },
                            },
                        },
                    },
                },
            },
        },
    }
  }

  -- Mirror of Rust `def_eq.rs::str_lit_to_constructor`. Expands
  -- Lit(Str(bs)) to ctor form
  -- `String.ofList (List.cons.{0} Char (Char.ofNat c) (... List.nil.{0} Char))`.
  -- Emits the constants unconditionally, with no check that they are
  -- present in the env: they are listed in `synthesizedPrimNames`, so the
  -- harness always seeds their bytes.
  fn str_lit_to_ctor(bs: ByteStream) -> KExpr {
    let zero_lvl = store(KLevelNode.Zero);
    let ulvls = store(ListNode.Cons(zero_lvl, store(ListNode.Nil)));
    let nil_const = store(KExprNode.Const(list_nil_addr(), ulvls));
    let cons_const = store(KExprNode.Const(list_cons_addr(), ulvls));
    let char_const = store(KExprNode.Const(char_type_addr(), store(ListNode.Nil)));
    let con_const = store(KExprNode.Const(char_of_nat_addr(), store(ListNode.Nil)));
    let str_const = store(KExprNode.Const(string_of_list_addr(), store(ListNode.Nil)));
    let nil_app = store(KExprNode.App(nil_const, char_const));
    let cons_partial = store(KExprNode.App(cons_const, char_const));
    let list_expr = build_char_list(bs, nil_app, cons_partial, con_const);
    store(KExprNode.App(str_const, list_expr))
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

  -- Mirror str_lit_delta_step (Primitive.lean:3074): take ONE delta
  -- step past `String.ofList` when it is a Defn, settling the body with
  -- whnf_nd — a plain whnf of the ofList application would fold straight
  -- back into the Str literal via the native ofList collapse.
  fn str_lit_delta_step(expanded: KExpr, types: List‹KExpr›) -> KExpr {
    match load(expanded) {
      KExprNode.App(f, list_arg) =>
        match load(f) {
          KExprNode.Const(caddr, _) =>
            let ci = load(get_ci(caddr));
            match ci {
              KConstantInfo.Defn(_, _, value, _, _) =>
                let body = expr_inst_levels(value, store(ListNode.Nil));
                match load(body) {
                  KExprNode.Lam(_, lam_body) =>
                    whnf_nd(expr_inst1(lam_body, list_arg, 0), types),
                  _ => whnf_nd(store(KExprNode.App(body, list_arg)), types),
                },
              _ => expanded,
            },
          _ => expanded,
        },
      _ => expanded,
    }
  }

  -- Lit(Str) → ctor form with the delta step; other exprs unchanged.
  -- Mirror str_lit_to_ctor_app_or_self (Primitive.lean:3099).
  fn str_lit_to_ctor_app_or_self(e: KExpr, types: List‹KExpr›) -> KExpr {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Str(bs) => str_lit_delta_step(str_lit_to_ctor(bs), types),
          _ => e,
        },
      _ => e,
    }
  }

  -- G (< 2^32) → single-limb KLimbs via prover-provided 4-byte split.
  -- Pinned by u8 range checks + reconstruction assert. `x >= 2^32`
  -- rejected (assert fails), not silently truncated.
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
        -- Pins the unconstrained byte-split hint: the four witnessed
        -- bytes must recompose to exactly the field element they claim
        -- to decompose.
        assert_eq!(x, to_field(b0) + 256 * to_field(b1)
                   + 65536 * to_field(b2) + 16777216 * to_field(b3),
          "u32 byte split does not recompose to the original value");
        store(ListNode.Cons([b0, b1, b2, b3, 0u8, 0u8, 0u8, 0u8],
                            store(ListNode.Nil))),
    }
  }

  -- Mirror walk_char_list_bytes: whnf `list`, expect a fully applied
  -- `List.nil` (1 lvl arg) or `List.cons` (1 lvl + head + tail).
  -- Returns (0, _) on any non-literal-ctor node, wrong arity, or invalid
  -- codepoint — caller falls back to structural.
  fn walk_char_list_bytes(list: KExpr, types: List‹KExpr›)
                              -> (G, ByteStream) {
    let w = whnf(list, types);
    match collect_spine(w) {
      (head, args) =>
        match load(head) {
          KExprNode.Const(caddr, _) =>
            match address_eq(caddr, list_nil_addr()) {
              1 =>
                match list_length(args) {
                  1 => (1, store(ListNode.Nil)),
                  _ => (0, store(ListNode.Nil)),
                },
              _ =>
                match address_eq(caddr, list_cons_addr()) {
                  0 => (0, store(ListNode.Nil)),
                  _ =>
                    match list_length(args) {
                      3 =>
                        match char_lit_codepoint(list_lookup(args, 1), types) {
                          (0, _) => (0, store(ListNode.Nil)),
                          (1, cp) =>
                            match walk_char_list_bytes(list_lookup(args, 2), types) {
                              (0, t) => (0, t),
                              (1, t) => (1, utf8_encode_prepend(cp, t)),
                            },
                        },
                      _ => (0, store(ListNode.Nil)),
                    },
                },
            },
          _ => (0, store(ListNode.Nil)),
        },
    }
  }

  -- Recognize App(Const(Char.ofNat), Nat-lit). Retry once through whnf
  -- when the syntactic match misses (mirror char_lit_value +
  -- whnf_prim_arg).
  fn char_lit_codepoint(e: KExpr, types: List‹KExpr›) -> (G, G) {
    match char_lit_codepoint_syn(e) {
      (1, cp) => (1, cp),
      _ =>
        let w = whnf(e, types);
        char_lit_codepoint_syn(w),
    }
  }

  fn char_lit_codepoint_syn(e: KExpr) -> (G, G) {
    match load(e) {
      KExprNode.App(f, arg) =>
        match load(f) {
          KExprNode.Const(caddr, _) =>
            match address_eq(caddr, char_of_nat_addr()) {
              0 => (0, 0),
              _ =>
                match load(arg) {
                  KExprNode.Lit(lit) =>
                    match lit {
                      KLiteral.Nat(limbs) => klimbs_scalar_value(limbs),
                      _ => (0, 0),
                    },
                  _ => (0, 0),
                },
            },
          _ => (0, 0),
        },
      _ => (0, 0),
    }
  }

  -- Single-limb KLimbs → codepoint; multi-limb literals bail. Guards
  -- to valid Unicode scalars (rejects surrogates 0xD800-0xDFFF and
  -- codepoints ≥ 0x110000).
  fn klimbs_scalar_value(limbs: KLimbs) -> (G, G) {
    match load(limbs) {
      ListNode.Cons(limb, rest) =>
        match load(rest) {
          ListNode.Nil =>
            let [b0, b1, b2, b3, b4, b5, b6, b7] = limb;
            let hi = to_field(b3) + to_field(b4) + to_field(b5) + to_field(b6) + to_field(b7);
            match eq_zero(hi) {
              0 => (0, 0),
              _ =>
                let cp = to_field(b0) + to_field(b1) * 256 + to_field(b2) * 65536;
                match u32_less_than(cp, 55296) {
                  1 => (1, cp),
                  _ =>
                    match u32_less_than(57343, cp) {
                      0 => (0, 0),
                      _ =>
                        match u32_less_than(cp, 1114112) {
                          1 => (1, cp),
                          _ => (0, 0),
                        },
                    },
                },
            },
          _ => (0, 0),
        },
      _ => (0, 0),
    }
  }

  -- Off-circuit 6-bit decomposition (repeated subtraction); prover-
  -- provided results MUST be pinned by u8 + window range checks +
  -- reconstruction assert.
  fn divmod_64u(x: G, q: G) -> (G, G) {
    match u32_less_than(x, 64) {
      1 => (x, q),
      _ => divmod_64u(x - 64, q + 1),
    }
  }

  fn utf8_groups(cp: G) -> (G, G, G, G) {
    match divmod_64u(cp, 0) {
      (g0, q1) =>
        match divmod_64u(q1, 0) {
          (g1, q2) =>
            match divmod_64u(q2, 0) {
              (g2, g3) => (g0, g1, g2, g3),
            },
        },
    }
  }

  -- Constrained UTF-8 encode of a valid scalar `cp`, prepended to `tail`.
  -- Length class chosen by u32_less_than compares on `cp` (already valid
  -- per caller — no overlong branch).
  fn utf8_encode_prepend(cp: G, tail: ByteStream) -> ByteStream {
    match #utf8_groups(cp) {
      (g0, g1, g2, g3) =>
        let g0u = u8_xor(u8_from_field_unsafe(g0), 0u8);
        let g1u = u8_xor(u8_from_field_unsafe(g1), 0u8);
        let g2u = u8_xor(u8_from_field_unsafe(g2), 0u8);
        let g3u = u8_xor(u8_from_field_unsafe(g3), 0u8);
        let f0 = to_field(g0u);
        let f1 = to_field(g1u);
        let f2 = to_field(g2u);
        let f3 = to_field(g3u);
        -- Pins the unconstrained UTF-8 group hint: each group is a
        -- 6-bit value and together they recompose to the codepoint.
        assert_eq!(u32_less_than(f0, 64), 1,
          "utf8 group 0 is not a 6-bit value");
        assert_eq!(u32_less_than(f1, 64), 1,
          "utf8 group 1 is not a 6-bit value");
        assert_eq!(u32_less_than(f2, 64), 1,
          "utf8 group 2 is not a 6-bit value");
        assert_eq!(u32_less_than(f3, 64), 1,
          "utf8 group 3 is not a 6-bit value");
        assert_eq!(cp, f0 + f1 * 64 + f2 * 4096 + f3 * 262144,
          "utf8 groups do not recompose to the codepoint");
        match u32_less_than(cp, 128) {
          1 => store(ListNode.Cons(u8_from_field_unsafe(cp), tail)),
          _ =>
            match u32_less_than(cp, 2048) {
              1 =>
                let t1 = u8_from_field_unsafe(f0 + 128);
                let l1 = u8_from_field_unsafe(f1 + 192);
                store(ListNode.Cons(l1, store(ListNode.Cons(t1, tail)))),
              _ =>
                match u32_less_than(cp, 65536) {
                  1 =>
                    let t2 = u8_from_field_unsafe(f0 + 128);
                    let t1 = u8_from_field_unsafe(f1 + 128);
                    let l2 = u8_from_field_unsafe(f2 + 224);
                    store(ListNode.Cons(l2, store(ListNode.Cons(t1, store(ListNode.Cons(t2, tail)))))),
                  _ =>
                    let t3 = u8_from_field_unsafe(f0 + 128);
                    let t2 = u8_from_field_unsafe(f1 + 128);
                    let t1 = u8_from_field_unsafe(f2 + 128);
                    let l3 = u8_from_field_unsafe(f3 + 240);
                    store(ListNode.Cons(l3, store(ListNode.Cons(t1, store(ListNode.Cons(t2, store(ListNode.Cons(t3, tail)))))))),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Family classification
  -- ============================================================================
  fn is_nat_prim_addr(a: Addr) -> G {
    match address_eq(a, nat_succ_addr()) {
      1 => 1,
      _ =>
      match address_eq(a, nat_pred_addr()) {
        1 => 1,
        _ =>
        match address_eq(a, nat_add_addr()) {
          1 => 1,
          _ =>
          match address_eq(a, nat_sub_addr()) {
            1 => 1,
            _ =>
            match address_eq(a, nat_mul_addr()) {
              1 => 1,
              _ =>
              match address_eq(a, nat_div_addr()) {
                1 => 1,
                _ =>
                match address_eq(a, nat_mod_addr()) {
                  1 => 1,
                  _ =>
                  match address_eq(a, nat_pow_addr()) {
                    1 => 1,
                    _ =>
                    match address_eq(a, nat_gcd_addr()) {
                      1 => 1,
                      _ =>
                      match address_eq(a, nat_beq_addr()) {
                        1 => 1,
                        _ =>
                        match address_eq(a, nat_ble_addr()) {
                          1 => 1,
                          _ =>
                          match address_eq(a, nat_land_addr()) {
                            1 => 1,
                            _ =>
                            match address_eq(a, nat_lor_addr()) {
                              1 => 1,
                              _ =>
                              match address_eq(a, nat_xor_addr()) {
                                1 => 1,
                                _ =>
                                match address_eq(a, nat_shift_left_addr()) {
                                  1 => 1,
                                  _ =>
                                  match address_eq(a, nat_shift_right_addr()) {
                                    1 => 1,
                                    _ => 0,
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

  -- ============================================================================
  -- Extract Nat literal from KExpr
  -- ============================================================================
  fn try_extract_nat(e: KExpr) -> (G, KLimbs) {
    match load(e) {
      KExprNode.Lit(lit) =>
        match lit {
          KLiteral.Nat(limbs) => (1, limbs),
          _ => (0, store(ListNode.Nil)),
        },
      KExprNode.Const(caddr, _) =>
        match address_eq(caddr, nat_zero_addr()) {
          1 => (1, store(ListNode.Nil)),
          _ => (0, store(ListNode.Nil)),
        },
      KExprNode.App(f, a) => try_extract_nat_app(f, a),
      _ => (0, store(ListNode.Nil)),
    }
  }

  -- Cold-extracted App arm: list_lookup + address_eq + recursive
  -- try_extract_nat + klimbs_succ is the widest arm; pulling it out lets
  -- `try_extract_nat`'s main width drop to the leaf-arm width.
  fn try_extract_nat_app(f: KExpr, a: KExpr) -> (G, KLimbs) {
    match load(f) {
      KExprNode.Const(caddr, _) =>
        match address_eq(caddr, nat_succ_addr()) {
          1 =>
            match try_extract_nat(a) {
              (1, pred_limbs) => (1, klimbs_succ(pred_limbs)),
              _ => (0, store(ListNode.Nil)),
            },
          _ => (0, store(ListNode.Nil)),
        },
      _ => (0, store(ListNode.Nil)),
    }
  }

  fn mk_nat_lit(n: KLimbs) -> KExpr {
    store(KExprNode.Lit(KLiteral.Nat(n)))
  }

  -- ============================================================================
  -- Apply spine (rebuild App chain).
  -- ============================================================================
  fn np_apply_spine(head: KExpr, spine: List‹KExpr›) -> KExpr {
    match load(spine) {
      ListNode.Nil => head,
      ListNode.Cons(a, rest) =>
        np_apply_spine(store(KExprNode.App(head, a)), rest),
    }
  }

  -- ============================================================================
  -- Binop dispatch by head address on two literal args.
  -- ============================================================================
  fn try_nat_binop_addr(head_addr: Addr, a: KLimbs, b: KLimbs) -> (G, KExpr) {
    match address_eq(head_addr, nat_add_addr()) {
      1 => (1, mk_nat_lit(klimbs_normalize(klimbs_add(a, b)))),
      _ =>
      match address_eq(head_addr, nat_sub_addr()) {
        1 => (1, mk_nat_lit(klimbs_normalize(klimbs_sub(a, b)))),
        _ =>
        match address_eq(head_addr, nat_mul_addr()) {
          1 => (1, mk_nat_lit(klimbs_normalize(klimbs_mul(a, b)))),
          _ =>
          match address_eq(head_addr, nat_div_addr()) {
            1 => (1, mk_nat_lit(klimbs_normalize(klimbs_div(a, b)))),
            _ =>
            match address_eq(head_addr, nat_mod_addr()) {
              1 => (1, mk_nat_lit(klimbs_normalize(klimbs_mod(a, b)))),
              _ =>
              match address_eq(head_addr, nat_gcd_addr()) {
                1 => (1, mk_nat_lit(klimbs_normalize(klimbs_gcd(a, b)))),
                _ =>
                match address_eq(head_addr, nat_pow_addr()) {
                  1 => (1, mk_nat_lit(klimbs_normalize(klimbs_pow(a, b)))),
                  _ =>
                  match address_eq(head_addr, nat_land_addr()) {
                    1 => (1, mk_nat_lit(klimbs_normalize(klimbs_land(a, b)))),
                    _ =>
                    match address_eq(head_addr, nat_lor_addr()) {
                      1 => (1, mk_nat_lit(klimbs_normalize(klimbs_lor(a, b)))),
                      _ =>
                      match address_eq(head_addr, nat_xor_addr()) {
                        1 => (1, mk_nat_lit(klimbs_normalize(klimbs_xor_op(a, b)))),
                        _ =>
                        match address_eq(head_addr, nat_shift_left_addr()) {
                          1 => (1, mk_nat_lit(klimbs_normalize(klimbs_shl(a, b)))),
                          _ =>
                          match address_eq(head_addr, nat_shift_right_addr()) {
                            1 => (1, mk_nat_lit(klimbs_normalize(klimbs_shr(a, b)))),
                            _ =>
                            match address_eq(head_addr, nat_beq_addr()) {
                              1 => (1, mk_bool(klimbs_eq(a, b))),
                              _ =>
                              match address_eq(head_addr, nat_ble_addr()) {
                                1 => (1, mk_bool(klimbs_le(a, b))),
                                _ => (0, store(KExprNode.BVar(0))),
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

  -- ============================================================================
  -- : nat_offset canonicalization + linear-rec fast path
  -- ============================================================================

  -- If head is Const(nat_add) applied to 2 args with rhs a Lit(Nat),
  -- return (1, lhs, limbs). Else (0, _, _).
  fn try_match_nat_add(head: KExpr, args: List‹KExpr›) -> (G, KExpr, KLimbs) {
    match load(head) {
      KExprNode.Const(caddr, _) =>
        match address_eq(caddr, nat_add_addr()) {
          0 => (0, head, store(ListNode.Nil)),
          _ =>
            match list_length(args) - 2 {
              0 =>
                let lhs = list_lookup(args, 0);
                let rhs = list_lookup(args, 1);
                match load(rhs) {
                  KExprNode.Lit(lit) =>
                    match lit {
                      KLiteral.Nat(limbs) => (1, lhs, limbs),
                      _ => (0, head, store(ListNode.Nil)),
                    },
                  _ => (0, head, store(ListNode.Nil)),
                },
              _ => (0, head, store(ListNode.Nil)),
            },
        },
      _ => (0, head, store(ListNode.Nil)),
    }
  }

  -- Build `Nat.succ pred` where pred = base if lit==1,
  -- else `Nat.add base (Lit lit-1)`.
  fn build_succ_offset(base: KExpr, lit: KLimbs) -> KExpr {
    let one = store(ListNode.Cons([1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
                                  store(ListNode.Nil)));
    let pred_lit_norm = klimbs_normalize(klimbs_sub(lit, one));
    let succ_const = store(KExprNode.Const(nat_succ_addr(), store(ListNode.Nil)));
    match klimbs_is_zero(pred_lit_norm) {
      1 => store(KExprNode.App(succ_const, base)),
      _ =>
        let add_const = store(KExprNode.Const(nat_add_addr(), store(ListNode.Nil)));
        let pred_lit_expr = store(KExprNode.Lit(KLiteral.Nat(pred_lit_norm)));
        let pred = store(KExprNode.App(
          store(KExprNode.App(add_const, base)),
          pred_lit_expr));
        store(KExprNode.App(succ_const, pred)),
    }
  }

  -- Expose one Nat.succ layer if `e` matches `Nat.add base (Lit n)` with
  -- n > 0. Enables iota to fire on the exposed successor without
  -- unfolding into an n-deep succ tower. Non-matching inputs pass through.
  fn cleanup_nat_offset_major(e: KExpr) -> KExpr {
    match load(e) {
      KExprNode.Lit(_) => e,
      _ =>
        match collect_spine(e) {
          (head, args) =>
            match load(head) {
              KExprNode.Const(_, _) =>
                match try_match_nat_add(head, args) {
                  (1, base, lit) =>
                    let lit_norm = klimbs_normalize(lit);
                    match klimbs_is_zero(lit_norm) {
                      1 => e,
                      _ => build_succ_offset(base, lit_norm),
                    },
                  _ => e,
                },
              _ => e,
            },
        },
    }
  }

  -- Build the compact stuck offset `Nat.add base (Lit n)` applied to
  -- `post`. n = 0 collapses to bare `base`. Used by try_nat_linear_rec
  -- to keep symbolic-base Nat.rec reductions in a memoizable
  -- canonical form (defeq collapses across `Nat.add base k` with the
  -- same base + k).
  fn mk_nat_offset_stuck(base_w: KExpr, n: KLimbs,
                              post: List‹KExpr›) -> (G, KExpr) {
    match klimbs_is_zero(n) {
      1 => (1, np_apply_spine(base_w, post)),
      _ =>
        let add_const = store(KExprNode.Const(nat_add_addr(), store(ListNode.Nil)));
        let off = store(KExprNode.App(
          store(KExprNode.App(add_const, base_w)),
          mk_nat_lit(n)));
        (1, np_apply_spine(off, post)),
    }
  }

  -- Recognize `λ _ (λ _ (Nat.succ #0))` step function shape.
  fn is_nat_succ_ih_step(step: KExpr) -> G {
    match load(step) {
      KExprNode.Lam(_, body1) =>
        match load(body1) {
          KExprNode.Lam(_, body2) =>
            match collect_spine(body2) {
              (head, args) =>
                match load(head) {
                  KExprNode.Const(caddr, _) =>
                    match address_eq(caddr, nat_succ_addr()) {
                      0 => 0,
                      _ =>
                        match list_length(args) - 1 {
                          0 =>
                            match load(list_lookup(args, 0)) {
                              KExprNode.BVar(i) => eq_zero(i),
                              _ => 0,
                            },
                          _ => 0,
                        },
                    },
                  _ => 0,
                },
            },
          _ => 0,
        },
      _ => 0,
    }
  }

  -- Fast path for `Nat.rec base (fun _ ih => succ ih) (Lit n)`. Yields
  -- `Lit(base + n)` for literal base or the compact stuck offset
  -- `Nat.add base (Lit n)` for symbolic base. Caller pre-whnfs step +
  -- major (via whnf_spine).
  fn try_nat_linear_rec(spine: List‹KExpr›, nparams: G, nmotives: G,
                             nminors: G, major_idx: G) -> (G, KExpr) {
    match u32_less_than(nminors, 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let raw_major = list_lookup(spine, major_idx);
        match try_extract_nat(raw_major) {
          (0, _) => (0, store(KExprNode.BVar(0))),
          (1, n_klimbs) =>
            let base_idx = nparams + nmotives;
            let step = list_lookup(spine, base_idx + 1);
            match is_nat_succ_ih_step(step) {
              0 => (0, store(KExprNode.BVar(0))),
              _ =>
                let base = list_lookup(spine, base_idx);
                let post = list_drop(spine, major_idx + 1);
                match try_extract_nat(base) {
                  (1, b_klimbs) =>
                    (1, np_apply_spine(mk_nat_lit(klimbs_add(b_klimbs, n_klimbs)), post)),
                  _ => mk_nat_offset_stuck(base, n_klimbs, post),
                },
            },
        },
    }
  }

  -- ============================================================================
  -- Top-level nat dispatch: unary (succ/pred) then binop.
  -- Caller must whnf spine args before matching Ctor / Lit / literal.
  -- ============================================================================
  fn try_nat_dispatch(head_addr: Addr, spine: List‹KExpr›,
                          types: List‹KExpr›) -> (G, KExpr) {
    let spine_len = list_length(spine);
    let is_pred = address_eq(head_addr, nat_pred_addr());
    let is_succ = address_eq(head_addr, nat_succ_addr());
    match is_succ {
      1 =>
        match u32_less_than(spine_len, 1) {
          1 => (0, store(KExprNode.BVar(0))),
          _ =>
            let a0 = list_lookup(spine, 0);
            match try_extract_nat(a0) {
              (1, na) =>
                let post = list_drop(spine, 1);
                (1, np_apply_spine(mk_nat_lit(klimbs_succ(na)), post)),
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
      _ =>
        match is_pred {
          1 =>
            match u32_less_than(spine_len, 1) {
              1 => (0, store(KExprNode.BVar(0))),
              _ =>
                let a0 = list_lookup(spine, 0);
                match try_extract_nat(a0) {
                  (1, na) =>
                    let post = list_drop(spine, 1);
                    (1, np_apply_spine(mk_nat_lit(klimbs_normalize(klimbs_dec(na))), post)),
                  _ => (0, store(KExprNode.BVar(0))),
                },
            },
          _ => try_nat_binop_dispatch(head_addr, spine, spine_len),
        },
    }
  }

  -- Cold-extracted binop arm (mirror try_nat_binop_dispatch,
  -- Primitive.lean:1671 / [[reference_aiur_hot_cold_split]]): the
  -- binop branch (2× extract + binop-addr chain + offset dispatch +
  -- apply_spine) is the widest arm of try_nat_dispatch, taxing
  -- every Nat.succ/Nat.pred row when inlined. Its width now only
  -- charges rows that actually dispatch a binop.
  fn try_nat_binop_dispatch(head_addr: Addr, spine: List‹KExpr›,
                                 spine_len: G) -> (G, KExpr) {
    match u32_less_than(spine_len, 2) {
      1 => (0, store(KExprNode.BVar(0))),
      _ =>
        let a0 = list_lookup(spine, 0);
        let a1 = list_lookup(spine, 1);
        match try_extract_nat(a0) {
          (1, na) =>
            match try_extract_nat(a1) {
              (1, nb) =>
                match try_nat_binop_addr(head_addr, na, nb) {
                  (1, result) =>
                    let post = list_drop(spine, 2);
                    (1, np_apply_spine(result, post)),
                  _ => (0, store(KExprNode.BVar(0))),
                },
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ =>
            -- Symbolic base: route to the offset-stuck check
            -- (mirror try_nat_binop_dispatch's fall-through).
            match try_extract_nat(a1) {
              (1, nb) =>
                try_nat_offset_dispatch(head_addr, a0, nb, spine),
              _ => (0, store(KExprNode.BVar(0))),
            },
        },
    }
  }

  -- Mirror try_nat_offset_dispatch (Primitive.lean:1712): a binary
  -- Nat op whose whnf'd base is symbolic and whose second arg is
  -- `Lit nb`. For `Nat.add` (any nb) and `Nat.div`/`Nat.mod` (nb >= 2)
  -- the term is irreducible: return verdict 2 = "already stuck in
  -- compact offset form" so whnf keeps it instead of delta-unfolding
  -- into a succ^nb tower / the division algorithm. Pairs with the
  -- offset-aware def_eq (try_def_eq_nat).
  fn try_nat_offset_dispatch(head_addr: Addr, a0_w: KExpr, nb: KLimbs,
                                  spine: List‹KExpr›) -> (G, KExpr) {
    let is_add = address_eq(head_addr, nat_add_addr());
    let is_divmod = address_eq(head_addr, nat_div_addr())
      + address_eq(head_addr, nat_mod_addr());
    let eligible =
      is_add + is_divmod * (1 - klimbs_is_zero(nb))
        * (1 - klimbs_is_zero(klimbs_normalize(klimbs_dec(nb))));
    match eligible {
      0 => (0, store(KExprNode.BVar(0))),
      _ =>
        let post = list_drop(spine, 2);
        -- `Nat.add` keeps the canonical add-offset shape (shared with
        -- the linear-rec collapse). Div/mod MUST keep their own head:
        -- routing them through the add builder rewrites `x / n` into
        -- `x + n`.
        match is_add {
          1 =>
            match mk_nat_offset_stuck(a0_w, nb, post) {
              (1, stuck) => (2, stuck),
              _ => (0, store(KExprNode.BVar(0))),
            },
          _ => (2, mk_nat_binop_stuck(head_addr, a0_w, nb, post)),
        },
    }
  }

  -- Rebuild a stuck binary Nat op `op base (Lit n)` applied to `post`,
  -- preserving the op's own head (div stays div, mod stays mod).
  -- Mirror mk_nat_binop_stuck (Primitive.lean:1750), addr-first.
  fn mk_nat_binop_stuck(op_addr: Addr, base_w: KExpr, n: KLimbs,
                             post: List‹KExpr›) -> KExpr {
    let op_const = store(KExprNode.Const(op_addr, store(ListNode.Nil)));
    let stuck = store(KExprNode.App(
      store(KExprNode.App(op_const, base_w)),
      mk_nat_lit(n)));
    np_apply_spine(stuck, post)
  }
⟧

end IxVM

end
