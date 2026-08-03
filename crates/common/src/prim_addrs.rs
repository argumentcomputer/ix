//! Hardcoded primitive content-addresses.
//!
//! Lives in `ix-common` rather than `ix-kernel` because several crates
//! need this table and `ixon` (and everything above it) cannot depend on
//! the kernel — `ix-kernel` already depends on `ixon`, so the edge would
//! be a cycle. Witness builders need it to seed primitives the kernel
//! FABRICATES during reduction rather than discovers by walking `refs`.
//!
//! Addresses are blake3 hashes of each primitive's Ixon-compiled form.
//! Regenerate with `lake test -- rust-kernel-build-primitives`, which
//! dumps the current `(name, hex)` pairs — paste the updated lines into
//! `PrimAddrs::new`. `lake test -- prim-addrs` pins this table against
//! the Lean mirror in `Ix/Tc/Primitive.lean`.

use std::sync::LazyLock;

use crate::address::Address;

/// Hardcoded primitive addresses (for lookup in the env).
pub struct PrimAddrs {
  pub nat: Address,
  pub nat_zero: Address,
  pub nat_succ: Address,
  pub nat_add: Address,
  pub nat_pred: Address,
  pub nat_sub: Address,
  pub nat_mul: Address,
  pub nat_pow: Address,
  pub nat_gcd: Address,
  pub nat_mod: Address,
  pub nat_div: Address,
  pub nat_bitwise: Address,
  pub nat_beq: Address,
  pub nat_ble: Address,
  pub nat_land: Address,
  pub nat_lor: Address,
  pub nat_xor: Address,
  pub nat_shift_left: Address,
  pub nat_shift_right: Address,
  pub bool_type: Address,
  pub bool_true: Address,
  pub bool_false: Address,
  pub string: Address,
  pub string_mk: Address,
  pub char_type: Address,
  pub char_mk: Address,
  pub char_of_nat: Address,
  pub string_of_list: Address,
  pub string_to_byte_array: Address,
  pub byte_array_empty: Address,
  pub list: Address,
  pub list_nil: Address,
  pub list_cons: Address,
  pub eq: Address,
  pub eq_refl: Address,
  pub quot_type: Address,
  pub quot_ctor: Address,
  pub quot_lift: Address,
  pub quot_ind: Address,
  pub reduce_bool: Address,
  pub reduce_nat: Address,
  pub eager_reduce: Address,
  pub system_platform_num_bits: Address,
  pub system_platform_get_num_bits: Address,
  pub subtype_val: Address,
  pub nat_dec_le: Address,
  pub nat_dec_eq: Address,
  pub nat_dec_lt: Address,
  pub decidable_rec: Address,
  pub decidable_is_true: Address,
  pub decidable_is_false: Address,
  pub nat_le_of_ble_eq_true: Address,
  pub nat_not_le_of_not_ble_eq_true: Address,
  pub nat_eq_of_beq_eq_true: Address,
  pub nat_ne_of_beq_eq_false: Address,
  pub fin: Address,
  pub bool_no_confusion: Address,
  // Int addresses — see `Primitives` for why these exist.
  pub int: Address,
  pub int_of_nat: Address,
  pub int_neg_succ: Address,
  pub int_add: Address,
  pub int_sub: Address,
  pub int_mul: Address,
  pub int_neg: Address,
  pub int_emod: Address,
  pub int_ediv: Address,
  pub int_bmod: Address,
  pub int_bdiv: Address,
  pub int_nat_abs: Address,
  pub int_pow: Address,
  pub int_dec_eq: Address,
  pub int_dec_le: Address,
  pub int_dec_lt: Address,
  pub punit: Address,
  pub pprod: Address,
  pub pprod_mk: Address,

  // See `Primitives<M>` for the rationale on these — names previously
  // matched via name-based `is_const_named` and now resolved by address.
  pub nat_rec: Address,
  pub nat_cases_on: Address,
  pub bit_vec: Address,
  pub bit_vec_to_nat: Address,
  pub bit_vec_of_nat: Address,
  pub bit_vec_ult: Address,
  pub decidable_decide: Address,
  pub lt_lt: Address,
  pub of_nat_of_nat: Address,
  pub unit: Address,
  pub punit_size_of_1: Address,
  pub size_of_size_of: Address,
  pub string_back: Address,
  pub string_legacy_back: Address,
  pub string_utf8_byte_size: Address,
  pub string_append: Address,
  pub string_dec_eq: Address,
}

impl Default for PrimAddrs {
  fn default() -> Self {
    Self::new()
  }
}

impl PrimAddrs {
  /// Addresses reserved for kernel-only reduction markers. These are not
  /// Lean constants and must never be accepted as user environment entries.
  pub fn reserved_marker_addrs() -> [(&'static str, Address); 2] {
    let canon = Self::new();
    let orig = Self::new_orig();
    [
      ("eager_reduce", canon.eager_reduce.clone()),
      ("orig.eager_reduce", orig.eager_reduce.clone()),
    ]
  }

  /// Canonical content-hash addresses, hardcoded from the Ixon-compiled
  /// form of each primitive. Used by `Primitives::from_env` to resolve
  /// primitives against a `kctx.kenv` whose KIds live at canonical
  /// addresses. Regenerate with `lake test -- rust-kernel-build-primitives`.
  pub fn new() -> Self {
    let h = |hex: &str| -> Address {
      Address::from_hex(hex).expect("invalid primitive address hex")
    };
    PrimAddrs {
      nat: h(
        "398a7706cf13f223992d173dce07946857240f49afcc743723e839f8f3f2b631",
      ),
      nat_zero: h(
        "d397370157fb9ae2c6e1eda79feb10bf497401741aba788fab726cfa4c467db6",
      ),
      nat_succ: h(
        "def52d1dad5f10cf9893c945e169718d62b15e2dd2c9066e597b9d4570ba056e",
      ),
      nat_add: h(
        "d6f62a9779108f9fb6b66b31cc94c3d84ca72d8bea185e13137c50c7ef84c969",
      ),
      nat_pred: h(
        "914f9c01884853652e9224dc511f867d5408517f3beb3192fc4477e0e9594c88",
      ),
      nat_sub: h(
        "fdbd5fef40149c85333c6f3ccebb4be741270d2066336cb2eef87623744b72b0",
      ),
      nat_mul: h(
        "6649665607b0750c2ca73f45de600f21cb670398504865bb97972438014f96d9",
      ),
      nat_pow: h(
        "33c604451d01cb19a433668246b98f6e874bd630b78a791d7a373a979849a1cf",
      ),
      nat_gcd: h(
        "3be48357ae17f74d4df27d697aed3f47c1307941f41affcf74da5f66d511a797",
      ),
      nat_mod: h(
        "5179638b82cc8337914a7bcaad858c85888844e9a292430cac51e5eadc41a1af",
      ),
      nat_div: h(
        "89deca86dd8f0066a5064fdb19a2c6897a3a9867caadc04f778d5c5cd0225362",
      ),
      nat_bitwise: h(
        "d2075e323bed82f23eaf75ebc0fae4ceb80794240c046b90c51a94d07f5e885f",
      ),
      nat_beq: h(
        "a34ab2daba34839e851fa3675124566f9f4dcde597349ecd54ae32f8424e44b8",
      ),
      nat_ble: h(
        "de0befa84faa22d1394379a0ba67296e116660f781b4eb639dbbaba200ef2bf8",
      ),
      nat_land: h(
        "818abb331150400d10b34fae4dfb9426741c4607baeed8d96271ba1659058ef8",
      ),
      nat_lor: h(
        "9b76f32bbb1dbdf4ff68e0221225015df0ca2d2a6023c1a81306d4020d4ef397",
      ),
      nat_xor: h(
        "97e325a96a6a1827194eeb7d2aa0d91921073aef9c2d333c24613e9ac956ed29",
      ),
      nat_shift_left: h(
        "dc81e41cad1190377dbe604bfc3afe658a413b9a2dcfbcab79fad7b7a5cdd954",
      ),
      nat_shift_right: h(
        "6db49304bf0f5acbfd1d9d9a0c1b7ae20ef99d0737887056129f5b5cb5a9ba8a",
      ),
      bool_type: h(
        "e6eba3c8b4d19f6a1076b39fa89aec61dccbb960f83d9a62e6acf35a69c9a0a4",
      ),
      bool_true: h(
        "a29a636176cf1135d077eb074798f9007c78e7801383e9cff363bae5edf05762",
      ),
      bool_false: h(
        "dda12bcb330727f6dfb816bc9752aabd0520e6515b79fc8a5a9e713866f4c63e",
      ),
      string: h(
        "7ab2d52ac52fd1f51809b718e53cd058ac4b50d65150e78ae619139ccf13c8fd",
      ),
      string_mk: h(
        "9671fd4fcfbc061c93c2824864cf03124ffee7cc22308de12a7c826473e49906",
      ),
      char_type: h(
        "29dd2d1986a525bdde49b4ad2defc349cec71d0484cd13f2da92f1fce89a4c79",
      ),
      char_mk: h(
        "97afa5ad3d86895e6d155019b66c256cd1aa862b4e3c89d8c6580b61939ee541",
      ),
      char_of_nat: h(
        "1a4c66f76760f5ef386de089682a55b752131e14a08557c4465ed17fe0c4dc86",
      ),
      // NOTE: `String.ofList` and `String.mk` share the canonical content-hash
      // because both compile to the same Ixon form (a one-constructor `String`
      // built from `List Char`). The Lean-side deprecation of `String.mk` in
      // favor of `String.ofList` is orthogonal to the compiled representation.
      string_of_list: h(
        "9671fd4fcfbc061c93c2824864cf03124ffee7cc22308de12a7c826473e49906",
      ),
      string_to_byte_array: h(
        "ed43c77e555593b6cd0d4bfbc4273ba122e1c0cdf1090571612a952f941eadb1",
      ),
      byte_array_empty: h(
        "7cfba8fa95847c213aa4066110ba01a97fb597daf29f5c07f72366072f250744",
      ),
      list: h(
        "144e207a88d1dfbde22a1b40689033b3a65a652c8f7500b9be3cb7f66366e0fe",
      ),
      list_nil: h(
        "258a7364b87c99fe9f83e05e0d05c935609a0dc5df8d77939130efe5e0efca3e",
      ),
      list_cons: h(
        "77d519259ec9fa489dbe0e3dc0b9352aef349ccdaa73ea58b08bb0bc683502a0",
      ),
      eq: h("036b63d5cc0961e920dee50e7364ec0dd3f9c38a9cace40e513b3835dec8e0c9"),
      eq_refl: h(
        "6c9bd60e1eae938e5626ca237dbca7fd950f2e99e234a99c23cfdc294ca7adce",
      ),
      quot_type: h(
        "ab682c1778a17bbeae4032974df36447ce8bfcab6764a36d378566e3ad63cab8",
      ),
      quot_ctor: h(
        "88266677fee774d109867e4b2240281aa2ee12d97920c1171cf5c1f6c87decf6",
      ),
      quot_lift: h(
        "8dc4a97527812f8b7817b77cd079ace61450aa0185ac5885661ec2acba8b7bd0",
      ),
      quot_ind: h(
        "124984bcb95208a0f30bb69d6736d3d59404e115e2202043fda3d34e01b0ad16",
      ),
      reduce_bool: h(
        "1c170098e23143fd8fd6172cefd2ecee305072d2991113cfc4d52840a5a9fa78",
      ),
      reduce_nat: h(
        "16853076b0d96d356d85485c56f3398014b6a0f2ee72ab16284a381d9c28e560",
      ),
      // Synthetic kernel-only marker. This is intentionally not the compiled
      // Lean content hash: `eagerReduce` canonicalizes to the same content
      // address as the real Lean constant `id`, so address-only dispatch would
      // give ordinary `id` terms special reduction semantics.
      eager_reduce: h(
        "ff00000000000000000000000000000000000000000000000000000000000003",
      ),
      system_platform_num_bits: h(
        "cf86263521d345c39076473ecdb9f6fd411b5b503bce83e2318ba3fb6f2376d8",
      ),
      system_platform_get_num_bits: h(
        "f5d256c1dd794d02cfdf1762c9e41b13abe5bddde12d929d02ada37e4f40e85f",
      ),
      subtype_val: h(
        "0b5958a3c822c99e8643a27f0b928dfb82c45447bee0353c200ad1b7d0e46092",
      ),
      nat_dec_le: h(
        "ec1f60c1a28d48bc98fe3ef72d255132735a503cc36e3ff0f22e3d486e266ebe",
      ),
      nat_dec_eq: h(
        "b4b26c2e29931c06e885914613faff5856138e5cb09620ddb6921a342ded8957",
      ),
      nat_dec_lt: h(
        "c013c153ebf02028aed264333c1e4c85017d0b87025d7596a96971bb2b67921d",
      ),
      decidable_rec: h(
        "ab3776985743af13a9cb1a7d2f8496997892e17983d14be5270a716570b35719",
      ),
      decidable_is_true: h(
        "0f9ee8d9033d8f7b852f5b7152fd124f7d411930c992e0f457f8104b60a98381",
      ),
      decidable_is_false: h(
        "0471e47158b2ae18d3c08dd5c77aae23e62d7bbc1e61116bc2813b1306bc5795",
      ),
      nat_le_of_ble_eq_true: h(
        "21e0e0783b7617b0cc4eff4d1fab7cffefe01cd43da77e2f98d15094a0d8f086",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "0183595b837b9b84da5f004b8ac4a4bbd3bc0628b99c8d550eb351f74ce16d48",
      ),
      nat_eq_of_beq_eq_true: h(
        "9ce6e322f19481f21cf4c48f88789876b69b8a9b1520439c101d983f96ea60b7",
      ),
      nat_ne_of_beq_eq_false: h(
        "3cf54d333821dd37683a0bf38739e687610a1991759220b77edec338ba3cfbc8",
      ),
      fin: h(
        "745936fcb9d86c4457f0fd1e537e67077f46f7841108419dac7984008b565b97",
      ),
      bool_no_confusion: h(
        "cd983a826c1e20c4570afca244916c79e20e816f618ffdda38be8a79079274ce",
      ),
      // Int primitives — canonical content-hashes from
      // `lake test -- rust-kernel-build-primitives`.
      int: h(
        "a5ca2e1d5ceb8d43367bc34d69a50c1650a25dc10780aa0c378cdfa931ff0424",
      ),
      int_of_nat: h(
        "09bc253147c36ce22c8e0ccd43c79b2cdae2206e0ddd168fca3609b2a584d3dc",
      ),
      int_neg_succ: h(
        "267c0a9c92e75638fc73ed52a9f9c81647eeeceeff2144c1f97e65e2aff149f1",
      ),
      int_add: h(
        "ca99084c9d2fcb4c5dd139aecaf159ebd04992d76230cb930f41b86074684817",
      ),
      int_sub: h(
        "d3141231800e012e8db7c240f794e4929bfd156b3845e22f1cf31d3fe39aecd9",
      ),
      int_mul: h(
        "482064e35634a95c0f252de73d687c24764ea4fa7dfd14cf7af8aa7531f17a5c",
      ),
      int_neg: h(
        "f61c7d3fce595430f86f0cd52da5bcb00bf910edd85e14dc0402130fcce34ebd",
      ),
      int_emod: h(
        "25c267ef44f15007f2d2e0819be6fb64902c33a7d27a6f2c9d61263898953804",
      ),
      int_ediv: h(
        "49b34dcbff1e60532825ff5af477eb5de9810ee38e0f7a32014d54c8c1a3a3c5",
      ),
      int_bmod: h(
        "6a6adf0e95b3a4ce18330ee22105712e9a640ee4311b5dd1022a8e0a30cba0af",
      ),
      int_bdiv: h(
        "a4f1d7a3fe5b6b2ef9522fa537f1e622fbb8176f9fb3358c56cebe1a379b6184",
      ),
      int_nat_abs: h(
        "83e3ce8a747520cc248a0dacf9bd1369467e4907e8aaaa433e1b438e1cad7ca4",
      ),
      int_pow: h(
        "73ecccfeab8a63a3a0faf8d71dc77995bda83418b13cd399b1fa571b50b4575e",
      ),
      int_dec_eq: h(
        "83fde38faa1164648e4227975abf2e8c260d7d4ef1c92676214ffe5826c2075d",
      ),
      int_dec_le: h(
        "38d60ffa07b50678d0c3bf0c06f86cd7967b35e87ab071bc55899fcbaed4744f",
      ),
      int_dec_lt: h(
        "5568e799198dad9fab0e784b7a4c58112bfc2688aecebe3c2c6563304210f956",
      ),
      punit: h(
        "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b",
      ),
      pprod: h(
        "81a422a42b2cb656b9a47e61a4422f89cdb0a0c166035d47bf5e2c2af02175fa",
      ),
      pprod_mk: h(
        "c9c584da782cdc453306be9a643244fa0bcbfc3b5dbcbafe3f6b9d65df031fed",
      ),
      // Names previously matched via `is_const_named` in whnf.rs.
      // Canonical content-hashes from `lake test -- rust-kernel-build-primitives`.
      nat_rec: h(
        "b975152f3f0cd9039433c68f5a5e5455f5cb5d917078baed0118b59067a74ea7",
      ),
      nat_cases_on: h(
        "1917841d2085796dd7ba346de93a579571b5641c33fc400408ec55b5778a9a51",
      ),
      bit_vec: h(
        "698dd593abfb63db362aaef57e70a793044fb657257291ee2c3e997caa423eae",
      ),
      bit_vec_to_nat: h(
        "77a025c19f8be131fb9d5b0bec494817a26538b9a550abbbcec8099fae9de4e4",
      ),
      bit_vec_of_nat: h(
        "90ca8130735c8d9a34005a8943b59fe1df182e08a9f2bfc7dc8323229659a574",
      ),
      bit_vec_ult: h(
        "9fd8e7459a1d2deef00a4992a50419bac66c03082b58ade07422896f13033d74",
      ),
      decidable_decide: h(
        "c5f7b19663e4499e70e1b2645162c5be15fa860f4f8157e331ae546c6f733723",
      ),
      lt_lt: h(
        "cacaea97f4cdba0a4a0af71005d0517d1818ab2623bd2ea7fa8c637a0e3d3312",
      ),
      of_nat_of_nat: h(
        "5a7292ad756ee1f2df4b92f18a27574a47cbbcf7094f98ab2865f92eb22342d7",
      ),
      unit: h(
        "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb",
      ),
      punit_size_of_1: h(
        "7bd8e19f47f6eae620a5c39f243ce415dd6a77f09590f4c227cef363007f4012",
      ),
      size_of_size_of: h(
        "389715f91e66683dc7108ccd853efce92949512fa659ad3c1902e754692919cd",
      ),
      string_back: h(
        "e95c8d876e7ccf780418615e33b747a245d94facd7567fecbe7ae73a5ac09206",
      ),
      string_legacy_back: h(
        "6bb6162aac7d6a01b6ec05580664e8a7f0d4b0ec1fc5afaae66018e9a1936dac",
      ),
      string_utf8_byte_size: h(
        "def4433d9547b53175e24a3ac182c88b072af0d4ad33fd04ec4cf2ba3d95ea93",
      ),
      string_append: h(
        "594fb1eedec7c939cc872b6c04cc3b3e0a9764fabec3e602ad9214d0e637d30f",
      ),
      string_dec_eq: h(
        "82e5568d88e24f24d5befac30ce915010e92596f55a822e29f4876ea3a579394",
      ),
    }
  }

  /// `(lean_name, canonical_address_hex)` table from `Self::new()`,
  /// in the same order as `Tests/Ix/Kernel/BuildPrimitives.lean`'s
  /// `kernelPrimitives` array. Used by the regen-parity test
  /// (`testPrimitivesParity`) to detect drift between hardcoded
  /// addresses and freshly-compiled ones: if any future
  /// compile/serialize change touches a primitive's content hash,
  /// the parity test fails with a printable diff before the
  /// breakage propagates to downstream consumers.
  ///
  /// Keep entries in lock-step with `kernelPrimitives` (same names,
  /// same order). The `eager_reduce` entry is intentionally a
  /// synthetic kernel marker — not the compiled Lean content hash —
  /// because the real `eagerReduce` canonicalizes to the same
  /// address as `id`; see the comment on the field in `new()`.
  pub fn lean_parity_table() -> Vec<(&'static str, String)> {
    let p = Self::new();
    vec![
      ("Nat", p.nat.hex()),
      ("Nat.zero", p.nat_zero.hex()),
      ("Nat.succ", p.nat_succ.hex()),
      ("Nat.add", p.nat_add.hex()),
      ("Nat.pred", p.nat_pred.hex()),
      ("Nat.sub", p.nat_sub.hex()),
      ("Nat.mul", p.nat_mul.hex()),
      ("Nat.pow", p.nat_pow.hex()),
      ("Nat.gcd", p.nat_gcd.hex()),
      ("Nat.mod", p.nat_mod.hex()),
      ("Nat.div", p.nat_div.hex()),
      ("Nat.bitwise", p.nat_bitwise.hex()),
      ("Nat.beq", p.nat_beq.hex()),
      ("Nat.ble", p.nat_ble.hex()),
      ("Nat.land", p.nat_land.hex()),
      ("Nat.lor", p.nat_lor.hex()),
      ("Nat.xor", p.nat_xor.hex()),
      ("Nat.shiftLeft", p.nat_shift_left.hex()),
      ("Nat.shiftRight", p.nat_shift_right.hex()),
      ("Bool", p.bool_type.hex()),
      ("Bool.true", p.bool_true.hex()),
      ("Bool.false", p.bool_false.hex()),
      ("String", p.string.hex()),
      ("String.mk", p.string_mk.hex()),
      ("Char", p.char_type.hex()),
      ("Char.mk", p.char_mk.hex()),
      ("Char.ofNat", p.char_of_nat.hex()),
      ("String.ofList", p.string_of_list.hex()),
      ("List", p.list.hex()),
      ("List.nil", p.list_nil.hex()),
      ("List.cons", p.list_cons.hex()),
      ("Eq", p.eq.hex()),
      ("Eq.refl", p.eq_refl.hex()),
      ("Quot", p.quot_type.hex()),
      ("Quot.mk", p.quot_ctor.hex()),
      ("Quot.lift", p.quot_lift.hex()),
      ("Quot.ind", p.quot_ind.hex()),
      ("Lean.reduceBool", p.reduce_bool.hex()),
      ("Lean.reduceNat", p.reduce_nat.hex()),
      ("eagerReduce", p.eager_reduce.hex()),
      ("System.Platform.numBits", p.system_platform_num_bits.hex()),
      ("System.Platform.getNumBits", p.system_platform_get_num_bits.hex()),
      ("Subtype.val", p.subtype_val.hex()),
      ("String.toByteArray", p.string_to_byte_array.hex()),
      ("ByteArray.empty", p.byte_array_empty.hex()),
      ("Nat.decLe", p.nat_dec_le.hex()),
      ("Nat.decEq", p.nat_dec_eq.hex()),
      ("Nat.decLt", p.nat_dec_lt.hex()),
      ("Decidable.rec", p.decidable_rec.hex()),
      ("Decidable.isTrue", p.decidable_is_true.hex()),
      ("Decidable.isFalse", p.decidable_is_false.hex()),
      ("Nat.le_of_ble_eq_true", p.nat_le_of_ble_eq_true.hex()),
      ("Nat.not_le_of_not_ble_eq_true", p.nat_not_le_of_not_ble_eq_true.hex()),
      ("Nat.eq_of_beq_eq_true", p.nat_eq_of_beq_eq_true.hex()),
      ("Nat.ne_of_beq_eq_false", p.nat_ne_of_beq_eq_false.hex()),
      ("Fin", p.fin.hex()),
      ("Bool.noConfusion", p.bool_no_confusion.hex()),
      ("Int", p.int.hex()),
      ("Int.ofNat", p.int_of_nat.hex()),
      ("Int.negSucc", p.int_neg_succ.hex()),
      ("Int.add", p.int_add.hex()),
      ("Int.sub", p.int_sub.hex()),
      ("Int.mul", p.int_mul.hex()),
      ("Int.neg", p.int_neg.hex()),
      ("Int.emod", p.int_emod.hex()),
      ("Int.ediv", p.int_ediv.hex()),
      ("Int.bmod", p.int_bmod.hex()),
      ("Int.bdiv", p.int_bdiv.hex()),
      ("Int.natAbs", p.int_nat_abs.hex()),
      ("Int.pow", p.int_pow.hex()),
      ("Int.decEq", p.int_dec_eq.hex()),
      ("Int.decLe", p.int_dec_le.hex()),
      ("Int.decLt", p.int_dec_lt.hex()),
      ("PUnit", p.punit.hex()),
      ("PProd", p.pprod.hex()),
      ("PProd.mk", p.pprod_mk.hex()),
      ("Nat.rec", p.nat_rec.hex()),
      ("Nat.casesOn", p.nat_cases_on.hex()),
      ("BitVec", p.bit_vec.hex()),
      ("BitVec.toNat", p.bit_vec_to_nat.hex()),
      ("BitVec.ofNat", p.bit_vec_of_nat.hex()),
      ("BitVec.ult", p.bit_vec_ult.hex()),
      ("Decidable.decide", p.decidable_decide.hex()),
      ("LT.lt", p.lt_lt.hex()),
      ("OfNat.ofNat", p.of_nat_of_nat.hex()),
      ("Unit", p.unit.hex()),
      ("PUnit._sizeOf_1", p.punit_size_of_1.hex()),
      ("SizeOf.sizeOf", p.size_of_size_of.hex()),
      ("String.back", p.string_back.hex()),
      ("String.Legacy.back", p.string_legacy_back.hex()),
      ("String.utf8ByteSize", p.string_utf8_byte_size.hex()),
      ("String.append", p.string_append.hex()),
      ("String.decEq", p.string_dec_eq.hex()),
    ]
  }

  /// LEON content-hash addresses, hardcoded from
  /// `ConstantInfo::get_hash()` applied to each primitive's original
  /// (pre-compile) Lean declaration. Used by `Primitives::from_env_orig`
  /// to resolve primitives against `orig_kenv` — the direct-ingress
  /// environment produced by `lean_ingress` where KIds live at LEON
  /// addresses rather than canonical addresses.
  ///
  /// Regenerate with `lake test -- rust-kernel-build-prim-origs`. The
  /// failure mode when these drift is a synthetic `@<hex>` KId in every
  /// primitive field of `orig_kenv.prims()`, which cascades into a
  /// flood of `AppTypeMismatch` errors during original-constant
  /// verification (any Nat literal reduction, Bool literal, `String`
  /// coercion, or reducer-marker comparison will diverge from the real
  /// `orig_kenv` entry for that primitive).
  pub fn new_orig() -> Self {
    let h = |hex: &str| -> Address {
      Address::from_hex(hex).expect("invalid primitive address hex")
    };
    PrimAddrs {
      nat: h(
        "0c0524ffa66fdbc0c9d3f12faf1a27b2ecd331ffa06da24a78f832e4f4145589",
      ),
      nat_zero: h(
        "adc9f7ba6a90c3caacf0be308c2012437e9dd810bfc2b9b286b4934be4e86cb1",
      ),
      nat_succ: h(
        "e4f2b35614ae2c6487084cb96e90852643a043296bc682b469ccfd430650cf8d",
      ),
      nat_add: h(
        "01ec6fdf63bc0de137becade5f420102f35338bef318b9d5fd44e70db82c3f42",
      ),
      nat_pred: h(
        "26245a09319bcf9d55a08431bce3b9d8a8d09e3dad25b9a83cc666e3736deeb4",
      ),
      nat_sub: h(
        "4017cc8c3a02d3eeab73d5cc5af8afe771f60d980f107fd24d3a1d59aaa41d5a",
      ),
      nat_mul: h(
        "a095de37a0e713551bd237f414ac7317f68b3986ce5734ca0063c504457f24de",
      ),
      nat_pow: h(
        "6e9d84492674fb8a36008214b2150c76a83da4af1cadcc303d5d680d0477235a",
      ),
      nat_gcd: h(
        "09ae07bc024bfb0317aa228d1274294b40aebb4229dc7014f7b22d56fa46a760",
      ),
      nat_mod: h(
        "7ee6854a6ef5afb0e83f8aae9ccc2cbb457110bd1013a6f7615a98667a34322a",
      ),
      nat_div: h(
        "acb405101f168dc08bf410d54a8f588893776ab61be81f2c7e5e1dd05685560e",
      ),
      nat_bitwise: h(
        "21a51ddc3faeec42c0f3897955d5e24c40ffb1924824bd919da5db0346962a98",
      ),
      nat_beq: h(
        "8960bdbe7e09dd15582a50de197cb5c28d87b147e3479e417b4c2ad43011f90c",
      ),
      nat_ble: h(
        "7e679407c5e5af964d3d3cb98c9b606218c6f4ac7b19210d375f1d76ddd5f022",
      ),
      nat_land: h(
        "dd73c5c1552ff6ad35537b83f46c9e8c4c2c979eda612fe169e29f3028c63db9",
      ),
      nat_lor: h(
        "8390650998cbee5ee2432a797635d7a331f623eb6fae9f26f17191fcdb880c60",
      ),
      nat_xor: h(
        "04ffebfee34f36c46f63ef6aa347b0b81db8c1cbf3fb9a282799cac024310e69",
      ),
      nat_shift_left: h(
        "89705cc0aca476aa6f161f91006980a425536757e2b7ea949d3aec0edcc3df76",
      ),
      nat_shift_right: h(
        "930ab9e4c2854a0af16c84f89a5aee8e297b65411c499ffae0cf9b27d4ee4b8e",
      ),
      bool_type: h(
        "95fc5d28972d1472a12ddfc2f4a5eefec9a81652fcb63ef06c7f6f6d21a951ab",
      ),
      bool_true: h(
        "fc3a88e4dc16055bc8b797f9544909043015a3a349f2b3fc3e86990b2b9f2999",
      ),
      bool_false: h(
        "c595b2c899f6f0ef39cfab3ac2fbe3b826a7ed21318defc64bbb861d754f8bdf",
      ),
      string: h(
        "3589e6266ed0703fb4008f1e134775dff6bc9a15619687e75222f44253ab8663",
      ),
      string_mk: h(
        "22d668557ab1f800aaf7312f10d9f36ec4d24d0389ac8d0b6d66fd2daf0be903",
      ),
      char_type: h(
        "16e10c6b75431ae16fc23ef43f07512a1f34cff2a33d85b44aae5898e002ac8d",
      ),
      char_mk: h(
        "feb0d0ed724893b5d3d57bafee59ff3cfbe76f43e03fad2b2cf237198aca4457",
      ),
      char_of_nat: h(
        "3ac41b61c538227409f133982435bc97d59489b9129a61d1c4baa14fdb1d6a6a",
      ),
      string_of_list: h(
        "0422aae71a49fd82c87cc8493725a927c1205a9418dc648947d7fde8ed240625",
      ),
      string_to_byte_array: h(
        "714e5b7ea77110a862699b662ecc0bc5a6d70e25bbf6b69dc0f0ec5feb2cfbb3",
      ),
      byte_array_empty: h(
        "5e80d9c092e5fd25417a3a011632e0d060adf9cfd4c0a0bd6798868f067a7cb2",
      ),
      list: h(
        "5886afc36363b59242671f7171bedb319d2a8fa514bc4dc322e3ebcadc85e8ad",
      ),
      list_nil: h(
        "c912ac74d13fa61091059bdae32484e44aea05f439cbbfff7998ef0bfb0e3409",
      ),
      list_cons: h(
        "40b5c0b66834f312bbe3afcadd07911be4182695313be33394eef53d0026e988",
      ),
      eq: h("bc3de4d3492ebcf56e98f63459ea705005c1a4216cfc57113617738ae4d84870"),
      eq_refl: h(
        "3b01e364067d2ce2ac308da57512992635212487359b62a3c75f60686febef26",
      ),
      quot_type: h(
        "7f7b22596ffee865e1be503216e360ab7dcbd0de645987916484c264ce52f9fe",
      ),
      quot_ctor: h(
        "f06cc3564d1d269e96a51a3f41f1fae1214884ab6d555a11213b8bb2e9e517ef",
      ),
      quot_lift: h(
        "ce268528ab8fe6ec17039a37e73079e3453eae1675c6c76ef302ac87e9a0bd90",
      ),
      quot_ind: h(
        "4ce41a11c66a351352ab27fdfbda9d980f6e296a2fa7f20fdd41377482ed3d52",
      ),
      reduce_bool: h(
        "43875997e42a7c9ea04f24b924da2299aa68e4f2dfb626d67fccfcf5b5132660",
      ),
      reduce_nat: h(
        "604dc8af16829c747638e4b6d58be2baf5280077f8de9db71acb6ef8bbc5f25d",
      ),
      // Synthetic kernel-only marker for the original Lean-addressed env.
      eager_reduce: h(
        "ff00000000000000000000000000000000000000000000000000000000000013",
      ),
      system_platform_num_bits: h(
        "6fb004fbafb4b68446a57550e21ac08d7599cb157ab194c52fcd7ba1671f10da",
      ),
      system_platform_get_num_bits: h(
        "b9fe4dfbc707ca46de307491541e35ad89a93115245bca3860b74ebcc96a1af2",
      ),
      subtype_val: h(
        "1cf910601d9d86d741333d9547d69d0e299bfe2f99a23a9e838d207fd641eac0",
      ),
      nat_dec_le: h(
        "e34083eb212a258b36374129f6170a9972adceb78356b6c83aa32284ad4edee3",
      ),
      nat_dec_eq: h(
        "a466eec5433bc056803f38b897d9913f91d836260c6ba4176374d1b66f98acc8",
      ),
      nat_dec_lt: h(
        "759a284b4f73e6aa405b409d741fa2b35642693bd041e74b790623121c5e1e33",
      ),
      decidable_rec: h(
        "19e688c7cc2966eb4f79a58eb501c776689f515a7a4cb39fdf7482f1294a1511",
      ),
      decidable_is_true: h(
        "d235a7033c457dfed0f1e34d1d50e97279893b63bdcab3c4490dd9da7d47327f",
      ),
      decidable_is_false: h(
        "2c26576bf92a0d9c2d169be19317e587eec54945a5a241c30dd84908d534d5a1",
      ),
      nat_le_of_ble_eq_true: h(
        "16c9cae0ac27b93644943a84c426db889766476ddb12b0a8b82f76cd2d848561",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "adb3eaf42d5f4c368bb929b20cec07fa96f9c9fe70d372ec72b25e6510ae14d4",
      ),
      nat_eq_of_beq_eq_true: h(
        "2a2e813ddd907721551718bdb3a2f8248231a041a39563d6d68798aa48425ec8",
      ),
      nat_ne_of_beq_eq_false: h(
        "a09735868d12586f23121cecf12ea2dd1f197f1d44dadc94b7e056d6cceb1980",
      ),
      fin: h(
        "aca8ccd74023a139175db5f1b5b4d037ba1559e25a5d091f2bdc797b23dbb275",
      ),
      bool_no_confusion: h(
        "68bd3c3b59b4bf7285096a8a0b90308db6307b082d24a08b91924b5e6cdcb53a",
      ),
      // Int primitives — LEON content-hashes from
      // `lake test -- rust-kernel-build-prim-origs`. These are the
      // addresses KIds live at in `orig_kenv`.
      int: h(
        "2c073df1601a9c8c7f26bdc51f22b8b7c6072fe6acbea71f244b4f67ceb1472b",
      ),
      int_of_nat: h(
        "c7804dff4a217f857cb6ff58e60d9cb405bc48caffba3240e3f5601d359f9f21",
      ),
      int_neg_succ: h(
        "a8fa07b6cbfec95b534e33a342ef8812aeecd00fbbd2378d71be0d45b876331a",
      ),
      int_add: h(
        "5ef343c73bd4a1c1c7de0701ee822797783a988f8c71965316c7f44a64d5a9c1",
      ),
      int_sub: h(
        "fbfbdc2f6d22d80e3ffb43897dfffedaf5729d5923d412c9bf5cd63ee7790bde",
      ),
      int_mul: h(
        "43b5d0d51e29a259302707a64508345354061bbf2249aba25bd9962d0cdd538e",
      ),
      int_neg: h(
        "8cf21639a1d062be65fa2a475a9a9945d43aa07344dac30a3eacdc512bab14de",
      ),
      int_emod: h(
        "f528f52cf0c85aa71a26f9ed88d11e488c110a7b0854c74ddd0c95ff8f8d1f72",
      ),
      int_ediv: h(
        "8b7ec664a8781cb34ec3678d2ce7fe4e22574ab5605c4988d841c84d8c63d6b0",
      ),
      int_bmod: h(
        "61b9e1d73ecf8dff84ed4e7499c7552211695c9cdfe4a432f17e36c432efc7b2",
      ),
      int_bdiv: h(
        "db0b8bb87b0d4d9fd68fa5039c3657866e122f2dea5e891bd2a0eb16569596b7",
      ),
      int_nat_abs: h(
        "cc43f34a58ce42dfedfdfb0c07a5f31dffa6ba3fb272f3c573ec547eaef722d6",
      ),
      int_pow: h(
        "ae92f05449a4d67697f3649225f88703a6a928a815b7cf6448e92b3a787a1103",
      ),
      int_dec_eq: h(
        "6dc280a4f5be950140e02d61f81ce01b1e21ec06f338a973039bcebf13e8e08b",
      ),
      int_dec_le: h(
        "dcce6645b4b207f4805c7c6878b7704ebd840903387f7848a3e544fe196f6ee3",
      ),
      int_dec_lt: h(
        "ecffd44f689ee7dd7462e3a4b4620ae72637bc59c38b91e8dd5c3d98d899623d",
      ),
      punit: h(
        "e4d0247a1393397d7efa718dc31229b3592a522531595290683ca63dfe420e4d",
      ),
      pprod: h(
        "ce996300ab608fc33ff251a16ac724b19f169dac8ba3fa1c5be2276158adcf5c",
      ),
      pprod_mk: h(
        "0a9e6c68e0531826a4b7e6cb74c5dacb7689e7ef1b78fc21f56acaf65ea25add",
      ),
      // Names previously matched via `is_const_named` in whnf.rs.
      // LEON content-hashes from `lake test -- rust-kernel-build-prim-origs`.
      nat_rec: h(
        "02af71bf807e615ee42b36d8d5b210329cddfd1e739fc11f6ba097a2bf74fe5a",
      ),
      nat_cases_on: h(
        "df2e7a477bd8b2ac4936f22c6a60a98e9055759cbcb856895497ee02bbd4af67",
      ),
      bit_vec: h(
        "6f450298341dec31bbbd159414a9193b437e8541e24304c9b680a7d5384643b3",
      ),
      bit_vec_to_nat: h(
        "ae3d3b7ad4c1376fe9d30b335ee19a6e5397672a5b5800f2a0276f8d249d2ed9",
      ),
      bit_vec_of_nat: h(
        "b685da004503283d7a3b2b73a3ad29100762de6eced0b305aede886af05cb3ee",
      ),
      bit_vec_ult: h(
        "7d0fd8eb0e739c1643319a0e6554ee7070aa575416d54c80f8f3d2b166cb7ac8",
      ),
      decidable_decide: h(
        "741a3a166dabcf41a357ad70893ac52feb84068a4bc9de54596bbe602648e3d0",
      ),
      lt_lt: h(
        "3f3eff2353822391e4db7f2b403cb79d2fca36c5a9a0d2dc4fce20850bb8b355",
      ),
      of_nat_of_nat: h(
        "f75083bb57a4a1c5ce0b83945e39da01e11fb9f28f2ab4b57d8f0615ccda8c9d",
      ),
      unit: h(
        "a9be73125f8d296246aa55a183e74d49c420b79c852c36df4fbb87a2ca1d751b",
      ),
      punit_size_of_1: h(
        "6f48fa355d342f1b035ef0777c1ad72e669978816c2c09a3048c4848de4ff443",
      ),
      size_of_size_of: h(
        "ac6c0f1adb8f8f74235dab15b624902bdc0832ed77fae0d62242d0e7717cb06a",
      ),
      string_back: h(
        "54317bf07a28017fbfccf7d9f11c97846c106be220ab98ce1e1b58a196c12be8",
      ),
      string_legacy_back: h(
        "2943dd3d52e8db4fc5b68543ec64d786ba8c70c1f304fe1c0164cc80f2aaaf17",
      ),
      string_utf8_byte_size: h(
        "06ba07154a1cd0e1e9eec2b6e27b195a6fc3ae20a70d1ced7643a61e4e3e6d0f",
      ),
      string_append: h(
        "93faafad0b7eff95765986eb5f5cb10635818129b72d8e7fdddaca2a5fb45844",
      ),
      string_dec_eq: h(
        "a53c141a7bbbbdf77d4a2cb049911fd4001f7d71b94ed5c3b877e837da94c349",
      ),
    }
  }
}

pub fn reserved_marker_name(addr: &Address) -> Option<&'static str> {
  static MARKERS: LazyLock<[(&'static str, Address); 2]> =
    LazyLock::new(PrimAddrs::reserved_marker_addrs);
  MARKERS
    .iter()
    .find_map(|(name, marker_addr)| (marker_addr == addr).then_some(*name))
}
