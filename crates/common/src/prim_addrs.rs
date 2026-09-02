//! Hardcoded primitive content-addresses.
//!
//! Lives in `ix-common` rather than `ix-kernel` because several crates
//! need this table and `ixon` (and everything above it) cannot depend on
//! the kernel — `ix-kernel` already depends on `ixon`, so the edge would
//! be a cycle. Witness builders need it to seed primitives the kernel
//! FABRICATES during reduction rather than discovers by walking `refs`.
//!
//! Addresses are blake3 hashes of each primitive's Ixon-compiled form.
//! Regenerate with `lake test -- --ignored rust-kernel-build-primitives`, which
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
  /// addresses. Regenerate with
  /// `lake test -- --ignored rust-kernel-build-primitives`.
  pub fn new() -> Self {
    let h = |hex: &str| -> Address {
      Address::from_hex(hex).expect("invalid primitive address hex")
    };
    PrimAddrs {
      nat: h(
        "1dfffde48c4ef6653b95ecc5474dee8b99461008d26d80ca384f1e59e927714d",
      ),
      nat_zero: h(
        "50e5d69d806bc1c616cace4230c982a0ee5b350b3efe3b1a15801df77fc00c8c",
      ),
      nat_succ: h(
        "8c09ca644b10decad158d37006e81cdc1b84761312260546449aa02e343b2b0c",
      ),
      nat_add: h(
        "f9ac92a11388a7cdca229a8024208554feb32d6c0a3af74a7bc12c28b949543c",
      ),
      nat_pred: h(
        "fce916cf3c6dd01ad8c6d38641bca7b3eeac5bc93b3529ad7812768b3407d64e",
      ),
      nat_sub: h(
        "df38352ffa1d6e292349259f33eb678024bb646b358638a02da1995ed4abeb09",
      ),
      nat_mul: h(
        "f38d4f7baaa021e3b555312145d9ffd3ddc5eacb7bfd5b86a7b0eafdfcf416aa",
      ),
      nat_pow: h(
        "68f61ef55b63cd23ad8ed185b7eec3dc754e61cc58056087a97e819d0e95e6fd",
      ),
      nat_gcd: h(
        "ad47f2bbe891b825c48a278f9a0d72997b78baac79891ca6651988b7c9b47f03",
      ),
      nat_mod: h(
        "f6eb742996c60f1068c2d437afdd8b3609040d64eec5e15f07a11dc11d070d7b",
      ),
      nat_div: h(
        "23173649a58ea5095d1c51a21c7ad2cf8e8dccef342698e07e241668ff7ad3e7",
      ),
      nat_bitwise: h(
        "85a6fefff63e96a963ef8406d394ab39992323a0ff4530e134a94d46e3a7ba4d",
      ),
      nat_beq: h(
        "72c6d4a3b653798850a9ed57018b87ceee0e34195c0902858fd41f6f0e9962ae",
      ),
      nat_ble: h(
        "c37f2e811f44d59c07094947146ffcbd3aec5ec7002ac3c48ebdebcd83d4688e",
      ),
      nat_land: h(
        "8f475cc72da2ac6ce2a9282b6b5df4ccf7bc3cee0649d22766bebd32d1806f3b",
      ),
      nat_lor: h(
        "8f3c1c432c598e4240d36f8945942174675c5c91e03f6b8ab018e8b052622c63",
      ),
      nat_xor: h(
        "800a8a2d6f91bd1a91d313d1e19ef69f37dedd07f7de4f929780be855a03fd1f",
      ),
      nat_shift_left: h(
        "5473592e707943ec072a2ee53c433da2c77aa45ed634da54b24374d19eb90cd2",
      ),
      nat_shift_right: h(
        "1b591149158d896937eebfd53232b5ae8a4bcdb25a6811c96bd94114a9f8bed5",
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
        "4288f92ed1d51f4935e5d2775f33ec585d6fe5ec63dadf0ea698554478fd9fad",
      ),
      string_mk: h(
        "d54db71fee55311aafeead74768e6e952262c29abd24b9319fa6859481dd44b8",
      ),
      char_type: h(
        "d55429725a19c1837b34624fb35784b91bc8b0e2d79f98b3c296317fb6c5c789",
      ),
      char_mk: h(
        "7b443f2f10fd4b2fb88b59e90f1a04b46552f73ea2e8f26d77290b7ae63dd531",
      ),
      char_of_nat: h(
        "29563da271c23f66b27d05f924fb0612272dcfba6b1083b348733e00f9b36b2a",
      ),
      // NOTE: `String.ofList` and `String.mk` share the canonical content-hash
      // because both compile to the same Ixon form (a one-constructor `String`
      // built from `List Char`). The Lean-side deprecation of `String.mk` in
      // favor of `String.ofList` is orthogonal to the compiled representation.
      string_of_list: h(
        "d54db71fee55311aafeead74768e6e952262c29abd24b9319fa6859481dd44b8",
      ),
      string_to_byte_array: h(
        "ad700c0806e673e74adcafc28ca659d30a616633a4a36420324fc29eae69eb9c",
      ),
      byte_array_empty: h(
        "d838bb6bb651533081ac2495a25d690c54f8e345fff41efbd5585eb468705308",
      ),
      list: h(
        "ae8d736dd3fcc89dc3f9d66aa54bed4ad8607fb9d4843f4c8736591dd0c9e000",
      ),
      list_nil: h(
        "3c0149c3432969ee5d9354c8d2d89ceec4a79711f8dec8710879a12a12b72c42",
      ),
      list_cons: h(
        "d1e0802c38bcda14061e2012f12e73c2a24a671137984f8ef76744ea04d188c4",
      ),
      eq: h("b20ea17ba3d9723f0bd06457d9cf48ce26ca36619b946980627de923873e9595"),
      eq_refl: h(
        "e308035bdf280c927556824d6a9f9236a1487651f0059a7df3bda85b331f67e6",
      ),
      quot_type: h(
        "e775aa31759a9d4acdbc2b8519ff73f57552bb0cba4daf1659bba00f6a931b4b",
      ),
      quot_ctor: h(
        "0a4cc7c930dd6726bbd7f1bc3fea685df5f666549d651d3e766fe5746ec459a4",
      ),
      quot_lift: h(
        "560276f95e0d93e27b8c05097995bf82876332c2e7e31033e0a194819e4e8d30",
      ),
      quot_ind: h(
        "02f358808fd4328d74850582d3608d2d31e49519b4c6c66b3605fbe6f42d3c5d",
      ),
      reduce_bool: h(
        "d4d775ceff37ab7a402416118f1d2ce5b9e7f2143d0c3dc8fe5431571df3260c",
      ),
      reduce_nat: h(
        "2075bda5457b299b27246770c8416273686bbf627aa6a01ac413a27e583eb95d",
      ),
      // Synthetic kernel-only marker. This is intentionally not the compiled
      // Lean content hash: `eagerReduce` canonicalizes to the same content
      // address as the real Lean constant `id`, so address-only dispatch would
      // give ordinary `id` terms special reduction semantics.
      eager_reduce: h(
        "ff00000000000000000000000000000000000000000000000000000000000003",
      ),
      system_platform_num_bits: h(
        "5060a22df86307dd8bbe656e13868f3a1618e7a0d880b8cbb00759cffd31800d",
      ),
      system_platform_get_num_bits: h(
        "80f975ded9d6ab7095e9db2ed1cfa6f5c35eafe5c56990e2c1321b02c5664e6c",
      ),
      subtype_val: h(
        "7e4e9b33b696a7d3fce1745dfb5fbeeb938fc8882a82bee15723e0d253e59158",
      ),
      nat_dec_le: h(
        "2999801598c1da48f562d4836064f635c045d0521452b5e74a12bf99d2e316ec",
      ),
      nat_dec_eq: h(
        "1bac041756ed22d73bbcac849a94f246ee2696999faf351940468d962970ca2a",
      ),
      nat_dec_lt: h(
        "12f386f486913b11b5473cb2538330d51f25aeec7f2d7d6b96904329c78b6967",
      ),
      decidable_rec: h(
        "6af73809a6128adcb9c5d7e73a30c28d489dba4d905717055ac2edd755ffa713",
      ),
      decidable_is_true: h(
        "7b3f6a6eebf32a9d5a54305e693dce60511afeb1fa11bc8844a5c21bbfd3214c",
      ),
      decidable_is_false: h(
        "ab1470196419f71d06feed9ccb8c1d03674528ec03012b095badc169d48d03d0",
      ),
      nat_le_of_ble_eq_true: h(
        "23bea3bbf3a8d0a8d0033cf7e56af0c4aee01582d5a758c0df5615929ca6204d",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "be50b6053df0b07438a4ac2eefd70a11708b0cbb0fc90564bafee6e165615de8",
      ),
      nat_eq_of_beq_eq_true: h(
        "c489329197b59a040d1e5e4d5de6a770478d1ea4f9750176026dd2bf8593bf22",
      ),
      nat_ne_of_beq_eq_false: h(
        "0eb5b987f12124be0575a477cc0a535516a24b0ae5ceddbee2d472765aed299c",
      ),
      fin: h(
        "a7e9a8b84a2fe96cc204acc93d7ed1366d9d0574aaf0f09633d2b09a94c9e860",
      ),
      bool_no_confusion: h(
        "99e7eaac2b27ffae4adc4902f8965520ee696c662438f10169cf36c8ad4cc4e5",
      ),
      // Int primitives — canonical content-hashes from
      // `lake test -- rust-kernel-build-primitives`.
      int: h(
        "fb2bd9d8fb7c3cc603bc021dcdbc5c6aa3ae80688b7d2e85ab18fa336ccc04ba",
      ),
      int_of_nat: h(
        "48786b7f7adc632ae35059f3fd181df32d9e5cc7360c4fd02c3e8b1181a1539b",
      ),
      int_neg_succ: h(
        "cfc934fd6d53a5b23b6a3b30d02165fdaa574e3b5eb13926bb166e6486fc0e50",
      ),
      int_add: h(
        "1e60bd377a746cb7bd7ae541d7dfb237097d883d28ec7aadd732c0674e0db964",
      ),
      int_sub: h(
        "0d74ba85f9749a0c25aa6a2b70348e57e709831fb7cc05229fecd7d66adf184d",
      ),
      int_mul: h(
        "c5bef6be6c3fdc520454c11e9950eb2f1a6c92f41a646b5ca168ff198f13c55a",
      ),
      int_neg: h(
        "bc61c10fcca6415223ed97bcae21cb99d4836d077b0786a2fc5c5905f8b04ba2",
      ),
      int_emod: h(
        "d435a15e6f222f786b6130fa764c7fbe98746f798e97a627a6237a17e74f7227",
      ),
      int_ediv: h(
        "3e13fc1a077eb692af40acbed4a6adae255c0cbbba9a3c1f0de29573b197cb0e",
      ),
      int_bmod: h(
        "9970f402c870e8a3146fbf4b76f949aa64b206de9b0157b469fde357b715f19c",
      ),
      int_bdiv: h(
        "867f8e9dfb752265ba4742368b6afa546ae4e240fc5ac69b4a4e86d85a6e46f6",
      ),
      int_nat_abs: h(
        "21d4dacc0f406b31e044fbf4d8987a332dd8b4244f7d9e62b086501474825544",
      ),
      int_pow: h(
        "878599e9f5bbccb942232ff93b62c63db4ebdf62b9f9237900a37049f422ad86",
      ),
      int_dec_eq: h(
        "7a06496d07b59710348a5f657851a4eea1f59492a5b7de3f51abbc84f9bc1d17",
      ),
      int_dec_le: h(
        "14eccee1deba05e9443bd169d00ed634170e3246b37921199edbbad3f67db5b4",
      ),
      int_dec_lt: h(
        "ad32c05d7e3c5ddf4e4c85cf8f60d83e0fba55e2676bf8a1e608db54b167c9fa",
      ),
      punit: h(
        "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b",
      ),
      pprod: h(
        "7eac420873e8f1ea8fe66831a6c6f69d88693bed6aeb30bfba82069af60ebea8",
      ),
      pprod_mk: h(
        "f3993d287c47b81c9e0902aa91d227650f6f4e55b3a1c63a87f283b4ed9e418e",
      ),
      // Names previously matched via `is_const_named` in whnf.rs.
      // Canonical content-hashes from `lake test -- rust-kernel-build-primitives`.
      nat_rec: h(
        "89d6690b0808b1da49e015a4f21df3fc3f00fb96ac502f5f097ce452e573704c",
      ),
      nat_cases_on: h(
        "b2f8855b5e76a480493cd6cc922977e60723b4bec665dd7e9b73ca2b215df576",
      ),
      bit_vec: h(
        "c7192ac507d67c3c3e1eb90633858ae7b7cbc80e3988312618c7ec09b483b04a",
      ),
      bit_vec_to_nat: h(
        "acd9f0a3f7e8c53a46b91759358366fa028240b0b6cc09205dde34a33544678d",
      ),
      bit_vec_of_nat: h(
        "5721ca2acf2c6994771509332fb185f783f442aefce417d2863e2d148edcdb8a",
      ),
      bit_vec_ult: h(
        "8d57c7c6aee1ba510d3208ddc4b08a83b44319f6af8ee09b3940d0ddedce1eb6",
      ),
      decidable_decide: h(
        "d1107c99ad9ebcb5028d9aea0da521ed5c12e71ea2ecdeaf637bb4a14d4a7e44",
      ),
      lt_lt: h(
        "c69df4833ecdce76bdb0d23159e1fac652d88919768c312c6611dc060da16f04",
      ),
      of_nat_of_nat: h(
        "c68bfa47519ff72b1d053b86e6e3b7356286eb2252616cc5b2acbed59ef1f5f0",
      ),
      unit: h(
        "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb",
      ),
      punit_size_of_1: h(
        "84fe3d0f08f0651a6f0936a9a0f18e4f0dace169ac4233bf1adad05d6e078a25",
      ),
      size_of_size_of: h(
        "78f38887f6bbe54339ecec6b3c5f66856de7baa530378d2d9065bfe2daf4b801",
      ),
      string_back: h(
        "3f92a46a1451fd66215aae9cf789ce38a2c73fdd55909d454f61259634d90b6b",
      ),
      string_legacy_back: h(
        "a2a310133d17371af67cd91d279aaf735fa8cb810c39aaa824a443c652e3df66",
      ),
      string_utf8_byte_size: h(
        "b1f6f04bde3d81f9102ea6b7d2c9f4236d72b17e01125523c5d5e261afc71105",
      ),
      string_append: h(
        "b6ec2d443f3ee61de45ad859b8cc41a896d8fba49bc29883fc34c427dbdf71f8",
      ),
      string_dec_eq: h(
        "d616327d4fc219bd7114bad46cd0866befe2551518b5bf2e10b5cac93381fb77",
      ),
    }
  }

  /// `(lean_name, canonical_address_hex)` table from `Self::new()`,
  /// in the same order as `Tests/Ix/Kernel/BuildPrimitives.lean`'s
  /// `kernelPrimitives` array. Used by the live-parity test
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
    Self::parity_table(&Self::new())
  }

  /// `(lean_name, original_address_hex)` table from `Self::new_orig()`.
  /// The name order matches [`Self::lean_parity_table`] so the same live
  /// primitive catalog can validate both address schemes.
  pub fn lean_orig_parity_table() -> Vec<(&'static str, String)> {
    Self::parity_table(&Self::new_orig())
  }

  fn parity_table(p: &Self) -> Vec<(&'static str, String)> {
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
  /// Regenerate with `lake test -- --ignored rust-kernel-build-prim-origs`.
  /// The
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
        "ed99025afee9212ecf57c260d56d5dce9c901628cb0080421989da4fe979ede7",
      ),
      nat_pred: h(
        "26245a09319bcf9d55a08431bce3b9d8a8d09e3dad25b9a83cc666e3736deeb4",
      ),
      nat_sub: h(
        "858e3184f315fc8f85614d8ccd6f854a71bb8ff1d2e2c0f2819bf411ff25f294",
      ),
      nat_mul: h(
        "ea30166fa0b64cf3da2d952ed470d6c3d33de3e85243f95026f3b5262367ec9f",
      ),
      nat_pow: h(
        "5cf09dd7481dee82376ed65b09a08ea716f3575dd5b0b2d76c04c4fbb2a36a5d",
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
        "6a397f8ed945046604a856b84b14a683b23916d83e794fd8ecc3348be87a8486",
      ),
      nat_ble: h(
        "25bacf590070ada376418c4eae60a90fa529d56951f451166cd6ba15cf0eeb68",
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
        "e09f39bd5d0655d8a7844447e85c5a865bb0d233e7512f21e3de78d15808eb59",
      ),
      nat_shift_right: h(
        "6be9556dba2dedb10ea06533ac97de79a1d4973f32f8d0657a1467ea1f746e32",
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
        "ce908a2c83164cb59df5afba6345e29fa1ae44032e2aed8ac4d7fc0c87951849",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "adb3eaf42d5f4c368bb929b20cec07fa96f9c9fe70d372ec72b25e6510ae14d4",
      ),
      nat_eq_of_beq_eq_true: h(
        "06f72598e90d27fd5ba7700a2920781048e9712693b5a2d20df885cb203aa2d3",
      ),
      nat_ne_of_beq_eq_false: h(
        "0bc9d7d2a3d61217967bec2dbdfdbda85e6c41dcb5340d859d0177beeee18437",
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
