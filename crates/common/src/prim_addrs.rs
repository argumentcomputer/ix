//! Hardcoded primitive content-addresses.
//!
//! Lives in `ix-common` because several crates need this table: witness
//! builders need it to seed primitives the kernel FABRICATES during
//! reduction rather than discovers by walking `refs`.
//!
//! Addresses are blake3 hashes of each primitive's Ixon-compiled form.
//! Regenerate with `lake test -- --ignored rust-kernel-build-primitives`, which
//! dumps the current `(name, hex)` pairs — paste the updated lines into
//! `PrimAddrs::new`. The Lean mirror is `Ix/PrimAddrs.lean`, which the
//! `prim-addrs` test compares with the live addresses.

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
  pub fn reserved_marker_addrs() -> [(&'static str, Address); 1] {
    let canon = Self::new();
    [("eager_reduce", canon.eager_reduce.clone())]
  }

  /// Canonical content-hash addresses, hardcoded from the Ixon-compiled
  /// form of each primitive. Used by `Primitives::from_env` to resolve
  /// primitives against a kenv whose KIds live at canonical
  /// addresses. Regenerate with
  /// `lake test -- --ignored rust-kernel-build-primitives`.
  pub fn new() -> Self {
    let h = |hex: &str| -> Address {
      Address::from_hex(hex).expect("invalid primitive address hex")
    };
    PrimAddrs {
      nat: h(
        "4eff35f9c8a98dc247d142cc249f4b3985df15f343536919e12edfa72bc4dd93",
      ),
      nat_zero: h(
        "c71205099a2902497f2150ab8e4cde07de6f7bacd9c92483bce4de96f137b14b",
      ),
      nat_succ: h(
        "8b1290e5bef5ec6fe00b659cd3488cf300b8393ec2dcccb7bc54c106213d9b21",
      ),
      nat_add: h(
        "dddceb4ce8f1c5e7a7a0a208d3a15e70b50c149577431658f50c39ddeb1ff2a0",
      ),
      nat_pred: h(
        "542e0c31f900818c9340ab6c892884e7cb986f6bf0dcc026971c1f69a3051465",
      ),
      nat_sub: h(
        "fef3e836e9df48c4df01657d7affa51fc45a8cef0ca88c2a4f573f467041a895",
      ),
      nat_mul: h(
        "ed09022d61ed8a1dbf0a8984ddc6b8f64c53c07aa1faf2a439644fc56f72c92d",
      ),
      nat_pow: h(
        "9f5172c1cb62afa53e3a1006990f49494bd2ccf15a6935780b8e2db36b9121e0",
      ),
      nat_gcd: h(
        "fe8e2ec10f267f0993337ec3ecc95b83dbc813c0d772cecf0ec314e1be91c406",
      ),
      nat_mod: h(
        "9ecd2580ba1e3f1167cd101da660a8a275ca4ababc5852953dcfc91110970121",
      ),
      nat_div: h(
        "3b449ee19fedf5943e918bdb4b1d434aa9e62cc0c8ab478eb10ddd2df43bfcf7",
      ),
      nat_bitwise: h(
        "7d0cc9e9aba5f2621021c034702b0c5751718e402b69c178972da23da3937d3d",
      ),
      nat_beq: h(
        "60715a1e76d31403a223485f28c74c4270b2bca66c437e9e11d1a5aff17ec861",
      ),
      nat_ble: h(
        "7ca154b768ee1421e4c68b931d29911325e342d821a53888e4647b706cab4caa",
      ),
      nat_land: h(
        "96e8408ccea0c808203eae83c07af598c7e6c7be42a41162cc25e89fad7a648e",
      ),
      nat_lor: h(
        "924195bf8769c1f82b1e9643f51896ace6f4474b9bccd451a6243287cf38039e",
      ),
      nat_xor: h(
        "2a854ccfd0f62a8a699e38607c0350853e324d790c40a4f27f1d684dca85bfcd",
      ),
      nat_shift_left: h(
        "6c5331afbd9de5eaeaeff6647398ebac0d71f6728946915b9e7df752cc5f25b1",
      ),
      nat_shift_right: h(
        "830fc024c194ad2ffa0f093ac8df77af05f32c9f06723f5effa9d369bd2f019b",
      ),
      bool_type: h(
        "77db82d7052a606eaaf324893161d6989049ef4e0f393e2fe9edaf52f4225ed8",
      ),
      bool_true: h(
        "ef156463a527bfd236472e606b2ccddf73f4585195e365e0430ee3c20921d8cc",
      ),
      bool_false: h(
        "a5fc856de635cfc40ab703eea51cb704dce6985fd7de921f94b8d635e9d3667f",
      ),
      string: h(
        "9453b6b0aeb66e0cd6e36b01b51e3bde67b15b837096ea96ba32b4e41db2dafc",
      ),
      string_mk: h(
        "05769905206b8a2cd9d9f82f2bb47084f6a97016efaef14cc6b3d7a14480e4a7",
      ),
      char_type: h(
        "72552513510812c5f5e12676d5a18e7c59d04aca7781fb9ad29b9f8549c2f79c",
      ),
      char_mk: h(
        "d54ba5429435d1a5fa6818757b40f6324b82241c5057abb640f8f777c5003e2d",
      ),
      char_of_nat: h(
        "c3aaf394d4d2d7a358423decfed631ec962bddda4467526d762767202113ecaf",
      ),
      // NOTE: `String.ofList` and `String.mk` share the canonical content-hash
      // because both compile to the same Ixon form (a one-constructor `String`
      // built from `List Char`). The Lean-side deprecation of `String.mk` in
      // favor of `String.ofList` is orthogonal to the compiled representation.
      string_of_list: h(
        "05769905206b8a2cd9d9f82f2bb47084f6a97016efaef14cc6b3d7a14480e4a7",
      ),
      string_to_byte_array: h(
        "8327ea2328818c14a44230ed31802012360bc0d10d80407c7b1f0802fa264ec3",
      ),
      byte_array_empty: h(
        "a2e6f9002d9c85a5b15ba4b84081c4d79d4953a4477f7eeef11c5347eb807391",
      ),
      list: h(
        "e4c9a8e4fb921be9d9b7ad0cdaaa4195ac2d0942141f2bfbea47e804f97591ff",
      ),
      list_nil: h(
        "892f3d35a4788c60b18e722f14215603a59fad868b0b8bdad68954fc312fabfb",
      ),
      list_cons: h(
        "80c5ba913d234543c9dec70cf3f39c348b1785b976684c35bae33ac9b96234c2",
      ),
      eq: h("8283e2ba6471c8318a8637d7346b54fef85c5e7eae35df4b2d482915e02c415d"),
      eq_refl: h(
        "9733a9248863e7ca2290dd97bc544c5e6bf8d54b29c8cf955c1db7d3dce99716",
      ),
      quot_type: h(
        "30cb0558b0b4e65d26189bcd146b044f2d8078e5e8a1328728212ceb70c2b37f",
      ),
      quot_ctor: h(
        "6c5f020fa71c2dc8661042152a8387bd9b451e44e7dfd22e2184e60d008ac98b",
      ),
      quot_lift: h(
        "0b3e6c618c4b071e66e8fcacb8f79e8ac973fc7269337fe534cd97a222e564d6",
      ),
      quot_ind: h(
        "9bbd6787a148a17068d2aac13e43addeee405f0015a8e164e146a6b86168c891",
      ),
      reduce_bool: h(
        "5de91d01cb0cc7e1ef182265342bbd734b17b6c6db05078cf5cd2b8940713148",
      ),
      reduce_nat: h(
        "1e17ba5f7d9b02f6b4ff567a892bd6f4674ee0ad779ddf50faec64b2c49e80fd",
      ),
      // Synthetic kernel-only marker. This is intentionally not the compiled
      // Lean content hash: `eagerReduce` canonicalizes to the same content
      // address as the real Lean constant `id`, so address-only dispatch would
      // give ordinary `id` terms special reduction semantics.
      eager_reduce: h(
        "ff00000000000000000000000000000000000000000000000000000000000003",
      ),
      system_platform_num_bits: h(
        "cad987902ae218507d32365ed1d50def0532787957e8967d24c47f088504f96f",
      ),
      system_platform_get_num_bits: h(
        "64091b011bbf318f26bb2c84650cd9b66bdf6f03d1f7da95830e1b04eb2405c3",
      ),
      subtype_val: h(
        "d3e5cecbbfae503cf2be2a01b7763f0f51aa89f358be156ba0805e3cc287f81b",
      ),
      nat_dec_le: h(
        "19a2fa64b6ec0fb9833405709daf397763fcd301e97126d6b94db6cc4b74486d",
      ),
      nat_dec_eq: h(
        "a1e1eb8c3f2d9911152170b4350acd7578fd350eba365019ba447743370c83f7",
      ),
      nat_dec_lt: h(
        "ca989f4ca063b20c3d7e906b1548f1113ec37639ed2af0242add396470b75bb6",
      ),
      decidable_rec: h(
        "e7012fff108d4f267d5262b8d3337a4eceee661a612c21136ba968f34a8ca8e0",
      ),
      decidable_is_true: h(
        "48f3948c2ff1756d8fd1dcbbfe389b4043b0ca1142810d086ba76810073e422b",
      ),
      decidable_is_false: h(
        "ef055b6807256b5ca9e0289aa48c37696bcb2c19e7526a7920d3d9fe4387bd62",
      ),
      nat_le_of_ble_eq_true: h(
        "95c70bd18c88a4b68216db65cc9f06a5f82db8c450eed60989475e81f2537ac4",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "3f1316e9d97f8e860d7c0571fa0cf9ed9cacf09f6877901c6d372a5dd5ddb5ff",
      ),
      nat_eq_of_beq_eq_true: h(
        "a5db2676b189496e2576d25050e131e7d9228ba6559a14ebf8647da9c6171fa7",
      ),
      nat_ne_of_beq_eq_false: h(
        "a36ca0338f1c021c54d1202b45e74d925d2bba61702bf506a89ad18554cf4fb4",
      ),
      fin: h(
        "ba0845fbe202248f55cd6dd065a8cf619d86d5f981cbe5b805a2cc1e034f9b72",
      ),
      bool_no_confusion: h(
        "2cf6bb040826ec937ca30af21a2fe0a00a753e6aaa3d19748150c5e093daecbb",
      ),
      // Int primitives — canonical content-hashes from
      // `lake test -- rust-kernel-build-primitives`.
      int: h(
        "600b310f606d3280d81592d87b9e1e3dbf65bb0588ab9c768ae93e42a0f1bc2b",
      ),
      int_of_nat: h(
        "02d9c1c33edb983f1762845fc835178fb0987428f103b7a661d921ca1ac83903",
      ),
      int_neg_succ: h(
        "ea5998100b288b15e8c2b86352d17a9543356bcfd01beeed067bca9ba4e421be",
      ),
      int_add: h(
        "2955ec5e18cf9e3b5d33a9b7b5c77fea2d1386255e29db3259b70dd915357743",
      ),
      int_sub: h(
        "2bf464cbedae2766db8b1abd8f506f9026867470bee5eb205b3d288f208a267f",
      ),
      int_mul: h(
        "d8fd892631ba66726eb869c6c209cfa2cce79bbdc90cd2cb787a23106f71c7d2",
      ),
      int_neg: h(
        "dff2ef576cadddcbabaf9901afaec633a8d9339adbfb995dc83649261100de31",
      ),
      int_emod: h(
        "409dec138fe3909a91bbc6ddead1acce7fb1456d68218bec16d4b45b1baaec8a",
      ),
      int_ediv: h(
        "c5e6f3e89b81ad150dd38ee8d2b9dbdeb71b97dba147cdd73e512a127d56fc4d",
      ),
      int_bmod: h(
        "abc16a0d33db31ef490e4e6375c60a86f70bae454cd2f3357138e735aa79741b",
      ),
      int_bdiv: h(
        "b99e130816aa7474c6606434d7893a0adb6529a68c0926e8ef9d8b68a5f7e11d",
      ),
      int_nat_abs: h(
        "61ca2ac86bf2ba5265c5ce0332157fb12259d2e8fb1c449e56c98dc77534ce1b",
      ),
      int_pow: h(
        "f84c33759cab12aa5502c141a700fc2345aae38ca8ee3bdbf5d45ddf9b6a1863",
      ),
      int_dec_eq: h(
        "b3f26f97f5a8bf58b0b872bb86dca4366ee843c7c5e66e9246d546aa68978884",
      ),
      int_dec_le: h(
        "9d5081f5cd648e4011f5432b4731ca908aeee30f631833230fccf53ae8ee004a",
      ),
      int_dec_lt: h(
        "a65d4c6d2901d6882ec994381e4d9bae23ebf44e439a3e0d8bf4a9f195ebcf9f",
      ),
      punit: h(
        "1f24b345045e83033dc57342cdd3bd2842d1c3a2c04b193c409873becb75b414",
      ),
      pprod: h(
        "0d2ce4c74d60afaff1374a1815386d85c5f2c8fffc022d68647321cc022483ca",
      ),
      pprod_mk: h(
        "5aa42169584200055600bde3b8299edba45a17a1659f371f7cbb53f1c6392598",
      ),
      // Names previously matched via `is_const_named` in whnf.rs.
      // Canonical content-hashes from `lake test -- rust-kernel-build-primitives`.
      nat_rec: h(
        "3dc32a7921881e8d7e882cc407c88a29ab9eb6886d4c8d06737f5fa5eb364d9d",
      ),
      nat_cases_on: h(
        "05bbf91cc5f5857dcf31889f1757af2f38d9aa19a400bcc1ce063703d06f44ca",
      ),
      bit_vec: h(
        "4035f2f9376c166678e218090d8ad310c831956e2dd1509a7721c0c8b9485087",
      ),
      bit_vec_to_nat: h(
        "09681380c93b474123dfe8a344481297dff500d266a28b0d3e456f8170cd3de6",
      ),
      bit_vec_of_nat: h(
        "f1cdd30b88094caf70371245abf5ff3f1acf5fded196f4155fa536e126a7df6d",
      ),
      bit_vec_ult: h(
        "43bee1d933c3e28ee41e17cccbf567e989ea45d835c7631be05a46ea8189494e",
      ),
      decidable_decide: h(
        "d1a0f891ac4b85cdff478113bbd5ca0029d9f121cb4e0c3bc26d1a2a494cf68b",
      ),
      lt_lt: h(
        "34ee35af6409123b16f55c67cd65d4f48f525a3139545d04b61d8b2fd7941550",
      ),
      of_nat_of_nat: h(
        "72c6287074ab54b933bebf28c45f50f4b3f411a8fc9be1cf989f7a85565def09",
      ),
      unit: h(
        "585e362473d1a5811630ce9ce11b21868b6053a1419e7e3e637d8fb8fb0f9fce",
      ),
      punit_size_of_1: h(
        "6a8b99388c4191b1652053eee475777a791655d0f42df5ff8c09f02062f2f56f",
      ),
      size_of_size_of: h(
        "0e87647301ea0cb27db9f3218c25a713fa713dcf71b42478a9bd7430d303ae3b",
      ),
      string_back: h(
        "1ae98f7e1d03a491f11bbe3b963af97245afa08ff818a26c9cd6f8cc342187e7",
      ),
      string_utf8_byte_size: h(
        "88091d363f2573e373d9a0bb0583eee794a444bf5349a0822945523477065104",
      ),
      string_append: h(
        "e79d3e9179930b799fdc73995ebb4d3cb54121eedc904366bdcf500e261d77e2",
      ),
      string_dec_eq: h(
        "0803fbe1abc2e1d180631c22ad7e29a832d2b871584b53ccd98a6092e4b2b4e0",
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
      ("String.utf8ByteSize", p.string_utf8_byte_size.hex()),
      ("String.append", p.string_append.hex()),
      ("String.decEq", p.string_dec_eq.hex()),
    ]
  }
}
