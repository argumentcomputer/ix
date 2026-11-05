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
        "35e1cc809f6f076521a43f85068d5592220407c0532b6a08952f40d8523d04bc",
      ),
      nat_zero: h(
        "eeb2e6268ff6d0e6b2e9764d9940b81bb64b9f8f4b1358d294ff9817e6941a46",
      ),
      nat_succ: h(
        "42d6ed31536f0958176f1dc973383808ac8583223746ebca78dbe389b65321a6",
      ),
      nat_add: h(
        "3e8aadcc611c4d8677cadf00c78506561d33738ee3d571f7a4196e260580c9b8",
      ),
      nat_pred: h(
        "3244687301d779ec757274761d903def3eb3135177327b709bcbd854ef496f79",
      ),
      nat_sub: h(
        "03b3a041285b0fe202d90b227d405c4cec252df18ba7616acd6dae2792e672bb",
      ),
      nat_mul: h(
        "373b7d74f6b40da11b7ed79603a45ec7011a8831b720b57d2efe92e82a3d57f0",
      ),
      nat_pow: h(
        "5baaf05c969d2cf377312111be51bb64c600c13fa164ee722e92243b0f771bab",
      ),
      nat_gcd: h(
        "aba94bfb41351d4db36172c379a512f04219ef21dc5454d71590967d4e8f913f",
      ),
      nat_mod: h(
        "11abbf986481c53a21c8cb21ee2581ae6238aedbec15f972959d086bef1a1985",
      ),
      nat_div: h(
        "824d1c53d8c1c3cf0a27f24639ec2be1ecc13d4a01c993171595edccf6949737",
      ),
      nat_bitwise: h(
        "adaf32f49aa6fee4ac8b0742563494b381e0742d9ea685fe2456eb71b25fec08",
      ),
      nat_beq: h(
        "d3d8ff924af9dc4b5cd869760615b3e7ee80916bb617259d45890c69f4128337",
      ),
      nat_ble: h(
        "9e445b9d5f8252772347872e909b5db4e7eca7086cedf4fec6de840f6b7b5f92",
      ),
      nat_land: h(
        "de8c100c22f82a5c3533c67e4370671813434a6fec5d023998ded090df4a4934",
      ),
      nat_lor: h(
        "93afc1cd298c63606e5f468d1e5989ab4680d256e95d07a8642a88b5c6b858e1",
      ),
      nat_xor: h(
        "77dd40d7b6ca310cc59466d1f24df4f180ef50e1b00fd850698458cd26901c5d",
      ),
      nat_shift_left: h(
        "05bb657e8b9d5dc224e7ef3d53e54153ce3ac26da8d1f1b1d61069a3726566cd",
      ),
      nat_shift_right: h(
        "25019ff485fcf5709597cd1e07fcc3ce796776ef3f715a6d187eb5831c63b4be",
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
        "221625a00ee2d6b96297e34d7e05bf7e4fd38d8d99d3e1d64a7cd2e06ca0752d",
      ),
      string_mk: h(
        "45dcb3c5e5ada3bc0ca52d62a66f7f9dda3507df71061a5c200adea0cf241014",
      ),
      char_type: h(
        "065fc8b41393f525c1e541b9d4bc97c20c13bf23a7209a2093b6f4527330114a",
      ),
      char_mk: h(
        "60cc6cfe4577b99a30113d09e9921f2253fac15fe3d5ad976b9dc3626edc6822",
      ),
      char_of_nat: h(
        "cff875914f3f8b4f0014d1eaa223c6b9da7201239bc5976e140b69d99cd1f357",
      ),
      // NOTE: `String.ofList` and `String.mk` share the canonical content-hash
      // because both compile to the same Ixon form (a one-constructor `String`
      // built from `List Char`). The Lean-side deprecation of `String.mk` in
      // favor of `String.ofList` is orthogonal to the compiled representation.
      string_of_list: h(
        "45dcb3c5e5ada3bc0ca52d62a66f7f9dda3507df71061a5c200adea0cf241014",
      ),
      string_to_byte_array: h(
        "de013024c598e5f0c3dcd067f506e1d2e32749573522acb539b61400627cf897",
      ),
      byte_array_empty: h(
        "4da661917a58152f5ca974d2256d98efa9d722c4f16382e9cdf016df4c574368",
      ),
      list: h(
        "4fb6b41c30532e6ab4acb4eefe01da1314ee7f2129af8989fd63f7ec277aaf01",
      ),
      list_nil: h(
        "3994bc51e3686f30a1d483d69d0a835a7b484d892393c084f87a5849de54f302",
      ),
      list_cons: h(
        "b3a7d80249fd823100ee03626232d1412a0e8335275d5df53b92943887b650f7",
      ),
      eq: h("c37d6290e00fb865fb5db7bce18fd69e6d1674ad573724b85466ea9f7578a207"),
      eq_refl: h(
        "d494dc601386ba8e8f0b711fe62a2d60ab60c6488c8cf6ce97796ebc3ad5fefb",
      ),
      quot_type: h(
        "45040b3126855169dad919a970a9c72cee5875658aedb3bd1f89fcdf8c88edfa",
      ),
      quot_ctor: h(
        "811600dfa59f3612cb03c0f0475af152399defff9226c6e19fd648041a6899a9",
      ),
      quot_lift: h(
        "86b365e75bb4230f04c6e4f3a7ca6988adf574616d79a3d7477ad65cac102110",
      ),
      quot_ind: h(
        "1745491c0d651de0bea589d5fffbc9bc4d7fbe897c1d805b1f7f59ca9696a6ef",
      ),
      reduce_bool: h(
        "bacc4c814a4572ddfd969a1857adfe18239eb6bd8b1627ee79744a6a9b23b030",
      ),
      reduce_nat: h(
        "b6327d9a1bbb461a447f0c971e622dd9a35132bd7de75bf69e20794d7a0e8595",
      ),
      // Synthetic kernel-only marker. This is intentionally not the compiled
      // Lean content hash: `eagerReduce` canonicalizes to the same content
      // address as the real Lean constant `id`, so address-only dispatch would
      // give ordinary `id` terms special reduction semantics.
      eager_reduce: h(
        "ff00000000000000000000000000000000000000000000000000000000000003",
      ),
      system_platform_num_bits: h(
        "57a31c1e34cf3993b20939dd29ba27263f24fbbeede2f6a6d089b8051fe32c3c",
      ),
      system_platform_get_num_bits: h(
        "236e46bde1f59309c2cc685a7379bc5294a9817e597915ddcc4b3d933284cd70",
      ),
      subtype_val: h(
        "d1bfec8df908c887e4f489adc2eec77a53e8ff28b5bd9a4c21a56da6381eed8f",
      ),
      nat_dec_le: h(
        "7bb659876671e03d0731c456e894ce9e6f7de8250ab4ae70113dc08e24532127",
      ),
      nat_dec_eq: h(
        "f1de7103802ebc5309041bdaadea4a65652d54af37e66aaaf41787b1d8919557",
      ),
      nat_dec_lt: h(
        "af586b07546e1fca9ab0780d1c236af8d360c4c6bb32bb0cd03ec9ca63d3da96",
      ),
      decidable_rec: h(
        "3ea7e18fcbb7c498b2a45237bda659c0edc97b3d54a4ad0d11bc2ebec80cfa17",
      ),
      decidable_is_true: h(
        "363d071182be414e1a58599b83f5e19f9b873723054f4287ba69705aafef27da",
      ),
      decidable_is_false: h(
        "8cc0e1360c1b29108dab3d6172e7fce8a9aa9640daa4bbe99ba1305d9623624b",
      ),
      nat_le_of_ble_eq_true: h(
        "5c99dc61889e4a1e06ff6f24d184dc6553028cc62b89fa61bc23115b6a762068",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "93c0ea70c5c33f7bcecd405dfdee5c5471f74aee61f8bb610b2552d7ffe28183",
      ),
      nat_eq_of_beq_eq_true: h(
        "c44c528578dab3903088d064cc9b679d2c0eb3fe73da3c1ce1cc9d1b8f2cadd3",
      ),
      nat_ne_of_beq_eq_false: h(
        "6a7739ca74fd0033ddcb1c4d98cde41920f173d3b8a6fade75a49b7496ec8cad",
      ),
      fin: h(
        "1e1a2bbb1920ed4a1281a3deca646ad313ca9c7bf7eabdc3655987797ccc0c55",
      ),
      bool_no_confusion: h(
        "55b3bf142fb5a8078ad3b7515f90ab239c32ae0443dfe383b67dae6f4ba17fc5",
      ),
      // Int primitives — canonical content-hashes from
      // `lake test -- rust-kernel-build-primitives`.
      int: h(
        "c60c95e3cdbf4ed010d999b3277f4e1fd3695e8c30260876102905d7b36241a2",
      ),
      int_of_nat: h(
        "0a99f49cc73ab9f42783092e7120613225670bab89b9d63533d1adefc876182f",
      ),
      int_neg_succ: h(
        "f7130d5864e1ba77b0f6a7338f92159c35bd5147e0febcf1ebed456e513538cc",
      ),
      int_add: h(
        "b666925b10473fbe1a7630ec496fe07d799c5248667db1e2302fca5fe4c50cb6",
      ),
      int_sub: h(
        "7c60043d6016e2f0ef5d764e1ab7923968d43d5c388186ddf6c83c28f024017a",
      ),
      int_mul: h(
        "9dff949e4d0282393213042a36a69af4b71a58709096eaa3de5130bae0af84f3",
      ),
      int_neg: h(
        "19c87649f9a17809f248beff7bc37f569f548e24a98d8a7cddd5b82eb808e5a6",
      ),
      int_emod: h(
        "13c97e84fb8ac3ee8120e923d61fca6f7e6bb9241ec3aa5d359ba5dce542aa11",
      ),
      int_ediv: h(
        "53e404f5dd3c53693bc3b5bfae582b0496ec3c05af0cee0a46c38ab662c57fdf",
      ),
      int_bmod: h(
        "d0380dc9b63afeeb3235a77adeb355a8b52b0730971595093741ec2c6d57cd49",
      ),
      int_bdiv: h(
        "209aca62cc1f9dd2c0a928cd84d72bb41570aa97c1fd833e5fffc567c1c6401f",
      ),
      int_nat_abs: h(
        "01e7c724508897e01e5d0b8f72e2cfa2607cea5ff0d352d008d0e7512aab2f46",
      ),
      int_pow: h(
        "a28958d747e87b5a60e4fa07ef7ed8d949f69adcbc44afe2958482d3ee9b3365",
      ),
      int_dec_eq: h(
        "35a9ed7202e3c43857cdc4063eac123fe7b77f0631154ac540dba2c997bdf224",
      ),
      int_dec_le: h(
        "1710034a517f249f5c8265e8e2783be60619f0c8e85f4eab625e85983abd722e",
      ),
      int_dec_lt: h(
        "5318877ae61e1da37980d80c11e3e47a36d850c3e43e99716122f1e6eff01e9f",
      ),
      punit: h(
        "2dfc16af01b82b3b91c2ff704409d76236a83f956c0c6e6659a64fe21d76695b",
      ),
      pprod: h(
        "90ca5bcf995d68d7dfcb3c7cfe466986dc4beaa402b262ca395b3e53c36f6cad",
      ),
      pprod_mk: h(
        "ce30fc0f4135e679cf3b16d0d667bd9df4e7a69dbb8177a29e5c75b48c4cec10",
      ),
      // Names previously matched via `is_const_named` in whnf.rs.
      // Canonical content-hashes from `lake test -- rust-kernel-build-primitives`.
      nat_rec: h(
        "c8322e03d558f85a8edc7fe68524013880ad0bbcb7dc890136d247154b230992",
      ),
      nat_cases_on: h(
        "937374ed09b8b62f36ef75f06f1ee46dd487c7a9f3e74db919bde48bb76b2cc6",
      ),
      bit_vec: h(
        "90022ae4c5d52ad28acd80051dd41f27f51c9c4afbab1bb391773c19ef0dc1e9",
      ),
      bit_vec_to_nat: h(
        "fade2dbfb1d7f77c30c247d52df128bf516eedce01f817d363ce88da13cfac2b",
      ),
      bit_vec_of_nat: h(
        "67160b97679306d2820445383a6d740e6fe9839c2545ea48680ff2a77b0be986",
      ),
      bit_vec_ult: h(
        "2f9c9c369045036d9a35ff7b38285dca3b976426c81a8f366fce1161b090d60d",
      ),
      decidable_decide: h(
        "11157bc3898f06e3e6f2ca83411efd0d43b8846b57d2f6088e18f3447ddc3b28",
      ),
      lt_lt: h(
        "061c2658c76a68d90978859824993bbbe15dbf9b9968619325420e7c839b05c7",
      ),
      of_nat_of_nat: h(
        "cb84bffa6d7092a309630214af29d9ec4e35cd5e0003eb9cdf75ee484e24925b",
      ),
      unit: h(
        "9232498667f765f437dedaac828e555f6cc67a20e6db28f614fdf3c262710feb",
      ),
      punit_size_of_1: h(
        "523699b6e827b74a950d4718bdf5b13c193e3c7c371aaad4d635667be74b05fa",
      ),
      size_of_size_of: h(
        "ea81aee4a7d154faa8211a2594406dfdc7442020c0f29d2d0f79b4e62314da51",
      ),
      string_back: h(
        "6a47d4c02a7bd096323488f1c115081fb0dfe8fc9651751de02e00ca6e0a68f1",
      ),
      string_utf8_byte_size: h(
        "4c086826cc679df3b6aa57a29f3d093a8a92d0de4edecef46a908d8398733dc0",
      ),
      string_append: h(
        "0eae69f3f8b198d1ffac67b9e88d39526b1b039ff519cd87eec106f63974860c",
      ),
      string_dec_eq: h(
        "da7bb331e098f9bf5cdabcb9609a7e953dffc609ad9d90871a14c016c52a3011",
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
