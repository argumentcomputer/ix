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
        "ee5d424f6fbb5410ce82a4657c586ed8dc57eb2588947578636676e42ed0072b",
      ),
      nat_zero: h(
        "09851a0422a18822447d9785123b46be1d53f1a2d0137992fe16ae693cb3f07d",
      ),
      nat_succ: h(
        "757ca9ddbbfdfcb939a42c164c435dede6d6d234279f89e1d13668f3ef4d891d",
      ),
      nat_add: h(
        "a04e7e6b19f5e48dbb0b53dae24db5dcc1b1a98c8e97551db8fb4b5f4a14caa8",
      ),
      nat_pred: h(
        "b8d8ab1875dbb7fdb150a34988c32d7006204b9506a0ba148f453e5c555bf218",
      ),
      nat_sub: h(
        "f8410bb7b91afaa0cb6f9162faeee2a682e98cde21acf19712380f4e9dbcbf00",
      ),
      nat_mul: h(
        "7e736639472dcc920bdc54d8ff0255a4c03b3c05375eacf08814e341deebd331",
      ),
      nat_pow: h(
        "473d7239744c820ddb45b6ce56d0506734ba90e5699e985444fd7a6647e9b0a0",
      ),
      nat_gcd: h(
        "f1286e3ceac7bf4afa1c95a2f70c69ffc0667295035661b9be57ed6f0b08babb",
      ),
      nat_mod: h(
        "fdc3d6f24a0d4968b0e2bd5502a95a54506566a6d6f8bf5673b95b5278da8cdd",
      ),
      nat_div: h(
        "2f22b34c61096990d6ce6b2485b31ed9696feaae6902855de6116b6a58e90331",
      ),
      nat_bitwise: h(
        "f67972af52c7a4fce7de2595075e6b6d0ca7d7f67e01e1a1383c6a270aa613cd",
      ),
      nat_beq: h(
        "dd0668fbe8c2b2a2260e95da62a2bea5df42c670a3e95ccffea03c3a7ffdc1c2",
      ),
      nat_ble: h(
        "a939cc7925834d04a7ced860c5c44484231c9f5c44728d83d55f19c08037f3b4",
      ),
      nat_land: h(
        "a4f25748d7376a55ce31462ae4ad90ac33181a6000b9908f398cc850ad865f67",
      ),
      nat_lor: h(
        "0330cfdb86165b40463f2931bf794d375aa7acecd21feaabe1319e03fd80a5d9",
      ),
      nat_xor: h(
        "7c79bfc28b46cca9137779a26b8da0b4aedc718eaf554f76e6e38650074327d6",
      ),
      nat_shift_left: h(
        "c2a2258d56e14ebdb8c9986365cf0c0f6dfe4128a8faf847dd5e50b4ae7bb310",
      ),
      nat_shift_right: h(
        "74a4836a0eddfd07e45e5da0929df974e0caef28fd26001f7de1712d5beddd4e",
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
        "9964f625c7e537f667af5c445f1c1cd4ea18d6094dd7b7083c49f59613566306",
      ),
      string_mk: h(
        "37f3bf73d4ef5dfa4705a3125b788141b980a48e7303e1f23e2465acca2e19d6",
      ),
      char_type: h(
        "f730fc437187a5bf297d6f68f125ab93a4f15da80eecf8379cef2a5ce3e9b015",
      ),
      char_mk: h(
        "85f033fda46ae0e305e02bcc83c9f76b04bffb005536a5bc7a15107d57a9c4b6",
      ),
      char_of_nat: h(
        "6b8d46124c1396c972f51482fe4f6afcf76bf50da76c9772be03a19ebf3564ac",
      ),
      // NOTE: `String.ofList` and `String.mk` share the canonical content-hash
      // because both compile to the same Ixon form (a one-constructor `String`
      // built from `List Char`). The Lean-side deprecation of `String.mk` in
      // favor of `String.ofList` is orthogonal to the compiled representation.
      string_of_list: h(
        "37f3bf73d4ef5dfa4705a3125b788141b980a48e7303e1f23e2465acca2e19d6",
      ),
      string_to_byte_array: h(
        "6fabcaf163e83cf02d51624cade44120c65b6e5dc439578fe68eb1972870d1dc",
      ),
      byte_array_empty: h(
        "e2872f038c01610a4f78126ca7abe6573a57f717edf7b990ce01e3d32f60b991",
      ),
      list: h(
        "487a90b33c7dcd5f3434aa04338e1a5b290552cbe922eeb59b025b1dcdbf5de0",
      ),
      list_nil: h(
        "acc4102c8c32f222b755f3f15b5046484ca98618da9a4932143a9711786818fa",
      ),
      list_cons: h(
        "63cc7dc0943c85e1d79b41c5ca23cbb5e080b67aec17e5c6bfca4fd0073e01ab",
      ),
      eq: h("9d3c7bcfcc8f1f1661bce87d371a5da0d5188c1bc05def21d4aa176138c91b10"),
      eq_refl: h(
        "54b03dedcfd0b6910e04eb06e402ee285adacfcf388b2cf924abe3b208e07b48",
      ),
      quot_type: h(
        "c87b29931ce4e002425f8566d1cbf012cb95383f7e7cc3533f5763d63b3f2060",
      ),
      quot_ctor: h(
        "b38e6ec63d3ac6caa456af698ffaf866e192bd3e84d8092a8415b793a7abb598",
      ),
      quot_lift: h(
        "abbb9c07b2c466ed630087842844ea0464b95ca0218b2a1ee67907542d443084",
      ),
      quot_ind: h(
        "2c05f283a450a057bb67a0b44225f478c2d00fbbfd9728b4f8cef6c0f3553cfd",
      ),
      reduce_bool: h(
        "6f934549cecd15776349147cb2d7b2161caae5ea2af0e5f773bf6e96a34501dd",
      ),
      reduce_nat: h(
        "9ff7e16f724d7aee1243b6b670cd19c13e153d7a7472789a9b5a6d68224963ab",
      ),
      // Synthetic kernel-only marker. This is intentionally not the compiled
      // Lean content hash: `eagerReduce` canonicalizes to the same content
      // address as the real Lean constant `id`, so address-only dispatch would
      // give ordinary `id` terms special reduction semantics.
      eager_reduce: h(
        "ff00000000000000000000000000000000000000000000000000000000000003",
      ),
      system_platform_num_bits: h(
        "7984aff2c623559abf205435ff3a193e4e8a1339c4d2db4f7fc4301840f121b4",
      ),
      system_platform_get_num_bits: h(
        "e8b0ce9336fdebfe436dc9ef0bf8141a137dce0533ef15d544295567fcae2054",
      ),
      subtype_val: h(
        "8289d019f214f560cfe57247da921a2cdfab41172cf3b56376c3a06e5edff08d",
      ),
      nat_dec_le: h(
        "50f5ae564c67023119e61cd8a1510970065582bdfedc7770bf88cc2f047ef079",
      ),
      nat_dec_eq: h(
        "cff050af9ca1951b0c4c4dd7280da5837e5390bcd6249f8e45c6b997fb63be34",
      ),
      nat_dec_lt: h(
        "dd7ee8e548a8aa482caf21c99c2f5c10254700d2ad3784530e740dd9f61a8cd3",
      ),
      decidable_rec: h(
        "6be931292c410641a78101e973c604b94da29b6ee09ea00a557968fb2efe252e",
      ),
      decidable_is_true: h(
        "23e3b904854e2f117770ac908a90ef0bdd50bf2ed11a6274b8c233db4cdb866f",
      ),
      decidable_is_false: h(
        "f1fe3bef188e3a340b3ba29ae5ecdd265c970439e3993b5b3fb3bf8d85342663",
      ),
      nat_le_of_ble_eq_true: h(
        "9648c8fade1402c8b4e05e7280d56ffdb6485a5b12c053eb409ddb2abe64d49e",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "47be72026cd031236a38d19bf7891e17e6b72b57347221a9f31d2500374bb1ce",
      ),
      nat_eq_of_beq_eq_true: h(
        "d464a3b9c60c79f1c15c42ba3ecd64f2aa9db4dc466dbeff9c2f7f8c6fe2f809",
      ),
      nat_ne_of_beq_eq_false: h(
        "680e71feb2d9ffab6d006358e66264c3898792eac445696061cdcd78e8e65c1e",
      ),
      fin: h(
        "638ff947a118e46c15195a4c6fb4dbe00f69beddefe9ba80e64fc31fe7de140f",
      ),
      bool_no_confusion: h(
        "1173d7b6f2bd5f453467d131f67d29e1f1f5a43a61262e1e8036bdb9e1ab640d",
      ),
      // Int primitives — canonical content-hashes from
      // `lake test -- rust-kernel-build-primitives`.
      int: h(
        "35597c7bd15920710c3e00596c6e31ee24a496beb5f61efaeb356dd9e4b2d9f4",
      ),
      int_of_nat: h(
        "7f2fc3d5811ae7540af7cd6943abed4e822e4939f8d73bc4cda4985ba2653503",
      ),
      int_neg_succ: h(
        "1c49eff96dc8bbc4d9d0f3faa21b3d90a67fe7ba5e0d6d5abcdef0013a683825",
      ),
      int_add: h(
        "514e4a1d06a0a11bc0de8e7723e56cf92402ea91914970c71666a2723d0a8948",
      ),
      int_sub: h(
        "5c0921619ad0e89e59589e4ee62da332382217da03df9978d81dc713724edc02",
      ),
      int_mul: h(
        "88f54e211e3d65e4e64ba847a24db743109268f1459724b3d50b8dbacfa2ac4d",
      ),
      int_neg: h(
        "93670808b6171d82d973d9e607cb056474a384ce0d3c10b87f3925d05436629f",
      ),
      int_emod: h(
        "5234a2d2ce00bf4e1df19ad5ffe55daac0424c7c74e5d1a2b740efd43d612b8e",
      ),
      int_ediv: h(
        "de44c29f84913a451ef5a3526db1000cbc87c8ed4d4417f646e0d841c59306b3",
      ),
      int_bmod: h(
        "26a7af17d6b4bd04d7d0a6280ed682982ac5e12d75280c83c9ebdb4f7cff64c9",
      ),
      int_bdiv: h(
        "953f3109bcbf54692990572bce05ff9f2ffb03438882b9d47fa01d914a3db52c",
      ),
      int_nat_abs: h(
        "9dff1da5f30f3cca942bbfce551d8e0a4d1f13d946ea1ef44c478ea3257551c1",
      ),
      int_pow: h(
        "1cddad5e261c1786036f900b15ce94de7cdec55dc741062e0de8b2192613bc04",
      ),
      int_dec_eq: h(
        "ad376bc32d8789ae58304b84cde55511f1b7cdca85cba9d593b87031d651fb5a",
      ),
      int_dec_le: h(
        "4da67faa95070121d3310db52aeadfffddbf4ce2dd8902398603e536d16c8d14",
      ),
      int_dec_lt: h(
        "976882e78acc2475953e59c23415750f1ec40f13d8a5dfc453385dfc18346ff1",
      ),
      punit: h(
        "1f24b345045e83033dc57342cdd3bd2842d1c3a2c04b193c409873becb75b414",
      ),
      pprod: h(
        "02944ab961161c59fe9f4bf62fd114344a79229f604aeb649440c53a9cfc3de9",
      ),
      pprod_mk: h(
        "0980754525afb7a32e274bef06865a7b03bab07b8343ca334e16ab8049baa6ff",
      ),
      // Names previously matched via `is_const_named` in whnf.rs.
      // Canonical content-hashes from `lake test -- rust-kernel-build-primitives`.
      nat_rec: h(
        "a37d28a22a02cd33b3c87380f45c8990c95cce53f154ad332a9cb5f9b1638753",
      ),
      nat_cases_on: h(
        "4c2eb46bd344dd88dd451538be890ecc4734373b8aeaf13b671c970570949109",
      ),
      bit_vec: h(
        "805395dc5aee5c43d794dc1fdf6015886d19c78d4ecc57c51685456c1685cce6",
      ),
      bit_vec_to_nat: h(
        "2e42823b21abae43f4c0624983662038e4ef9c01e8eeb6d39ec5253b24b2b8db",
      ),
      bit_vec_of_nat: h(
        "0d0e2c6e31c12bcba061871f4eeef439d95aa536771931e7fdbf6036d0c88f7a",
      ),
      bit_vec_ult: h(
        "c5bd60dbef7e03d7afcb4ea1436b3f7b283262e2e025449ad8b0d5828b47dfba",
      ),
      decidable_decide: h(
        "702607152432fb22bd2a59d80423b9f7a369a55acc6a4c16d3654523a5788d16",
      ),
      lt_lt: h(
        "0eeab75a4c4d71e2f7f745ab54fd64a9ce45e9f506ef09f3312711c4619fd178",
      ),
      of_nat_of_nat: h(
        "8c074cca466bf7a3a5ec2b1f0c11886da5d003837d3b29ca4973b89ab01e0382",
      ),
      unit: h(
        "585e362473d1a5811630ce9ce11b21868b6053a1419e7e3e637d8fb8fb0f9fce",
      ),
      punit_size_of_1: h(
        "2f546e3974f2ab35d4cb8e2a452b0c7fc24f6e515cec781744ee78d52fd0fdf0",
      ),
      size_of_size_of: h(
        "7c51fbcfd57ae985f7f6845874da7c171aa7edceef4daee875eb53899d4685cd",
      ),
      string_back: h(
        "1d9ed0da7f32dd9e16399c57b5cf7f3120928f127803e45835f1d58c6fc3e3b2",
      ),
      string_utf8_byte_size: h(
        "e47a3627ce6d979fee7b68a3aa86abf2b2b67b8eb24d4d984f10e284c2384d7a",
      ),
      string_append: h(
        "606e3f9fd1b1cb9484145af8ee112dcf66fa3203f1ff11322ebd1f4f63403a3e",
      ),
      string_dec_eq: h(
        "f799ab07a9dc29e3c2d7492e21262e4f38752fd6b00c6813fb14039748e6185e",
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
