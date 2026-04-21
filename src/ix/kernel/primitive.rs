//! Well-known primitive constant KIds.
//!
//! Content-addresses are hardcoded blake3 hashes matching the kernel's
//! `build_primitives` in `src/ix/kernel/ingress.rs`. Regenerate with
//! `lake test -- rust-kernel-build-primitives`, which dumps the current
//! `(name, hex)` pairs for every `kernelPrimitives` entry — paste the
//! updated lines into `PrimAddrs::new`.
//!
//! `Primitives<M>` stores `KId<M>` values, resolved from the environment by
//! address so that names match in both Meta and Anon modes. Optional
//! markers (`reduce_bool`, `reduce_nat`, `eager_reduce`) don't exist in the
//! env and always use the synthetic-KId fallback — they are dispatched on
//! by address only, never invoked.

use crate::ix::address::Address;

use super::env::KEnv;
use super::id::KId;
use super::mode::KernelMode;

/// Well-known primitive KIds.
#[derive(Clone)]
pub struct Primitives<M: KernelMode> {
  // -- Nat --
  pub nat: KId<M>,
  pub nat_zero: KId<M>,
  pub nat_succ: KId<M>,
  pub nat_add: KId<M>,
  pub nat_pred: KId<M>,
  pub nat_sub: KId<M>,
  pub nat_mul: KId<M>,
  pub nat_pow: KId<M>,
  pub nat_gcd: KId<M>,
  pub nat_mod: KId<M>,
  pub nat_div: KId<M>,
  pub nat_bitwise: KId<M>,
  pub nat_beq: KId<M>,
  pub nat_ble: KId<M>,
  pub nat_land: KId<M>,
  pub nat_lor: KId<M>,
  pub nat_xor: KId<M>,
  pub nat_shift_left: KId<M>,
  pub nat_shift_right: KId<M>,

  // -- Bool --
  pub bool_type: KId<M>,
  pub bool_true: KId<M>,
  pub bool_false: KId<M>,

  // -- String / Char --
  pub string: KId<M>,
  pub string_mk: KId<M>,
  pub char_type: KId<M>,
  pub char_mk: KId<M>,
  pub char_of_nat: KId<M>,
  pub string_of_list: KId<M>,

  // -- List --
  pub list: KId<M>,
  pub list_nil: KId<M>,
  pub list_cons: KId<M>,

  // -- Eq --
  pub eq: KId<M>,
  pub eq_refl: KId<M>,

  // -- Quotient --
  pub quot_type: KId<M>,
  pub quot_ctor: KId<M>,
  pub quot_lift: KId<M>,
  pub quot_ind: KId<M>,

  // -- Reduction markers --
  pub reduce_bool: KId<M>,
  pub reduce_nat: KId<M>,
  pub eager_reduce: KId<M>,

  // -- Platform --
  pub system_platform_num_bits: KId<M>,

  // -- Decidable / Nat comparison --
  pub nat_dec_le: KId<M>,
  pub nat_dec_eq: KId<M>,
  pub nat_dec_lt: KId<M>,
  pub decidable_is_true: KId<M>,
  pub decidable_is_false: KId<M>,
  pub nat_le_of_ble_eq_true: KId<M>,
  pub nat_not_le_of_not_ble_eq_true: KId<M>,
  pub nat_eq_of_beq_eq_true: KId<M>,
  pub nat_ne_of_beq_eq_false: KId<M>,
  pub bool_no_confusion: KId<M>,

  // -- Int (type, ctors, native ops) --
  // Native reduction of `Int.bmod` etc. dispatches on these addresses,
  // mirroring the Nat primitive scheme. Driven by `try_reduce_int` in
  // `whnf.rs`. See `Primitives::from_env_with` for address resolution.
  pub int: KId<M>,
  pub int_of_nat: KId<M>,
  pub int_neg_succ: KId<M>,
  pub int_add: KId<M>,
  pub int_sub: KId<M>,
  pub int_mul: KId<M>,
  pub int_neg: KId<M>,
  pub int_emod: KId<M>,
  pub int_ediv: KId<M>,
  pub int_bmod: KId<M>,
  pub int_bdiv: KId<M>,
  pub int_nat_abs: KId<M>,
}

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
  pub nat_dec_le: Address,
  pub nat_dec_eq: Address,
  pub nat_dec_lt: Address,
  pub decidable_is_true: Address,
  pub decidable_is_false: Address,
  pub nat_le_of_ble_eq_true: Address,
  pub nat_not_le_of_not_ble_eq_true: Address,
  pub nat_eq_of_beq_eq_true: Address,
  pub nat_ne_of_beq_eq_false: Address,
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
  pub punit: Address,
  pub pprod: Address,
  pub pprod_mk: Address,
}

impl Default for PrimAddrs {
  fn default() -> Self {
    Self::new()
  }
}

impl PrimAddrs {
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
        "fc0e1e912f2d7f12049a5b315d76eec29562e34dc39ebca25287ae58807db137",
      ),
      nat_zero: h(
        "fac82f0d2555d6a63e1b8a1fe8d86bd293197f39c396fdc23c1275c60f182b37",
      ),
      nat_succ: h(
        "7190ce56f6a2a847b944a355e3ec595a4036fb07e3c3db9d9064fc041be72b64",
      ),
      nat_add: h(
        "9eb5f067888c2ebf643e2fba899b6c18943ffa1016f4f713da5e76c63b3e9246",
      ),
      nat_pred: h(
        "e24aca27bb68241c8408f82d9d0ebfe8a14b2c5c7d072a57e8be153482af0aa3",
      ),
      nat_sub: h(
        "43589a9ad509d9e3903105b58c6a8ed57fd287428f69d4d0bceabc75eb1a3442",
      ),
      nat_mul: h(
        "0b9b306e1294a6b28ba38738d776b1212a26490a93239e0a35a8211915fe33e8",
      ),
      nat_pow: h(
        "e6243fc0c656b1dc227e02b9964f9c37c3dc7940cd0f3608c8e5c9beda95cecb",
      ),
      nat_gcd: h(
        "68b1cd4bdfe5d9dbb532e39145f100bb5b15f500749bd32bf840bf050568318f",
      ),
      nat_mod: h(
        "dfbb5855166a1478ff866042ad48514ddd59204efa9616597ec291698801d9d6",
      ),
      nat_div: h(
        "f23fc5ce69c0a96fce0d8b238acd8d80d337df9c0950d822af2dd52eaf50e792",
      ),
      nat_bitwise: h(
        "c5869a7f8f18e2131a6c99db95b5adae195971a19439d89406bae713bd5f3238",
      ),
      nat_beq: h(
        "8b63f97f5fe133df9fdaee27a049abfe928a179c48067e41b176112b32eb15ab",
      ),
      nat_ble: h(
        "77da9490da2908a0460d27a271dc2a8bee41c1cb47601020722dadd321ba37b7",
      ),
      nat_land: h(
        "497f87814f7fcddc61618145787ff75e53d73d4aacaac86a81da5ec469c61c0f",
      ),
      nat_lor: h(
        "9b7992771f84b561a637b64ee7cc21aee519b4616760b6ad496b4d17c14602eb",
      ),
      nat_xor: h(
        "580c6d3f632dbe97c5efe10d0ca76dcf993bf633a87ea5b45bb8c38bb181c397",
      ),
      nat_shift_left: h(
        "96fccb7ab8eb33280948661d57cd92af2632eb9ba693a199c946d2fb0b1b012c",
      ),
      nat_shift_right: h(
        "882ee7b12f532899a549cd0aad43b2c14c30469bf3255fc0ac7dfd79c0ee5eba",
      ),
      bool_type: h(
        "6405a455ba70c2b2179c7966c6f610bf3417bd0f3dd2ba7a522533c2cd9e1d0b",
      ),
      bool_true: h(
        "420dead2168abd16a7050edfd8e17d45155237d3118782d0e68b6de87742cb8d",
      ),
      bool_false: h(
        "c127f89f92e0481f7a3e0631c5615fe7f6cbbf439d5fd7eba400fb0603aedf2f",
      ),
      string: h(
        "e42dd85bf0d0aef95501eb91f93bc0dd31a9bc28f2b8147f9c0ea40c7b699aa0",
      ),
      string_mk: h(
        "6dfb55a0905acbb447e37f11e64c6fd136f0e51b26f123fa124c31b831d6fe6a",
      ),
      char_type: h(
        "dab96f1cffc3eb69303bf253d0947b09c2581ec8e5e3f046a536b3a3ff795b7d",
      ),
      char_mk: h(
        "7b1fe2e331b699241bc83842c879baab51ae342235d4ba80fe5acf38b230c241",
      ),
      char_of_nat: h(
        "94f05c77b4dbdcba974581c48a4e26e5ff9a495e80dd4079a4acd4b7f7a8c464",
      ),
      string_of_list: h(
        "6dfb55a0905acbb447e37f11e64c6fd136f0e51b26f123fa124c31b831d6fe6a",
      ),
      list: h(
        "abed9ff1aba4634abc0bd3af76ca544285a32dcfe43dc27b129aea8867457620",
      ),
      list_nil: h(
        "0ebe345dc46917c824b6c3f6c42b101f2ac8c0e2c99f033a0ee3c60acb9cd84d",
      ),
      list_cons: h(
        "f79842f10206598929e6ba60ce3ebaa00d11f201c99e80285f46cc0e90932832",
      ),
      eq: h("c1b8d6903a3966bfedeccb63b6702fe226f893740d5c7ecf40045e7ac7635db3"),
      eq_refl: h(
        "154ff4baae9cd74c5ffd813f61d3afee0168827ce12fd49aad8141ebe011ae35",
      ),
      quot_type: h(
        "c921b6c7a436a087df626ed10481acfe8872e0b9be11411b657fb40e14c48e6f",
      ),
      quot_ctor: h(
        "f6ced3154ed2bceb2a775f1d97b43c55f840c755fb2752a72ad44bfbec908014",
      ),
      quot_lift: h(
        "33b791909105eff442e7577c641722f326b1b88829895b18869a5ff9cf637803",
      ),
      quot_ind: h(
        "b85b8052b28d37b6dd3eff67e53a5bd256f824788dbce1ba6b7cff81f191663c",
      ),
      reduce_bool: h(
        "f06a188b0808ddd62c656513e8c3b08f7e0e847122787441eafa2fc583df4d40",
      ),
      reduce_nat: h(
        "6dbac9c0a1e1f8a2d5e3bca1c3733640b8924cb353481196423bcd2d84811310",
      ),
      eager_reduce: h(
        "71526128a0948658969223303fc252dde43778527a4793dcf2ef0b3bf6ec19eb",
      ),
      system_platform_num_bits: h(
        "68fa5ce6081e1bcbb15d67122a83c3582e49a4b97160666363a810e2859d2cbd",
      ),
      nat_dec_le: h(
        "631b6b215182ce79c7404581e4f0e1dc47c851b2db2e66a9f0db123d141b418b",
      ),
      nat_dec_eq: h(
        "f08f1c7c0c26b236db2f86e0410ebc49d8a86678c510d260aadb0165f5066c68",
      ),
      nat_dec_lt: h(
        "1726b59a1fc33ee52fe32f885e606dcab8c140fe1c59f08fca714d097082abc3",
      ),
      decidable_is_true: h(
        "3ae2c71da2bf34179a5a8808857c34a3b7662ff5654d8c247c43e85a7cde493f",
      ),
      decidable_is_false: h(
        "10ac5f48798b3ff01b0f74c0b544d22796c9775f6d43d328316bbb3aa1638999",
      ),
      nat_le_of_ble_eq_true: h(
        "f99dbacc212a09f62bdd89120b361fc86d4ec83efc1a145ae4e69a983a617c46",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "f66f3ab90d666010e6331e262b53ad489e0824f0378c29fa0a57964468ccec95",
      ),
      nat_eq_of_beq_eq_true: h(
        "541be2062680b17cae675f0a7e8071e3301dcff28a45d50929a37c7aa6acd383",
      ),
      nat_ne_of_beq_eq_false: h(
        "5c0ba4f47403f37d3050dda3ae3010ac3ba5616c9719543ba7debc62c897aaf6",
      ),
      bool_no_confusion: h(
        "43aaa253568c8458cd2f3cd2fb957670a6da3e909c5634da5ccd8d71767c9a1a",
      ),
      // Int primitives — canonical content-hashes from
      // `lake test -- rust-kernel-build-primitives`. Used by
      // `try_reduce_int` to dispatch native Int reductions.
      int: h(
        "e7dc2d5a2e153e1ab0c78797bcbfd53a2c01ff40918877cfad8ade8c4169a43a",
      ),
      int_of_nat: h(
        "46b5eb6768c1f49587d653c12e37338912153386832f0fd0e472484e26322632",
      ),
      int_neg_succ: h(
        "25bbcd756b52eb78bce170410defa4c15b238dedef5f7b89691621dcbe919780",
      ),
      int_add: h(
        "4559d31171cd56a5db2e8edf4ca1b8512b36b0a16c064e0c938cc99eaa5533be",
      ),
      int_sub: h(
        "e621381a7a172a6c34b4d15306bc8c0bbc1cb6173dd533a3a5e0e39b8a3cb693",
      ),
      int_mul: h(
        "1228f343d24c4e833a264cca70587ca1f0bd27a94ad82f4a35c4115f8e17cb1b",
      ),
      int_neg: h(
        "edfedb88c6268b63c1a954af4f8e73cb5f3c7e7fe1109b38368317fe57bd3dfd",
      ),
      int_emod: h(
        "3890bf165ce378fa58a838d50c56c8d64ad6d9c6b985d42183765118ea1ffbea",
      ),
      int_ediv: h(
        "7d78d9f6f65becae51196f45d7d3e6b38c160ed5d68a574764fde285045c8c70",
      ),
      int_bmod: h(
        "e0278ad1c59ce799268fbb0e1062e8c12e0cf8818c223eca6e9170cd54abfc6e",
      ),
      int_bdiv: h(
        "a22913a2ba75bbeb3c58763626441f89b773d42f35f5be5a4cec313fb0ba6185",
      ),
      int_nat_abs: h(
        "387423bacfde4c6ab21a1ca97f63fd9c194290d1b25a0f24587d17a16533afc0",
      ),
      punit: h(
        "16a2dc76a2cfcc9440f443c666536f2fa99c0250b642fd3971fbad25d531262a",
      ),
      pprod: h(
        "7bd9dffee376ce0221cd83cc6aa94055cfe2046bfc5fb36acd2428598a25fb63",
      ),
      pprod_mk: h(
        "4ab0f13838e997e9546dc9644a095ef23a58cf5b61f1055afd26524b7a25b600",
      ),
    }
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
      eager_reduce: h(
        "fa60e28de4275583d04e0cd02d6bf876da017d8e1fcb9180674d2d8f1302ce08",
      ),
      system_platform_num_bits: h(
        "6fb004fbafb4b68446a57550e21ac08d7599cb157ab194c52fcd7ba1671f10da",
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
      punit: h(
        "e4d0247a1393397d7efa718dc31229b3592a522531595290683ca63dfe420e4d",
      ),
      pprod: h(
        "ce996300ab608fc33ff251a16ac724b19f169dac8ba3fa1c5be2276158adcf5c",
      ),
      pprod_mk: h(
        "0a9e6c68e0531826a4b7e6cb74c5dacb7689e7ef1b78fc21f56acaf65ea25add",
      ),
    }
  }
}

impl<M: KernelMode> Primitives<M> {
  /// Resolve primitives from the environment using the canonical
  /// content-hash address table (`PrimAddrs::new`). This is the correct
  /// call for `kctx.kenv` (the incrementally-compiled canonical
  /// environment).
  ///
  /// Addresses that don't resolve fall back to a synthetic KId with the
  /// address hex as the name — expected for optional markers
  /// (`reduce_bool`, `reduce_nat`, `eager_reduce`) that have no
  /// corresponding Lean constant, and a symptom of hash drift
  /// otherwise. Regenerate stale hashes with
  /// `lake test -- rust-kernel-build-primitives`.
  pub fn from_env(env: &KEnv<M>) -> Self {
    Self::from_env_with(env, &PrimAddrs::new())
  }

  /// Resolve primitives from the environment using the LEON
  /// content-hash address table (`PrimAddrs::new_orig`). This is the
  /// correct call for `orig_kenv` (the direct-from-Lean environment
  /// produced by `lean_ingress`), whose KIds live at LEON addresses.
  ///
  /// Without this variant, `from_env` would look up every primitive by
  /// its canonical content address — which doesn't exist in `orig_kenv`
  /// — and build a synthetic `@<hex>` KId for each. That cascades into
  /// spurious `AppTypeMismatch` errors during original-constant
  /// verification. Regenerate stale hashes with
  /// `lake test -- rust-kernel-build-prim-origs`.
  pub fn from_env_orig(env: &KEnv<M>) -> Self {
    Self::from_env_with(env, &PrimAddrs::new_orig())
  }

  /// Core primitive-resolution logic parameterized on the address
  /// table. See `from_env` (canonical) and `from_env_orig` (LEON) for
  /// the entry points.
  fn from_env_with(env: &KEnv<M>, a: &PrimAddrs) -> Self {
    // Build addr → KId index from the env.
    let mut by_addr = rustc_hash::FxHashMap::default();
    for (id, _) in env.iter() {
      by_addr.entry(id.addr.clone()).or_insert_with(|| id.clone());
    }

    // Resolve: look up in env, fall back to a synthetic KId with the address
    // hex as the name (should only happen for constants not yet in the env,
    // e.g. reduce_bool/reduce_nat markers that may not be real constants).
    let r = |addr: &Address| -> KId<M> {
      by_addr.get(addr).cloned().unwrap_or_else(|| {
        let hex = addr.hex();
        let name = crate::ix::env::Name::str(
          crate::ix::env::Name::anon(),
          format!("@{}", &hex[..8]),
        );
        KId::new(addr.clone(), M::meta_field(name))
      })
    };

    Primitives {
      nat: r(&a.nat),
      nat_zero: r(&a.nat_zero),
      nat_succ: r(&a.nat_succ),
      nat_add: r(&a.nat_add),
      nat_pred: r(&a.nat_pred),
      nat_sub: r(&a.nat_sub),
      nat_mul: r(&a.nat_mul),
      nat_pow: r(&a.nat_pow),
      nat_gcd: r(&a.nat_gcd),
      nat_mod: r(&a.nat_mod),
      nat_div: r(&a.nat_div),
      nat_bitwise: r(&a.nat_bitwise),
      nat_beq: r(&a.nat_beq),
      nat_ble: r(&a.nat_ble),
      nat_land: r(&a.nat_land),
      nat_lor: r(&a.nat_lor),
      nat_xor: r(&a.nat_xor),
      nat_shift_left: r(&a.nat_shift_left),
      nat_shift_right: r(&a.nat_shift_right),
      bool_type: r(&a.bool_type),
      bool_true: r(&a.bool_true),
      bool_false: r(&a.bool_false),
      string: r(&a.string),
      string_mk: r(&a.string_mk),
      char_type: r(&a.char_type),
      char_mk: r(&a.char_mk),
      char_of_nat: r(&a.char_of_nat),
      string_of_list: r(&a.string_of_list),
      list: r(&a.list),
      list_nil: r(&a.list_nil),
      list_cons: r(&a.list_cons),
      eq: r(&a.eq),
      eq_refl: r(&a.eq_refl),
      quot_type: r(&a.quot_type),
      quot_ctor: r(&a.quot_ctor),
      quot_lift: r(&a.quot_lift),
      quot_ind: r(&a.quot_ind),
      reduce_bool: r(&a.reduce_bool),
      reduce_nat: r(&a.reduce_nat),
      eager_reduce: r(&a.eager_reduce),
      system_platform_num_bits: r(&a.system_platform_num_bits),
      nat_dec_le: r(&a.nat_dec_le),
      nat_dec_eq: r(&a.nat_dec_eq),
      nat_dec_lt: r(&a.nat_dec_lt),
      decidable_is_true: r(&a.decidable_is_true),
      decidable_is_false: r(&a.decidable_is_false),
      nat_le_of_ble_eq_true: r(&a.nat_le_of_ble_eq_true),
      nat_not_le_of_not_ble_eq_true: r(&a.nat_not_le_of_not_ble_eq_true),
      nat_eq_of_beq_eq_true: r(&a.nat_eq_of_beq_eq_true),
      nat_ne_of_beq_eq_false: r(&a.nat_ne_of_beq_eq_false),
      bool_no_confusion: r(&a.bool_no_confusion),
      int: r(&a.int),
      int_of_nat: r(&a.int_of_nat),
      int_neg_succ: r(&a.int_neg_succ),
      int_add: r(&a.int_add),
      int_sub: r(&a.int_sub),
      int_mul: r(&a.int_mul),
      int_neg: r(&a.int_neg),
      int_emod: r(&a.int_emod),
      int_ediv: r(&a.int_ediv),
      int_bmod: r(&a.int_bmod),
      int_bdiv: r(&a.int_bdiv),
      int_nat_abs: r(&a.int_nat_abs),
    }
  }
}
