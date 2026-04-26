//! Well-known primitive constant KIds.
//!
//! Content-addresses are hardcoded blake3 hashes matching the kernel's
//! `build_primitives` in `src/ix/kernel/ingress.rs`. Regenerate with
//! `lake test -- rust-kernel-build-primitives`, which dumps the current
//! `(name, hex)` pairs for every `kernelPrimitives` entry — paste the
//! updated lines into `PrimAddrs::new`.
//!
//! `Primitives<M>` stores `KId<M>` values, resolved from the environment by
//! address so that names match in both Meta and Anon modes. `Lean.reduceBool`
//! and `Lean.reduceNat` are real primitive constants and are dispatched by
//! content address. `eager_reduce` is a synthetic kernel-only marker because
//! Lean's `eagerReduce` compiles to the same canonical content address as
//! `id`; address-only dispatch on the real constant would be unsound.

use std::sync::LazyLock;

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
  pub string_to_byte_array: KId<M>,
  pub byte_array_empty: KId<M>,

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
  pub system_platform_get_num_bits: KId<M>,
  pub subtype_val: KId<M>,

  // -- Decidable / Nat comparison --
  pub nat_dec_le: KId<M>,
  pub nat_dec_eq: KId<M>,
  pub nat_dec_lt: KId<M>,
  pub decidable_rec: KId<M>,
  pub decidable_is_true: KId<M>,
  pub decidable_is_false: KId<M>,
  pub nat_le_of_ble_eq_true: KId<M>,
  pub nat_not_le_of_not_ble_eq_true: KId<M>,
  pub nat_eq_of_beq_eq_true: KId<M>,
  pub nat_ne_of_beq_eq_false: KId<M>,
  pub fin: KId<M>,
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
  pub int_pow: KId<M>,
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
        "fc0e1e912f2d7f12049a5b315d76eec29562e34dc39ebca25287ae58807db137",
      ),
      nat_zero: h(
        "fac82f0d2555d6a63e1b8a1fe8d86bd293197f39c396fdc23c1275c60f182b37",
      ),
      nat_succ: h(
        "7190ce56f6a2a847b944a355e3ec595a4036fb07e3c3db9d9064fc041be72b64",
      ),
      nat_add: h(
        "f94192058e41bc29e88924d857a6bd33f8b3e0a90f8786828270d1cc1dd0adc6",
      ),
      nat_pred: h(
        "6b59cf449781f07b04207d665978b5c5ef9688afa7448590a68f7da7ff88c516",
      ),
      nat_sub: h(
        "fa98dabf44d2a6307b490ac9e811433efc2f958996c67be1398cb4d1b264cf39",
      ),
      nat_mul: h(
        "9b5c57ea1cf2fb1de67ee5bec15e360d20a9635990273014e67851e049ff3619",
      ),
      nat_pow: h(
        "d015987bb10dd22863ddc41160d27dd3d1ea74f754fb2412432436f3ea5b5071",
      ),
      nat_gcd: h(
        "ee8ba9216b3fc81e7968586b43cebea15d0e143d5d4b1fde1bd301a74093f606",
      ),
      nat_mod: h(
        "8ef8b28b4e9e0a59f3822e243e71299f06bb6e7afdb6cdd97976fb290b667bb4",
      ),
      nat_div: h(
        "fa583794c8ef368eff6881e816a4e889f95061116ce49b154056d38fce4b7f52",
      ),
      nat_bitwise: h(
        "f21d747aca3e08f5290093bf8f4020838d8e1742a78b3e1f48d83ef159395e6a",
      ),
      nat_beq: h(
        "e8b7149d8a7d12414b06252f318d408204723ca4c02f3a38edfa37792448c0da",
      ),
      nat_ble: h(
        "2275080a89c327904e3ad127ba44370a7c6c1bef3aa74792079f8f3159636957",
      ),
      nat_land: h(
        "a0db90e68ee3b7a166e35f619bd7b02c0896efd60eb46914ff3e4fb81252fb94",
      ),
      nat_lor: h(
        "d14419aaa47a03bf9a46938bf72e40f96cab853f9cc5869879e7699f45171773",
      ),
      nat_xor: h(
        "ae68fd416ecb9ce20612272d43c2f86eaf21d9547f565968391e9e12e39372dc",
      ),
      nat_shift_left: h(
        "f606b7c23180a20ace60fe24d52bc0ea3854698d2d14da05c4837a97e1ab4469",
      ),
      nat_shift_right: h(
        "d860b560156da68e801c8bd51d892e557fbe3526d7d198696ffb4d551ae04bb7",
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
        "cb1bca7fc5dbb1bdfbf6319df89da9fda3a679d22554b8a9d5dd4663c0a97312",
      ),
      string_mk: h(
        "63d95a0fd6a1144348d0f20e20cc5c3af61ac955923f45f42a782de933aad594",
      ),
      char_type: h(
        "38aa12059fad3afa1e1e8740dc9470a47c26986350f6cb3bea1fae1276d7b5f1",
      ),
      char_mk: h(
        "e62238c54b91395c2c06192cfccb5e80fce41ed11d1bf6db142d2c39d7c81a20",
      ),
      char_of_nat: h(
        "7a5754386b30bb86f0b6f70fd368bb50e603273a50ad79d8c17fc3cb59f80fac",
      ),
      // NOTE: `String.ofList` and `String.mk` share the canonical content-hash
      // because both compile to the same Ixon form (a one-constructor `String`
      // built from `List Char`). The Lean-side deprecation of `String.mk` in
      // favor of `String.ofList` is orthogonal to the compiled representation.
      string_of_list: h(
        "63d95a0fd6a1144348d0f20e20cc5c3af61ac955923f45f42a782de933aad594",
      ),
      string_to_byte_array: h(
        "65f644286bc49464cc7a36b7d7952f8543ab67564cd509ee878a95375609069b",
      ),
      byte_array_empty: h(
        "d97417c49206c61fe28cbb7a0b6095f722cdfbc213e034aa59de51b9218af074",
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
      eq: h("9c0af2a393cb5c0835e44e60e4c3e68eeb266fd16affad3216096a35fe91b9c1"),
      eq_refl: h(
        "1e251198f30625628e2eb0983f7be9efe8d719a104a861f2bef2f47eabeed4f9",
      ),
      quot_type: h(
        "ab682c1778a17bbeae4032974df36447ce8bfcab6764a36d378566e3ad63cab8",
      ),
      quot_ctor: h(
        "88266677fee774d109867e4b2240281aa2ee12d97920c1171cf5c1f6c87decf6",
      ),
      quot_lift: h(
        "aa57e8c3f4f9e1cf6b02a038ac158198c3af4b28d61cea7995bf5ca7c7b82c29",
      ),
      quot_ind: h(
        "124984bcb95208a0f30bb69d6736d3d59404e115e2202043fda3d34e01b0ad16",
      ),
      reduce_bool: h(
        "6e453a7cedafe2edbbc1f0503442be499e4cbf18a6c00dc99f3903ee7f05dbaf",
      ),
      reduce_nat: h(
        "5419187fbf67ef1c4ff9ab0be1b01d4631a270647ffe434bf7e1f788b3c81dd4",
      ),
      // Synthetic kernel-only marker. This is intentionally not the compiled
      // Lean content hash: `eagerReduce` canonicalizes to the same content
      // address as the real Lean constant `id`, so address-only dispatch would
      // give ordinary `id` terms special reduction semantics.
      eager_reduce: h(
        "ff00000000000000000000000000000000000000000000000000000000000003",
      ),
      system_platform_num_bits: h(
        "d483966438ad47ce4155b3485819a377e22605b59a1aafd0b681cb38aca83107",
      ),
      system_platform_get_num_bits: h(
        "ad44c90449faf86f63c170f092e2249bccab1e741c1fe10df84c95b44b384371",
      ),
      subtype_val: h(
        "ad58c3656044d7faef697637f516d72674d35b18663cb263f7ccca8cdd2e6f00",
      ),
      nat_dec_le: h(
        "e08c5141c44b27653957ae00a926a2dd68dcd7779c4fdf850e668fdc92b408de",
      ),
      nat_dec_eq: h(
        "38323fd9e17e9d1f17536dbb7f196b94b5ba19e4bf625d9e7c607c47365c15ad",
      ),
      nat_dec_lt: h(
        "f445084f6805faf9be62aa328415651343c98ffe52db159dfb1b9a14cb28cf23",
      ),
      decidable_rec: h(
        "f323a549ad4df6b2f32899237a281136f34d431ed72b33857c085e6c4d852738",
      ),
      decidable_is_true: h(
        "3ae2c71da2bf34179a5a8808857c34a3b7662ff5654d8c247c43e85a7cde493f",
      ),
      decidable_is_false: h(
        "10ac5f48798b3ff01b0f74c0b544d22796c9775f6d43d328316bbb3aa1638999",
      ),
      nat_le_of_ble_eq_true: h(
        "7e5d1f1118a89f77f89d469a27731a754de336a05e33f383056bc92b36947812",
      ),
      nat_not_le_of_not_ble_eq_true: h(
        "c1e23b8dafb3778b996312068a2bec3dcbcc72132efbf43c235e573084668241",
      ),
      nat_eq_of_beq_eq_true: h(
        "b9acc81f2801af89b95e0962aa9d7390a3acfe8fb760559a811a82ed7443dbb5",
      ),
      nat_ne_of_beq_eq_false: h(
        "248779884109eed00600a0bd968f740db7f3d924fb2b1706ab552e7876062855",
      ),
      fin: h(
        "272aa9e16c03e9ad7337e706d73efd14ccf1da10e2f8367dd34374b60e1556fa",
      ),
      bool_no_confusion: h(
        "473b2c948ddbce4ddb4b369e5cf6199ff185b64e9fbb1e90901d746de55190ef",
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
        "d8e6cdc988d4288e48cc6092730bc5387176cff6592471a328cc4354f1878412",
      ),
      int_sub: h(
        "93b2d12d7797fd62c20bec255336c1e91ca1cef7a6951071296fc1ab5bd1d8c8",
      ),
      int_mul: h(
        "9ad6ee18ef6d7d74bbe449ab61aa31f84a0e78951e9560d28fd82e0c3b071d01",
      ),
      int_neg: h(
        "8c3f64e6b5baaaa125f0637d7a824df627dbede0115968f3c80c55e022554462",
      ),
      int_emod: h(
        "7cdb112725d3a4f542bfb0cd309268641bd89ddc9890c7221ed01f99b6a00b63",
      ),
      int_ediv: h(
        "ba194c0a3674e67b9968d0a65cdda3a4ddb9dcdce48ad6c62e91d478a10a3ddd",
      ),
      int_bmod: h(
        "c8431b7adb918967aa05ba6fd8297f33e97d67003e4138021d912ea92cc1887f",
      ),
      int_bdiv: h(
        "ab72477254d1ca4738123ad612eae4dfb9126ef78310ed7d2ebde8100963bfb1",
      ),
      int_nat_abs: h(
        "60662e33224f55be9e367683378c7bf6093c125c04ff7c4e3eca370112e1c562",
      ),
      int_pow: h(
        "0dfe8f22bd6cb67d538a2f018f0e406fc0b5d730caa63e1a798dfa9ad78bab07",
      ),
      punit: h(
        "16a2dc76a2cfcc9440f443c666536f2fa99c0250b642fd3971fbad25d531262a",
      ),
      pprod: h(
        "6e99b086700f2901804a107cad5ef0fe878077b1723f4b824615dd021d4d5157",
      ),
      pprod_mk: h(
        "00ddf26efd5f7e5eee5561c2467b16ac856efcb3a1226544487645dd46208596",
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
  /// address hex as the name. That is expected for the synthetic
  /// `eager_reduce` marker and is a symptom of hash drift otherwise.
  /// Regenerate stale hashes with
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
    // hex as the name. For real primitives this should only happen in small
    // unit-test envs or when the hardcoded table has drifted.
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
    let marker = |addr: &Address, marker_name: &str| -> KId<M> {
      let name = crate::ix::env::Name::str(
        crate::ix::env::Name::anon(),
        format!("@{marker_name}"),
      );
      KId::new(addr.clone(), M::meta_field(name))
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
      string_to_byte_array: r(&a.string_to_byte_array),
      byte_array_empty: r(&a.byte_array_empty),
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
      eager_reduce: marker(&a.eager_reduce, "eager_reduce"),
      system_platform_num_bits: r(&a.system_platform_num_bits),
      system_platform_get_num_bits: r(&a.system_platform_get_num_bits),
      subtype_val: r(&a.subtype_val),
      nat_dec_le: r(&a.nat_dec_le),
      nat_dec_eq: r(&a.nat_dec_eq),
      nat_dec_lt: r(&a.nat_dec_lt),
      decidable_rec: r(&a.decidable_rec),
      decidable_is_true: r(&a.decidable_is_true),
      decidable_is_false: r(&a.decidable_is_false),
      nat_le_of_ble_eq_true: r(&a.nat_le_of_ble_eq_true),
      nat_not_le_of_not_ble_eq_true: r(&a.nat_not_le_of_not_ble_eq_true),
      nat_eq_of_beq_eq_true: r(&a.nat_eq_of_beq_eq_true),
      nat_ne_of_beq_eq_false: r(&a.nat_ne_of_beq_eq_false),
      fin: r(&a.fin),
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
      int_pow: r(&a.int_pow),
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

#[cfg(test)]
mod tests {
  use std::collections::HashMap;

  use super::*;
  use crate::ix::env::Name;
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::expr::KExpr;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::level::KUniv;
  use crate::ix::kernel::mode::Anon;

  /// Collect every (field_name, addr) pair from `PrimAddrs` via reflection
  /// over a macro invocation at the caller — done here by an inline array.
  /// Keep in lockstep with `PrimAddrs`.
  ///
  /// Fields intentionally present as address-only dispatch markers (no Lean
  /// constant) are marked below.
  fn addrs_with_names(a: &PrimAddrs) -> Vec<(&'static str, &Address)> {
    vec![
      ("nat", &a.nat),
      ("nat_zero", &a.nat_zero),
      ("nat_succ", &a.nat_succ),
      ("nat_add", &a.nat_add),
      ("nat_pred", &a.nat_pred),
      ("nat_sub", &a.nat_sub),
      ("nat_mul", &a.nat_mul),
      ("nat_pow", &a.nat_pow),
      ("nat_gcd", &a.nat_gcd),
      ("nat_mod", &a.nat_mod),
      ("nat_div", &a.nat_div),
      ("nat_bitwise", &a.nat_bitwise),
      ("nat_beq", &a.nat_beq),
      ("nat_ble", &a.nat_ble),
      ("nat_land", &a.nat_land),
      ("nat_lor", &a.nat_lor),
      ("nat_xor", &a.nat_xor),
      ("nat_shift_left", &a.nat_shift_left),
      ("nat_shift_right", &a.nat_shift_right),
      ("bool_type", &a.bool_type),
      ("bool_true", &a.bool_true),
      ("bool_false", &a.bool_false),
      ("string", &a.string),
      ("string_mk", &a.string_mk),
      ("char_type", &a.char_type),
      ("char_mk", &a.char_mk),
      ("char_of_nat", &a.char_of_nat),
      ("string_of_list", &a.string_of_list),
      ("string_to_byte_array", &a.string_to_byte_array),
      ("byte_array_empty", &a.byte_array_empty),
      ("list", &a.list),
      ("list_nil", &a.list_nil),
      ("list_cons", &a.list_cons),
      ("eq", &a.eq),
      ("eq_refl", &a.eq_refl),
      ("quot_type", &a.quot_type),
      ("quot_ctor", &a.quot_ctor),
      ("quot_lift", &a.quot_lift),
      ("quot_ind", &a.quot_ind),
      ("reduce_bool", &a.reduce_bool),
      ("reduce_nat", &a.reduce_nat),
      ("eager_reduce", &a.eager_reduce),
      ("system_platform_num_bits", &a.system_platform_num_bits),
      ("system_platform_get_num_bits", &a.system_platform_get_num_bits),
      ("subtype_val", &a.subtype_val),
      ("nat_dec_le", &a.nat_dec_le),
      ("nat_dec_eq", &a.nat_dec_eq),
      ("nat_dec_lt", &a.nat_dec_lt),
      ("decidable_rec", &a.decidable_rec),
      ("decidable_is_true", &a.decidable_is_true),
      ("decidable_is_false", &a.decidable_is_false),
      ("nat_le_of_ble_eq_true", &a.nat_le_of_ble_eq_true),
      ("nat_not_le_of_not_ble_eq_true", &a.nat_not_le_of_not_ble_eq_true),
      ("nat_eq_of_beq_eq_true", &a.nat_eq_of_beq_eq_true),
      ("nat_ne_of_beq_eq_false", &a.nat_ne_of_beq_eq_false),
      ("fin", &a.fin),
      ("bool_no_confusion", &a.bool_no_confusion),
      ("int", &a.int),
      ("int_of_nat", &a.int_of_nat),
      ("int_neg_succ", &a.int_neg_succ),
      ("int_add", &a.int_add),
      ("int_sub", &a.int_sub),
      ("int_mul", &a.int_mul),
      ("int_neg", &a.int_neg),
      ("int_emod", &a.int_emod),
      ("int_ediv", &a.int_ediv),
      ("int_bmod", &a.int_bmod),
      ("int_bdiv", &a.int_bdiv),
      ("int_pow", &a.int_pow),
      ("int_nat_abs", &a.int_nat_abs),
      ("punit", &a.punit),
      ("pprod", &a.pprod),
      ("pprod_mk", &a.pprod_mk),
    ]
  }

  /// Collapse the (field, addr) vec into address → fields-that-share-it.
  fn find_duplicates(a: &PrimAddrs) -> Vec<(String, Vec<&'static str>)> {
    let entries = addrs_with_names(a);
    let mut by_addr: HashMap<String, Vec<&'static str>> = HashMap::new();
    for (name, addr) in entries {
      by_addr.entry(addr.hex()).or_default().push(name);
    }
    let mut dups: Vec<(String, Vec<&'static str>)> = by_addr
      .into_iter()
      .filter(|(_, v)| v.len() > 1)
      .map(|(k, mut v)| {
        v.sort();
        (k, v)
      })
      .collect();
    dups.sort_by(|a, b| a.0.cmp(&b.0));
    dups
  }

  #[test]
  fn prim_addrs_new_orig_has_no_duplicates() {
    // LEON pre-compile table is regenerated from Lean reference and
    // must never have field collisions.
    let a = PrimAddrs::new_orig();
    let dups = find_duplicates(&a);
    assert!(
      dups.is_empty(),
      "PrimAddrs::new_orig() has duplicate addresses:\n{dups:#?}"
    );
  }

  /// `string_mk` and `string_of_list` intentionally share a canonical
  /// content address: in Lean they're the same declaration.
  /// `refs/lean4/src/Init/Prelude.lean` has
  ///
  /// ```lean
  /// @[extern "lean_string_mk"]
  /// def String.ofList (data : List Char) : String :=
  ///   ⟨List.utf8Encode data, .intro data rfl⟩
  /// ```
  ///
  /// `String.ofList` is the pure Lean definition; `lean_string_mk` is
  /// its FFI extern name. The canonical (alpha-invariant, content-hashed)
  /// form coalesces the two kernel-dispatch slots onto one address, which
  /// is why `PrimAddrs::new()` stores the same hex for both — both
  /// `prims.string_mk` and `prims.string_of_list` end up pointing at the
  /// same `KId`. `PrimAddrs::new_orig()` holds them as distinct LEON
  /// addresses because pre-compile the two names exist as separate
  /// lookup keys.
  ///
  /// This test pins the intentional alias: if a future canonical-table
  /// regeneration accidentally splits them we want a loud signal.
  #[test]
  fn prim_addrs_new_string_mk_and_of_list_are_intentionally_aliased() {
    let a = PrimAddrs::new();
    assert_eq!(
      a.string_mk.hex(),
      a.string_of_list.hex(),
      "string_mk and string_of_list must share a canonical address — \
       they are the same Lean declaration (String.ofList with extern \
       \"lean_string_mk\"). If this assertion fires after a hash-table \
       regeneration, check whether a Lean-side rename broke the alias \
       or whether the regeneration tool started emitting distinct hashes."
    );
  }

  /// Canonical hash table regression guard: everything except the known
  /// `string_mk` / `string_of_list` alias must be distinct.
  #[test]
  fn prim_addrs_new_no_unexpected_duplicates() {
    let a = PrimAddrs::new();
    let dups = find_duplicates(&a);
    // Filter out the intentional alias (string_mk + string_of_list) —
    // see `prim_addrs_new_string_mk_and_of_list_are_intentionally_aliased`.
    let unexpected: Vec<_> = dups
      .into_iter()
      .filter(|(_, fields)| {
        !(fields.len() == 2
          && fields.contains(&"string_mk")
          && fields.contains(&"string_of_list"))
      })
      .collect();
    assert!(
      unexpected.is_empty(),
      "PrimAddrs::new() has unexpected duplicate addresses:\n{unexpected:#?}"
    );
  }

  #[test]
  fn primitives_from_env_empty_uses_synthetic_fallback() {
    // With an empty env, every `r(&a.*)` lookup misses and produces a
    // synthetic `@<hex prefix>` KId. Confirm construction succeeds and
    // yields recognizable synthetic names (in Meta mode).
    let env = KEnv::<crate::ix::kernel::mode::Meta>::new();
    let p = Primitives::from_env(&env);
    // The fallback name is `@<first 8 hex chars>`, a string part under an
    // anonymous Name. Verify the `nat` field lives at the expected
    // canonical address.
    let canon = PrimAddrs::new();
    assert_eq!(p.nat.addr.hex(), canon.nat.hex());
  }

  #[test]
  fn primitives_from_env_populated_resolves_against_env() {
    // Insert a single constant at the canonical Nat address and confirm
    // `Primitives::from_env` picks it up instead of falling back to
    // synthesis.
    let env = KEnv::<Anon>::new();
    let canon = PrimAddrs::new();

    let nat_id = KId::<Anon>::new(canon.nat.clone(), ());
    let nat_axio = KConst::<Anon>::Axio {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
    };
    env.insert(nat_id.clone(), nat_axio);

    let p = Primitives::from_env(&env);
    // Address still matches — the interesting property in Anon mode is
    // that name metadata is erased anyway, so we only check the addr.
    assert_eq!(p.nat.addr.hex(), canon.nat.hex());
    // The env entry should be the one the KEnv has (same address table).
    assert!(env.get(&p.nat).is_some());
  }

  #[test]
  fn primitives_from_env_orig_uses_orig_addrs() {
    // from_env_orig uses PrimAddrs::new_orig (LEON addrs), not new().
    let env = KEnv::<crate::ix::kernel::mode::Meta>::new();
    let p = Primitives::from_env_orig(&env);
    let orig = PrimAddrs::new_orig();
    let canon = PrimAddrs::new();
    assert_eq!(p.nat.addr.hex(), orig.nat.hex());
    // And the canonical addr is different from the LEON one — confirming
    // the two tables aren't accidentally aliased.
    assert_ne!(orig.nat.hex(), canon.nat.hex());
  }

  #[test]
  fn primitives_from_env_orig_empty_fallback_name_is_synthetic() {
    // Check that the synthetic fallback name has the `@<8hex>` shape for
    // an address that doesn't exist in the env. Uses Meta mode so the
    // name metadata is observable.
    let env = KEnv::<crate::ix::kernel::mode::Meta>::new();
    let p = Primitives::from_env_orig(&env);
    // Name of `p.nat` should be `@<first 8 hex of nat_orig addr>`.
    let orig = PrimAddrs::new_orig();
    let expected = format!("@{}", &orig.nat.hex()[..8]);
    let got_name = p.nat.name.clone();
    // Convert Name to string for comparison.
    let got_str = format!("{got_name}");
    assert!(
      got_str.contains(&expected),
      "expected synthetic name containing {expected:?}, got {got_str:?}"
    );
    // Silence unused-import lint.
    let _: Name = Name::anon();
  }

  #[test]
  fn new_and_default_match() {
    // `Default` is implemented via `new`, so they must agree.
    let a = PrimAddrs::new();
    let d = PrimAddrs::default();
    let entries_a = addrs_with_names(&a);
    let entries_d = addrs_with_names(&d);
    assert_eq!(entries_a.len(), entries_d.len());
    for ((name_a, addr_a), (name_d, addr_d)) in
      entries_a.iter().zip(entries_d.iter())
    {
      assert_eq!(name_a, name_d);
      assert_eq!(addr_a.hex(), addr_d.hex());
    }
  }
}
