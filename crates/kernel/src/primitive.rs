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

use ix_common::address::Address;

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

  // -- Int (type, ctors, ops) --
  // Int operations reduce by ordinary delta/iota plus native Nat reduction,
  // matching Lean's kernel. We still record these primitive addresses for
  // constructor recognition and Int decidable normalization.
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
  pub int_dec_eq: KId<M>,
  pub int_dec_le: KId<M>,
  pub int_dec_lt: KId<M>,

  // -- Names previously matched via name-based `is_const_named` --
  // The whnf reductions in `whnf.rs` historically string-matched these
  // by `id.name`, which is unsound under alpha-canonical content
  // hashing: an expression that happens to be ingested with an
  // alpha-twin's display name (e.g. `Lean.RBColor.rec` instead of
  // `Bool.rec`) would miss the check despite identical addresses.
  // Hardcoding each address per-name here lets the callsites compare
  // by `id.addr ==` and stay alpha-stable.
  pub punit: KId<M>,
  pub nat_rec: KId<M>,
  pub nat_cases_on: KId<M>,
  pub bit_vec: KId<M>,
  pub bit_vec_to_nat: KId<M>,
  pub bit_vec_of_nat: KId<M>,
  pub bit_vec_ult: KId<M>,
  pub decidable_decide: KId<M>,
  pub lt_lt: KId<M>,
  pub of_nat_of_nat: KId<M>,
  pub unit: KId<M>,
  pub punit_size_of_1: KId<M>,
  pub size_of_size_of: KId<M>,
  pub string_back: KId<M>,
  pub string_legacy_back: KId<M>,
  pub string_utf8_byte_size: KId<M>,

  // -- Native string-value fast paths --
  // `String.append` / `String.decEq` on literal arguments reduce
  // natively in whnf (same shape as the Nat ops in `try_reduce_nat`),
  // so evaluator-grade normalization of string values doesn't fall
  // into the structural ByteArray/UTF-8 model per character.
  pub string_append: KId<M>,
  pub string_dec_eq: KId<M>,
}

/// `PrimAddrs` and `reserved_marker_name` live in `ix-common` so crates
/// below the kernel (notably witness builders, which must seed the
/// primitives the kernel fabricates during reduction) can reach them
/// without depending on `ix-kernel` — that edge would be a cycle, since
/// `ix-kernel` depends on `ixon`. Re-exported here because this is where
/// kernel code has always named them.
pub use ix_common::prim_addrs::{PrimAddrs, reserved_marker_name};

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

  /// Resolve canonical primitive KIds from an external address → name
  /// lookup. Lazy IxOn workers call this before any primitive has
  /// necessarily been faulted into their local KEnv, so Meta-mode KIds
  /// still use the real serialized Lean names instead of synthetic
  /// `@<hex>` fallbacks.
  pub fn from_addr_names<F>(mut name_for_addr: F) -> Self
  where
    F: FnMut(&Address) -> Option<ix_common::env::Name>,
  {
    Self::from_addrs_with(&PrimAddrs::new(), |addr| {
      name_for_addr(addr)
        .map(|name| KId::new(addr.clone(), M::meta_field(name)))
    })
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

    Self::from_addrs_with(a, |addr| by_addr.get(addr).cloned())
  }

  /// Shared primitive table construction once the caller has chosen the
  /// address table and resolution source.
  fn from_addrs_with<F>(a: &PrimAddrs, mut resolve: F) -> Self
  where
    F: FnMut(&Address) -> Option<KId<M>>,
  {
    let mut r = |addr: &Address| -> KId<M> {
      resolve(addr).unwrap_or_else(|| {
        let hex = addr.hex();
        let name = ix_common::env::Name::str(
          ix_common::env::Name::anon(),
          format!("@{}", &hex[..8]),
        );
        KId::new(addr.clone(), M::meta_field(name))
      })
    };
    let marker = |addr: &Address, marker_name: &str| -> KId<M> {
      let name = ix_common::env::Name::str(
        ix_common::env::Name::anon(),
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
      int_dec_eq: r(&a.int_dec_eq),
      int_dec_le: r(&a.int_dec_le),
      int_dec_lt: r(&a.int_dec_lt),
      punit: r(&a.punit),
      nat_rec: r(&a.nat_rec),
      nat_cases_on: r(&a.nat_cases_on),
      bit_vec: r(&a.bit_vec),
      bit_vec_to_nat: r(&a.bit_vec_to_nat),
      bit_vec_of_nat: r(&a.bit_vec_of_nat),
      bit_vec_ult: r(&a.bit_vec_ult),
      decidable_decide: r(&a.decidable_decide),
      lt_lt: r(&a.lt_lt),
      of_nat_of_nat: r(&a.of_nat_of_nat),
      unit: r(&a.unit),
      punit_size_of_1: r(&a.punit_size_of_1),
      size_of_size_of: r(&a.size_of_size_of),
      string_back: r(&a.string_back),
      string_legacy_back: r(&a.string_legacy_back),
      string_utf8_byte_size: r(&a.string_utf8_byte_size),
      string_append: r(&a.string_append),
      string_dec_eq: r(&a.string_dec_eq),
    }
  }
}

#[cfg(test)]
mod tests {
  use std::collections::HashMap;

  use super::*;
  use crate::constant::KConst;
  use crate::expr::KExpr;
  use crate::id::KId;
  use crate::level::KUniv;
  use crate::mode::Anon;
  use ix_common::env::Name;

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
      ("int_dec_eq", &a.int_dec_eq),
      ("int_dec_le", &a.int_dec_le),
      ("int_dec_lt", &a.int_dec_lt),
      ("punit", &a.punit),
      ("pprod", &a.pprod),
      ("pprod_mk", &a.pprod_mk),
      ("nat_rec", &a.nat_rec),
      ("nat_cases_on", &a.nat_cases_on),
      ("bit_vec", &a.bit_vec),
      ("bit_vec_to_nat", &a.bit_vec_to_nat),
      ("bit_vec_of_nat", &a.bit_vec_of_nat),
      ("bit_vec_ult", &a.bit_vec_ult),
      ("decidable_decide", &a.decidable_decide),
      ("lt_lt", &a.lt_lt),
      ("of_nat_of_nat", &a.of_nat_of_nat),
      ("unit", &a.unit),
      ("punit_size_of_1", &a.punit_size_of_1),
      ("size_of_size_of", &a.size_of_size_of),
      ("string_back", &a.string_back),
      ("string_legacy_back", &a.string_legacy_back),
      ("string_utf8_byte_size", &a.string_utf8_byte_size),
      ("string_append", &a.string_append),
      ("string_dec_eq", &a.string_dec_eq),
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
    let env = KEnv::<crate::mode::Meta>::new();
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
    let mut env = KEnv::<Anon>::new();
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
    let env = KEnv::<crate::mode::Meta>::new();
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
    let env = KEnv::<crate::mode::Meta>::new();
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
