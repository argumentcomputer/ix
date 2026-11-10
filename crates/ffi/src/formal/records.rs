//! Typed Lean records of `Ix/FormalProver.lean`, declared with
//! `lean_inductive!` and read and built through the generated accessors.
//! A record read from Lean is checked against its declared layout before
//! any field is touched, so a Lean structure that changes shape fails
//! loudly instead of being misread.
//!
//! Lean stores object fields first, then scalars by descending width in
//! declaration order within each width. `Bool` and enumerations without
//! fields are one-byte scalars.
use std::path::PathBuf;

use crate::lean::LeanOptionField;
use aggregate_controller::catalog;
use ix_common::address::Address;
use ix_prover::{
  aggregate::{AggregateConfig, CatalogConfig, LaneConfig, NormalizeConfig},
  protocol::{Options, RetentionPolicy},
  system::ProtocolParameters,
  tools::{Outcome, Planned},
};
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanByteArray, LeanCtorLayout, LeanNat, LeanOption,
  LeanOwned, LeanRef, LeanString,
};

lean_ffi::lean_inductive! {
  /// `logBlowup`, `numQueries`, `commitProofOfWorkBits`,
  /// `queryProofOfWorkBits`.
  LeanProtocolParameters [ { num_obj: 4 } ];
  /// `maxRows`, `maxRamBytes`, `device`; `retention`.
  LeanJobOptions [ { num_obj: 3, num_8: 1 } ];
  /// `availableBytes`, `cores`.
  LeanResources [ { num_obj: 2 } ];
  /// `suggestedParts`, `generationPeakBytes`, `provingPeakBytes`; `fits`,
  /// `canSplit`.
  LeanPlanSummary [ { num_obj: 3, num_8: 2 } ];
  /// `plan`, `report`; `status`.
  LeanOutcome [ { num_obj: 2, num_32: 1 } ];
  /// `manifest` … `options` (ten objects); `useCache`, `useIndex`,
  /// `claimsOnly`, `assumeBinding`.
  LeanLaneConfig [ { num_obj: 10, num_8: 4 } ];
  LeanLaneResult [
    { num_obj: 2 },  // root: `address`, `claimTraceShards`
    { num_obj: 1 },  // claims
  ];
  /// `manifest` … `options` (ten objects); `planOnly`, `useCache`,
  /// `writeOutputs`, `wrapRoot`, `assumeBinding`.
  LeanAggregateConfig [ { num_obj: 10, num_8: 5 } ];
  /// `label`, `claim`, `bindingSection`, `literalClass`.
  LeanCatalogMember [ { num_obj: 4 } ];
  /// `members`, `proofs`, `expectedRoot`, `device`, `options`; `useCache`,
  /// `writeOutputs`.
  LeanCatalogConfig [ { num_obj: 5, num_8: 2 } ];
  /// `device`, `options`.
  LeanNormalizeConfig [ { num_obj: 2 } ];
}

/// `object` as the Lean type `T`, checked against its layouts first: a
/// boxed scalar must name a constructor without fields, and a constructor
/// object must have its variant's object fields. Returns the tag too.
pub(super) fn variant<'a, T: LeanCtorLayout>(
  object: LeanBorrowed<'a>,
  wrap: fn(LeanBorrowed<'a>) -> T,
  name: &str,
) -> Result<(usize, T), String> {
  let (tag, objects) = if object.is_scalar() {
    (object.unbox_usize(), None)
  } else {
    (usize::from(object.tag()), Some(object.as_ctor().num_objs()))
  };
  let layout =
    T::LAYOUTS.get(tag).ok_or_else(|| format!("invalid {name} tag {tag}"))?;
  match objects {
    None if layout.num_obj == 0 => {},
    None => return Err(format!("{name}: expected a constructor object")),
    Some(found) if found == layout.num_obj => {},
    Some(found) => {
      return Err(format!(
        "{name}: expected {} object fields, found {found}",
        layout.num_obj
      ));
    },
  }
  Ok((tag, wrap(object)))
}

pub(super) fn record<'a, T: LeanCtorLayout>(
  object: LeanBorrowed<'a>,
  wrap: fn(LeanBorrowed<'a>) -> T,
  name: &str,
) -> Result<T, String> {
  Ok(variant(object, wrap, name)?.1)
}

pub(super) fn nat(object: LeanBorrowed<'_>) -> Result<usize, String> {
  if object.is_scalar() {
    Ok(object.unbox_usize())
  } else {
    Err("natural number argument is too large".into())
  }
}

fn u64_nat(object: LeanBorrowed<'_>) -> Result<u64, String> {
  u64::try_from(nat(object)?).map_err(|e| e.to_string())
}

fn option<T>(
  object: LeanBorrowed<'_>,
  f: impl FnOnce(LeanBorrowed<'_>) -> Result<T, String>,
) -> Result<Option<T>, String> {
  match variant(object, LeanOptionField, "Option")? {
    (0, _) => Ok(None),
    (_, some) => f(some.get_obj(0)).map(Some),
  }
}

fn flag(byte: u8) -> Result<bool, String> {
  match byte {
    0 => Ok(false),
    1 => Ok(true),
    other => Err(format!("invalid Bool {other}")),
  }
}

fn string(object: LeanBorrowed<'_>) -> String {
  object.as_string().as_str().to_owned()
}

fn bytes(object: LeanBorrowed<'_>) -> Vec<u8> {
  object.as_byte_array().as_bytes().to_vec()
}

fn address(object: LeanBorrowed<'_>) -> Result<Address, String> {
  Address::from_slice(object.as_byte_array().as_bytes())
    .map_err(|e| format!("a store address has 32 bytes: {e}"))
}

fn addresses(object: LeanBorrowed<'_>) -> Result<Vec<Address>, String> {
  object.as_array().iter().map(address).collect()
}

fn device(object: LeanBorrowed<'_>) -> Result<Option<i32>, String> {
  option(object, |d| {
    i32::try_from(nat(d)?).map_err(|e| format!("CUDA device index: {e}"))
  })
}

pub(super) fn parameters(
  object: LeanProtocolParameters<LeanBorrowed<'_>>,
) -> Result<ProtocolParameters, String> {
  let p =
    record(*object.inner(), LeanProtocolParameters, "ProtocolParameters")?;
  Ok(ProtocolParameters {
    log_blowup: nat(p.get_obj(0))?,
    num_queries: nat(p.get_obj(1))?,
    commit_proof_of_work_bits: nat(p.get_obj(2))?,
    query_proof_of_work_bits: nat(p.get_obj(3))?,
  })
}

pub(super) fn options(object: LeanBorrowed<'_>) -> Result<Options, String> {
  let o = record(object, LeanJobOptions, "JobOptions")?;
  let retention = match o.get_num_8(0) {
    0 => RetentionPolicy::Auto,
    1 => RetentionPolicy::Retain,
    2 => RetentionPolicy::Regenerate,
    other => return Err(format!("invalid retention {other}")),
  };
  Ok(Options {
    max_rows: option(o.get_obj(0), nat)?,
    max_ram_bytes: option(o.get_obj(1), u64_nat)?,
    device: device(o.get_obj(2))?,
    retention,
    ..Options::default()
  })
}

pub(super) fn lane_config(
  object: LeanLaneConfig<LeanBorrowed<'_>>,
) -> Result<LaneConfig, String> {
  let c = record(*object.inner(), LeanLaneConfig, "LaneConfig")?;
  Ok(LaneConfig {
    manifest: PathBuf::from(string(c.get_obj(0))),
    lanes: nat(c.get_obj(1))?,
    device: device(c.get_obj(2))?,
    max_ram_bytes: nat(c.get_obj(3))?,
    exec_jobs: nat(c.get_obj(4))?,
    structural_above: nat(c.get_obj(5))?,
    out_manifest: option(c.get_obj(6), |p| Ok(PathBuf::from(string(p))))?,
    select: option(c.get_obj(7), |ids| {
      ids
        .as_array()
        .iter()
        .map(|id| u32::try_from(nat(id)?).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>, String>>()
    })?,
    binding_proof: option(c.get_obj(8), address)?,
    options: options(c.get_obj(9))?,
    use_cache: flag(c.get_num_8(0))?,
    use_index: flag(c.get_num_8(1))?,
    claims_only: flag(c.get_num_8(2))?,
    assume_binding: flag(c.get_num_8(3))?,
  })
}

pub(super) fn aggregate_config(
  object: LeanAggregateConfig<LeanBorrowed<'_>>,
) -> Result<AggregateConfig, String> {
  let c = record(*object.inner(), LeanAggregateConfig, "AggregateConfig")?;
  Ok(AggregateConfig {
    manifest: PathBuf::from(string(c.get_obj(0))),
    proofs: addresses(c.get_obj(1))?,
    lanes: nat(c.get_obj(2))?,
    device: device(c.get_obj(3))?,
    exec_ahead: nat(c.get_obj(4))?,
    structural_above: nat(c.get_obj(5))?,
    reprove_slot: option(c.get_obj(6), nat)?,
    subtree: option(c.get_obj(7), nat)?,
    binding_proof: option(c.get_obj(8), address)?,
    options: options(c.get_obj(9))?,
    plan_only: flag(c.get_num_8(0))?,
    use_cache: flag(c.get_num_8(1))?,
    write_outputs: flag(c.get_num_8(2))?,
    wrap_root: flag(c.get_num_8(3))?,
    assume_binding: flag(c.get_num_8(4))?,
  })
}

fn catalog_member(object: LeanBorrowed<'_>) -> Result<catalog::Member, String> {
  let m = record(object, LeanCatalogMember, "CatalogMember")?;
  Ok(catalog::Member {
    label: string(m.get_obj(0)),
    claim: ixon::Claim::from_bytes(m.get_obj(1).as_byte_array().as_bytes())?,
    binding_section: bytes(m.get_obj(2)),
    literal_class: option(m.get_obj(3), address)?,
  })
}

pub(super) fn catalog_config(
  object: LeanCatalogConfig<LeanBorrowed<'_>>,
) -> Result<CatalogConfig, String> {
  let c = record(*object.inner(), LeanCatalogConfig, "CatalogConfig")?;
  Ok(CatalogConfig {
    members: c
      .get_obj(0)
      .as_array()
      .iter()
      .map(catalog_member)
      .collect::<Result<_, _>>()?,
    proofs: addresses(c.get_obj(1))?,
    expected_root: bytes(c.get_obj(2)),
    device: device(c.get_obj(3))?,
    options: options(c.get_obj(4))?,
    use_cache: flag(c.get_num_8(0))?,
    write_outputs: flag(c.get_num_8(1))?,
  })
}

pub(super) fn normalize_config(
  object: LeanNormalizeConfig<LeanBorrowed<'_>>,
) -> Result<NormalizeConfig, String> {
  let c = record(*object.inner(), LeanNormalizeConfig, "NormalizeConfig")?;
  Ok(NormalizeConfig {
    device: device(c.get_obj(0))?,
    options: options(c.get_obj(1))?,
  })
}

pub(super) fn lean_nat(n: u64) -> LeanNat<LeanOwned> {
  LeanNat::new(LeanOwned::from_nat_u64(n))
}

pub(super) fn some_or_none<T: Into<LeanOwned>>(
  value: Option<T>,
) -> LeanOption<LeanOwned> {
  value.map_or_else(LeanOption::none, LeanOption::some)
}

fn planned(plan: &Planned) -> LeanPlanSummary<LeanOwned> {
  let summary = LeanPlanSummary::alloc(0);
  summary.set_obj(0, lean_nat(plan.suggested_parts as u64));
  summary.set_obj(1, lean_nat(plan.generation_peak_bytes));
  summary.set_obj(2, lean_nat(plan.proving_peak_bytes));
  summary.set_num_8(0, u8::from(plan.fits));
  summary.set_num_8(1, u8::from(plan.can_split));
  summary
}

/// `report` is empty unless requested.
pub(super) fn outcome(
  outcome: &Outcome,
  report: bool,
) -> LeanOutcome<LeanOwned> {
  let result = LeanOutcome::alloc(0);
  result.set_obj(0, some_or_none(outcome.plan.as_ref().map(planned)));
  let text = if report { outcome.report.to_string() } else { String::new() };
  result.set_obj(1, LeanString::new(&text));
  result.set_num_32(0, outcome.status);
  result
}

pub(super) fn resources(
  available: Option<u64>,
  cores: usize,
) -> LeanResources<LeanOwned> {
  let result = LeanResources::alloc(0);
  result.set_obj(0, some_or_none(available.map(lean_nat)));
  result.set_obj(1, lean_nat(cores as u64));
  result
}

pub(super) fn lean_address(address: &Address) -> LeanByteArray<LeanOwned> {
  LeanByteArray::from_bytes(address.as_bytes())
}

pub(super) fn lean_array(
  items: impl ExactSizeIterator<Item = impl Into<LeanOwned>>,
) -> LeanArray<LeanOwned> {
  let array = LeanArray::alloc(items.len());
  for (i, item) in items.enumerate() {
    array.set(i, item);
  }
  array
}

/// Test-only mirror of `Tests.FFI.Basic.MixedScalars`, whose fields cover
/// every scalar width in an order unlike the runtime's.
#[cfg(feature = "test-ffi")]
// `lean_inductive!` completes each layout with `..SingleCtorLayout::ZERO`,
// which is redundant here because every width is given.
#[allow(clippy::needless_update)]
mod mixed {
  use lean_ffi::object::{
    LeanArray, LeanBorrowed, LeanNat, LeanOwned, LeanProd, LeanRef, LeanString,
  };

  lean_ffi::lean_inductive! {
    /// `name`, `count`; `size`; `wide`; `word`; `half`; `flag`, `small`.
    LeanMixedScalars [ {
      num_obj: 2, num_usize: 1, num_64: 1, num_32: 1, num_16: 1, num_8: 2
    } ];
  }

  /// `Tests.FFI.Basic.mixedScalarsFields : @& MixedScalars →
  /// String × Array Nat`: the fields as Rust read them, in declaration
  /// order.
  #[unsafe(no_mangle)]
  extern "C" fn rs_mixed_scalars_fields(
    value: LeanMixedScalars<LeanBorrowed<'_>>,
  ) -> LeanProd<LeanOwned> {
    let fields = (|| {
      let m = super::record(*value.inner(), LeanMixedScalars, "MixedScalars")?;
      let numbers = vec![
        u64::from(m.get_num_8(0)),
        m.get_num_64(0),
        u64::from(m.get_num_8(1)),
        u64::from(m.get_num_16(0)),
        u64::from(m.get_num_32(0)),
        m.get_usize(0) as u64,
        super::nat(m.get_obj(1))? as u64,
      ];
      Ok::<_, String>((m.get_obj(0).as_string().as_str().to_owned(), numbers))
    })();
    let (name, numbers) = fields.unwrap_or_else(|e| (e, Vec::new()));
    let array = LeanArray::alloc(numbers.len());
    for (i, n) in numbers.into_iter().enumerate() {
      array.set(i, LeanNat::new(LeanOwned::from_nat_u64(n)));
    }
    LeanProd::new(LeanString::new(&name), array)
  }

  /// `Tests.FFI.Basic.roundtripMixedScalars : @& MixedScalars →
  /// MixedScalars`: rebuilt field by field.
  #[unsafe(no_mangle)]
  extern "C" fn rs_roundtrip_mixed_scalars(
    value: LeanMixedScalars<LeanBorrowed<'_>>,
  ) -> LeanMixedScalars<LeanOwned> {
    let out = LeanMixedScalars::alloc(0);
    out.set_obj(0, value.get_obj(0).to_owned_ref());
    out.set_obj(1, value.get_obj(1).to_owned_ref());
    out.set_usize(0, value.get_usize(0));
    out.set_num_64(0, value.get_num_64(0));
    out.set_num_32(0, value.get_num_32(0));
    out.set_num_16(0, value.get_num_16(0));
    out.set_num_8(0, value.get_num_8(0));
    out.set_num_8(1, value.get_num_8(1));
    out
  }
}
