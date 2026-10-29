//! Main CLI bridge; compression is linked into the ix executable.
use crate::aiur::aggregate::normalize::{self, RootWrap};
use crate::aiur::lean_unbox_nat_as_usize;
use aiur::synthesis::AiurSystem;
use ix_proof_compression::pipeline::{self, FixedRoot};
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanExternal, LeanIOResult, LeanNat, LeanOwned,
  LeanString,
};

fn optional(text: &LeanString<LeanBorrowed<'_>>) -> Option<String> {
  let text = text.to_string();
  (!text.is_empty()).then_some(text)
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_run(
  vk: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  statement: LeanByteArray<LeanBorrowed<'_>>,
  fixed_root: LeanString<LeanBorrowed<'_>>,
  dir: LeanString<LeanBorrowed<'_>>,
  cache_root: LeanString<LeanBorrowed<'_>>,
  dev_srs: bool,
  log_height: u32,
  terminal: u8,
) -> LeanIOResult<LeanOwned> {
  let dir = dir.to_string();
  let cache_root = cache_root.to_string();
  let terminal = match pipeline::TerminalOptions::try_from(terminal) {
    Ok(system) => system,
    Err(error) => return LeanIOResult::error_string(error),
  };
  match pipeline::compress_with_terminal(
    vk.as_bytes(),
    proof.as_bytes(),
    claim.as_bytes(),
    statement.as_bytes(),
    optional(&fixed_root).as_deref(),
    std::path::Path::new(&dir),
    std::path::Path::new(&cache_root),
    dev_srs,
    log_height,
    terminal,
  ) {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(bytes.as_slice())),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_verify(
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  dev_srs: bool,
) -> LeanIOResult<LeanOwned> {
  match pipeline::verify(proof.as_bytes(), claim.as_bytes(), dev_srs) {
    Ok(class) => LeanIOResult::ok(LeanString::new(class.label())),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_curve() -> LeanIOResult<LeanOwned> {
  LeanIOResult::ok(LeanString::new(ix_proof_compression::kzg::curve::NAME))
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_setup(dev_srs: bool) -> LeanIOResult<LeanOwned> {
  match pipeline::setup_description(dev_srs) {
    Ok(description) => LeanIOResult::ok(LeanString::new(description)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_check_claim(
  claim: LeanByteArray<LeanBorrowed<'_>>,
  statement: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match pipeline::check_claim(claim.as_bytes(), statement.as_bytes()) {
    Ok(_statement) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

fn root_wrap<'a>(
  system: &'a LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_idx: &LeanNat<LeanBorrowed<'_>>,
  allowed: &'a LeanByteArray<LeanBorrowed<'_>>,
  ixvm_vk: &'a LeanByteArray<LeanBorrowed<'_>>,
  claim: &'a LeanByteArray<LeanBorrowed<'_>>,
) -> RootWrap<'a> {
  RootWrap {
    system: system.get(),
    aggr_idx: lean_unbox_nat_as_usize(aggr_idx.inner()),
    allowed: allowed.as_bytes(),
    ixvm_vk: ixvm_vk.as_bytes(),
    claim: claim.as_bytes(),
  }
}

/// Per-circuit rows of one root wrap execution, as a JSON array.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_root_rows(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_idx: LeanNat<LeanBorrowed<'_>>,
  allowed: LeanByteArray<LeanBorrowed<'_>>,
  ixvm_vk: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let wrap = root_wrap(&system, &aggr_idx, &allowed, &ixvm_vk, &claim);
  match wrap.rows(proof.as_bytes()) {
    Ok(rows) => LeanIOResult::ok(LeanString::new(
      &serde_json::to_string(&rows).expect("row counts serialize"),
    )),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

/// The fixed layout holding every row-count array in the JSON array `rows`.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_root_layout(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  rows: LeanString<LeanBorrowed<'_>>,
  headroom: u32,
  claim_len: u32,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<String, String> {
    let executions: Vec<Vec<usize>> =
      serde_json::from_str(&rows.to_string()).map_err(|e| e.to_string())?;
    let first = executions.first().ok_or("no root executions to size")?;
    if executions.iter().any(|rows| rows.len() != first.len()) {
      return Err("root executions have different circuit counts".into());
    }
    let maxima: Vec<_> = (0..first.len())
      .map(|i| executions.iter().map(|rows| rows[i]).max().unwrap_or(0))
      .collect();
    let layout = normalize::layout(
      system.get(),
      &maxima,
      u8::try_from(headroom).map_err(|e| e.to_string())?,
      claim_len as usize,
    )?;
    Ok(layout.to_json())
  })();
  match result {
    Ok(json) => LeanIOResult::ok(LeanString::new(&json)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

/// Wrap and prove the root in `layout`'s fixed shape.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_normalize_root(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_idx: LeanNat<LeanBorrowed<'_>>,
  allowed: LeanByteArray<LeanBorrowed<'_>>,
  ixvm_vk: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
  layout: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let wrap = root_wrap(&system, &aggr_idx, &allowed, &ixvm_vk, &claim);
  let result = FixedRoot::from_json(&layout.to_string())
    .map_err(|e| e.to_string())
    .and_then(|layout| wrap.normalize(proof.as_bytes(), &layout));
  match result {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(&bytes)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

/// Write the FRI worker's root input directory without compressing.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_write_root(
  vk: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  statement: LeanByteArray<LeanBorrowed<'_>>,
  fixed_root: LeanString<LeanBorrowed<'_>>,
  dir: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match pipeline::write_root_input(
    std::path::Path::new(&dir.to_string()),
    vk.as_bytes(),
    proof.as_bytes(),
    claim.as_bytes(),
    statement.as_bytes(),
    optional(&fixed_root).as_deref(),
  ) {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}
