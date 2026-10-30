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
  dev_kzg_srs: bool,
  dev_final_srs: bool,
  final_proof: u8,
  fresh: bool,
) -> LeanIOResult<LeanOwned> {
  let dir = dir.to_string();
  let cache_root = cache_root.to_string();
  let final_proof = match pipeline::FinalSystem::try_from(final_proof) {
    Ok(system) => {
      pipeline::FinalOptions { system, allow_development: dev_final_srs }
    },
    Err(error) => return LeanIOResult::error_string(error),
  };
  let fixed_root = optional(&fixed_root);
  let result = pipeline::CompressConfig::from_env(
    std::path::Path::new(&cache_root),
    dev_kzg_srs,
    final_proof,
  )
  .and_then(|mut config| {
    config.fresh = fresh;
    pipeline::compress(
      pipeline::CompressInput {
        vk: vk.as_bytes(),
        proof: proof.as_bytes(),
        claim: claim.as_bytes(),
        statement: statement.as_bytes(),
        fixed_root: fixed_root.as_deref(),
        out: std::path::Path::new(&dir),
      },
      &config,
    )
  });
  match result {
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
extern "C" fn rs_compression_verify_development(
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  bundle: LeanByteArray<LeanBorrowed<'_>>,
  trusted_digest: LeanString<LeanBorrowed<'_>>,
  allow_development: bool,
) -> LeanIOResult<LeanOwned> {
  let pin_text = trusted_digest.to_string();
  let pin = match blake3::Hash::from_hex(pin_text.as_bytes()) {
    Ok(pin) => pin,
    Err(error) => {
      return LeanIOResult::error_string(&format!(
        "invalid verifier bundle BLAKE3 pin: {error}"
      ));
    },
  };
  match pipeline::verify_with_development_verifier(
    proof.as_bytes(),
    claim.as_bytes(),
    bundle.as_bytes(),
    pin.as_bytes(),
    allow_development,
  ) {
    Ok(class) => LeanIOResult::ok(LeanString::new(class.label())),
    Err(error) => LeanIOResult::error_string(&error.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_curve() -> LeanIOResult<LeanOwned> {
  LeanIOResult::ok(LeanString::new(ix_proof_compression::kzg::curve::NAME))
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_setup(
  dev_kzg_srs: bool,
  dev_final_srs: bool,
  final_proof: u8,
) -> LeanIOResult<LeanOwned> {
  let final_proof = match pipeline::FinalSystem::try_from(final_proof) {
    Ok(system) => {
      pipeline::FinalOptions { system, allow_development: dev_final_srs }
    },
    Err(error) => return LeanIOResult::error_string(error),
  };
  match pipeline::setup_description(dev_kzg_srs, final_proof) {
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

/// The versioned normalization layout for the selected aggregation backend.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_release_root_layout(
  vk: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match pipeline::release_root_layout(vk.as_bytes()) {
    Ok(layout) => LeanIOResult::ok(LeanString::new(layout)),
    Err(error) => LeanIOResult::error_string(&error.to_string()),
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

/// Write the FRI stage's root input directory without compressing.
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

/// Return the GPU memory the Aiur prover's allocation pool retains to the
/// driver, so compression starts with the whole device. A CPU build has none.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_release_gpu_memory() -> LeanIOResult<LeanOwned> {
  #[cfg(feature = "cuda")]
  multi_stark::cuda::release_device_memory();
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

fn merge_kind(kind: u8) -> Result<pipeline::MergeKind, String> {
  match kind {
    0 => Ok(pipeline::MergeKind::Join),
    1 => Ok(pipeline::MergeKind::Import),
    other => Err(format!("unknown merge kind {other}")),
  }
}

/// The bundled merge release, or the one in `keys` when it names a key
/// directory.
fn merge_release(
  keys: &LeanString<LeanBorrowed<'_>>,
) -> pipeline::Result<pipeline::Release> {
  match optional(keys) {
    Some(dir) => pipeline::Release::load(std::path::Path::new(&dir)),
    None => pipeline::Release::bundled(),
  }
}

/// The inputs of a merge of `kind`: a join reads both, an import the left.
fn merge_inputs<'a>(
  kind: pipeline::MergeKind,
  left: (&'a [u8], &'a [u8]),
  right: (&'a [u8], &'a [u8]),
) -> Vec<(&'a [u8], &'a [u8])> {
  match kind {
    pipeline::MergeKind::Join => vec![left, right],
    pipeline::MergeKind::Import => vec![left],
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_merged_claim(
  kind: u8,
  left: LeanByteArray<LeanBorrowed<'_>>,
  right: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let kind = match merge_kind(kind) {
    Ok(kind) => kind,
    Err(error) => return LeanIOResult::error_string(&error),
  };
  let claims: Vec<_> =
    merge_inputs(kind, (left.as_bytes(), &[]), (right.as_bytes(), &[]))
      .into_iter()
      .map(|(claim, _)| claim)
      .collect();
  match pipeline::merged_claim(kind, &claims) {
    Ok(claim) => LeanIOResult::ok(LeanByteArray::from_bytes(&claim)),
    Err(error) => LeanIOResult::error_string(&error.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_merge(
  kind: u8,
  left_claim: LeanByteArray<LeanBorrowed<'_>>,
  left_proof: LeanByteArray<LeanBorrowed<'_>>,
  right_claim: LeanByteArray<LeanBorrowed<'_>>,
  right_proof: LeanByteArray<LeanBorrowed<'_>>,
  keys: LeanString<LeanBorrowed<'_>>,
  dir: LeanString<LeanBorrowed<'_>>,
  cache_root: LeanString<LeanBorrowed<'_>>,
  dev_kzg_srs: bool,
  fresh: bool,
) -> LeanIOResult<LeanOwned> {
  let kind = match merge_kind(kind) {
    Ok(kind) => kind,
    Err(error) => return LeanIOResult::error_string(&error),
  };
  let dir = dir.to_string();
  let cache_root = cache_root.to_string();
  let children: Vec<_> = merge_inputs(
    kind,
    (left_claim.as_bytes(), left_proof.as_bytes()),
    (right_claim.as_bytes(), right_proof.as_bytes()),
  )
  .into_iter()
  .map(|(claim, proof)| pipeline::MergeChild { claim, proof })
  .collect();
  let result = merge_release(&keys).and_then(|release| {
    let mut config = pipeline::CompressConfig::from_env(
      std::path::Path::new(&cache_root),
      dev_kzg_srs,
      pipeline::FinalOptions {
        system: pipeline::FinalSystem::None,
        allow_development: dev_kzg_srs,
      },
    )?;
    config.fresh = fresh;
    pipeline::merge(
      kind,
      &children,
      &release,
      &config,
      std::path::Path::new(&dir),
    )
  });
  match result {
    Ok((_, proof)) => LeanIOResult::ok(LeanByteArray::from_bytes(&proof)),
    Err(error) => LeanIOResult::error_string(&error.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_verify_merged(
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  keys: LeanString<LeanBorrowed<'_>>,
  dev_srs: bool,
) -> LeanIOResult<LeanOwned> {
  let result = merge_release(&keys).and_then(|release| {
    pipeline::verify_merged(
      proof.as_bytes(),
      claim.as_bytes(),
      &release,
      dev_srs,
    )
  });
  match result {
    Ok(class) => LeanIOResult::ok(LeanString::new(class.label())),
    Err(error) => LeanIOResult::error_string(&error.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_prepare(
  root_vk: LeanByteArray<LeanBorrowed<'_>>,
  cache_root: LeanString<LeanBorrowed<'_>>,
  dev_kzg_srs: bool,
  plonk: bool,
) -> LeanIOResult<LeanOwned> {
  let cache_root = cache_root.to_string();
  let result = pipeline::CompressConfig::from_env(
    std::path::Path::new(&cache_root),
    dev_kzg_srs,
    pipeline::FinalOptions {
      system: pipeline::FinalSystem::None,
      allow_development: dev_kzg_srs,
    },
  )
  .and_then(|config| {
    pipeline::prepare(root_vk.as_bytes(), &config)?;
    if plonk {
      pipeline::prepare_plonk(&config)?;
    }
    Ok(())
  });
  match result {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(error) => LeanIOResult::error_string(&error.to_string()),
  }
}
