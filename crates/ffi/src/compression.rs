//! Main CLI bridge; compression is linked into the ix executable.
use ix_proof_compression::pipeline;
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanIOResult, LeanOwned, LeanString,
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

/// Verify a recursive KZG proof of `claim` under a verifying key the caller
/// trusts by its BLAKE3 digest, for the root statement `expected_claims`
/// the caller derived from its own aggregation backend.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_verify_with_vk(
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  expected_claims: LeanByteArray<LeanBorrowed<'_>>,
  vk: LeanByteArray<LeanBorrowed<'_>>,
  trusted_digest: LeanString<LeanBorrowed<'_>>,
  allow_development: bool,
) -> LeanIOResult<LeanOwned> {
  let pin = match blake3::Hash::from_hex(trusted_digest.to_string().as_bytes())
  {
    Ok(pin) => pin,
    Err(error) => {
      return LeanIOResult::error_string(&format!(
        "invalid verifying key BLAKE3 pin: {error}"
      ));
    },
  };
  match pipeline::verify_with_vk(
    proof.as_bytes(),
    claim.as_bytes(),
    expected_claims.as_bytes(),
    vk.as_bytes(),
    pin.as_bytes(),
    allow_development,
  ) {
    Ok(class) => LeanIOResult::ok(LeanString::new(class.label())),
    Err(error) => LeanIOResult::error_string(&error.to_string()),
  }
}

/// Derive, without any proof, the recursive verifying key that compressions
/// of roots of `vk` normalized to `layout` prove to.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_derive_vk(
  vk: LeanByteArray<LeanBorrowed<'_>>,
  layout: LeanString<LeanBorrowed<'_>>,
  cache_root: LeanString<LeanBorrowed<'_>>,
  dev_kzg_srs: bool,
) -> LeanIOResult<LeanOwned> {
  let result = pipeline::CompressConfig::from_env(
    std::path::Path::new(&cache_root.to_string()),
    dev_kzg_srs,
    pipeline::FinalOptions {
      system: pipeline::FinalSystem::None,
      allow_development: dev_kzg_srs,
    },
  )
  .and_then(|config| {
    pipeline::derive_recursive_vk(
      vk.as_bytes(),
      &layout.to_string(),
      &config.setup,
    )
  });
  match result {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(&bytes)),
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

/// Check the inner KZG setup and, given a nonempty aggregation backend key
/// and layout, publish its stages' fixed preprocessing (`pipeline::prepare`).
#[unsafe(no_mangle)]
extern "C" fn rs_compression_prepare(
  root_vk: LeanByteArray<LeanBorrowed<'_>>,
  layout: LeanString<LeanBorrowed<'_>>,
  cache_root: LeanString<LeanBorrowed<'_>>,
  dev_kzg_srs: bool,
  plonk: bool,
) -> LeanIOResult<LeanOwned> {
  let cache_root = cache_root.to_string();
  let layout = optional(&layout);
  let result = pipeline::CompressConfig::from_env(
    std::path::Path::new(&cache_root),
    dev_kzg_srs,
    pipeline::FinalOptions {
      system: pipeline::FinalSystem::None,
      allow_development: dev_kzg_srs,
    },
  )
  .and_then(|config| {
    let root = layout.as_deref().map(|layout| (root_vk.as_bytes(), layout));
    pipeline::prepare(root, &config)?;
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
