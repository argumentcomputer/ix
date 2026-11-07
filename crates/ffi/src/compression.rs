//! Main CLI bridge; compression is linked into the ix executable.
use aiur::{
  artifact::Package,
  bytecode::CheckedProgram,
  field::{FieldBackend, NativeField},
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, BatchProof, Parameters},
  },
};
use ix_proof_compression::pipeline::{self, FixedRoot};
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanIOResult, LeanOwned, LeanString,
};
use multi_stark::types::Val;

/// The aggregation artifact's checked program and trace plan.
fn aggregate(
  path: &LeanString<LeanBorrowed<'_>>,
) -> Result<(CheckedProgram<NativeField<Val>>, TraceArtifact), String> {
  let (package, _) = Package::load(path.to_string().as_ref())?;
  let (program, trace) = package.traced()?;
  Ok((program.check_field::<Val>()?, trace))
}

/// An optional `.ixl` layout: empty means none.
fn optional(bytes: &LeanByteArray<LeanBorrowed<'_>>) -> Option<Vec<u8>> {
  let bytes = bytes.as_bytes();
  (!bytes.is_empty()).then(|| bytes.to_vec())
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_run(
  vk: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  statement: LeanByteArray<LeanBorrowed<'_>>,
  fixed_root: LeanByteArray<LeanBorrowed<'_>>,
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

/// The versioned normalization layout (`.ixl` bytes) for the selected
/// aggregation backend.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_release_root_layout(
  vk: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match pipeline::release_root_layout(vk.as_bytes()) {
    Ok(layout) => LeanIOResult::ok(LeanByteArray::from_bytes(layout)),
    Err(error) => LeanIOResult::error_string(&error.to_string()),
  }
}

/// Per-circuit rows of one root wrap execution, as a JSON array. The
/// invocation is in Ixon (`aiur::artifact`).
#[unsafe(no_mangle)]
extern "C" fn rs_compression_root_rows(
  aggr_artifact: LeanString<LeanBorrowed<'_>>,
  invocation: LeanByteArray<LeanBorrowed<'_>>,
  raw_proof: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<String, String> {
    let (program, trace) = aggregate(&aggr_artifact)?;
    let plan = TracePlan::new(&program, trace)?;
    let backend =
      Backend::for_batch_verification(&plan, Parameters::default())?;
    let invocation = stark_verifier::Invocation::decode(invocation.as_bytes())?;
    let args = program.field().decode(&invocation.args)?;
    let proof_bytes = raw_proof.as_bytes();
    let proof = BatchProof::from_bytes(proof_bytes)
      .map_err(|e| format!("root proof decode failed: {e}"))?;
    if proof.to_bytes().map_err(|e| e.to_string())? != proof_bytes {
      return Err("noncanonical or trailing root proof bytes".into());
    }
    backend.verify_batch(&invocation.entry, &args, &[], &proof)?;
    let hints = stark_verifier::prepare(&program, &invocation.streams)?;
    let record =
      hints.execute(&invocation.entry, args).map_err(|e| e.to_string())?;
    if !record.output.is_empty() {
      return Err("verifier returned a non-unit value".into());
    }
    let rows = backend.execution_rows(&record);
    serde_json::to_string(&rows).map_err(|e| e.to_string())
  })();
  match result {
    Ok(rows) => LeanIOResult::ok(LeanString::new(&rows)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

/// The fixed layout (`.ixl` bytes) holding every row-count array in the JSON
/// array `rows`.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_root_layout(
  aggr_artifact: LeanString<LeanBorrowed<'_>>,
  rows: LeanString<LeanBorrowed<'_>>,
  headroom: u32,
  claim_len: u32,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<Vec<u8>, String> {
    let executions: Vec<Vec<usize>> =
      serde_json::from_str(&rows.to_string()).map_err(|e| e.to_string())?;
    let first = executions.first().ok_or("no root executions to size")?;
    if executions.iter().any(|rows| rows.len() != first.len()) {
      return Err("root executions have different circuit counts".into());
    }
    let maxima: Vec<_> = (0..first.len())
      .map(|i| executions.iter().map(|rows| rows[i]).max().unwrap_or(0))
      .collect();
    let (program, trace) = aggregate(&aggr_artifact)?;
    let plan = TracePlan::new(&program, trace)?;
    let backend =
      Backend::for_batch_verification(&plan, Parameters::default())?;
    let log_heights = backend.normalized_log_heights(
      &maxima,
      u8::try_from(headroom).map_err(|e| e.to_string())?,
    )?;
    let layout = FixedRoot::new(
      log_heights,
      backend.memory_circuits(),
      claim_len as usize,
    )
    .map_err(|e| e.to_string())?;
    Ok(layout.to_bytes())
  })();
  match result {
    Ok(layout) => LeanIOResult::ok(LeanByteArray::from_bytes(&layout)),
    Err(e) => LeanIOResult::error_string(&e),
  }
}

/// Wrap and prove the root in `layout`'s fixed shape.
#[unsafe(no_mangle)]
extern "C" fn rs_compression_normalize_root(
  aggr_artifact: LeanString<LeanBorrowed<'_>>,
  invocation: LeanByteArray<LeanBorrowed<'_>>,
  raw_proof: LeanByteArray<LeanBorrowed<'_>>,
  layout: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> Result<Vec<u8>, String> {
    let layout =
      FixedRoot::from_bytes(layout.as_bytes()).map_err(|e| e.to_string())?;
    let (program, trace) = aggregate(&aggr_artifact)?;
    let plan = TracePlan::new(&program, trace)?;
    let backend = Backend::for_batch(&plan, Parameters::default())?;
    let invocation = stark_verifier::Invocation::decode(invocation.as_bytes())?;
    let args = program.field().decode(&invocation.args)?;
    let proof_bytes = raw_proof.as_bytes();
    let proof = BatchProof::from_bytes(proof_bytes)
      .map_err(|e| format!("root proof decode failed: {e}"))?;
    if proof.to_bytes().map_err(|e| e.to_string())? != proof_bytes {
      return Err("noncanonical or trailing root proof bytes".into());
    }
    backend.verify_batch(&invocation.entry, &args, &[], &proof)?;
    let hints = stark_verifier::prepare(&program, &invocation.streams)?;
    let record = hints
      .execute(&invocation.entry, args.clone())
      .map_err(|e| e.to_string())?;
    if !record.output.is_empty() {
      return Err("verifier returned a non-unit value".into());
    }
    let (claim, normalized) = backend.prove_normalized(
      &invocation.entry,
      &args,
      &[],
      record,
      layout.log_heights(),
    )?;
    let expected = backend.claim(&invocation.entry, &args, &[])?;
    if claim != expected {
      return Err(
        "normalized root claim differs from expected outer claim".into(),
      );
    }
    normalized.to_bytes().map_err(|e| e.to_string())
  })();
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
  fixed_root: LeanByteArray<LeanBorrowed<'_>>,
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
