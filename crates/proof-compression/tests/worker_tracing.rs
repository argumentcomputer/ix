use std::{fs, process::Command};

fn worker(texray: bool) -> Command {
  let mut command = Command::new(env!("CARGO_BIN_EXE_ix-compression-worker"));
  command
    .env("IX_TEXRAY", if texray { "1" } else { "0" })
    .env_remove("IX_KZG_FILECOIN_CACHE")
    .env_remove("IX_KZG_FILECOIN_MANIFEST")
    .env_remove("IX_KZG_IGNITION_CACHE")
    .env_remove("IX_KZG_IGNITION_CACHE_BLAKE3")
    .env_remove("IX_KZG_IGNITION_ADMISSION")
    .env_remove("IX_KZG_IGNITION_ADMISSION_BLAKE3")
    .env_remove("IX_KZG_PREFETCH_GIB");
  command
}

#[test]
fn worker_traces_early_failures_and_keeps_stdout_machine_readable() {
  let directory = std::env::temp_dir()
    .join(format!("ix-worker-tracing-{}", std::process::id()));
  fs::create_dir(&directory).unwrap();
  for enabled in [false, true] {
    let output =
      worker(enabled).args(["fri", "capabilities"]).output().unwrap();
    assert!(output.status.success());
    let capabilities: serde_json::Value =
      serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(capabilities["binary"], "ix-compression-worker");
    assert_eq!(capabilities["curve"], ix_proof_compression::kzg::curve::NAME);
    assert_eq!(capabilities["development_setup_only"], false);
    assert_eq!(capabilities["ignition_setup"], cfg!(feature = "bn254"));
    assert_eq!(
      String::from_utf8_lossy(&output.stderr)
        .contains("[texray] compression/fri:"),
      enabled
    );
    for (stage, args) in [
      ("fri", vec!["fri", "missing", "fri-out", "--native-only"]),
      ("kzg", vec!["kzg", "run", "missing", "kzg-out", "24", "--dev-srs"]),
      (
        "wrap",
        vec!["wrap", "native-verify", "missing", "report.json", "--dev-srs"],
      ),
    ] {
      let output =
        worker(enabled).args(args).current_dir(&directory).output().unwrap();
      assert!(!output.status.success());
      let stderr = String::from_utf8_lossy(&output.stderr);
      assert_eq!(
        stderr.contains(&format!("[texray] compression/{stage}:")),
        enabled,
        "{stderr}"
      );
      assert_eq!(
        stderr.contains("[texray] compression/load_input:"),
        enabled,
        "{stderr}"
      );
    }
  }
  fs::remove_dir_all(directory).unwrap();
}

#[test]
fn worker_pipeline_requires_an_explicit_vk_digest_before_io() {
  let output = worker(false)
    .args([
      "pipeline",
      "verify",
      "missing-proof",
      "missing-claim",
      "missing-claims",
      "missing-vk",
      "not-a-digest",
      "--dev-srs",
    ])
    .output()
    .unwrap();
  assert!(!output.status.success());
  assert!(
    String::from_utf8_lossy(&output.stderr)
      .contains("64 hexadecimal characters")
  );
}

#[cfg(feature = "bn254")]
#[test]
fn ignition_verification_requires_both_pins_and_refuses_development_mode() {
  let pin = "00".repeat(32);
  let args = [
    "pipeline",
    "verify-ignition",
    "missing-proof",
    "missing-claim",
    "missing-claims",
    "missing-vk",
    pin.as_str(),
    "missing-admission",
  ];
  let output = worker(false).args(args).arg("not-a-digest").output().unwrap();
  assert!(!output.status.success());
  assert!(
    String::from_utf8_lossy(&output.stderr)
      .contains("64 hexadecimal characters")
  );
  let output =
    worker(false).args(args).arg(&pin).arg("--dev-srs").output().unwrap();
  assert!(!output.status.success());
  assert!(
    String::from_utf8_lossy(&output.stderr)
      .contains("does not accept --dev-srs")
  );
}
