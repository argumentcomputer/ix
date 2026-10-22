use std::{fs, process::Command};

fn worker(texray: bool) -> Command {
  let mut command = Command::new(env!("CARGO_BIN_EXE_ix-compression-worker"));
  command
    .env("IX_TEXRAY", if texray { "1" } else { "0" })
    .env_remove("IX_KZG_FILECOIN_CACHE")
    .env_remove("IX_KZG_FILECOIN_MANIFEST")
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
