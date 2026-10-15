mod outer;
mod saved;

/// Device bytes the recursive prover keeps resident per device unless
/// `IX_KZG_CUDA_RESIDENT_GIB` overrides it. Its traces are the largest
/// in the pipeline, so a wider reservation starves the constraint passes.
#[cfg(feature = "cuda")]
pub(super) const DEFAULT_CUDA_RESIDENT_BYTES: usize = 8 << 30;

pub(super) fn run(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
  let args = crate::pipeline::setup::take_development_flag(args);
  let args = &args[..];
  if args
    .first()
    .is_some_and(|s| matches!(s.as_str(), "native-verify" | "stage-and-prove"))
  {
    if args.len() != 3 {
      return Err("usage: ix-compression-worker wrap <native-verify|stage-and-prove> <saved-artifact-dir> <report-or-output-dir>".into());
    }
    let dir = std::path::Path::new(&args[2]);
    if args[0] == "stage-and-prove" {
      spawn_memory_monitor();
      std::fs::create_dir_all(dir)?;
      return saved::check(
        std::path::Path::new(&args[1]),
        &dir.join("circuit-report.json"),
        Some(dir),
      );
    }
    return saved::check(std::path::Path::new(&args[1]), dir, None);
  }
  Err(
    "usage: ix-compression-worker wrap <stage-and-prove|native-verify> ..."
      .into(),
  )
}

fn spawn_memory_monitor() {
  std::thread::spawn(|| {
    loop {
      std::thread::sleep(std::time::Duration::from_secs(30));
      if let Ok(status) = std::fs::read_to_string("/proc/self/status") {
        eprintln!(
          "{}",
          status
            .lines()
            .filter(|l| l.starts_with("VmRSS:") || l.starts_with("VmHWM:"))
            .collect::<Vec<_>>()
            .join(" ")
        );
      }
    }
  });
}

pub(super) use outer::verify_saved as verify;

pub(super) use outer::VerifierProfile;
