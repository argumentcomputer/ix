use super::init_claim;
use crate::recursive::native_curve;
mod outer;
mod saved;

/// Device bytes the recursive prover keeps resident per device unless
/// `IX_KZG_CUDA_RESIDENT_GIB` overrides it. Its traces are the largest
/// in the pipeline, so a wider reservation starves the constraint passes.
#[cfg(feature = "cuda")]
pub(super) const DEFAULT_CUDA_RESIDENT_BYTES: usize = 8 << 30;

pub(super) fn run(args: &[String]) -> Result<(), Box<dyn std::error::Error>> {
  if args.first().is_some_and(|s| {
    matches!(s.as_str(), "native-verify" | "stage" | "stage-and-prove")
  }) {
    if args.len() != 3 {
      return Err("usage: init-kzg-wrap <native-verify|stage|stage-and-prove> <saved-artifact-dir> <report-or-output-dir>".into());
    }
    let dir = std::path::Path::new(&args[2]);
    if args[0] != "native-verify" {
      std::fs::create_dir_all(dir)?;
      return saved::check(
        std::path::Path::new(&args[1]),
        &dir.join("circuit-report.json"),
        Some(dir),
        args[0] == "stage-and-prove",
      );
    }
    return saved::check(std::path::Path::new(&args[1]), dir, None, false);
  }
  if args.first().is_some_and(|s| s == "prove" || s == "verify") {
    let resident = args.get(2).is_some_and(|arg| arg == "--resident");
    if !(2..=3).contains(&args.len())
      || (args.len() == 3 && (!resident || args[0] != "prove"))
    {
      return Err(
                "usage: init-kzg-wrap prove <staged-dir> [--resident] | verify <staged-dir>".into(),
            );
    }
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
    return outer::prove(
      std::path::Path::new(&args[1]),
      args[0] == "verify",
      resident,
    );
  }
  if let Some(operation) = args.first().filter(|_| args.len() == 1)
    && matches!(
      operation.as_str(),
      "native-add" | "native-double" | "native-subgroup"
    )
  {
    println!("{}", native_curve::measure(operation)?);
    return Ok(());
  }
  Err("usage: init-kzg-wrap <stage|stage-and-prove|native-verify|prove|verify> ...".into())
}

pub(super) use outer::verify_saved as verify;

pub(super) use outer::VerifierProfile;
