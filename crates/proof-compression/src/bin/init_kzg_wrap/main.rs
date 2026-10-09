#[path = "../support/init_claim.rs"]
mod init_claim;
use ix_proof_compression::recursive::native_curve;
use ix_proof_compression::recursive::native_verifier;
mod outer;
mod saved;

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if args.first().is_some_and(|s| s == "native-verify" || s == "stage") {
    if args.len() != 3 {
      return Err("usage: init-kzg-wrap <native-verify|stage> <saved-artifact-dir> <report-or-output-dir>".into());
    }
    let dir = std::path::Path::new(&args[2]);
    if args[0] == "stage" {
      std::fs::create_dir_all(dir)?;
      return saved::check(
        std::path::Path::new(&args[1]),
        &dir.join("circuit-report.json"),
        Some(dir),
      );
    }
    return saved::check(std::path::Path::new(&args[1]), dir, None);
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
  Err("usage: init-kzg-wrap <stage|native-verify|prove|verify> ...".into())
}
