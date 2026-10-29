//! Exercise the complete role binding emitted by the Lean generator.
//! The caller supplies a retained generator artifact through IX_ROLE_ARTIFACT.

use ix_kernel::anon_work::build_artifact_work;
use ix_kernel::artifact_checker::ArtifactChecker;
use ix_kernel::mode::Anon;
use ix_kernel::role_admission::ArtifactSource;
use ixon::env::Env;
use ixon::role_table::Role;

#[test]
#[ignore = "requires IX_ROLE_ARTIFACT from the validated Lean generator"]
fn generated_artifact_admits_every_role_and_checks_every_carried_unit() {
  std::thread::Builder::new()
    .stack_size(256 * 1024 * 1024)
    .spawn(check_generated_artifact)
    .unwrap()
    .join()
    .unwrap();
}

fn check_generated_artifact() {
  let path = std::env::var("IX_ROLE_ARTIFACT")
    .expect("IX_ROLE_ARTIFACT must name a generated all-role artifact");
  let bytes = std::fs::read(&path).expect("read generated role artifact");
  let mut input = bytes.as_slice();
  let env = Env::get(&mut input).expect("decode generated role artifact");
  assert!(input.is_empty(), "trailing artifact bytes");
  let source =
    ArtifactSource::prepare(env).expect("authenticate role artifact");
  let started = std::time::Instant::now();
  let admission = source.admission();
  for (role, reason) in admission.refused() {
    eprintln!("{} refused: {reason}", role.lean_name());
  }
  eprintln!(
    "admitted {} roles in {:?}",
    admission.admitted_count(),
    started.elapsed()
  );
  assert!(admission.refused().is_empty());
  assert_eq!(admission.admitted_count(), Role::ALL.len());
  for role in Role::ALL {
    assert!(source.is_admitted(role), "{} is not admitted", role.lean_name());
  }
  let work =
    build_artifact_work(&source).expect("exact authenticated unit coverage");
  let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source));
  let mut failures = Vec::new();
  for item in &work {
    if let Err(error) = checker.check_work(item) {
      failures.push((item.primary().hex(), error.to_string()));
    }
  }
  eprintln!("checked {} units in {:?}", work.len(), started.elapsed());
  assert!(failures.is_empty(), "{failures:?}");
}
