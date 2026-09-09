use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

fn host() -> Memory {
  Memory {
    capacity: 500 * GIB,
    available: 480 * GIB,
    rss: 20 * GIB,
    swap: 0,
    stall_us: 0,
    stall_avg10_bp: 0,
    cgroup: None,
  }
}

#[test]
fn cgroup_headroom_subtracts_current_and_reserves_capacity() {
  let mut memory = host();
  memory.constrain(60 * GIB, 420 * GIB);
  assert_eq!(memory.available, 360 * GIB);
  assert_eq!(memory.capacity, 420 * GIB);
  assert_eq!(memory.budget(), 276 * GIB);
  memory.constrain(170 * GIB, 200 * GIB);
  assert_eq!(memory.available, 30 * GIB);
  assert_eq!(memory.budget(), 0);
  assert_eq!(memory.cgroup, Some((170 * GIB, 200 * GIB)));
}

#[test]
fn host_pressure_and_over_limit_charges_never_wrap() {
  let mut memory = Memory { available: 10 * GIB, ..host() };
  memory.constrain(20 * GIB, 420 * GIB);
  assert_eq!(memory.available, 10 * GIB);
  memory.constrain(421 * GIB, 420 * GIB);
  assert_eq!(memory.available, 0);
  memory.constrain(1, 0);
  assert_eq!(memory.capacity, 0);
  assert_eq!(memory.budget(), 0);
}

#[test]
fn cgroup_paths_include_ancestors_and_namespace_root() {
  let mount = "30 20 0:25 / /sys/fs/cgroup rw - cgroup2 cgroup rw";
  assert_eq!(
    cgroup_dirs("0::/a/b\n", mount).unwrap(),
    vec![
      PathBuf::from("/sys/fs/cgroup/a/b"),
      PathBuf::from("/sys/fs/cgroup/a"),
      PathBuf::from("/sys/fs/cgroup")
    ]
  );
  let namespaced =
    "30 20 0:25 /host/container /cg\\040mount rw - cgroup2 cgroup rw";
  assert_eq!(
    cgroup_dirs("0::/\n", namespaced).unwrap(),
    vec![PathBuf::from("/cg mount")]
  );
  assert_eq!(
    cgroup_dirs("0::/host/container/child\n", namespaced).unwrap(),
    vec![PathBuf::from("/cg mount/child"), PathBuf::from("/cg mount")]
  );
  for group in ["0::/../../escape", "0::relative", "1:memory:/old"] {
    assert!(cgroup_dirs(group, mount).is_err());
  }
  assert!(cgroup_dirs("0::/a", "bad mountinfo").is_err());
}

static NEXT_DIR: AtomicUsize = AtomicUsize::new(0);
struct TempDir(PathBuf);
impl TempDir {
  fn new() -> Self {
    let path = std::env::temp_dir().join(format!(
      "ix-memory-test-{}-{}",
      std::process::id(),
      NEXT_DIR.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).unwrap();
    Self(path)
  }
}
impl Drop for TempDir {
  fn drop(&mut self) {
    fs::remove_dir_all(&self.0).unwrap();
  }
}

#[test]
fn unlimited_child_still_obeys_parent_and_live_high_changes() {
  let dir = TempDir::new();
  let child = dir.0.join("child");
  fs::create_dir(&child).unwrap();
  for path in [&dir.0, &child] {
    fs::write(path.join("memory.max"), "max\n").unwrap();
    fs::write(path.join("memory.high"), "max\n").unwrap();
  }
  fs::write(dir.0.join("memory.current"), (100 * GIB).to_string()).unwrap();
  fs::write(dir.0.join("memory.max"), (420 * GIB).to_string()).unwrap();
  let reader = MemoryReader { cgroups: vec![child.clone(), dir.0.clone()] };
  let mut memory = host();
  reader.constrain(&mut memory).unwrap();
  assert_eq!(memory.available, 320 * GIB);
  // The child's previously unlimited high limit changes during execution.
  fs::write(child.join("memory.high"), (50 * GIB).to_string()).unwrap();
  fs::write(child.join("memory.current"), (30 * GIB).to_string()).unwrap();
  let mut memory = host();
  reader.constrain(&mut memory).unwrap();
  assert_eq!(memory.available, 20 * GIB);
  assert_eq!(memory.capacity, 50 * GIB);
  assert_eq!(memory.cgroup, Some((30 * GIB, 50 * GIB)));
  fs::remove_file(child.join("memory.current")).unwrap();
  assert!(reader.constrain(&mut host()).is_err());
  fs::write(child.join("memory.current"), "not a number").unwrap();
  assert!(reader.constrain(&mut host()).is_err());
  fs::write(child.join("memory.high"), "not a limit").unwrap();
  assert!(reader.constrain(&mut host()).is_err());
}

#[test]
fn missing_telemetry_does_not_become_an_unlimited_group() {
  let dir = TempDir::new();
  let reader = MemoryReader { cgroups: vec![dir.0.join("missing")] };
  assert!(reader.constrain(&mut host()).is_err());
  assert_eq!(field("VmRSS: 123 kB\n", "VmRSS:").unwrap(), 123);
  assert!(field("VmRSS: nope\n", "VmRSS:").is_err());
}

#[test]
fn psi_reads_full_stalls_and_fixed_point_trend_without_silent_bad_values() {
  assert_eq!(
    psi_full("some avg10=99.00 total=777\nfull avg10=2.50 avg60=1.00 avg300=0.00 total=12345\n")
      .unwrap(),
    (12345, 250)
  );
  assert_eq!(psi_full("full avg10=100.00 total=0").unwrap(), (0, 10_000));
  for text in [
    "some avg10=0.00 total=0",
    "full total=0",
    "full avg10=0.00 total=bad",
    "full avg10=NaN total=0",
    "full avg10=inf total=0",
    "full avg10=-1.00 total=0",
    "full avg10=0.+1 total=0",
    "full avg10=1.001 total=0",
    "full avg10=100.01 total=0",
    "full avg10=18446744073709551615.00 total=0",
  ] {
    assert!(psi_full(text).is_err(), "accepted {text}");
  }
  let dir = TempDir::new();
  let path = dir.0.join("memory.pressure");
  assert_eq!(optional_pressure(&path).unwrap(), (0, 0));
  assert_eq!(
    pressure_result(&path, Err(std::io::ErrorKind::Unsupported.into()))
      .unwrap(),
    (0, 0)
  );
  for kind in [std::io::ErrorKind::PermissionDenied, std::io::ErrorKind::Other]
  {
    assert!(pressure_result(&path, Err(kind.into())).is_err());
  }
  fs::write(&path, "broken telemetry").unwrap();
  assert!(optional_pressure(&path).is_err());
  // Read errors other than an absent optional file must also fail closed.
  assert!(optional_pressure(&dir.0).is_err());
}

#[test]
#[ignore = "prints live process memory constraints for external cgroup smoke tests"]
fn live_memory_probe() {
  let memory = MemoryReader::new().unwrap().unwrap().read().unwrap();
  eprintln!("[ixvm_memory_probe] {memory:?}; budget={}", memory.budget());
  if let Ok(expected) = std::env::var("IX_TEST_MEMORY_MAX_BYTES") {
    assert_eq!(memory.capacity, expected.parse::<u64>().unwrap());
    assert!(memory.available <= memory.capacity);
    assert!(memory.cgroup.is_some());
  }
}
