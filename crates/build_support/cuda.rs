use std::{
  env,
  path::{Path, PathBuf},
  process::Command,
};

pub(crate) fn nvcc_path() -> std::ffi::OsString {
  if let Some(nvcc) = env::var_os("NVCC") {
    return nvcc;
  }
  if let Some(root) =
    env::var_os("CUDA_HOME").or_else(|| env::var_os("CUDA_PATH"))
  {
    let candidate = PathBuf::from(root).join("bin/nvcc");
    if candidate.is_file() {
      return candidate.into_os_string();
    }
  }
  "nvcc".into()
}

pub(crate) fn architectures(
  nvcc: &std::ffi::OsStr,
  variables: &[&str],
) -> Vec<String> {
  let supported = supported_architectures(nvcc);
  let configured = variables
    .iter()
    .find_map(|name| env::var(name).ok())
    .or_else(detect_nvidia_architectures)
    .unwrap_or_else(|| {
      panic!("no NVIDIA GPU detected; set {}", variables.join(" or "))
    });
  let architectures: Vec<_> = configured
    .split(',')
    .map(str::trim)
    .filter(|architecture| !architecture.is_empty())
    .map(|architecture| {
      assert!(
        (2..=3).contains(&architecture.len())
          && architecture.chars().all(|character| character.is_ascii_digit()),
        "invalid CUDA architecture {architecture:?}; expected comma-separated numbers such as 80,90"
      );
      assert!(
        supported.is_empty()
          || supported.iter().any(|item| item == architecture),
        "nvcc does not support CUDA architecture sm_{architecture}"
      );
      architecture.to_owned()
    })
    .collect();
  assert!(
    !architectures.is_empty(),
    "CUDA architecture selection must contain at least one architecture"
  );
  architectures
}

fn supported_architectures(nvcc: &std::ffi::OsStr) -> Vec<String> {
  let Ok(output) = Command::new(nvcc).arg("--list-gpu-code").output() else {
    return Vec::new();
  };
  if !output.status.success() {
    return Vec::new();
  }
  String::from_utf8_lossy(&output.stdout)
    .split_whitespace()
    .filter_map(|code| code.strip_prefix("sm_"))
    .filter(|code| code.chars().all(|character| character.is_ascii_digit()))
    .map(str::to_owned)
    .collect()
}

fn detect_nvidia_architectures() -> Option<String> {
  let output = Command::new("nvidia-smi")
    .args(["--query-gpu=compute_cap", "--format=csv,noheader"])
    .output()
    .ok()?;
  if !output.status.success() {
    return None;
  }
  let capabilities = String::from_utf8(output.stdout).ok()?;
  let mut architectures: Vec<String> = capabilities
    .lines()
    .map(|capability| {
      capability
        .chars()
        .filter(|character| character.is_ascii_digit())
        .collect()
    })
    .filter(|architecture: &String| !architecture.is_empty())
    .collect();
  architectures.sort_unstable();
  architectures.dedup();
  (!architectures.is_empty()).then(|| architectures.join(","))
}

pub(crate) fn cuda_library_directories(nvcc: &std::ffi::OsStr) -> Vec<PathBuf> {
  let root = env::var_os("CUDA_HOME")
    .or_else(|| env::var_os("CUDA_PATH"))
    .map(PathBuf::from)
    .or_else(|| {
      let nvcc = Path::new(nvcc);
      nvcc
        .is_absolute()
        .then(|| nvcc.parent()?.parent().map(Path::to_path_buf))
        .flatten()
    })
    .unwrap_or_else(|| PathBuf::from("/usr/local/cuda"));
  vec![root.join("lib64"), root.join("targets/x86_64-linux/lib")]
}
