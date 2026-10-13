//! Optional Linux userspace CPU sampling for the two benchmark harnesses.
//! Set AIUR_CPU_PROFILE to an output directory and preload libprofiler.so.0.
//! Each guard covers execution alone; setup, warmups, counts, and record drops
//! stay outside the profile. No profiler dependency is linked into the runtime.
use std::{error::Error, ffi::CString, path::PathBuf};

type Start = unsafe extern "C" fn(*const std::ffi::c_char) -> std::ffi::c_int;
type Stop = unsafe extern "C" fn();

pub struct Profiler {
  directory: PathBuf,
  start: Start,
  stop: Stop,
}

pub struct Guard<'a>(&'a Profiler);

impl Profiler {
  pub fn from_env() -> Result<Option<Self>, Box<dyn Error>> {
    let Some(directory) = std::env::var_os("AIUR_CPU_PROFILE") else {
      return Ok(None);
    };
    #[cfg(not(target_os = "linux"))]
    {
      let _ = directory;
      Err("CPU profiling is supported on Linux only".into())
    }
    #[cfg(target_os = "linux")]
    {
      #[link(name = "dl")]
      unsafe extern "C" {
        fn dlsym(
          handle: *mut std::ffi::c_void,
          symbol: *const std::ffi::c_char,
        ) -> *mut std::ffi::c_void;
      }
      // RTLD_DEFAULT resolves symbols from the preloaded profiler. Its
      // documented C API has these signatures and remains loaded for
      // the process lifetime. Fail instead of profiling the wrong scope.
      let (start, stop) = unsafe {
        let start = dlsym(std::ptr::null_mut(), c"ProfilerStart".as_ptr());
        let stop = dlsym(std::ptr::null_mut(), c"ProfilerStop".as_ptr());
        if start.is_null() || stop.is_null() {
          return Err(
            "preload libprofiler.so.0 to enable AIUR_CPU_PROFILE".into(),
          );
        }
        (
          std::mem::transmute::<*mut std::ffi::c_void, Start>(start),
          std::mem::transmute::<*mut std::ffi::c_void, Stop>(stop),
        )
      };
      let directory = PathBuf::from(directory);
      std::fs::create_dir_all(&directory)?;
      Ok(Some(Self { directory, start, stop }))
    }
  }

  pub fn start(
    &self,
    engine: &str,
    sample: usize,
  ) -> Result<Guard<'_>, Box<dyn Error>> {
    let path = self.directory.join(format!("{engine}-{sample:03}.prof"));
    let name = CString::new(path.to_str().ok_or("profile path is not UTF-8")?)?;
    if unsafe { (self.start)(name.as_ptr()) } == 0 {
      return Err(
        format!("failed to start CPU profile at {}", path.display()).into(),
      );
    }
    Ok(Guard(self))
  }
}

impl Drop for Guard<'_> {
  fn drop(&mut self) {
    unsafe { (self.0.stop)() }
  }
}
