//! FFI shim for installing the `tracing-texray` subscriber from Lean.
//!
//! With `streaming = true`, each tracked span (e.g. `aiur/execute`,
//! `aiur/witness`, `aiur/prove`) emits a one-line `[texray] <name>: <dur>
//!   ── RAM Δ +X peak Y` to stderr as it closes, followed by a companion
//! `[texray] <name> peak-rss-bytes=<N> (<X.YZ MiB>)` line (raw bytes for
//! CI/grep). The full texray graph prints when the examined root span
//! exits.

use lean_ffi::object::{LeanBorrowed, LeanIOResult, LeanOwned, LeanString};
use tracing_subscriber::{
  Layer, Registry, filter::FilterFn, layer::SubscriberExt,
  util::SubscriberInitExt,
};

/// Install the `tracing-texray` subscriber as the global default.
///
/// Idempotent: subsequent calls are no-ops once the global subscriber has
/// been set.
///
/// Parameters:
/// - `name_prefixes`: comma-separated list of span-name prefixes to render
///   (e.g. `"aiur/,stark/"`). Empty string disables filtering and renders
///   everything, including upstream library spans.
/// - `track_ram`: sample VmRSS/VmHWM per span. Linux-only; zeros elsewhere.
/// - `streaming`: emit per-span `[texray] <name>: <dur>  ── RAM Δ +X peak Y`
///   plus a `[texray] <name> peak-rss-bytes=<N> (<X.YZ MiB>)` companion on
///   stderr as each span closes. The texray graph prints either way when
///   the examined root span exits.
#[unsafe(no_mangle)]
extern "C" fn rs_texray_init(
  name_prefixes: LeanString<LeanBorrowed<'_>>,
  track_ram: bool,
  streaming: bool,
) -> LeanIOResult<LeanOwned> {
  let prefixes: Vec<String> = name_prefixes
    .to_string()
    .split(',')
    .map(|s| s.trim().to_string())
    .filter(|s| !s.is_empty())
    .collect();

  let mut layer = tracing_texray::TeXRayLayer::new();
  if track_ram {
    layer = layer.track_ram();
  }
  if streaming {
    layer = layer.streaming();
  }

  let filter = FilterFn::new(move |metadata| {
    if !metadata.is_span() || prefixes.is_empty() {
      return true;
    }
    let name = metadata.name();
    prefixes.iter().any(|p| name.starts_with(p.as_str()))
  });

  let _ = Registry::default().with(layer.with_filter(filter)).try_init();
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

/// Start tracing-texray's process-tree RSS sampler (idempotent). `interval_ms`
/// is the sampling period in milliseconds. Runs on a background daemon thread;
/// [`rs_texray_peak_tree_rss_bytes`] reads back the high-water mark. Captures
/// child-process memory (e.g. a zkVM host's helper processes) that a bare
/// `/proc/self/status` read misses.
#[unsafe(no_mangle)]
extern "C" fn rs_texray_start_sampler(
  interval_ms: u64,
) -> LeanIOResult<LeanOwned> {
  tracing_texray::rss_sampler::start(std::time::Duration::from_millis(
    interval_ms,
  ));
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

/// Peak resident-set size (bytes) across this process and its children per the
/// tree sampler. `0` until [`rs_texray_start_sampler`] has run or off Linux.
#[unsafe(no_mangle)]
extern "C" fn rs_texray_peak_tree_rss_bytes() -> LeanIOResult<LeanOwned> {
  let bytes = tracing_texray::rss_sampler::peak_tree_rss_bytes();
  LeanIOResult::ok(LeanOwned::box_u64(bytes))
}

/// Direct tracing-texray's per-span timing sink to `path` (one
/// `{"span","seconds"}` JSON line per closed examined span). Combine with a
/// `streaming`/examined subscriber so the prover's `aiur/*` + `stark/*` spans
/// are recorded for the CI drill-down.
#[unsafe(no_mangle)]
extern "C" fn rs_texray_json_sink(
  path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let _ = tracing_texray::json_sink::to_file(&path.to_string());
  LeanIOResult::ok(LeanOwned::box_usize(0))
}
