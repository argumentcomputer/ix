//! FFI shim for installing the `tracing-texray` subscriber from Lean.
//!
//! Cronos was driven by an explicit Lean-side `rsPrint` call. tracing-texray
//! dumps automatically when an `examine`'d span exits, so the only thing the
//! Lean side needs is a one-shot subscriber install.

use std::time::Duration;

use lean_ffi::object::{LeanIOResult, LeanOwned};
use tracing_subscriber::{
  Layer, Registry, filter::FilterFn, layer::SubscriberExt,
  util::SubscriberInitExt,
};

/// Default span-name prefixes that pass the filter — the logical phases
/// emitted by ix and multi-stark. Upstream Plonky3 spans (`fold_matrix`,
/// `build merkle tree`, etc.) don't match and never reach texray.
const DEFAULT_NAME_PREFIXES: &str = "aiur/,stark/";

/// Install the `tracing-texray` subscriber as the global default.
///
/// Idempotent: subsequent calls are no-ops once the global subscriber has
/// been set. Knobs (read once on first call):
/// - `TEXRAY_NAME_PREFIXES` — comma-separated list of span-name prefixes to
///   render. Default `"aiur/,stark/"`. Empty string disables the filter
///   (renders everything, including upstream library spans).
/// - `TEXRAY_MIN_DURATION_MS` — also hide spans shorter than this. Default
///   `0` (no duration filter). Composes with the name filter.
/// - `TEXRAY_RAM=0` — disable RAM tracking (default: on, Linux-only).
/// - `TEXRAY_WIDTH` — override auto-detected render width. By default
///   tracing-texray probes stdout, then stderr, then stdin for a TTY.
///
/// Once installed, every `aiur/prove` call emits the per-stage timeline
/// (and RAM block, if tracked) on stderr when it finishes.
#[unsafe(no_mangle)]
extern "C" fn rs_texray_init() -> LeanIOResult<LeanOwned> {
  let prefixes_raw = std::env::var("TEXRAY_NAME_PREFIXES")
    .unwrap_or_else(|_| DEFAULT_NAME_PREFIXES.to_string());
  let prefixes: Vec<String> = prefixes_raw
    .split(',')
    .map(|s| s.trim().to_string())
    .filter(|s| !s.is_empty())
    .collect();

  let min_ms = std::env::var("TEXRAY_MIN_DURATION_MS")
    .ok()
    .and_then(|s| s.parse::<u64>().ok())
    .unwrap_or(0);
  let track_ram = std::env::var("TEXRAY_RAM")
    .ok()
    .map(|s| !matches!(s.as_str(), "0" | "false" | ""))
    .unwrap_or(true);
  let width_override = std::env::var("TEXRAY_WIDTH")
    .ok()
    .and_then(|s| s.parse::<usize>().ok());

  let mut layer = tracing_texray::TeXRayLayer::new();
  if let Some(w) = width_override {
    layer = layer.width(w);
  }
  if track_ram {
    layer = layer.track_ram();
  }
  if min_ms > 0 {
    layer = layer.min_duration(Duration::from_millis(min_ms));
  }

  let filter = FilterFn::new(move |metadata| {
    // Always let events through — only filter spans by name.
    if !metadata.is_span() || prefixes.is_empty() {
      return true;
    }
    let name = metadata.name();
    prefixes.iter().any(|p| name.starts_with(p.as_str()))
  });

  let _ = Registry::default().with(layer.with_filter(filter)).try_init();
  LeanIOResult::ok(LeanOwned::box_usize(0))
}
