/-
  tracing-texray + streaming Lean API.

  The Rust prover emits `tracing` spans for each major Aiur proving stage
  (`aiur/execute`, `aiur/witness`, `aiur/prove`) and each STARK proving
  stage (`stark/...`). After `init` installs the subscriber:
    * a one-line `[texray] <span>: <dur>  ── RAM Δ +X peak Y` is streamed
      to stderr as each tracked span closes (when `streaming = true`),
      followed by a companion `[texray] <span> peak-rss-bytes=<N>
      (<X.YZ MiB>)` line carrying the raw peak in bytes for programmatic
      consumers (CI bench, grep);
    * the full texray graph prints when `aiur/prove` exits.
-/

module

public section

namespace TracingTexray

/-- Configuration for the tracing-texray subscriber. -/
structure Settings where
  /-- Comma-separated span-name prefixes to keep
      (default `"aiur/,stark/"`; empty string disables filtering). -/
  namePrefixes : String := "aiur/,stark/"
  /-- Sample VmRSS/VmHWM per span. Linux-only; zeros elsewhere. -/
  trackRam : Bool := true
  /-- Emit per-span `[texray] <name>: <dur>  ── RAM Δ +X peak Y` lines
      on stderr as each span closes. The texray graph prints either way
      when the examined root span exits. -/
  streaming : Bool := true

@[extern "rs_texray_init"]
private opaque initWith
  (namePrefixes : @& String)
  (trackRam : Bool)
  (streaming : Bool) : IO Unit

/-- Install the global tracing-texray subscriber with the given settings.
    Idempotent: subsequent calls are no-ops once installed. -/
def init (s : Settings := {}) : IO Unit :=
  initWith s.namePrefixes s.trackRam s.streaming

@[extern "rs_texray_start_sampler"]
private opaque startSamplerFFI (intervalMs : UInt64) : IO Unit

/-- Start the process-tree RSS sampler (idempotent). Unlike the per-span
    `/proc/self/status` reads, this sums RSS across this process and all its
    children, so [`peakTreeRssBytes`] captures memory resident in helper
    processes (e.g. a zkVM host's services). `intervalMs` is the sample period. -/
def startSampler (intervalMs : UInt64 := 50) : IO Unit :=
  startSamplerFFI intervalMs

@[extern "rs_texray_peak_tree_rss_bytes"]
private opaque peakTreeRssBytesFFI : IO UInt64

/-- Peak resident-set size in bytes across this process and its children. `0`
    until [`startSampler`] has run or on non-Linux platforms. -/
def peakTreeRssBytes : IO Nat := do
  return (← peakTreeRssBytesFFI).toNat

@[extern "rs_texray_reset_peak_tree_rss"]
private opaque resetPeakTreeRssFFI : IO Unit

/-- Reset the tree sampler's high-water mark, opening a new measurement
    window — use between benchmark items so each reports its own peak. -/
def resetPeakTreeRss : IO Unit := resetPeakTreeRssFFI

@[extern "rs_texray_json_sink"]
private opaque jsonSinkFFI (path : @& String) : IO Unit

/-- Direct the per-span timing sink to `path` (JSON Lines). Pair with `init`
    (streaming) so the examined `aiur/*` / `stark/*` spans are recorded. -/
def jsonSink (path : String) : IO Unit :=
  jsonSinkFFI path

end TracingTexray

end
