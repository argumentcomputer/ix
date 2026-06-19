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

end TracingTexray

end
