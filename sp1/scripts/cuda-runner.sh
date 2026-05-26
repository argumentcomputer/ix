#!/usr/bin/env bash
# Cargo runner that works around an SP1 6.0.2 startup race in the CUDA prover:
#   - SDK spawns sp1-gpu-server and only retries socket connect for ~1s
#     (sp1-cuda-6.0.2/src/client.rs:148), but gpu-server's CUDA init can take
#     much longer; whether you win the race depends on driver warmth.
#   - SDK's _child handle is kill_on_drop(true), so on exit gpu-server gets
#     SIGKILLed without unlinking /tmp/sp1-cuda-{id}.sock; the next run finds
#     an orphaned socket and gets ConnectionRefused.
# We clean leftover state and retry on non-zero exit. Pass-through when not
# running under cuda — cargo invokes us for every binary.
set -uo pipefail

binary="$1"
shift

if [[ "${SP1_PROVER:-}" != "cuda" ]]; then
    exec "$binary" "$@"
fi

cleanup() {
    pkill -KILL -x sp1-gpu-server 2>/dev/null || true
    rm -f /tmp/sp1-cuda-*.sock
}

trap cleanup EXIT INT TERM

# When a prior gpu-server is SIGKILLed by SDK kill_on_drop, the NVIDIA driver
# can hold contexts for tens of seconds; subsequent gpu-server processes hang
# in cuInit and silently fail. Back off progressively so the driver has time
# to settle before the next attempt.
backoff_seconds() {
    case "$1" in
        1) echo 1 ;;
        2) echo 3 ;;
        3) echo 8 ;;
        *) echo 15 ;;
    esac
}

max_attempts=${SP1_CUDA_MAX_RETRIES:-5}
status=0
for attempt in $(seq 1 "$max_attempts"); do
    cleanup
    sleep "$(backoff_seconds "$attempt")"
    "$binary" "$@"
    status=$?
    if [[ $status -eq 0 ]]; then
        exit 0
    fi
    if [[ $attempt -lt $max_attempts ]]; then
        next_sleep=$(backoff_seconds "$((attempt + 1))")
        echo "[cuda-runner] attempt $attempt failed (exit $status); retrying in ${next_sleep}s..." >&2
    fi
done
echo "[cuda-runner] giving up after $max_attempts attempts" >&2
exit "$status"
