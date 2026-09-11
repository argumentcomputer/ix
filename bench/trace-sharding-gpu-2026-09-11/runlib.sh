# Shared helpers for the GPU run queues. The watchdog and sampler watch the
# prover process itself (the child of /usr/bin/time), not the timer.
watchdog() { local PID=$1 LOG=$2; while kill -0 $PID 2>/dev/null; do RSS=$(awk '/VmRSS/{print $2}' /proc/$PID/status 2>/dev/null); [ -n "$RSS" ] && [ "$RSS" -gt 225000000 ] && { echo "WATCHDOG KILL rss=$RSS" >> $LOG; kill -9 $PID; }; sleep 2; done; }
sampler() { local PID=$1 OUT=$2; while kill -0 $PID 2>/dev/null; do echo "$(date +%s) gpu=$(nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv,noheader,nounits | tr -d ' ') rss_kib=$(awk '/VmRSS/{print $2}' /proc/$PID/status 2>/dev/null)"; sleep 1; done > $OUT; }
# run TAG BIN ARGS...: prove under time -v with the child watched.
run() { local tag=$1 bin=$2; shift 2
  echo "=== $tag $(date)"
  env AIUR_TRACE_ONLY_LOOKUPS=1 AIUR_MAX_PIECE_LOG_HEIGHT=24 /usr/bin/time -v $bin "$@" > init-gpu-$tag.log 2>&1 &
  local TPID=$!; sleep 2; local PID=$(pgrep -P $TPID | head -1); [ -z "$PID" ] && PID=$TPID
  sampler $PID init-gpu-$tag-util.log & local S=$!; watchdog $PID init-gpu-$tag.log; wait $TPID; wait $S
  grep -E "Elapsed|Maximum resident|WATCHDOG|panicked|record budget" init-gpu-$tag.log
  local A=$(grep -oE "^[0-9a-f]{64}$" init-gpu-$tag.log | head -1); echo "$tag proof $A"
  [ -n "$A" ] && $bin verify --ixe init.ixe --ixes init-1.ixes $A 2>&1 | tail -1
}
