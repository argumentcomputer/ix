#!/usr/bin/env bash
# cli.sh IXCC OUT.tsv PROGRAMS [MODES] [PERROOT]
# Run from an IxCC directory. PROGRAMS lists "CLOSURE.ixe SIDECAR.json" per line.
# For each program and each --rc mode (default "off on auto"): `ixcc compile` on every
# sidecar root (and, when PERROOT=1, on each root alone), then `ixcc check-cert` on the
# certificate it emitted; wall time and peak RSS from /usr/bin/time, the stage times
# from --stats, output sizes and SHA-256 of the certificate and the object. With NOTC=1 both
# commands skip erased typing at ingress (--no-typecheck), which does not change their output.
set -u
X="$1"; OUT="$2"; LIST="$3"; MODES="${4:-off on auto}"; PERROOT="${5:-0}"
TMP=$(mktemp -d)
TC=(); [ "${NOTC:-0}" = 1 ] && TC=(--no-typecheck)
printf 'program\troot\tmode\texit\twall_s\trss_kb\tingress_ms\tproduce_ms\trun_ms\tcert_bytes\tobject_bytes\tcert_sha\tobject_sha\tpolicy\tcheck_exit\tcheck_wall_s\tcheck_rss_kb\tcheck_run_ms\terror\n' > "$OUT"
one() {
  local ixe=$1 eq=$2 root=$3 mode=$4
  local rootArgs=()
  [ "$root" = all ] || rootArgs=(--root "$root")
  /usr/bin/time -f "%e %M %x" -o "$TMP/t" timeout 900 "$X" compile "$ixe" --equations "$eq" "${rootArgs[@]}" \
    -o "$TMP/o" --rc "$mode" --emit-cert "$TMP/c" --stats "${TC[@]}" > "$TMP/out" 2> "$TMP/err"
  read -r wall rss ex < <(tail -1 "$TMP/t")
  local ing prod run certb objb csha osha pol err
  ing=$(sed -n 's/^time: .*ingress \([0-9]*\) ms.*/\1/p' "$TMP/out")
  prod=$(sed -n 's/^time: .*produce \([0-9]*\) ms.*/\1/p' "$TMP/out")
  run=$(sed -n 's/^time: .*run \([0-9]*\) ms.*/\1/p' "$TMP/out")
  pol=$(sed -n 's/^rc policy: \(.*\)/\1/p' "$TMP/out" | tr '\t' ' ')
  err=$(grep -v '^Command' "$TMP/err" | head -1 | cut -c1-200 | tr '\t' ' ')
  certb=; objb=; csha=; osha=; local cex= cwall= crss= crun=
  if [ "$ex" = 0 ]; then
    certb=$(stat -c %s "$TMP/c"); objb=$(stat -c %s "$TMP/o")
    csha=$(sha256sum "$TMP/c" | cut -c1-16); osha=$(sha256sum "$TMP/o" | cut -c1-16)
    /usr/bin/time -f "%e %M %x" -o "$TMP/t2" timeout 900 "$X" check-cert "$ixe" --equations "$eq" "${rootArgs[@]}" \
      --cert "$TMP/c" --stats "${TC[@]}" > "$TMP/out2" 2> "$TMP/err2"
    read -r cwall crss cex < <(tail -1 "$TMP/t2")
    crun=$(sed -n 's/^time: .*run \([0-9]*\) ms.*/\1/p' "$TMP/out2")
    rm -f "$TMP/c" "$TMP/o"
  fi
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$ixe" "$root" "$mode" "$ex" "$wall" "$rss" \
    "$ing" "$prod" "$run" "$certb" "$objb" "$csha" "$osha" "$pol" "$cex" "$cwall" "$crss" "$crun" "$err" >> "$OUT"
}
while read -r ixe eq; do
  [ -n "$ixe" ] || continue
  roots=(all)
  if [ "$PERROOT" = 1 ]; then
    mapfile -t named < <(jq -r '.roots[]?.name // empty' "$eq")
    [ "${#named[@]}" -gt 1 ] && roots+=("${named[@]}")
  fi
  for mode in $MODES; do
    for r in "${roots[@]}"; do one "$ixe" "$eq" "$r" "$mode"; done
  done
done < "$LIST"
rm -f "$TMP/t" "$TMP/t2" "$TMP/out" "$TMP/out2" "$TMP/err" "$TMP/err2"
rmdir "$TMP"
