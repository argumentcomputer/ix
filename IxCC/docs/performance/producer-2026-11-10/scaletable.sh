#!/usr/bin/env bash
# scaletable.sh OUTDIR : the scaling medians as a markdown table, before and after side by side
set -u
O="$1"
bash "$(dirname "$0")/summarize.sh" "$O" 2>/dev/null | sed -n '/scaling medians/,$p' | awk '
  /^-- base/ {t = "b"; next} /^-- final/ {t = "f"; next} /^==/ {next}
  { split($0, c, "\t"); k = c[1]; sub(/^wall /, "", c[2]); sub(/^produce /, "", c[3]); sub(/^run /, "", c[4]); sub(/^check /, "", c[5]); sub(/^exit /, "", c[7])
    W[t, k] = c[2]; P[t, k] = c[3]; R[t, k] = c[4]; C[t, k] = c[5]; E[t, k] = c[7]; keys[k] = 1 }
  END {
    print "| Closure | Before: compile s (produce / re-run ms) | check-cert s | After: compile s (produce / re-run ms) | check-cert s |"
    print "| --- | ---: | ---: | ---: | ---: |"
    n = split("dag-12 dag-16 dag-20 tree-16 wide-16 deep-500 deep-1000 body-8 body-10 many-500 many-1000 many-2000 many-4000 fns-100 fns-200 fns-500 fns-1000 fns-2000 fns6-500 fns6-1000 fns6-2000 fns6-3000", order, " ")
    for (i = 1; i <= n; i++) { k = order[i]; if (!(k in keys)) continue
      split(k, nm, "-")
      b = (E["b", k] == 0 ? sprintf("%s (%s / %s)", W["b", k], P["b", k], R["b", k]) : sprintf("%s, refused", W["b", k]))
      f = (E["f", k] == 0 ? sprintf("%s (%s / %s)", W["f", k], P["f", k], R["f", k]) : sprintf("%s, refused", W["f", k]))
      printf "| `%s %s` | %s | %s | %s | %s |\n", nm[1], nm[2], b, C["b", k], f, C["f", k] } }'
