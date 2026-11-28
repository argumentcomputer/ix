#!/usr/bin/env bash
# summarize.sh OUTDIR : identity of the producer's output before and after (notc-base.tsv against
# notc-final.tsv), the slowest compiles (typed-*.tsv) and the scaling medians (scale/*.tsv).
set -u
O="$1"
echo "== identity (program, root, mode): exit status, certificate and object SHA-256, refusal message"
awk -F'\t' 'FNR==1{next} FILENAME~/notc-base/{k=$1"|"$2"|"$3; b[k]=$4"|"$12"|"$13"|"$19; next}
  {k=$1"|"$2"|"$3; n++; if(!(k in b)){miss++; print "only after: " k; next}
   if(b[k]==$4"|"$12"|"$13"|"$19){same++; if($4==0) ok++; else refused++} else {diff++; print "DIFFERS: " k " before " b[k] " after " $4"|"$12"|"$13"|"$19}}
  END{printf "%d runs compared: %d identical (%d compiled, %d refused alike), %d differ, %d missing before\n", n, same, ok, refused, diff, miss}' \
  "$O/notc-base.tsv" "$O/notc-final.tsv"
echo "== slowest compiles, typed, --rc off, every root (wall s, ingress/produce/run ms, check-cert wall s)"
for t in base final; do
  echo "-- $t"
  awk -F'\t' 'FNR>1{printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n", $5, $1, $7, $8, $9, $16, $4}' "$O/typed-$t.tsv" | sort -g -r | head -12
done
echo "== scaling medians (compile wall s, produce ms, run ms, check-cert wall s, peak RSS KB)"
for t in base final; do
  echo "-- $t"
  awk -F'\t' 'FNR>1{k=$1; n=split(k, a, "/"); k=a[n]; sub(/\.ixe$/, "", k); w[k]=w[k]" "$5; p[k]=p[k]" "$8; r[k]=r[k]" "$9; c[k]=c[k]" "$16; m[k]=m[k]" "$6; e[k]=$4}
    function med(s,   a, n, i, j, t) { n = split(s, a, " "); for (i = 1; i <= n; i++) for (j = i + 1; j <= n; j++) if (a[j] + 0 < a[i] + 0) { t = a[i]; a[i] = a[j]; a[j] = t }; return n ? a[int((n + 1) / 2)] : "" }
    END{for (k in w) printf "%s\twall %s\tproduce %s\trun %s\tcheck %s\trss %s\texit %s\t(%d runs)\n", k, med(w[k]), med(p[k]), med(r[k]), med(c[k]), med(m[k]), e[k], split(w[k], z, " ")}' \
    "$O"/scale/$t.*.tsv | sort
done
