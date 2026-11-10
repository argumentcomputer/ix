#!/usr/bin/env bash
# compact.sh OUTDIR DEST : the raw tables of the record, compacted: identity.tsv, typed.tsv, scaling.tsv
set -u
O="$1"; D="$2"
printf 'build\tprogram\troot\tmode\texit\tcert_bytes\tobject_bytes\tcert_sha\tobject_sha\tproduce_ms\trun_ms\trefusal\n' > "$D/identity.tsv"
for b in base final; do
  awk -F'\t' -v b=$([ $b = base ] && echo before || echo after) 'FNR>1{printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", b, $1, $2, $3, $4, $10, $11, $12, $13, $8, $9, substr($19, 1, 120)}' "$O/notc-$b.tsv" >> "$D/identity.tsv"
done
printf 'build\tprogram\texit\tcompile_s\tcompile_rss_kb\tingress_ms\tproduce_ms\trun_ms\tcheck_s\tcheck_rss_kb\trefusal\n' > "$D/typed.tsv"
for b in base final; do
  awk -F'\t' -v b=$([ $b = base ] && echo before || echo after) 'FNR>1{printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", b, $1, $4, $5, $6, $7, $8, $9, $16, $17, substr($19, 1, 120)}' "$O/typed-$b.tsv" >> "$D/typed.tsv"
done
printf 'build\trep\tinput\texit\tcompile_s\tcompile_rss_kb\tingress_ms\tproduce_ms\trun_ms\tcert_bytes\tobject_bytes\tcheck_s\tcheck_rss_kb\trefusal\n' > "$D/scaling.tsv"
for f in "$O"/scale/*.tsv; do
  n=$(basename "$f" .tsv); b=${n%%.*}; r=${n#*.}
  awk -F'\t' -v b=$([ $b = base ] && echo before || echo after) -v r=$r 'FNR>1 && !($4==0 && $8==""){k=$1; n=split(k, a, "/"); k=a[n]; sub(/\.ixe$/, "", k); printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", b, r, k, $4, $5, $6, $7, $8, $9, $10, $11, $16, $17, substr($19, 1, 120)}' "$f" >> "$D/scaling.tsv"
done
wc -c "$D"/identity.tsv "$D"/typed.tsv "$D"/scaling.tsv
