#!/usr/bin/env bash
# Commit citations: every token of 7 to 40 hex digits that names a commit of the local object
# store (or a known one missing from it), with its file, line and reachability (main: survives
# the branch's squash; branch-history: only this branch's own history, which a squash removes;
# off-branch: neither; not-in-store). Output: TSV (file, line, token, reachability).
#
#   IxCC/tools/citations.sh            tracked text files under IxCC/ (plans excluded) and the
#                                      root files this branch added or changed against origin/main
#   IxCC/tools/citations.sh --fixtures what regenerate.sh --check must keep clean: the fixtures,
#                                      their manifests and READMEs and the generated modules, for
#                                      commits other than those on main, and for absolute paths
#                                      (/home, /nix/store, /tmp). Not scanned: the vendored Aiur
#                                      reference fixtures (fixtures/aiur-*), described where
#                                      they live.
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
known_missing="fc058f935 a8c4d2d2"
if [ "${1:-}" = --fixtures ]; then
  paths=(IxCC/fixtures ':!IxCC/fixtures/aiur-*'
         IxCC/IxCCTests/Src/Artifacts IxCC/IxCCTests/Recheck/Artifacts IxCC/IxCCTests/Corpus/Artifacts
         IxCC/IxCCTests/Fir/Artifacts.lean IxCC/benchmarks/fixtures)
  git grep -I -n -E '(/home/|/nix/store/|/tmp/)' -- "${paths[@]}" | sed 's/^\([^:]*\):\([0-9]*\):.*/\1\t\2\tabsolute path\tpath/'
else
  mapfile -t rootfiles < <(git diff --name-only --diff-filter=AM origin/main...HEAD -- . ':!IxCC')
  paths=(IxCC ':!IxCC/plans' ':!IxCC/tools/citations.sh' "${rootfiles[@]}")
fi
git grep -I -n -o -w -E '[0-9a-f]{7,40}' -- "${paths[@]}" |
while IFS=: read -r file line tok; do
  case "$tok" in *[a-f]*) ;; *) continue;; esac          # all-digit tokens are numbers
  kind=$(git cat-file -t "$tok" 2>/dev/null)
  if [ "$kind" = commit ]; then
    full=$(git rev-parse "$tok^{commit}")
    if git merge-base --is-ancestor "$full" origin/main 2>/dev/null; then reach=main
    elif git merge-base --is-ancestor "$full" HEAD 2>/dev/null; then reach=branch-history
    else reach=off-branch; fi
    [ "${1:-}" = --fixtures ] && [ $reach = main ] && continue
    printf '%s\t%s\t%s\t%s\n' "$file" "$line" "$tok" "$reach"
  else
    for k in $known_missing; do case "$k" in "$tok"*|"${tok:0:8}"*) printf '%s\t%s\t%s\t%s\n' "$file" "$line" "$tok" "not-in-store";; esac; done
  fi
done
