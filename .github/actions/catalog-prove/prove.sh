#!/usr/bin/env bash
# Prove the caller's Lake libraries on a persistent runner, using the last
# catalog proved for this repository as the base. Proof objects accumulate in
# ~/.ix; catalogs live under ~/ix-catalogs/<owner>/<repo>/<sha>.ixc, and
# `latest` points at the most recent verified one.
#
# The axiom policy is inherited from the libraries: a baseline allows every
# axiom in their export, and later runs inherit the base record's policy.
set -euo pipefail

dir="$HOME/ix-catalogs/$GITHUB_REPOSITORY"
catalog="$dir/$GITHUB_SHA.ixc"
work="$RUNNER_TEMP/ix-catalog-prove"
mkdir -p "$dir" "$work"

exec 9>"$dir/.lock"
flock 9

read -ra libraries <<<"$IX_LIBRARIES"
label=$(IFS=-; echo "${libraries[*]}")

base=none
reused=false
if [[ -f "$catalog/proving.json" ]]; then
  reused=true
else
  if jq -e '.packages[] | select(.name == "mathlib")' lake-manifest.json >/dev/null; then
    lake exe cache get
  fi
  lake build "${libraries[@]}"
  lake query --json "${libraries[@]/%/:modules}" | jq -r '.[]' >"$work/modules"
  sed 's/^/import /' "$work/modules" >"$work/Export.lean"
  lake env ix compile "$work/Export.lean" --no-build --out "$work/snapshot.ixe"

  # An existing manifest is an interrupted run for this commit; keep it so
  # `ix catalog prove` resumes from its pending state.
  if [[ ! -f "$catalog/manifest" ]]; then
    ix catalog assemble "$catalog" "$work/snapshot.ixe" --labels "$label" \
      --pins "git:$GITHUB_SERVER_URL/$GITHUB_REPOSITORY@$GITHUB_SHA"
  fi

  # A resumed run must use the base its pending plan was made against.
  base_file="$dir/$GITHUB_SHA.base"
  if [[ ! -f "$base_file" ]]; then
    if [[ -e "$dir/latest" ]]; then
      readlink -f "$dir/latest" >"$base_file"
    else
      echo none >"$base_file"
    fi
  fi
  base=$(<"$base_file")

  prove_args=()
  if [[ "$base" != none ]]; then
    prove_args+=(--base "$base")
  else
    mapfile -t modules <"$work/modules"
    lake env lean --run "$GITHUB_ACTION_PATH/Axioms.lean" "${modules[@]}" |
      while read -r name; do
        ix addr-of --ixe "$work/snapshot.ixe" "$name"
      done >"$work/baseline-axioms.txt"
    prove_args+=(--allow-axioms "$work/baseline-axioms.txt")
  fi
  ix catalog prove "$catalog" "${prove_args[@]}" --json >"$work/prove.json"
fi

jq -r '.profile.allowedAxioms[]' "$catalog/proving.json" >"$work/axioms.txt"
ix catalog verify-proof "$catalog" --allow-axioms "$work/axioms.txt" --json \
  >"$work/verify.json"
# Re-verifying an older commit must not move `latest` backwards.
if [[ "$reused" == false ]]; then
  ln -sfn "$catalog" "$dir/latest"
fi
echo "catalog=$catalog" >>"$GITHUB_OUTPUT"

{
  echo "### ix proof for \`${GITHUB_SHA:0:12}\`"
  echo
  if [[ "$reused" == true ]]; then
    echo "Already proved on this runner; the existing certificate verified."
  else
    echo "Libraries: \`${libraries[*]}\`. Base: \`$(basename "$base")\`. Certificate verified."
    echo
    echo '<details><summary>Proving record</summary>'
    echo
    echo '```json'
    cat "$work/prove.json"
    echo '```'
    echo
    echo '</details>'
  fi
} | tee "$RUNNER_TEMP/ix-summary.md" >>"$GITHUB_STEP_SUMMARY"

if [[ -n "${IX_PR_NUMBER:-}" ]]; then
  gh pr comment "$IX_PR_NUMBER" --repo "$GITHUB_REPOSITORY" \
    --body-file "$RUNNER_TEMP/ix-summary.md" --edit-last --create-if-none
fi
