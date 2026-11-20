#!/usr/bin/env bash
# Extract a premise-selection scope from the Mathlib build that Ix compiles.
#   extract.sh NAME MODULE[,MODULE…] SCOPE-PREFIX
# writes .truthmines/datasets/NAME/{decls.tsv,seeds.txt,scope.ixe,report.json,names.tsv}:
#   decls.tsv   declarations, statements and proof-term constants (Extract.lean)
#   scope.ixe   the Ixon compile of every library theorem with its dependency closure
#   names.tsv   NAME<TAB>ADDRESS for every named constant of scope.ixe
# Run it through ix/heavy.sh.
set -euo pipefail
name="$1"; module="$2"; prefix="$3"
here="$(cd "$(dirname "$0")" && pwd)"
project="$(dirname "$(dirname "$here")")"
out="$project/.truthmines/datasets/$name"
mkdir -p "$out"
worktree=/home/sam/repos/ix.ixai-aiur
src="$worktree/IxAIData"
mkdir -p "$src"

{ echo "package mathlib"
  echo "commit $(git -C "$worktree/.lake/packages/mathlib" rev-parse HEAD)"
  echo "licence Apache-2.0"
  echo "toolchain $(cat "$worktree/.lake/packages/mathlib/lean-toolchain")"
  echo "ix $(git -C /home/sam/repos/ix.ci-merge-tests rev-parse HEAD)"
  echo "modules $module"
} > "$out/source.txt"
t0=$(date +%s)
"$here/lean341.sh" --run "$here/Extract.lean" "$out/decls.tsv" "$prefix" ${module//,/ }
t1=$(date +%s)
# The axioms the acceptance policy names are seeded too, so each has an address.
{ awk -F'\t' '$1 == "lib" { print $2 }' "$out/decls.tsv"
  printf '%s\n' sorryAx propext Classical.choice Quot.sound Lean.ofReduceBool Lean.ofReduceNat
} > "$out/seeds.txt"

# The compile input imports the scope; `ix compile` elaborates it in the worktree's Lake project.
printf 'import %s\n' ${module//,/ } > "$src/PremiseScope.lean"
printf 'axiom IxAIDataEmpty.marker : Prop\n' > "$src/PremiseEmpty.lean"
"$project/ix/ixw" compile "$src/PremiseScope.lean" --no-build --consts-file "$out/seeds.txt" \
  --out "$out/scope.ixe" --report "$out/report.json"
t2=$(date +%s)
# An environment with its names stripped: diffing against it lists every named constant of the scope.
"$project/ix/ixw" compile "$src/PremiseEmpty.lean" --no-build --local --anon --out "$out/empty.ixe"
"$project/ix/ixw" diff "$out/empty.ixe" "$out/scope.ixe" --verbose > "$out/diff.txt" || [ $? -eq 1 ]
awk '$1 == "+" && NF == 3 { print $2 "\t" $3 }' "$out/diff.txt" > "$out/names.tsv"
t3=$(date +%s)
echo "extract $((t1 - t0)) s, compile $((t2 - t1)) s, names $((t3 - t2)) s; $(wc -l < "$out/names.tsv") names"
