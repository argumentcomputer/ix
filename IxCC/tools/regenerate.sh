#!/usr/bin/env bash
# Regenerate every fixture, table and generated module that this repository's `ix` determines
# (docs/corpus.md, "Refreezing"), in place or, with --check, in a scratch copy of the committed
# tree, and report per file whether the result equals what is committed.
#
#   IxCC/tools/regenerate.sh [--check] [--work DIR] [--jobs N]
#
# Run from anywhere inside the repository, in ix's dev shell (`nix develop`), with `ix` and the
# IxCC tools buildable. Without --check it rewrites the checkout (a refreeze; review the diff,
# docs/corpus.md lists the reviews). With --check it leaves the checkout alone, regenerates into
# WORK/tree (an export of HEAD), lists every file that differs, then scans the committed tree for
# commits and paths outside the repository; it exits 0 only if nothing differs and nothing is
# cited ("current and self-contained").
#
# Not covered (frozen by decision or not written by ix): fixtures/ixon-v4/typing and catalog (the
# erased checker's unbound typing bundles and the catalogs over them), the dated
# fixtures/ownership/historical records, the vendored Aiur snapshot and its reference exports,
# fixtures/ixon-v4/bench-k1/steps.json (a measurement of the compiled code: check-steps), docs/.
# The families are every `corpus.json` under fixtures/ (the registered ones, `corpus families`,
# and the unregistered k1, ownership and phase2-arity), so a new family needs no change here.
set -uo pipefail
CHECK=0; WORK=""; JOBS=10
while [ $# -gt 0 ]; do
  case "$1" in
    --check) CHECK=1; shift;;
    --work) WORK="$2"; shift 2;;
    --jobs) JOBS="$2"; shift 2;;
    *) echo "usage: regenerate.sh [--check] [--work DIR] [--jobs N]" >&2; exit 2;;
  esac
done
ROOT=$(git rev-parse --show-toplevel)
WORK=${WORK:-$ROOT/IxCC/plans/regenerate}
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)
LOG=$WORK/logs; mkdir -p "$LOG"
LAKE=$(command -v lake)
step() { local s=$SECONDS; echo "== $*"; "$@"; local rc=$?; echo "   ($(( SECONDS - s )) s, exit $rc)"; return $rc; }
die() { echo "regenerate: $*" >&2; exit 1; }

# 0. the producer, the tools, and a `lake` stand-in for ix (it asks `lake env printenv LEAN_PATH`
#    where it compiles; the stand-in answers with the root workspace's libraries)
(cd "$ROOT" && step lake build ix > "$LOG/ix-build.log" 2>&1) || die "lake build ix failed ($LOG/ix-build.log)"
IX=$ROOT/.lake/build/bin/ix
FAKE=$WORK/fake; mkdir -p "$FAKE"
LP=$(cd "$ROOT" && lake env printenv LEAN_PATH)
printf '#!/usr/bin/env bash\n[ "$*" = "env printenv LEAN_PATH" ] && { echo "%s"; exit 0; }\nexit 1\n' "$LP" > "$FAKE/lake"
chmod +x "$FAKE/lake"
TOOLS="corpus tests-own refreeze-ixon pin-src-tables gen-src-artifacts gen-recheck-artifacts tests-fir"
(cd "$ROOT/IxCC" && step lake build $TOOLS > "$LOG/tools-build.log" 2>&1) || die "the tools did not build ($LOG/tools-build.log)"
BIN=$ROOT/IxCC/.lake/build/bin

# The tree the tools write: the checkout, or an export of HEAD under version control of its own
if [ $CHECK = 1 ]; then
  TREE=$WORK/tree
  [ -e "$TREE" ] && die "$TREE exists; remove it or pass another --work"
  mkdir -p "$TREE"
  git -C "$ROOT" archive HEAD IxCC | tar -x -C "$TREE"
  (cd "$TREE" && git init -q && git add -A && git -c user.name=regenerate -c user.email=regenerate commit -qm HEAD) \
    || die "could not record the exported tree"
  IXCC=$TREE/IxCC
else
  IXCC=$ROOT/IxCC
fi
cd "$IXCC"

# 1. the tables, first (the census and ingress read them): ix's fixture package and primitive
#    table, the Src tables, then Src.Pinned and the fixed pins
git -C "$ROOT" show HEAD:IxCC/fixtures/ixon-v4/primitives.tsv > "$WORK/old-primitives.tsv"
git -C "$ROOT" show HEAD:IxCC/fixtures/ixon-v4/src-tables.tsv > "$WORK/old-src-tables.tsv"
step "$BIN/refreeze-ixon" package --ix-repo "$ROOT" --ix-revision HEAD > "$LOG/package.log" 2>&1 || die "package"
step "$BIN/refreeze-ixon" tc-primitives --ix-repo "$ROOT" --ix-revision HEAD > "$LOG/tc-primitives.log" 2>&1 || die "tc-primitives"
step env PATH="$FAKE:$PATH" "$BIN/pin-src-tables" --ix "$IX" --work "$WORK/src-tables" > "$LOG/src-tables.log" 2>&1 || die "src tables"
for f in IxCC/Src/Pinned.lean IxCC/Src/Syntax.lean; do
  step "$BIN/pin-src-tables" --repin $f --old-primitives "$WORK/old-primitives.tsv" --old-tables "$WORK/old-src-tables.tsv" \
    >> "$LOG/repin.log" 2>&1 || die "repin $f"
done
TABLES="fixtures/ixon-v4 IxCC/Src/Pinned.lean IxCC/Src/Syntax.lean IxCC/Ixon/V3/PrimAddrs.lean"
if [ $CHECK = 1 ]; then
  if [ -n "$(git -C "$TREE" status --porcelain -- $(for t in $TABLES; do echo IxCC/$t; done))" ]; then
    echo "The tables differ from the committed ones, so the tools built from the checkout are stale"
    echo "for the rest of the check: the fixtures are not current. Regenerate in place (without --check)."
    git -C "$TREE" status --short
    exit 1
  fi
else
  (cd "$ROOT/IxCC" && step lake build $TOOLS > "$LOG/tools-rebuild.log" 2>&1) || die "the tools did not rebuild"
fi

# 2. every family, in parallel; then the ownership verdicts, the RC input and the roots-only
#    fixtures (LEAN_PATH: the root workspace's, for the interpreter runs of the ownership sources)
export LEAN_PATH="$LP"
git -C "$ROOT" ls-files 'IxCC/fixtures/**/corpus.json' | sed 's|^IxCC/||' | grep -v '/historical/' > "$WORK/manifests"
echo "== $(wc -l < "$WORK/manifests") families: $(tr '\n' ' ' < "$WORK/manifests")"
s=$SECONDS
xargs -P "$JOBS" -I{} sh -c 'm={}; n=$(echo $m | tr / _); "$0" rebuild "$m" --ix "$1" --ix-path "$2" --work "$3/rebuild/$n" > "$3/logs/rebuild-$n.log" 2>&1 && echo "   $m ok" || echo "   $m FAILED (see $3/logs/rebuild-$n.log)"' \
  "$BIN/corpus" "$IX" "$FAKE" "$WORK" < "$WORK/manifests" | tee "$WORK/rebuild.out"
echo "   ($(( SECONDS - s )) s)"
grep -q FAILED "$WORK/rebuild.out" && die "a family did not rebuild"
step "$BIN/tests-own" verdicts --ix "$IX" --ix-path "$FAKE" --work "$WORK/verdicts" > "$LOG/verdicts.log" 2>&1 || die "verdicts ($LOG/verdicts.log)"
step "$BIN/refreeze-ixon" rc-real-source --ix "$IX" --ix-path "$FAKE" --work "$WORK" > "$LOG/rc.log" 2>&1 || die "rc-real-source"
unset LEAN_PATH
step env PATH="$FAKE:$PATH" "$BIN/pin-src-tables" --ix "$IX" --diagnostics fixtures/ixon-v4/src-diag --work "$WORK/diag" > "$LOG/diag.log" 2>&1 || die "src-diag"
step env PATH="$FAKE:$PATH" "$BIN/pin-src-tables" --ix "$IX" --sortpoly fixtures/ixon-v4/src-sortpoly --work "$WORK/sortpoly" > "$LOG/sortpoly.log" 2>&1 || die "src-sortpoly"

# 3. the generated modules (written into the tree; the generators read its fixtures)
step "$BIN/gen-src-artifacts" > "$LOG/gen-src.log" 2>&1 || die "gen-src-artifacts"
step "$BIN/gen-recheck-artifacts" > "$LOG/gen-recheck.log" 2>&1 || die "gen-recheck-artifacts"
step "$BIN/corpus" kernel-artifacts > "$LOG/kernel-artifacts.log" 2>&1 || die "corpus kernel-artifacts"
step sh -c "'$BIN/tests-fir' --render-artifacts > IxCCTests/Fir/Artifacts.lean" || die "tests-fir --render-artifacts"

# 4. the report
if [ $CHECK = 1 ]; then
  CHANGED=$(git -C "$TREE" status --porcelain)
  TOTAL=$(git -C "$TREE" ls-files | wc -l)
  echo "== per file: $(echo -n "$CHANGED" | grep -c '^' ) of $TOTAL files differ from HEAD"
  [ -n "$CHANGED" ] && echo "$CHANGED"
  echo "== citations (commits and paths outside the repository, in fixtures, manifests, READMEs and generated modules)"
  CITED=$(cd "$ROOT" && bash IxCC/tools/citations.sh --fixtures)
  [ -n "$CITED" ] && echo "$CITED"
  [ -z "$CHANGED" ] && [ -z "$CITED" ] && { echo "regenerate --check: current and self-contained"; exit 0; }
  echo "regenerate --check: NOT current or not self-contained"; exit 1
else
  echo "== regenerated in place; review with git diff (docs/corpus.md, Refreezing)"
  git -C "$ROOT" status --short | head -50
fi
