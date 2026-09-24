#!/bin/bash
# Restore the Anthropic FLT (flt_e2e) build artifacts from S3 into Benchmarks/Compile,
# the way Mathlib's `lake exe cache get` does it: download the .ltar archives, unpack them
# all with a single multithreaded leantar call, then let Lake verify the traces.
#
# Prerequisites (run from Benchmarks/Compile):
#   lake exe cache get        # clones deps and restores Mathlib + its 7 deps from Mathlib's cache
#   aws configure             # IAM credentials that can read the bucket
#
# Lean must be on PATH: either the Nix dev shell (`nix develop`) or elan. The cache was
# built with leanprover/lean4:v4.33.1 on x86_64-unknown-linux-gnu, and Lake's traces only
# validate against the same toolchain, so any other version fails verification.
set -euo pipefail
LEAN_VERSION=4.33.1
PREFIX="s3://argument-lake-cache-063002298335-us-east-1-an/staged/anthropic-flt/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/lean-4.33.1/x86_64-unknown-linux-gnu/flt_e2e"
DEST="${FLT_CACHE_DIR:-$HOME/.cache/flt_e2e}"
PKG="$PWD/.lake/packages/flt_e2e"

if [ -d "$HOME/.elan/bin" ]; then export PATH="$HOME/.elan/bin:$PATH"; fi

grep -q 'name = "Compile"' lakefile.toml 2>/dev/null || { echo "run from Benchmarks/Compile" >&2; exit 1; }
test -f "$PKG/lean-toolchain" || { echo "flt_e2e not checked out; run 'lake exe cache get' first" >&2; exit 1; }
command -v lean >/dev/null || { echo "lean not on PATH; enter 'nix develop' or install elan" >&2; exit 1; }
lean --version | grep -q "version $LEAN_VERSION," || { echo "need Lean $LEAN_VERSION, found: $(lean --version)" >&2; exit 1; }
LEANTAR="$(lean --print-prefix)/bin/leantar"
test -x "$LEANTAR" || { echo "leantar not found at $LEANTAR" >&2; exit 1; }

echo "Downloading archives to $DEST"
aws s3 sync "$PREFIX/" "$DEST/" --region us-east-1 --size-only --only-show-errors

echo "Unpacking $(wc -l < "$DEST/modules.jsonl") modules into $PKG/.lake/build"
python3 - "$DEST" "$PKG" <<'PY' | "$LEANTAR" -x -j -
import json, sys, os
dest, pkg = sys.argv[1:3]
lib, ir = f"{pkg}/.lake/build/lib/lean", f"{pkg}/.lake/build/ir"
entries = []
for line in open(f"{dest}/modules.jsonl"):
    mod, h, ltar = json.loads(line)
    sub = os.path.dirname(mod.replace(".", "/"))
    for d in (f"{lib}/{sub}", f"{ir}/{sub}"):
        os.makedirs(d, exist_ok=True)
    entries.append({"file": f"{dest}/{ltar}", "base": [f"{lib}/{sub}", f"{ir}/{sub}"], "hash": h})
print(json.dumps(entries))
PY

echo "Verifying the cached package with Lake"
lake build flt_e2e/FinalCheck --no-build

# The benchmark driver is a local one-line module outside the cache, so it is
# compiled here rather than checked with --no-build.
echo "Compiling the CompileAnthropicFLT driver module"
lake build CompileAnthropicFLT
