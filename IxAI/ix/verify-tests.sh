#!/usr/bin/env bash
# Regression tests for the verification boundary (docs/verification.md), run on built binaries:
#   ix/heavy.sh ix/verify-tests.sh
# Pure properties (Merkle roots and paths, curation, trajectory jobs, submission parsing) are
# `#guard`s in IxAITest and IxAIVerifyTest and run when those libraries build. This script covers
# what needs processes and files: step-proof chains, verifier failures, model words, the reward
# harness and its sandbox, startup, a job issued before training checked against the full run,
# the compressed certificates verified against a pinned PLONK key and a statement computed here,
# and the combined certificate of training and its environment (`aiur_join_check`, from
# IXAI_AIUR_JOIN_CHECK or ix/toolchain-cert/bin).
# The fork's verifier builds (IXAI_AIUREXEC, the fork's checkout) link libmulti_stark_cuda.so
# (IXAI_MULTI_STARK_LIB) and libix_bn254_cuda.so (IXAI_BN254_LIB), and need the CUDA driver
# preloaded. IX_LEAN names the Lean toolchain that compiles the claim templates.
set -uo pipefail
cd "$(dirname "$0")/.."
ixai=.lake/build/bin/ixai
verify=.lake/build/bin/ixai-verify
pkg=.truthmines/package/full
proofs=.truthmines/aiur/full-bound
export IXAI_VERIFY_WORK="${IXAI_VERIFY_WORK:-/tmp}"
fork="${IXAI_AIUREXEC:-/home/sam/repos/forks/ix-aiurexec}"
export LD_LIBRARY_PATH="${IXAI_MULTI_STARK_LIB:-$fork/target/release/build/multi-stark-edcba16ae0404757/out}:${IXAI_BN254_LIB:-$fork/target/release/build/ix-proof-compression-1b83b61d527ce023/out}${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
export LD_PRELOAD="${LD_PRELOAD:-/usr/lib/x86_64-linux-gnu/libcuda.so.1}"
lean="${IX_LEAN:-/nix/store/xnh27vasww8vbnh7a18g3xkdg1r4kl6w-lean-4.34.1}"
work=$(mktemp -d -p "$IXAI_VERIFY_WORK")
trap 'rm -rf "$work"' EXIT
fails=0
pass() { echo "PASS: $1"; }
fail() { echo "FAIL: $1"; fails=$((fails + 1)); }
expect() {  # expect NAME EXIT_CODE PATTERN COMMAND...
  local name=$1 code=$2 pattern=$3; shift 3
  local out; out=$("$@" 2>&1); local got=$?
  if [ "$got" = "$code" ] && grep -qE "$pattern" <<<"$out"; then pass "$name"
  else fail "$name (exit $got, wanted $code /$pattern/): $(tail -3 <<<"$out")"; fi
}

# 1. Step-proof chains: complete chains only, proofs verified, reports never trusted.
mkdir -p "$work/empty" "$work/report-only"
cp /tmp/ix-ai-review-20261119/report-only/step-000.report.json "$work/report-only/" 2>/dev/null \
  || cp "$proofs/step-000.report.json" "$work/report-only/"
expect "empty chain directory is incomplete, not accepted" 4 "INCOMPLETE" $ixai aiur-chain "$work/empty"
expect "a report without proofs is incomplete" 4 "INCOMPLETE.*|0 of 600" $ixai aiur-chain "$work/report-only"
expect "report diagnostics say they verify nothing" 4 "DIAGNOSTIC ONLY" $ixai aiur-diagnose "$work/report-only"
mkdir -p "$work/swapped"
for f in "$proofs"/step-*.proof; do ln -s "$(realpath "$f")" "$work/swapped/$(basename "$f")"; done
ln -sf "$(realpath "$proofs/step-001.proof")" "$work/swapped/step-000.proof"
step=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["programs"]["Fixed::step"])' "$pkg/commitment.json")
expect "a proof of another step is rejected" 1 "REJECTED" $verify chain --config full \
  --program "$pkg/program-step.ixp" --program-blake3 "$step" --proofs "$work/swapped" \
  --models "$proofs/expected.txt" --model "$pkg/model.txt"
expect "a program other than the approved one is rejected" 1 "REJECTED.*|not the approved" $verify chain --config full \
  --program "$pkg/program-train.ixp" --program-blake3 "$step" --proofs "$proofs" \
  --models "$proofs/expected.txt" --model "$pkg/model.txt"

chain() { $verify chain --config full --program "$pkg/program-step.ixp" --program-blake3 "$step" "$@"; }

# 2. Verifier failures: a tool that cannot start says nothing about the evidence; one that started
# on the proofs and failed or panicked rejects the route.
printf '#!/usr/bin/env bash\necho "key ready: fake"\necho "thread main panicked at proof.rs: crafted proof" >&2\nexit 101\n' > "$work/panic-verifier"
printf '#!/usr/bin/env bash\necho "thread main panicked at setup.rs: no key" >&2\nexit 101\n' > "$work/setup-panic-verifier"
chmod +x "$work/panic-verifier" "$work/setup-panic-verifier"
expect "a verifier that panics on the proofs rejects the route" 1 "REJECTED" \
  env IXAI_VERIFY_CLAIM="$work/panic-verifier" $verify chain --config full --program "$pkg/program-step.ixp" \
  --program-blake3 "$step" --proofs "$proofs" --models "$proofs/expected.txt" --model "$pkg/model.txt"
expect "a verifier that cannot start leaves the route incomplete" 4 "INCOMPLETE" \
  env IXAI_VERIFY_CLAIM=/nonexistent/verify_claim $verify chain --config full --program "$pkg/program-step.ixp" \
  --program-blake3 "$step" --proofs "$proofs" --models "$proofs/expected.txt" --model "$pkg/model.txt"
expect "a verifier that fails before reading a proof leaves the route incomplete" 4 "INCOMPLETE" \
  env IXAI_VERIFY_CLAIM="$work/setup-panic-verifier" $verify chain --config full --program "$pkg/program-step.ixp" \
  --program-blake3 "$step" --proofs "$proofs" --models "$proofs/expected.txt" --model "$pkg/model.txt"

# 3. Model words: canonical integers in the weight range, for every model of the chain.
awk 'NR == 300 { $1 = 5000 } { print }' "$proofs/expected.txt" > "$work/out-of-range.txt"
expect "an intermediate model outside the weight range is rejected" 1 "REJECTED.*|outside the weight range" \
  chain --proofs "$proofs" --models "$work/out-of-range.txt" --model "$pkg/model.txt"
python3 -I -c 'import sys
ls = open(sys.argv[1]).read().split("\n"); w = ls[0].split(); w[0] = str(int(w[0]) + 18446744069414584321)
ls[0] = " ".join(w); open(sys.argv[2], "w").write("\n".join(ls))' "$proofs/expected.txt" "$work/alias.txt"
expect "a word congruent to a weight modulo the field is rejected" 1 "REJECTED.*|outside the weight range" \
  chain --proofs "$proofs" --models "$work/alias.txt" --model "$pkg/model.txt"
awk '{ $1 = "+" ($1 < 0 ? -$1 : $1); print }' "$pkg/model.txt" > "$work/plus.txt"
expect "a non-canonical integer in the model is rejected" 1 "REJECTED.*|not a canonical integer" \
  chain --proofs "$proofs" --models "$proofs/expected.txt" --model "$work/plus.txt"

# 4. Trajectories: the consumer's job, not the header.
$ixai data "$work/data.txt" >/dev/null
sed -e 's/^config \([0-9]*\) \([0-9]*\) \([0-9-]*\) 30 /config \1 \2 \3 0 /' -e '/^item /d' "$work/data.txt" > "$work/zero.txt"
expect "a header with 0 epochs is rejected (ixai check)" 1 "REJECT" $ixai check "$work/zero.txt"
expect "a header with 0 epochs is rejected (ixai-verify)" 1 "REJECT" $verify trajectory "$work/zero.txt"

# 5. Reward harness: proof text is a term only, and elaboration is isolated.
bundle=ix/bundle
escape=/tmp/ixai-review-escape-$$.txt
inrepo=ix/bundle/reward-work/escaped-$$.txt
printf 'by decide\n\n#eval IO.FS.writeFile "%s" "proof text executed IO"\n' "$escape" > "$work/escape.proof"
expect "proof text with a command is rejected before elaboration" 1 "rejectedSubmission" \
  $ixai reward-submit "$bundle" identity "$work/escape.proof"
[ ! -e "$escape" ] && pass "the rejected submission ran nothing" || fail "the rejected submission ran: $escape exists"
printf 'by decide\n' > "$work/honest.proof"
expect "an honest proof is accepted" 0 "RewardVerdict.accepted" $ixai reward-submit "$bundle" identity "$work/honest.proof"
cat > "$work/Escape.lean" <<EOF
import IxAICore
#eval IO.FS.writeFile "$escape" "escaped /tmp"
#eval IO.FS.writeFile "$(realpath ix)/escaped-$$.txt" "escaped the repo"
#eval IO.FS.writeFile "$(realpath .truthmines)/escaped-$$.txt" "reached the store"
EOF
$ixai sandbox-compile "$bundle" "$work/Escape.lean" >/dev/null 2>&1
if [ ! -e "$escape" ] && [ ! -e "ix/escaped-$$.txt" ] && [ ! -e ".truthmines/escaped-$$.txt" ]; then
  pass "#eval in the sandbox reaches neither /tmp, the repository nor .truthmines"
else fail "#eval escaped the sandbox"; rm -f "$escape" "ix/escaped-$$.txt" ".truthmines/escaped-$$.txt"; fi
rm -f "$inrepo"

# 5b. The reward harness's own cases (self-contained).
if ix/reward-tests.sh > "$work/reward-tests.log" 2>&1; then pass "reward harness: $(tail -1 "$work/reward-tests.log")"
else fail "reward harness: $(grep -E '^FAIL' "$work/reward-tests.log" | head -3; tail -1 "$work/reward-tests.log")"; fi

# 6. Startup: no benchmark runs before the command is read.
t0=$(date +%s%N); $ixai no-such-command >/dev/null 2>&1; t1=$(date +%s%N)
ms=$(( (t1 - t0) / 1000000 )); [ "$ms" -lt 5000 ] && pass "ixai rejects a bad command in $ms ms" || fail "ixai startup $ms ms"
t0=$(date +%s%N); $verify no-such-command >/dev/null 2>&1; t1=$(date +%s%N)
ms=$(( (t1 - t0) / 1000000 )); [ "$ms" -lt 5000 ] && pass "ixai-verify rejects a bad command in $ms ms" || fail "ixai-verify startup $ms ms"

# 7. A job issued before training: built from the specification and the config alone (templates
# compiled by the consumer), then the trained package is checked against it.
$verify template --config full --out "$work/Template_full.lean" >/dev/null
(cd ix/bundle && IX_PROFILE=ci-pinned PATH="$lean/bin:$PATH" ../ixw compile "$work/Template_full.lean" \
  --local --no-build --out "$work/template_full.ixe" >"$work/template.log" 2>&1) \
  || fail "the claim templates do not compile: $(tail -3 "$work/template.log")"
$verify commit --config full --template-source "$work/Template_full.lean" --template-env "$work/template_full.ixe" \
  --program "Fixed::step=$pkg/program-step.ixp" --program "Fixed::train=$pkg/program-train.ixp" \
  --program "AiurExec::aiur_exec=$pkg/aggregator.ixa" --out "$work/job.json" >/dev/null \
  || fail "the job cannot be built from the templates"
job=$($verify blake3 "$work/job.json")
if grep -q '"9db499ddc355de7c43ac779e36ae868a0a513deb68bf0f4bd1d780f599cd114b"\|45ea4f5f' "$work/job.json"; then
  fail "the job names a trained claim or model"
else pass "the job names no trained claim or model"; fi
receipt() {  # receipt OUT PYTHON-EDIT: a copy of the full receipt with absolute paths, edited
  python3 -I - "$pkg/receipt.json" "$1" "$(realpath "$pkg")" "$2" <<'PY'
import json, os, sys
r = json.load(open(sys.argv[1])); base = sys.argv[3]
for k in ("model",):
    r[k] = os.path.join(base, r[k])
for t in r["training"]:
    for k in ("program", "aggregator", "proofs", "models", "proof", "root", "plonk", "plonkKey"):
        if k in t: t[k] = os.path.join(base, t[k])
exec(sys.argv[4])
json.dump(r, open(sys.argv[2], "w"))
PY
}
pkgcheck() { $verify package --commitment "$work/job.json" --commitment-blake3 "$job" --receipt "$@"; }
receipt "$work/claims-only.json" 'r["training"] = []'
expect "claims alone verify against the job: the model is checked only by its evaluation" 3 "OUTCOME: PREDICTED" \
  pkgcheck "$work/claims-only.json"
receipt "$work/swapped-claims.json" 'r["training"] = []
c = {x["name"].split(".")[-1]: x for x in r["claims"]}
c["cardCertified"]["proof"], c["decision0"]["proof"] = c["decision0"]["proof"], c["cardCertified"]["proof"]'
expect "a proof of another claim does not instantiate the template" 1 "does not state the committed template" \
  pkgcheck "$work/swapped-claims.json"
awk '{ $1 = $1 + 1; print }' "$pkg/model.txt" > "$work/other-model.txt"
receipt "$work/other-model.json" "r[\"training\"] = []; r[\"model\"] = \"$work/other-model.txt\""
expect "the claims' model is the submitted model" 1 "whose value is not the submitted model" \
  pkgcheck "$work/other-model.json"
python3 -I -c 'import json, sys
j = json.load(open(sys.argv[1])); j["claimPolicy"]["binding"] = "2d3ce019b9aca91f8c860eccc9ce907c10eb42cc03825710e7785a92256ed4b1"
json.dump(j, open(sys.argv[2], "w"))' "$work/job.json" "$work/other-binding.json"
expect "a proof under another role binding than the job's is not the policy's claim" 1 "role binding .*the policy's is" \
  $verify package --commitment "$work/other-binding.json" --commitment-blake3 "$($verify blake3 "$work/other-binding.json")" \
  --receipt "$work/claims-only.json"
receipt "$work/missing-claim.json" 'r["training"] = []; r["claims"] = r["claims"][1:]'
expect "a claim without a proof leaves the package incomplete" 4 "OUTCOME: INCOMPLETE" pkgcheck "$work/missing-claim.json"
python3 -I -c 'import json, sys
b = bytearray(open(json.load(open(sys.argv[1]))["environment"]["ixe"], "rb").read())
b[len(b) // 2] ^= 1; open(sys.argv[2], "wb").write(b)' "$pkg/receipt.json" "$work/tampered.ixe"
receipt "$work/tampered-env.json" "r[\"training\"] = []; r[\"environment\"][\"ixe\"] = \"$work/tampered.ixe\""
expect "an environment record that does not hash to its address is rejected" 1 "does not hash to its address" \
  pkgcheck "$work/tampered-env.json"
t0=$(date +%s)
expect "a job issued before training verifies the full package" 0 "OUTCOME: PROVED" pkgcheck "$pkg/receipt.json"
echo "full package check: $(( $(date +%s) - t0 )) s"

# 8. The compressed certificates: a job that pins the compression pipeline (the terminal PLONK
# verifying key and the wrapper layout), and each certificate verified against that key and a
# statement computed from the specification and the keys recompiled from the approved packages.
vk=ix/toolchain/base/target/e2e-l3/plonk-prepared/prepared/verifying-key.bin
layout=ix/toolchain/base/crates/stark-verifier/compress-wrap/m16384w64-v3.layout.json
$verify commit --config full --template-source "$work/Template_full.lean" --template-env "$work/template_full.ixe" \
  --program "Fixed::step=$pkg/program-step.ixp" --program "Fixed::train=$pkg/program-train.ixp" \
  --program "AiurExec::aiur_exec=$pkg/aggregator.ixa" --plonk-key "$vk" --wrap-layout "$layout" \
  --out "$work/job-plonk.json" >/dev/null || fail "the job cannot pin the compression pipeline"
jobp=$($verify blake3 "$work/job-plonk.json")
pkgplonk() { $verify package --commitment "$work/job-plonk.json" --commitment-blake3 "$jobp" --receipt "$@"; }
exec_only="r[\"training\"] = [dict(t, plonkKey=\"$(realpath "$vk")\") for t in r[\"training\"] if t[\"kind\"] == \"aiur-exec\"]"
receipt "$work/exec-only.json" "$exec_only"
t0=$(date +%s%N)
expect "the compressed certificate alone proves the training" 0 "\[aiur-exec\] verified" pkgplonk "$work/exec-only.json"
echo "package check through the certificate: $(( ($(date +%s%N) - t0) / 1000000 )) ms"
# A package assembled with the terminal key names it in its aiur-exec route, so the job that pins
# the pipeline verifies the certificate instead of reporting the route attested.
$ixai package-assemble --out "$work/assembled" --plonk-key "$vk" > "$work/assemble.log" 2>&1 \
  || fail "the package cannot be assembled with the PLONK key: $(tail -3 "$work/assemble.log")"
python3 -I -c 'import json, sys
r = json.load(open(sys.argv[1])); r["training"] = [t for t in r["training"] if t["kind"] == "aiur-exec"]
json.dump(r, open(sys.argv[2], "w"))' "$work/assembled/receipt.json" "$work/assembled/exec-only.json"
expect "a package assembled with --plonk-key has its certificate verified" 0 "\[aiur-exec\] verified" \
  pkgplonk "$work/assembled/exec-only.json"
plonk=$(python3 -I -c 'import json,sys; print([t for t in json.load(open(sys.argv[1]))["training"] if t["kind"] == "aiur-exec"][0]["plonk"])' "$pkg/receipt.json")
python3 -I -c 'import sys
b = bytearray(open(sys.argv[1], "rb").read()); b[100] ^= 1; open(sys.argv[2], "wb").write(b)' "$plonk" "$work/tampered.plonk"
receipt "$work/tampered-plonk.json" "$exec_only
for t in r[\"training\"]: t[\"plonk\"] = \"$work/tampered.plonk\"; t[\"plonkBlake3\"] = \"$($verify blake3 "$work/tampered.plonk")\""
expect "a certificate with one byte changed is rejected by the PLONK verifier" 1 "aiur_plonk_verify: .*REJECT" \
  pkgplonk "$work/tampered-plonk.json"
python3 -I -c 'import sys
b = bytearray(open(sys.argv[1], "rb").read()); b[len(b) // 2] ^= 1; open(sys.argv[2], "wb").write(b)' "$vk" "$work/other.vk"
receipt "$work/other-key.json" "$exec_only
for t in r[\"training\"]: t[\"plonkKey\"] = \"$work/other.vk\""
expect "a verifying key other than the pinned one is rejected" 1 "has BLAKE3 .*not the pinned" pkgplonk "$work/other-key.json"
expect "a PLONK verifier that cannot start leaves the route incomplete" 4 "\[aiur-exec\] INCOMPLETE" \
  env IXAI_PLONK_VERIFY=/nonexistent/aiur_plonk_verify $verify package --commitment "$work/job-plonk.json" \
  --commitment-blake3 "$jobp" --receipt "$work/exec-only.json"
printf '#!/usr/bin/env bash\necho "error: no Ignition parameters" >&2\nexit 2\n' > "$work/setup-fail-plonk"
chmod +x "$work/setup-fail-plonk"
expect "a PLONK verifier that stops before reading the proof leaves the route incomplete" 4 "\[aiur-exec\] INCOMPLETE" \
  env IXAI_PLONK_VERIFY="$work/setup-fail-plonk" $verify package --commitment "$work/job-plonk.json" \
  --commitment-blake3 "$jobp" --receipt "$work/exec-only.json"
# The certificate alone (`compressed`), for each kind of root: no file of the prover but the
# certificate (and, for one train_tree execution, the intermediate models it hashed) is read.
wrapkey=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["layout"]["key_blake3"])' "$layout")
vkd=$($verify blake3 "$vk")
compressed() {  # compressed SHAPE AGGREGATOR PROGRAM PLONK MODEL [ARGS...]
  local shape=$1 ax=$2 prog=$3 cert=$4 model=$5; shift 5
  $verify compressed --config full --shape "$shape" --aggregator "$ax" --aggregator-blake3 "$($verify blake3 "$ax")" \
    --program "$prog" --program-blake3 "$($verify blake3 "$prog")" --plonk "$cert" --plonk-key "$vk" \
    --plonk-key-blake3 "$vkd" --wrap-key-blake3 "$wrapkey" --model "$model" "$@"
}
a=.truthmines/aiur
expect "600 Fixed::step executions: certificate d8551c47… verified" 0 "\] verified" \
  compressed steps "$pkg/aggregator.ixa" "$pkg/program-step.ixp" "$a/aiurexec/ladder/plonk/proof.bin" "$pkg/model.txt"
expect "30 Fixed::train_block executions: certificate 20d80b11… verified" 0 "\] verified" \
  compressed blocks:20 "$a/aiurexec-block/aiur-exec.ixa" "$a/aiurexec-block/packages/block-000.ixa" \
  "$a/aiurexec-block/ladder/plonk/proof.bin" "$pkg/model.txt"
expect "one FixedTree::train_tree execution: certificate 26eb66b9… verified, Merkle root rebuilt" 0 "\] verified" \
  compressed tree "$a/single/aiur-exec-train.ixa" "$a/single/package/train-tree.ixa" \
  "$a/single/ladder/plonk/proof.bin" "$pkg/model.txt" --models "$a/single/package/models.txt"
awk '{ $7 = $7 + 1; print }' "$pkg/model.txt" > "$work/one-word.txt"
expect "the right certificate against a statement with one model word changed is rejected" 1 "aiur_plonk_verify: .*REJECT" \
  compressed steps "$pkg/aggregator.ixa" "$pkg/program-step.ixp" "$a/aiurexec/ladder/plonk/proof.bin" "$work/one-word.txt"
expect "one certificate against another root's statement is rejected" 1 "aiur_plonk_verify: .*REJECT" \
  compressed steps "$pkg/aggregator.ixa" "$pkg/program-step.ixp" "$a/single/ladder/plonk/proof.bin" "$pkg/model.txt"
awk 'NR == 300 { $1 = $1 + 1 } { print }' "$a/single/package/models.txt" > "$work/tree-models.txt"
expect "a tree certificate against one changed intermediate model is rejected" 1 "aiur_plonk_verify: .*REJECT" \
  compressed tree "$a/single/aiur-exec-train.ixa" "$a/single/package/train-tree.ixa" \
  "$a/single/ladder/plonk/proof.bin" "$pkg/model.txt" --models "$work/tree-models.txt"


# 9. One certificate for training and the environment of its refinement theorem (`combined`):
# aiur_join_check on the joined root against the pinned artifacts and the run computed from the
# specification and the submitted model, then the PLONK proof against the job's pinned key and the
# statement computed here. Flags given to `combined` come first, so they replace the defaults.
cb=.truthmines/combined
blk=$a/aiurexec-block
combined() {
  $verify combined "$@" --commitment "$work/job-plonk.json" --commitment-blake3 "$jobp" \
    --template-env "$work/template_full.ixe" --root "$cb/cert/full/root" \
    --plonk "$cb/cert/full/plonk/plonk/proof.bin" --plonk-key "$vk" --env "$cb/env/full.ixe" \
    --partition "$cb/cert/full/proven.ixes" --run-root "$cb/run-root" \
    --aggregator "$blk/aiur-exec.ixa" --aggregator-blake3 "$($verify blake3 "$blk/aiur-exec.ixa")" \
    --program "$blk/packages/block-000.ixa" --program-blake3 "$($verify blake3 "$blk/packages/block-000.ixa")" \
    --model "$pkg/model.txt"
}
with_join_check() { local tool=$1; shift; IXAI_AIUR_JOIN_CHECK="$tool" combined "$@"; }
t0=$(date +%s%N)
expect "the combined certificate 7a2a00c5… proves training and its environment" 0 "OUTCOME: PROVED" combined
echo "combined certificate check: $(( ($(date +%s%N) - t0) / 1000000 )) ms"
python3 -I -c 'import sys
b = bytearray(open(sys.argv[1], "rb").read()); b[100] ^= 1; open(sys.argv[2], "wb").write(b)' \
  "$cb/cert/full/plonk/plonk/proof.bin" "$work/tampered-combined.plonk"
expect "a combined certificate with one byte changed is rejected by the PLONK verifier" 1 "aiur_plonk_verify: .*REJECT" \
  combined --plonk "$work/tampered-combined.plonk"
expect "the combined certificate against a model with one word changed is rejected" 1 "chain ends at the expected model" \
  combined --model "$work/one-word.txt"
expect "another certificate's root in place of the joined root is rejected" 1 "REJECT: the certificate's root key is ix_aggr's" \
  combined --root "$blk/top/root"
expect "a missing aiur_join_check leaves the combined route incomplete" 4 "\[combined\] INCOMPLETE" \
  with_join_check /nonexistent/aiur_join_check
printf '#!/usr/bin/env bash\necho "ok: the certificate'"'"'s root key is ix_aggr'"'"'s"\necho "thread main panicked at join.rs: crafted root" >&2\nexit 101\n' > "$work/panic-join-check"
printf '#!/usr/bin/env bash\necho "artifact differs from its pin"\nexit 1\n' > "$work/setup-fail-join-check"
chmod +x "$work/panic-join-check" "$work/setup-fail-join-check"
expect "an aiur_join_check that panics on the evidence rejects the combined route" 1 "\[combined\] REJECTED" \
  with_join_check "$work/panic-join-check"
expect "an aiur_join_check that fails before reading the evidence leaves the combined route incomplete" 4 "\[combined\] INCOMPLETE" \
  with_join_check "$work/setup-fail-join-check"
expect "a job that pins no compression pipeline cannot accept the combined certificate" 4 "pins no compression pipeline" \
  combined --commitment "$work/job.json" --commitment-blake3 "$job"

echo "$fails failure(s)"
exit $((fails > 0))
