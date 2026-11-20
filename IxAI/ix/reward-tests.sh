#!/usr/bin/env bash
# Regression tests for the reward harness and its sandbox, on the built `ixai`:
#   ix/heavy.sh ix/reward-tests.sh
# What the worker can read and inherit, one job directory per submission, the goal's statement
# checked in the compiled environment, the output path of `ixai reward`, and CLI argument parsing.
set -uo pipefail
cd "$(dirname "$0")/.."
ixai=.lake/build/bin/ixai
bundle=ix/bundle
work=$(mktemp -d -p "${IXAI_VERIFY_WORK:-/tmp}")
sentinels=()
trap 'rm -rf "$work" "${sentinels[@]}"' EXIT
fails=0
pass() { echo "PASS: $1"; }
fail() { echo "FAIL: $1"; fails=$((fails + 1)); }
expect() {  # expect NAME EXIT_CODE PATTERN COMMAND...
  local name=$1 code=$2 pattern=$3; shift 3
  local out; out=$("$@" 2>&1); local got=$?
  if [ "$got" = "$code" ] && grep -qE "$pattern" <<<"$out"; then pass "$name"
  else fail "$name (exit $got, wanted $code /$pattern/): $(tail -3 <<<"$out")"; fi
}
# probe NAME PATH: a file whose elaboration fails with PROBE-VISIBLE iff PATH exists in the sandbox.
probe() {
  cat > "$work/$1.lean" <<EOF
import IxAICore
#eval show IO Unit from do
  if ← System.FilePath.pathExists "$2" then throw (IO.userError "PROBE-VISIBLE $2")
EOF
}

# 1. Reads: nothing outside the mounts. The probe itself works on a mounted path.
repo_sentinel="$(pwd)/.reward-sandbox-sentinel-$$"
home_sentinel="$HOME/.reward-sandbox-sentinel-$$"
echo secret > "$repo_sentinel"; echo secret > "$home_sentinel"
sentinels+=("$repo_sentinel" "$home_sentinel")
probe Control "$(realpath $bundle)/lakefile.toml"
expect "the probe sees a mounted path (control)" 1 "PROBE-VISIBLE" $ixai sandbox-compile "$bundle" "$work/Control.lean"
probe RepoSentinel "$repo_sentinel"
expect "a sentinel in the repository is not visible" 0 "compiled in the sandbox" $ixai sandbox-compile "$bundle" "$work/RepoSentinel.lean"
probe HomeSentinel "$home_sentinel"
expect "a sentinel in the home directory is not visible" 0 "compiled in the sandbox" $ixai sandbox-compile "$bundle" "$work/HomeSentinel.lean"
probe Store "$(pwd)/.truthmines/index.tsv"
expect "the project's records are not visible" 0 "compiled in the sandbox" $ixai sandbox-compile "$bundle" "$work/Store.lean"
probe Sources "$(pwd)/Ixai.lean"
expect "the project's other sources are not visible" 0 "compiled in the sandbox" $ixai sandbox-compile "$bundle" "$work/Sources.lean"

# 2. Environment: the caller's is not inherited.
cat > "$work/Env.lean" <<'EOF'
import IxAICore
#eval show IO Unit from do
  if (← IO.getEnv "IXAI_SANDBOX_CANARY").isSome then throw (IO.userError "ENV-VISIBLE")
  if (← IO.getEnv "HOME") == some (← IO.getEnv "IXAI_CALLER_HOME").get! then throw (IO.userError "HOME-VISIBLE")
EOF
expect "the caller's environment is not inherited" 0 "compiled in the sandbox" \
  env IXAI_SANDBOX_CANARY=1 IXAI_CALLER_HOME="$HOME" $ixai sandbox-compile "$bundle" "$work/Env.lean"

# 3. Concurrent submissions to one task each get their own job directory and verdict.
printf 'by decide\n' > "$work/honest.proof"
printf 'by sorry\n' > "$work/sorry.proof"
before=$(ls "$bundle/reward-work" | sort)
$ixai reward-submit "$bundle" identity "$work/honest.proof" > "$work/a.out" 2>&1 & a=$!
$ixai reward-submit "$bundle" identity "$work/sorry.proof" > "$work/b.out" 2>&1 & b=$!
$ixai reward-submit "$bundle" identity "$work/honest.proof" > "$work/c.out" 2>&1 & c=$!
wait $a; ea=$?; wait $b; eb=$?; wait $c; ec=$?
if [ $ea = 0 ] && grep -q "RewardVerdict.accepted" "$work/a.out" && [ $ec = 0 ] && grep -q "RewardVerdict.accepted" "$work/c.out" \
   && [ $eb = 1 ] && grep -q "RewardVerdict.policyViolation" "$work/b.out"; then
  pass "three concurrent submissions to one task get their own verdicts"
else fail "concurrent submissions: $(cat "$work/a.out" "$work/b.out" "$work/c.out" | tail -6)"; fi
grep -q "states the target" "$work/a.out" && pass "the accepted goal's statement was checked in the .ixe" \
  || fail "no statement check reported: $(cat "$work/a.out")"
after=$(ls "$bundle/reward-work" | sort)
[ "$before" = "$after" ] && pass "job directories are removed after the verdict" || fail "job directories left: $(comm -13 <(echo "$before") <(echo "$after"))"

# 4. The submission is parsed by the toolchain that compiles it.
printf 'by decide\n\n#eval 1\n' > "$work/command.proof"
expect "a command is refused by the compiling toolchain's parser" 1 "rejectedSubmission.*Lean 4|rejectedSubmission" \
  $ixai reward-submit "$bundle" identity "$work/command.proof"

# 5. `ixai reward` writes where it is told.
expect "reward writes its table to --out" 0 "wrote $work/rewards.tsv" $ixai reward "$bundle" --out "$work/rewards.tsv"
if [ "$(wc -l < "$work/rewards.tsv")" = 12 ] && [ "$(grep -c accepted "$work/rewards.tsv")" = 2 ]; then
  pass "reward table: 12 verdicts, the two honest valid proofs accepted"
else fail "reward table: $(cat "$work/rewards.tsv")"; fi

# 6. CLI arguments are checked.
expect "a chunk size of 0 is a usage error" 2 "positive integer" $ixai certified "$work" tiny 0
expect "a non-numeric chunk size is a usage error" 2 "positive integer" $ixai certified "$work" tiny x
expect "non-numeric format seeds are a usage error" 2 "comma-separated" $ixai formats a,b 1,2
expect "non-numeric learning rates are a usage error" 2 "comma-separated" $ixai formats 1 1,x

echo "$fails failure(s)"
exit $((fails > 0))
