#!/usr/bin/env bash
# Run prove.sh inside the prover image. Host paths are mounted at the same
# paths in the container so GitHub's file commands and the workspace need no
# translation. Prover state persists in ~/.ix-prover on the host, which is the
# container's HOME.
set -euo pipefail

state="$HOME/.ix-prover"
mkdir -p "$state"

docker run --rm --gpus all \
  --user "$(id -u):$(id -g)" \
  -v "$state:$state" -e HOME="$state" \
  -v "$GITHUB_WORKSPACE:$GITHUB_WORKSPACE" -w "$GITHUB_WORKSPACE" \
  -v "$RUNNER_TEMP:$RUNNER_TEMP" \
  -v "$GITHUB_ACTION_PATH:$GITHUB_ACTION_PATH:ro" \
  -e GITHUB_SHA -e GITHUB_REPOSITORY -e GITHUB_SERVER_URL \
  -e GITHUB_OUTPUT -e GITHUB_STEP_SUMMARY -e GITHUB_ACTION_PATH -e RUNNER_TEMP \
  -e IX_LIBRARIES -e IX_PR_NUMBER -e GH_TOKEN \
  "$IX_IMAGE" "$GITHUB_ACTION_PATH/prove.sh"
