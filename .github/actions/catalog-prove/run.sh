#!/usr/bin/env bash
# Run prove.sh inside the prover image. Host paths are mounted at the same
# paths in the container so GitHub's file commands and the workspace need no
# translation. Prover state persists in ~/.ix-prover on the host, which is the
# container's HOME.
set -euo pipefail

state="$HOME/.ix-prover"
mkdir -p "$state"

# Upload credentials for the proof bucket live on the runner, not in callers.
aws=()
if [[ -f "$HOME/.aws/credentials" ]]; then
  aws=(-v "$HOME/.aws/credentials:/run/aws-credentials:ro"
    -e AWS_SHARED_CREDENTIALS_FILE=/run/aws-credentials)
fi

# Containers live under the Docker daemon's cgroup, not the runner service's,
# so the memory ceiling is set here; ix's automatic budgeting plans within it.
docker run --rm --gpus all --memory=950g \
  --user "$(id -u):$(id -g)" \
  -v "$state:$state" -e HOME="$state" \
  -v "$GITHUB_WORKSPACE:$GITHUB_WORKSPACE" -w "$GITHUB_WORKSPACE" \
  -v "$RUNNER_TEMP:$RUNNER_TEMP" \
  -v "$GITHUB_ACTION_PATH:$GITHUB_ACTION_PATH:ro" \
  -e GITHUB_SHA -e GITHUB_REPOSITORY -e GITHUB_SERVER_URL \
  -e GITHUB_OUTPUT -e GITHUB_STEP_SUMMARY -e GITHUB_ACTION_PATH -e RUNNER_TEMP \
  -e IX_LIBRARIES -e IX_PR_NUMBER -e GH_TOKEN "${aws[@]}" \
  "$IX_IMAGE" "$GITHUB_ACTION_PATH/prove.sh"
