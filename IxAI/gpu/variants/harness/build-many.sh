#!/usr/bin/env bash
set -e
for v in "$@"; do /opt/dlami/nvme/ix-ai/review2-gpu/r2/build.sh $v; done
