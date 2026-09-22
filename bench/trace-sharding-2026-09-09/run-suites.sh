#!/bin/bash
set -u
export PATH=/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin:$PATH
cd /home/ubuntu/ix-work
L=/home/ubuntu/ix/bench-2026-09-09/logs/suites.log
{ lake build IxTests && lake exe IxTests; echo "exit=$?"; } > $L 2>&1
