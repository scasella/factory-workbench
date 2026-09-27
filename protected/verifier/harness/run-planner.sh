#!/bin/sh
# FIXED planner-execution harness: runs an already-built package binary over
# a JSONL file of planner views. No network, no credentials, read-only inputs.
set -u
/pkg/package.bin plan </in/views.jsonl >/out/plans.jsonl 2>/out/planner.stderr
echo "$?" >/out/planner.rc
exit 0
