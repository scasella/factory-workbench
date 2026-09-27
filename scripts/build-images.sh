#!/bin/sh
# Build the pinned protected images and record their IDs in toolchains.lock.json.
# The Lean toolchain download happens here (bootstrap-time network); candidate
# builds/proofs later run with --network none. Protected source digests are
# baked into the verifier image as labels (what the image actually contains).
set -eu
cd "$(dirname "$0")/.."
if ! docker image inspect factory-lean-base:v4.34.1 >/dev/null 2>&1; then
  docker build -t factory-lean-base:v4.34.1 -f protected/runner-profiles/images/lean-base.Dockerfile protected/runner-profiles/images
fi
# shellcheck disable=SC2046
docker build $(node scripts/source-identities.ts) -t factory-verifier:dev -f protected/runner-profiles/images/verifier.Dockerfile protected
node scripts/update-lock.ts
