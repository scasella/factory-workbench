#!/bin/sh
# FIXED build phase. Inputs: /in/src (read-only candidate snapshot prepared by the
# trusted materializer). Output: /out. Network is disabled and
# no credentials are mounted. Exit code is observed by the host verifier.
set -u
W=/work/pkg
rm -rf "$W"; mkdir -p "$W"
cp -R /in/src/. "$W"/
cp /opt/harness/lakefile.toml /opt/harness/FactoryExport.lean /opt/harness/lean-toolchain "$W"/
# discard any candidate-supplied build products or caches
rm -rf "$W/.lake" "$W/lake-manifest.json"
find "$W" -name '*.olean' -o -name '*.ilean' -o -name '*.c' | xargs rm -f 2>/dev/null
cd "$W"
lake build factory-package >/out/build.log 2>&1
rc=$?
echo "$rc" >/out/build.rc
[ "$rc" -eq 0 ] || exit 10
cp .lake/build/bin/factory-package /out/package.bin
/out/package.bin export >/out/export.json 2>>/out/build.log || exit 11
exit 0
