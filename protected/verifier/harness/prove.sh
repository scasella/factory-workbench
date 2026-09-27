#!/bin/sh
# FIXED proof phase: fresh snapshot, compile with the trusted statement bridge,
# report axioms, then independently replay with leanchecker --fresh.
set -u
W=/work/pkg
rm -rf "$W"; mkdir -p "$W"
cp -R /in/src/. "$W"/
cp /in/FactoryBridge.lean "$W"/FactoryBridge.lean
cp /opt/harness/lakefile.toml /opt/harness/FactoryExport.lean /opt/harness/lean-toolchain "$W"/
rm -rf "$W/.lake" "$W/lake-manifest.json"
find "$W" -name '*.olean' -o -name '*.ilean' -o -name '*.c' | xargs rm -f 2>/dev/null
cd "$W"
lake build FactoryBridge >/out/prove.log 2>&1
rc=$?
echo "$rc" >/out/prove.rc
[ "$rc" -eq 0 ] || exit 20
# axiom report: a separate trusted file (not candidate-controlled) elaborated
# after the bridge; only its messages are parsed.
lake env lean /in/Audit.lean >/out/axioms.txt 2>&1
arc=$?
echo "$arc" >/out/axioms.rc
[ "$arc" -eq 0 ] || exit 21
lake env leanchecker --fresh FactoryBridge >/out/leanchecker.log 2>&1
lrc=$?
echo "$lrc" >/out/leanchecker.rc
[ "$lrc" -eq 0 ] || exit 22
exit 0
