#!/usr/bin/env bash
# Verify pinned source hashes, then compile from an empty temporary directory.
# Core/Std only; one compiler thread, with warnings treated as errors.
set -euo pipefail
cd "$(dirname "$0")"
LEAN_BIN="${LEAN_BIN:-lean}"
if ! "$LEAN_BIN" --version | grep -q "version 4.34.1,"; then
  echo "This certificate is pinned to Lean 4.34.1; got: $("$LEAN_BIN" --version)" >&2
  exit 1
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
order=$(python3 - "$work" <<'PYTHON'
import sys, json, hashlib, shutil
from pathlib import Path
data = json.loads(Path('snapshot.json').read_text())
for row in data['modules']:
    p = Path(row['path'])
    assert hashlib.sha256(p.read_bytes()).hexdigest() == row['sha256'], str(p)
    shutil.copy2(p, Path(sys.argv[1]) / (row['module'] + '.lean'))
print(' '.join(data['build_order']))
PYTHON
)
export LEAN_PATH="$work"
cd "$work"
"$LEAN_BIN" --version
for module in $order; do
  echo "Checking $module"
  "$LEAN_BIN" -j1 -DwarningAsError=true -o "$work/$module.olean" "$work/$module.lean"
done
echo "All 33 modules compiled with warnings as errors."
