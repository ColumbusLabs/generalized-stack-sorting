#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
: "${LEAN_BIN:?Set LEAN_BIN to a Lean 4.34.1 executable}"
# Obtain any compiler-resource authorization required by your environment.
# Source-only build under the unchanged sampled 3 GiB group / 1.5 GiB host guard.
python3 verify_sources.py
mkdir -p "${CHECK_WORK_ROOT:-replays}"
base=$(cd "${CHECK_WORK_ROOT:-replays}" && pwd)
run=$(mktemp -d "$base/check-XXXXXX")
printf 'All diagnostics and failures will remain in: %s\n' "$run"
python3 rss_guard.py --output "$run/guard" --rss-limit 3221225472 --host-floor 1610612736 -- \
  python3 -B replay.py --lean "$LEAN_BIN" --output "$run/replay"
python3 - "$run" <<'PYVERIFY'
from pathlib import Path
import json
import sys
run = Path(sys.argv[1])
summary = json.loads((run / 'replay/SUMMARY.json').read_text())
guard = json.loads((run / 'guard/result.json').read_text())
assert summary['status'] == 'SOURCE_ONLY_REPLAY_PASS'
assert summary['source_modules'] == 1613 and summary['project_object_reuse'] is False
assert summary['original_source_manifest_sha256'] == '1838e0116265d52060fcba3524da8afedef36b31cff0b8e42352c7b60fd1862d'
assert guard['status'] == 'passed' and guard['exit_code'] == 0
assert guard['remaining_live_group_members'] == []
assert guard['peak_sampled_group_rss_bytes'] <= guard['rss_limit_bytes'] == 3221225472
assert guard['minimum_mem_available_bytes'] >= guard['host_floor_bytes'] == 1610612736
print('Verified source-only summary and successful clean guard termination.')
PYVERIFY
printf 'Completed source-only replay: %s\n' "$run"
