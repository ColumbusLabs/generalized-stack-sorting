#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LEAN_BIN="${LEAN_BIN:-lean}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
python3 - "$work" <<'PYTHON'
import sys,json,hashlib,shutil
from pathlib import Path
for row in json.loads(Path('snapshot.json').read_text())['modules']:
 p=Path(row['module']+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
 shutil.copy2(p,Path(sys.argv[1])/p.name)
PYTHON
export LEAN_PATH="$work"
cd "$work"
for module in ForestWord LabelledForest OutputRanks OrderedTraces EagerTraces CanonicalUniqueness OriginalMachine RawExchange RawDeletion RawNormalization RawCanonical GeneralizedDeletion GeneralizedRawMachine GeneralizedCompatibility GeneralizedRelational GeneralizedLazy GeneralizedRangeLazy GeneralizedChecks TwoPushBlocks MaximumBlockDeletion IntervalMinimum RelabelledBlocks BlockPushClosure RankBlockTransitions SmallBlocks BlockCycles BlockTerminal InfiniteFamily RangeLazyInversion FamilyInitial FamilyCycles FamilyObstruction; do
  "$LEAN_BIN" -DwarningAsError=true -o "$work/$module.olean" "$work/$module.lean"
done
