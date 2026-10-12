#!/usr/bin/env bash
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
lean_bin=${LEAN_BIN:-lean}
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
"$lean_bin" --version
for module in ForestWord LabelledForest OutputRanks OrderedTraces EagerTraces CanonicalUniqueness OriginalMachine RawExchange RawDeletion RawNormalization RawCanonical ForestCompleteness RawWiring OperationWords FiniteWords FirstReturnTrees CompleteGrammar GrammarPermutations; do
  LEAN_PATH="$build" "$lean_bin" -DwarningAsError=true \
    -o "$build/$module.olean" "$here/$module.lean" | tee "$build/$module.log"
  if grep -q 'sorryAx' "$build/$module.log"; then
    echo "Proof hole detected in $module" >&2
    exit 1
  fi
done
