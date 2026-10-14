# General positive-width Stack theorem

For every positive integer push/pop-width pair r,s, the actual distinct-output and sortable-input ordinary generating series are algebraic over RatFunc Q. Exact counting holds for every token count n, including n=0, where the empty permutation contributes one. Counts are distinct permutations, not operation histories.

The 607 project modules contain the constructed uniform-admissibility witness; this is not a conditional theorem assuming that witness. The final module is sources/PositiveWidthStackAlgebraicity.lean. In namespace StackSorting.GraphWidth.GeneralConstruction, the endpoints are stack_uniform_admissibility, stack_exact_count, stack_output_series_algebraic and stack_sortable_series_algebraic. Uniform admissibility is constructed for natural r,s; the physical counting and algebraicity conclusions require 0<r and 0<s.

The A.2 construction realizes one supported selector tuple. It does not prove that every arbitrary assignment to the optional selector sentence is sound; accepted-language soundness is established separately. The result is classical existence with coarse parameter-only bounds. No zero-width counting result or efficient extracted algorithm is claimed.

Independent final acceptance rebuilt all 607 project sources without author project objects, ran four semantic negatives, and completed 25 recursive-audit slices over 15,372 distinct safe roots and 46,373 dependencies. The only axioms were Classical.choice, Quot.sound and propext. The 122 runtime exclusions were root-enumeration inventory only, never permitted unsafe or partial logical dependencies. These historical facts are distinct from the portable replay status below.

The replay preserves the historical thresholds: at least 6 GiB available before each launch, at most 4 GiB sampled process-group RSS, a 2 GiB available-host floor and 120 seconds per compiler invocation. There is no internal Lean -M cap.

## Publication header correction (2026-10-14)

6 source headers in this package were revised to reflect completed historical acceptance. Original accepted hashes and revised publication hashes are distinct. Outside the initial documentation comment, each affected source is byte-identical to its original; the other source files remain unchanged. Independent review accepted these bounded documentation-only revisions after checking exact bytes outside each header, the pinned Lean module-docstring behavior, and the absence of relevant source-position-sensitive or documentation-reading hooks. Revised-source compilation was NOT_RUN_MEMORY_GATE: the unchanged prelaunch memory requirements prevented any compiler invocation. No new full project replay, recursive audit or identical compiled-object bytes are claimed. See COMMENT_ONLY_REVIEW.json.

## Portable replay

Use Linux, Python 3.9 or newer, the official Lean 4.34.1 Linux distribution, and a clean checkout of Mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612 with its lake-manifest-pinned packages and compiled library caches. The driver performs no download or installation. These dependencies must be prepared separately. TOOLCHAIN.json records exact revisions, the Mathlib manifest digest, and the pinned compiler/runtime files.

From this directory:

```sh
python3 -B replay.py --verify-only
python3 -B -m unittest test_replay -v
python3 -B replay.py --lean /path/to/lean-4.34.1-linux/bin/lean --mathlib /path/to/mathlib4 --output /path/to/new-output
```

The output directory must be new and outside this certificate. Replay copies every declared source into it, checks complete project import closure, excludes collisions with library paths, and freshly compiles the entire manifest in dependency order. No historical project .olean file is needed or accepted. Compiles are serial with -j1. Warning exceptions are limited to exact pinned sources and exact historical warning headlines. All printed axiom reports must stay within Classical.choice, Quot.sound and propext; required endpoints must be present. Positive controls must succeed; negative controls must fail with intended proof diagnostics, never because imports or resources are missing. Source and built-object hashes are checked again at completion.

The Linux /proc resource guard samples process groups every 0.2 seconds (0.05 seconds for the inherited scalar Core stage). It is not a hard operating-system limit. It requires 768 MiB free disk before replay, 256 MiB before each compiler launch and 128 MiB live capture headroom. Interrupted/failed runs are not accepted. Review captures go only into the requested output directory and should be inspected for local paths before sharing.

## Verification status and trust

This public source-only repackaging was checked statically and by offline integrity tests. Its new portable replay driver has not been used for a new full Lean rebuild during packaging. Historical acceptance applies to the original source hashes and scopes described in ACCEPTANCE.json. Later documentation-header-only revisions are mapped separately in COMMENT_ONLY_REVISIONS.json; they preserve all imports, declarations and proofs. Their separate documentation-only semantic review is recorded in COMMENT_ONLY_REVIEW.json. Fresh compilation of the revised sources was not run because the unchanged prelaunch memory gate was unmet. Endpoint axiom checks here do not reproduce the separate historical exhaustive recursive audit. Official compiler and installed Core/Std plus Mathlib/package cache objects are trusted; no claim is made that every external library cache byte was rebuilt or certified. SHA-256 manifests provide content binding, not a digital signature.

Seven obsolete review-status headers were corrected across the general and degree packages on 2026-10-14. This package records its affected source files, original accepted hashes, revised publication hashes and exact comment-only boundaries in COMMENT_ONLY_REVISIONS.json. Genuine local module-boundary caveats remain intact. Raw historical logs, private execution paths and compiled artifacts are not included.
