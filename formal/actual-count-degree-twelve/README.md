# Actual physical (3,3) counting series have exact degree twelve

The all-length ordinary series for distinct outputs and one-based raw sortable input permutations of the original unrestricted-height (3,3) machine equal the concrete literal branch. Both satisfy the unchanged 69-term scalar polynomial, are integral over RatFunc Q, and have minimal-polynomial degree exactly 12 in LaurentSeries Q. Every nonzero annihilating polynomial over RatFunc Q has degree at least 12.

These statements quantify over all natural indices, not a finite coefficient fit. The empty permutation contributes one, and negative-index Laurent coefficients are zero. Membership uses the original physical Run and CanSort predicates, with duplicate-free permutation lists and proved inverse orientation plus one-based relabeling. No root hypothesis is supplied to the final degree endpoints.

The final module is sources/ActualCountsDegreeTwelve.lean, in namespace StackSorting.MathlibSeriesBridge. Required endpoints include generatedCounts_minpoly_degree, sortableCounts_minpoly_degree, generatedCounts_annihilator_degree and sortableCounts_annihilator_degree; the complete required root/integrality/identification audit list is in SOURCE_MANIFEST.json.

## Complete source closure

This package uses 1,649 project modules: all 1,613 unchanged sources in the sibling ../actual-scalar-equation/sources directory, plus 36 local source files. Keep the repository layout intact. The shared source files are each pinned directly in this manifest and are copied from source into a new isolated build by the driver. No private build or inherited project object is needed. Eleven modules shared by the historical 1,613-source Core and 38-source branch packets were deduplicated only after exact hash comparison.

Historical independent acceptance freshly rebuilt nine join/control modules, hash-validated the 1,640 inherited identities against the completed Core replay and accepted literal replay, and ran semantic controls. It did not independently recompile all 1,649 sources a second time. The new public driver supports that complete fresh rebuild; packaging did not execute it.

Replay preserves each inherited stage: the 1,613 Core modules use a 3 GiB sampled compiler-plus-controller RSS cap, at least 6 GiB prelaunch availability and no internal -M cap; the 27 additional branch modules use 4 GiB, 6 GiB prelaunch and -M3584; the nine joins and ten semantic controls use 5 GiB, 7 GiB prelaunch and -M4608. The live available-host floor is 2 GiB throughout, stricter than the older Core stage's 1.5 GiB. No wall timeout is imposed; long inherited scalar-certificate modules may take substantial time. The per-module resource profiles are pinned in SOURCE_MANIFEST.json.

## Publication header correction (2026-10-14)

1 source headers in this package were revised to reflect completed historical acceptance. Original accepted hashes and revised publication hashes are distinct. Outside the initial documentation comment, each affected source is byte-identical to its original; the other source files remain unchanged. Independent review accepted these bounded documentation-only revisions after checking exact bytes outside each header, the pinned Lean module-docstring behavior, and the absence of relevant source-position-sensitive or documentation-reading hooks. Revised-source compilation was NOT_RUN_MEMORY_GATE: the unchanged prelaunch memory requirements prevented any compiler invocation. No new full project replay, recursive audit or identical compiled-object bytes are claimed. See COMMENT_ONLY_REVIEW.json.

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
