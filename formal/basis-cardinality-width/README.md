# Finite-capacity basis cardinality and obstruction widths

This directory combines two independently accepted results, with 32 unchanged project sources after deduplicating their 20 common modules. It includes six unchanged independent semantic controls.

## Exact finite-capacity basis cardinality

For natural push/pop widths r,s with 0<r and 0<s and physical capacity H ≤ max(r,s)+1, the actual generated minimal-forbidden permutations over all lengths form finiteGeneratedBasis H and have H! elements. The inverse-image sortable-input basis finiteSortableBasis H has the same cardinality. Every obstruction has length H+1. Capacity zero is included: {[0]} is the basis and 0!=1.

In sources/FiniteCapacityBasisCardinality.lean, namespace StackSorting.Generalized.Unequal, finiteGeneratedBasis_all_sizes and finiteSortableBasis_all_sizes prove all-length identification with the original-machine predicates. finiteGeneratedBasis_exact and finiteSortableBasis_exact state the length-H+1 versions. finiteGeneratedBasis_card and finiteSortableBasis_card hold for every natural H; their interpretation as machine bases needs the positive-width and capacity hypotheses. This result does not add an unrestricted one-sided or (2,2) classification.

## Exact obstruction displacement widths

In sources/ObstructionFamilyWidths.lean, namespace StackSorting.Generalized:

- Unequal.family r s m has endpointWidth and generatedDisplacementWidth s+2 when 2≤r<s, for every natural m. Endpoints: Unequal.family_endpointWidth and Unequal.family_generatedDisplacementWidth.
- Equal.famA r k has both widths r+3 when r≥3, for every natural k. Endpoints: Equal.famA_endpointWidth and Equal.famA_generatedDisplacementWidth.
- Equal.famB r k has both widths r+2 under the same hypotheses. Endpoints: Equal.famB_endpointWidth and Equal.famB_generatedDisplacementWidth.

Corresponding family_boundedAt_iff, famA_boundedAt_iff and famB_boundedAt_iff characterize all endpoint bounds H. BoundedAt H p means p[i]+1≤H+i at each zero-based position. generatedDisplacementWidth is 1+max_i(max(p[i]-i,0)). For nonempty lists this equals endpointWidth; on the empty list their values are 1 and 0 respectively. The bridge therefore requires a positive endpoint width. These are displacement identities and exact endpoint bounds, not successful machine runs or least feasible physical stack capacities.

The cardinality review freshly replayed 21 sources; the width review freshly replayed 31 sources. Printed endpoint transitive axioms were limited to propext, Classical.choice and Quot.sound. These were scoped endpoint checks, not a declaration-by-declaration audit. The new combined replay retains the width packet's 2 GiB sampled RSS cap and -M1536 for its 31-source closure and three controls, and the cardinality packet's 4 GiB cap and -M3584 for its additional leaf and three controls. All stages require 6 GiB prelaunch availability and a 2 GiB live available-host floor. Neither historical packet imposed a wall timeout, so none is added here. Per-module profiles are pinned in SOURCE_MANIFEST.json.

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

This public source-only repackaging was checked statically and by offline integrity tests. Its new portable replay driver has not been used for a new full Lean rebuild during packaging. Historical acceptance applies to the exact unchanged Lean bytes and scopes described in ACCEPTANCE.json; it does not imply that this new driver has already completed. Endpoint axiom checks here do not reproduce the separate historical exhaustive recursive audit. Official compiler and installed Core/Std plus Mathlib/package cache objects are trusted; no claim is made that every external library cache byte was rebuilt or certified. SHA-256 manifests provide content binding, not a digital signature.

Historical draft comments within unchanged Lean sources may say that review was pending. The subsequent independent acceptance summarized here supersedes those time-local comments without changing source bytes. Raw historical logs, private execution paths and compiled artifacts are not included.
