# Reproduction guide

Run from the repository root unless otherwise stated. Keep the downloaded release unchanged; place generated files and logs in disposable scratch directories. Python assertions are part of the checkers, so do not use `python -O`.

## 1. Verify the distribution

With Python 3.10 or later:

    python3 verify_release.py
    python3 formal/actual-scalar-equation/verify_sources.py
    python3 research/direct-counting-equation/run_replay.py --verify-only

These commands verify source hashes and closure. They do not invoke Lean or prove the mathematical claims themselves.

## 2. Bounded implementation checks

The Python model uses the standard library. From a disposable copy:

    python3 -m unittest discover -s tests -v
    PYTHONPATH=src python3 -m stack_sorting
    python3 -m compileall -q src tests
    python3 papers/algebraicity/check_manuscript.py

The 120 regression tests exercise literal finite reachability, exact encodings, deletion histories and supporting equation fixtures. The manuscript checker re-expands the displayed 69-term polynomial, checks its selected-branch blowup and recomputes the finite-field irreducibility test. These commands do not rerun the Lean certificates. The general positive-width theorem and exact-degree conclusion have their own source-only formal replay below.

## 3. Exact symbolic replay

Use Python 3.12 with SymPy 1.14.0 and python-flint 0.9.0, installed from their official package distributions. For example, create a dedicated virtual environment and install the two pinned packages with pip. Then:

    python3 research/direct-counting-equation/run_replay.py --output /scratch/new-direct-equation-replay

Replace the output placeholder with a new directory outside this repository. The six drivers check exact divisions, the branch, reversible reconstruction, the displayed polynomial, irreducibility and negative controls. The original per-driver resource safeguards remain in force. The runner preserves each output and failure log. Supporting written arguments remain in `research/full-class-equation/author/` and `docs/`.

## 4. Source-only Lean reproduction

The `(3,3)` endpoint requires the official Lean 4.34.1 compiler and Core/Std. No mathlib installation is needed for this endpoint. First read `formal/actual-scalar-equation/README.md`, then:

    cd formal/actual-scalar-equation
    LEAN_BIN=/absolute/path/to/lean-4.34.1/bin/lean CHECK_WORK_ROOT=/scratch/lean-replays bash check.sh

The harness compiles the exact 1,613-module closure in an isolated directory, checks the expected warning policy, records every result, and checks the two endpoint axiom reports. Resource requirements and the sampled guard are documented beside the harness. Both the compilation summary and guard result must pass.

The completed general theorem, exact-degree extension, and finite-side basis extension have separate portable source-only packets:

- `formal/general-positive-width/`: exact actual counts and algebraicity for every fixed positive width pair; 607-module source closure.
- `formal/actual-count-degree-twelve/`: original-machine `(3,3)` generated and sortable counting series, literal branch, irreducibility and exact degree 12.
- `formal/basis-cardinality-width/`: finite-side basis cardinalities and exact explicit-family widths.

Read each packet's README before running its parameterized replay. Supply the official Lean 4.34.1 executable and, where required, the pinned mathlib checkout/cache; no machine-specific path is assumed. Replays use isolated output directories and preserve resource safeguards. Source-integrity checks alone are not compilation. See [CLAIMS.md](formal/CLAIMS.md) for the exact accepted scope and provenance of each source set.

The smaller companion certificates have separate commands:

    cd formal
    lake build
    bash check-enumeration.sh
    bash check-capacity-enumeration.sh
    bash generalized/check-generalized-obstruction.sh
    bash unequal/check-unequal-basis.sh
    bash equal/check-equal-basis.sh
    bash container/check-container-basis.sh

Inspect the scripts before running them. The root mathlib requirement is pinned in `lakefile.toml` and `lake-manifest.json`; use those pinned dependencies rather than upgrading them. Core/Std companion scripts do not require mathlib. A successful check of one certificate does not certify a different theorem family.

## 5. Rebuild the papers

Install standard TeX Live packages (`article`, AMS, Latin Modern, geometry, microtype, hyperref, mathtools, enumitem, needspace, booktabs, longtable and natbib), plus BibTeX. In `papers/algebraicity/`:

    pdflatex generalized-stack-algebraicity.tex
    bibtex generalized-stack-algebraicity
    pdflatex generalized-stack-algebraicity.tex
    pdflatex generalized-stack-algebraicity.tex

For each companion, run `pdflatex` twice on its TeX file in that paper's directory. The companion bibliography is embedded. After regenerating a Markdown reading copy from the TeX, preserve its GitHub-compatible math blocks, linked citations, and section anchors, and check the rendered GitHub page. Inspect rendered pages after changing content; a successful build is not a visual-layout check.

## Interpreting results

Source-integrity checks establish exact-byte consistency. Finite tests establish their stated finite bounds. Exact symbolic replay establishes the identities and certificate checks it executes. Lean checks the precise statements of the included formal theorems. Written arguments outside those theorem statements retain their separately stated scope.
