# The actual `(3,3)` counting equation

`SOURCE_MANIFEST.json` identifies every one of the 1,613 Lean modules, its SHA-256 hash, imports, recursive closure hash and compile order. The sources total 97,526,535 bytes. They are provided transparently under `sources/`.

Verify the exact source closure without invoking Lean:

    python3 verify_sources.py

For source-only compilation, install the official Lean 4.34.1 compiler. Then:

    LEAN_BIN=/absolute/path/to/lean-4.34.1/bin/lean CHECK_WORK_ROOT=/scratch/path bash check.sh

Choose a writable scratch directory outside the immutable source distribution. The harness copies sources to a fresh isolated build, records each compiler result, compares the four pinned warning exceptions with `WARNING_POLICY.json`, and audits the two endpoint axiom reports. It does not reuse supplied project objects.

The sampled resource guard limits the process group to 3 GiB RSS, requires a 1.5 GiB host-available floor during execution and checks for at least 6 GiB available memory before each compiler launch. This is a sampled safeguard, not a hard OS limit. Both the replay summary and guard result must pass; preserve unsuccessful attempt records as well as successful ones.

The precise theorem scope is the all-length literal unrestricted-height `(3,3)` distinct-output count and coefficientwise scalar relation. It is narrower than the combined written results in the paper.
