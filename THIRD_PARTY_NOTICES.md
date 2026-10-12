# Third-party dependencies and attribution

The manuscript bibliographies identify prior mathematical results. Citing a paper does not include or re-license that paper.

The repository contains original project sources; it does not vendor Lean, Lean Core/Std, mathlib, SymPy, python-flint, Python, TeX Live, Pandoc, or their compiled binaries. Install those dependencies from their official distributions or reputable package registries. Their own copyright notices and licenses continue to apply.

- Lean 4.34.1 and Core/Std: https://github.com/leanprover/lean4
- The `(2,2)`/capacity certificate uses mathlib at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`; its complete transitive lockfile is `formal/lake-manifest.json`: https://github.com/leanprover-community/mathlib4
- Exact symbolic replay uses SymPy 1.14.0 and python-flint 0.9.0: https://www.sympy.org/ and https://python-flint.readthedocs.io/
- PDF production uses standard TeX packages and BibTeX; Markdown conversion uses Pandoc.

The MIT grant for this project's original code does not change any dependency's license or waive attribution owed to third parties.
