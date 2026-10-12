# Sources and conventions

Primary sources checked on 2026-10-09:

1. Vincent Vatter, *An Assortment of Problems in Permutation Patterns:
   Unimodality, Equivalence, Derangements, and Sorting*,
   [arXiv:2602.16355v2, Section 5](https://arxiv.org/html/2602.16355v2#S5).
   Theorem 5.9 gives the avoidance basis; Problem 5.11 asks for a direct
   mechanism-based derivation. The displayed minimal polynomial includes the
   empty permutation. The paper attributes the existing proof through
   Combinatorial Exploration to Jay Pantone (personal communication).
2. [OEIS A393395](https://oeis.org/A393395), offset 0: number of permutations
   sortable by a (2,2)-stack. It records the top-two-slot model, basis, and cubic.
   Use it for regression data, never as an independent implementation.
3. M. D. Atkinson, *Generalized stack permutations*, Combinatorics, Probability
   and Computing 7 (1998), 239–246,
   [DOI](https://doi.org/10.1017/S096354839800354X).
   Theorem 4.1 is cited by Vatter for the basis. Section 4 also provides a greedy sorting algorithm, reviewed in the later
   exact-model phase. Source attribution is not a new proof.

4. M. H. Albert, C. Homberger, J. Pantone, N. Shar, and V. Vatter,
   *Generating permutations with restricted containers*, Journal of
   Combinatorial Theory, Series A 157 (2018), 205–232,
   [arXiv:1510.00269, Section 1.4, Proposition 1.2](https://arxiv.org/html/1510.00269).
   This is relevant prior work on canonical operation histories. Its uniqueness
   argument is for leftmost-only popping; it does not automatically extend to
   the two-pop model studied here.

## Published basis

    23451, 23541, 32451, 32541,
    245163, 246153, 425163, 426153

An eventual basis recognizer must be implemented independently of the
mechanical search. Matching membership through a finite n is a consistency
check, not a fresh proof of the basis theorem.

## Orientation and multiplicity

A mechanical sorter starts with arbitrary input p and targets increasing
output. A generator starts with increasing input and permits arbitrary output
q. Relabelling values by the inverse of p maps a sorting history for p to a
generation history for q = inverse(p). Preserve this distinction in APIs and
reports.

A history records every push/pop and the selected zero-based slot. Different
histories can sort the same permutation, so a history-language grammar needs a
proved canonical representative or an explicit multiplicity correction before
it can enumerate permutations.
