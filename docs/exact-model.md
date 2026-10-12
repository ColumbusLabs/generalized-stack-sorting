# Exact mechanical model and first checks

An exact finite oracle for the mechanical model. The structural enumeration is in [first-return-derivation.md](first-return-derivation.md).

## State and correctness contract

The input is a permutation of 1..n. A state `(i, stack)` stores the consumed
prefix length and a top-first tuple of entries still in the stack. The output
prefix is implicit: exactly `i - len(stack)` values have been emitted, in
increasing order. The next required output is therefore
`i - len(stack) + 1`.

The search tries each legal input insertion slot (0 or 1), and each legal
output slot (0 or 1) containing that next value. An empty stack allows only
insertion slot 0. Only existing entries may be removed. Its transition helper
is private and assumes a reachable state with the stated invariant.

Every transition raises `2*i - len(stack)` by one. This measure starts at zero
and ends at 2n, so recursion is acyclic. Every legal sorting history follows
these transitions, and every accepting search path is a legal sorting history.
Memoization merges equal states without merging input permutations. Returning
one witness is sufficient for membership. `history_count` instead adds all
accepting suffix counts, preserving incoming-path multiplicity; those totals
must never be used as permutation counts.

`replay` is an independent mutable-list interpreter. It validates operation
kind, slot, and input/stack availability and requires all input consumed and
the stack empty. It returns the actual output rather than assuming it sorted.

## Independent checks

The mechanical search never calls the pattern oracle or greedy recognizer.
The pattern oracle separately checks subsequences for the published eight
forbidden patterns. The generator independently explores increasing-input
output-prefix states, deduplicating equal generated permutations. Its output
must be inverted before membership comparison with sortable inputs.

The bounded validation checks all
46,234 input permutations across lengths 0..8. The counts are

    1, 1, 2, 6, 24, 116, 628, 3636, 21956.

No membership disagreement or failed witness replay occurred. Distinct-output
generation agrees after inversion through length 6. These are consistency
checks against prior results, not new counts or an all-length proof.

## Atkinson's existing greedy algorithm

Atkinson's 1998 paper, Section 4 (PDF page 7), supplies a greedy algorithm.
Our explicit top-first implementation is:

1. If the next required output is in either accessible slot, pop it.
2. Otherwise, consume the next input x. If the stack is empty or x is smaller
   than its top, insert x at the top; otherwise insert it immediately below.
3. Reject if input is exhausted and the next required output is inaccessible.

The first two entries after a push are therefore increasing top-to-bottom.
The paper's ordering prose is easy to misread across stack orientations; the
operational rule above is the convention actually tested here. The reversed
inequality fails on 2341. We attribute the algorithm to Atkinson and do not
claim it as a new canonicalization theorem.

The implementation agrees with exhaustive reachability through n=8 and its
accepted histories are independently replayed. The structural enumeration argument is separate from the sorting algorithm;
see the subsequent first-return derivation.

Source: [Atkinson author-hosted PDF](https://www.cs.otago.ac.nz/staffpriv/mike/Papers/Genstack/Genstack.pdf).
See also [the source list](references.md).

## Minimal cautions for candidate grammars

For input 12, there are three accepting slot-labelled histories:

    P0 O0 P0 O0
    P0 P0 O1 O0
    P0 P1 O0 O0

For input 21 there are two. Thus raw histories total five at length two while
there are only two sortable permutations. A grammar of all legal histories
cannot be treated as an unambiguous permutation grammar.

A policy that pops the next value when available and always pushes at the top
otherwise fails on the sortable input 2341. Always pushing in the second slot
when possible fails on 3241. Exhaustive search establishes minimality in
length and returns the first lexicographic example of each policy through
length four. Witnesses are in the evidence JSON. These examples refute only
those particular policies; they do not refute value-dependent canonical rules.

## Reproduction

```sh
python3 -m unittest discover -s tests -v
PYTHONPATH=src python3 -m stack_sorting.experiments --max-n 8 --generation-max-n 6
```

Run finite checks in a disposable local working copy.
The exhaustive experiment command refuses bounds above 8; the generator bound
is capped at 6. The separate fixed-policy counterexample search always runs
through length 4, even when the membership census bound is smaller. API functions are intended for small research inputs and do
not promise practical scaling. The finite record includes code hashes, Python
version, timestamps, and elapsed time by length.
