# Self-contained exchange proof for the prior canonical sorter

This reproves the canonical sorting rule used by Atkinson (1998), Section 4. Stacks are written top first, input values are distinct, the unread input order is fixed, and the target output is increasing.

## Eager-output lemma

If the next required output m is currently in either accessible slot and the
configuration has a successful continuation, there is a successful
continuation that outputs m immediately.

**Proof.** Before the original continuation outputs m it cannot output any
other symbol. It therefore performs only pushes. Remove m now and simulate
those pushes with m omitted from each intermediate stack. For a push at slot
j in {0,1}, use slot j minus one if the omitted m was before that insertion
point, and slot j otherwise. The resulting slot remains legal and is at most
one. When the original continuation pops m, omit that operation. The two
configurations now coincide, with the same unread input. Continue identically.
The output order is unchanged. QED.

## Top-pair exchange lemma

Let x<y and let R be any fixed stack suffix. For the same unread input and
next-output requirement, if (y,x,R) has a successful continuation, then
(x,y,R) has a successful continuation.

**Proof.** Follow a successful continuation from (y,x,R) until it outputs x.
The symbol y cannot be output during this interval, because y>x. Relative
order among existing stack entries never changes, so y stays above x.

Every input token z pushed during this interval lies above x: x already has
at least y above it, and every legal insertion is in slot 0 or 1. Moreover
every such z is smaller than x. Otherwise z and y would both remain above x
until x's output, since neither could be output earlier in increasing order;
then x could not be among the accessible top two, a contradiction.

Thus all tokens pushed in this interval are output before x. No entry of R
can be output before x, since x and y both remain above every entry of R.

For each intermediate original stack, construct the simulated stack by
deleting y and reinserting it immediately below x. This construction starts
at (x,y,R). A push before x remains a push in slot 0 or 1 after deleting y;
the adjusted slot is its original slot minus one precisely when y preceded
the original insertion point. Reinserting y below x does not affect that
slot. Every pop before x removes a newly pushed token above x, and deleting y
can only lower its position. Hence all simulated operations are legal.

Immediately before x is output, all newly introduced tokens have been
removed. The original stack is (y,x,R), the simulated stack is (x,y,R).
Pop x from slot 1 in the former and slot 0 in the latter. Both then have
(y,R), the same unread input, and the same output prefix. Complete the
simulation using the original remaining continuation. QED.

## Canonical sorting theorem

The following deterministic algorithm sorts every (2,2)-stack-sortable input:

1. Output the next required value immediately if it is in the first two slots.
2. Otherwise push the next unread input, placing the smaller of that value and
   the previous top above the larger. For an empty stack use its sole slot.
3. If neither move is available, reject.

**Proof.** Maintain existence of a successful continuation. Rule 1 preserves it
by the eager-output lemma. If the next required output is not accessible, any
successful continuation must next push the next unread input. There are at
most two placements; after that push they have the same suffix and differ only
in the ordering of the top two entries. The top-pair exchange lemma says that
the smaller-on-top placement is at least as capable as the other placement.
Thus rule 2 also preserves existence. The algorithm performs exactly one
push and one pop per input entry on success; it cannot run forever. Starting
from a sortable input it cannot reach a rejected state, because such a state
has no successful continuation. Conversely every accepted run is itself a
legal sorting history. QED.

For a fixed input each move is uniquely determined. This proves the exact
existence and uniqueness needed by the forest bijection, independently of
any finite experiment or forbidden-pattern theorem.

Prior source: M. D. Atkinson, *Generalized Stack Permutations*, Combinatorics,
Probability and Computing 7 (1998), 239–246, Section 4.
https://www.cs.otago.ac.nz/staffpriv/mike/Papers/Genstack/Genstack.pdf
