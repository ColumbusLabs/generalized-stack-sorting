# Canonical histories as ordered forests

The finite check below is not a generating-function derivation. Atkinson's sorting algorithm is prior work.

## 1. Prior algorithm and orientation

Atkinson, *Generalized Stack Permutations* (1998), Section 4, gives a canonical
sorting algorithm in the proof of the basis theorem. The author-hosted version
was visually checked at PDF pages 7–8:
https://www.cs.otago.ac.nz/staffpriv/mike/Papers/Genstack/Genstack.pdf .

In our top-first convention its operational form is:

1. Pop the next required output if it is among the top two entries.
2. Otherwise push the next input above the old top if it is smaller, and below
   the old top if it is larger. With an empty stack there is only one slot.
3. Fail if neither operation is possible.

Thus the first two entries immediately after a push are increasing when read
top first. The source's phrase about decreasing order should not be copied
without an orientation warning: its following argument explicitly treats a
larger top above a smaller second entry as the noncanonical arrangement.
Putting the larger entry on top fails on the sortable input 2341.

We use Atkinson's theorem that this deterministic algorithm accepts precisely
the sortable permutations. Its uniqueness for each accepted input follows
immediately from determinism. This is prior work, not our new result.

## 2. Compression of canonical histories

Write P0 and P1 for pushes at zero-based positions, and O0 and O1 for pops.
Replace each immediately consecutive P0 O0 pair that inserts and removes the
same token by B, a bypass that consumes and outputs the next input token.
That token is necessarily the next required output, because the uncompressed
history sorts increasingly. Every B is introduced only by this replacement.

**Lemma 1.** Every immediate push-pop pair in a successful canonical history
is such a P0 O0 pair. After compression there is no adjacent Pj Ok pair.

**Proof.** P0 puts a smaller token above the old top, so a following O1 would
output the old, larger token before the new one, impossible in increasing
output. P1 puts a larger token below the old top, so following O1 is likewise
impossible. A P1 O0 pair would output the old top, which was already accessible
before the push, contrary to the pop priority. The only remaining possibility
is P0 O0. Compression leaves a B at every replacement site, so it cannot create
a new adjacent push-pop pair across that site. QED.

## 3. The constraint forest

An ordered rooted tree has a root and an ordered list of child trees. A leaf
has no children. An ordered forest is a list of such trees. Read nodes in
preorder, traversing each tree before the next one.

Start with the empty forest and a flag c = true. Every B or pop sets c = true;
every nonbypass push sets c = false. A pop requires c = true. Operations are:

- B: add a new input/output token, without changing the forest.
- P0, empty forest: insert one leaf as the sole tree.
- P0, nonempty forest: replace the first tree T by a new root whose sole child
  is T. Leave all later trees unchanged.
- P1, nonempty forest: add a new leaf as the first child of the first root.
- O0, nonempty forest: remove the first root, replacing its tree by its list
  of child trees, ahead of the remaining forest.
- O1: require at least two trees and require the first tree to be a leaf.
  Remove the second root and replace its tree by its child list. Keep the
  first leaf and all later trees in place.

P1 is unavailable on an empty forest. A complete path starts and ends with
the empty forest. Each B and each push introduces one distinct token. A pop
outputs the removed token; B outputs its own new token.

Every directed parent-child edge is a comparison obligation: the parent must
be output before its child. Edges do not assert relations between siblings.

**Lemma 2 (exact constraint update).** The forest operations are precisely the
top-two stack operations compatible with the comparison obligations imposed
by the canonical push rule.

**Proof.** Maintain the outstanding stack tokens in forest preorder. P0 places
a new token before the old top and obliges the new token to precede that old
top in output; wrapping the first tree records exactly this new edge. P1
inserts a new token second and obliges the old top to precede it; a new first
leaf child records exactly this edge. On an empty stack no edge is created.

The first preorder node is a root, so O0 may remove it and release all its
children as new roots. If the first tree is nontrivial, the second preorder
node is its first child and cannot be output while its parent remains. If the
first tree is a leaf, the second preorder node (if present) is instead the
root of the second tree, has no outstanding predecessor, and can be removed.
This is exactly the stated O1 rule. Removing a root loses no obligation
between remaining nodes; it only satisfies its outgoing obligations. QED.

## 4. Bijection

**Theorem 3.** Complete constraint-forest paths with the flag rule are in
size-preserving bijection with (2,2)-stack-sortable permutations.

**Forward map from a permutation.** Run Atkinson's deterministic successful
sorting algorithm and apply Lemma 1's compression. Record each canonical push
comparison by an edge as in Lemma 2. Since the output is increasing, every edge
is respected. Lemma 2 therefore gives a legal forest path; Lemma 1 gives the
flag rule. All n input entries correspond to n introduced tokens.

**Reverse map from a path.** Temporarily distinguish tokens by introduction
order. Give the first output token value 1, the second value 2, and so on.
Read these values in introduction order to obtain the input permutation.
Expand every B to P0 O0. Lemma 2 gives a legal stack history, and by construction
its output is increasing.

Every P0 comparison makes the new token's assigned value smaller than the old
top; every P1 comparison makes it larger. Thus every push uses the canonical
slot. A B also uses this slot on expansion: its newly assigned value is the
next output, hence smaller than every existing token.

It remains to prove the pop priority. Suppose a push occurs when the next
output token t is already accessible. Until t is emitted there can be no other
output. In the compressed path, all operations up to the output of t must
therefore be pushes, followed by a pop of t: B would output a different new
token. This forces an adjacent push-pop pair, contrary to the flag rule.
Consequently no such delayed accessible token exists. The expanded history
therefore is exactly the deterministic canonical sorting history of its input.

The two maps are inverse: token identities, introduction order, output order,
and each operation are preserved. Uniqueness comes from Atkinson's canonical
algorithm, not from counting all possible sorting histories. QED.

## 5. Exact recurrence, still infinite-state

Represent a tree by the tuple of its child trees, and a forest by a tuple of
trees. Let C(m,F,c) count completions using exactly m further input tokens.
Each push or B lowers m by one; each pop lowers the number of held nodes by
one. Thus the rank 2m + number_of_held_nodes strictly decreases on every move.
Sum C over the legal successors above. C(0,empty,c)=1; other states with no
legal move contribute zero.

`src/stack_sorting/forests.py` implements this recurrence using only the
standard library. It does not import the mechanical solver, avoidance basis,
or known generating-function coefficients. Running it at n=0 through 8 gave:

    1, 1, 2, 6, 24, 116, 628, 3636, 21956

It visited 552 memoized (m,F,c) states. The values agree with the published
sequence, but finite agreement is not the proof of the bijection.

Theorem 3 supplies a machine-derived, unambiguous combinatorial model.
This recurrence by itself has arbitrarily large forest states and is not a
generating-function derivation. A subsequent companion note,
`first-return-derivation.md`, supplies a binary-word quotient and an finite first-return derivation of the cubic. That later argument has separate
proof obligations; finite agreement here does not establish it.

The prior canonical algorithm can also be justified using the self-contained
exchange argument in `canonical-exchange.md`, a reproof of Atkinson's result.

## 6. Auxiliary drainability lemma

A top-first stack of distinct values can be emptied in increasing order using
top-two pops iff every entry has at most one larger predecessor. Necessity:
two larger predecessors could not disappear before that entry is emitted.
Sufficiency: the smallest remaining entry is among the first two, and deletion
preserves the condition, so induction empties the stack.

Equivalently, its standardization is a unique direct sum of blocks
H_k = k,1,2,...,k-1, including H_1 = 1. To see this, if the first value is k,
all values below k must occur in increasing order: a descent among them would
give its smaller value two larger predecessors. All these values also precede
any value larger than k, for the same reason. Hence the first block is H_k,
and induction applies to the remaining larger values. The decomposition is
the usual unique direct-sum decomposition.

Every stack state in any successful history is drainable. Delete all future
input tokens from the successful continuation. Deletion never increases a
remaining token's position, so its recorded pop stays within the top two.
The surviving pops give an increasing drain of the current stack.

These are elementary machine facts, included as proof tools without a novelty
claim. They are not a characterization of which remaining inputs are sortable
from a given state.

## Reproduce finite implementation checks

Run `PYTHONPATH=src python3 -m stack_sorting.forest_validation --max-n 6`.
This checks exact labelled-path
sets, uniqueness, canonical-history equality, and legal replay through n=6.
These checks support implementation fidelity; the proof above is separate.
