# Exact composition states for every (2,s)-stack

Here `s >= 2`; the one-pop case is classical. The written proof is separate from finite experiments and does not establish historical novelty.

## 1. Statement and scope

Take increasing input `1,2,...,n` and a single generalized `(2,s)`-stack, written
top first. For each fixed output prefix, first normalize histories so that no
input larger than the maximum output so far has been read. The set of all
possible current physical stack orders has an exact representation by an
ordered composition of the held values into consecutive rank intervals.
Each interval has independently all stack orders obtainable by top-two pushes.

The following explicit transitions maintain this representation exactly. They
therefore give a deterministic recognition algorithm for the generated outputs,
and, after permutation inversion, for the sortable inputs. A direct list
implementation uses `O(n^2)` elementary operations and `O(n)` integer storage
for an input of length `n`. This is a complete all-length recognition result,
not a claim that the earlier first-larger greedy sorting policy is complete.

The result also yields finite exact automata for every physical capacity `H`.
General bounded-storage rationality has substantial prior literature and is
not claimed as new here. This argument does not establish an algebraic
generating function, a finite forbidden basis, or a full basis classification
for unbounded `(2,s)`-stacks.

## 2. Lazy-input normalization

The next lemma holds for every `(r,s)` with positive parameters.

**Lemma.** If increasing input can generate an output permutation with physical
capacity `H`, then it can do so with the same capacity while reading new inputs
only when the next requested output is a new maximum, and then reading exactly
up to that maximum before outputting it.

**Proof.** Consider adjacent operations `push(x), pop(y)` with `x != y`.
The token `y` already existed before the push. Swap their order. If `y` was
above the original insertion position, lower that insertion position by one;
otherwise keep it. The pop position before the push is at most its original
position, so it is still among the first `s`. The adjusted push position is
nonnegative, does not exceed `r-1`, and is a valid position in the shorter
stack. The two operations give the same final stack. Their intermediate height
has decreased from `h+1` to `h-1`, so capacity has not increased.

Normalize outputs from left to right. Between two consecutive pops there is
only a run of pushes. Move its unnecessary final pushes to the right of the
next pop by these swaps, preserving their order. If the requested output is
already held, all these pushes are unnecessary. If it is a new maximum `v`,
exactly the pushes through `v` are necessary, and the pushes of values greater
than `v` can be postponed. This fixes one further output boundary without
changing earlier boundaries. Induction yields the claimed history. QED.

There is consequently a unique *output code* for each permutation `p`:

- If the next output `v` exceeds the previous output maximum `M`, use `N_b`
  with `b=v-M`. Read the next `b` input tokens and output the last one.
- Otherwise use `H_k`, where `k` is the ascending rank of `v` among currently
  held values. Read nothing and output that held token.

One code letter emits one output. Codes describe the permutation, not a choice
of physical history. Starting with `M=0` and an empty held set, these rules also
decode any complete valid code uniquely. A code is complete exactly when its
held set is empty. Then its output is a permutation of `1,...,n`, where `n`
is the number of code letters.

## 3. A stack-order block

Let `C_a` be the set of physical orders obtained by pushing `1,...,a` into
positions zero or one, with no pops. Put `C_0={()}`.

**Block description.** Partition `1,...,a` into consecutive nonempty intervals.
List the intervals from highest to lowest. Within each interval `[l,u]`, list

    l, u, u-1, ..., l+1.

The resulting stack orders are exactly `C_a`, one for each interval partition.

**Proof.** For `a=0,1` the statement is immediate. Inserting a new maximum at
position zero starts a new highest singleton interval. Inserting it at
position one extends the highest interval: its minimum remains first and the
new maximum precedes that interval's descending tail. These two operations are
inverse to deleting the maximum and determining whether its interval was a
singleton. Induction proves the description and uniqueness. QED.

Thus `|C_a|=2^(a-1)` for `a>0`. In the familiar maximum-deletion bit encoding,
a composition state below is a Boolean cube: each bit is either free or
forced to be zero. This observation alone is not the proof of the transitions.

## 4. Restricted deletion from one block

Within `C_a`, suppose only the first `t` physical entries are accessible, where
`1 <= t <= a`. Delete the token of ascending rank `k`, `1 <= k <= a`, and
standardize the remaining ranks. The set of resulting orders is precisely the
composition of `C`-blocks described by

    D(a,k,t) = (a-1)                         if k > a-t+1,
    D(a,k,t) = (t-1, 1^(a-t-k+1), k-1)      if k <= a-t+1.

Zero-size parts are omitted, and `1^m` means `m` singleton parts. If a requested
pop has more than `a` positions available, replace `t` by `a` first.

**Proof.** If `k` is not the minimum of its interval `[l,u]`, its zero-based
physical position is

    (a-u) + 1 + (u-k) = a-k+1.

If `k` is the minimum, its position is `a-u`, which is no greater.

For `k > a-t+1`, every occurrence of `k` is therefore accessible. Deleting it
from any interval-partition order gives an interval-partition order on the
remaining ordered set: if it was an interval minimum, its descending remainder
is a string of singleton intervals; otherwise delete it from the descending
tail. Conversely, every interval partition on the remaining ranks lifts to an
interval partition before deletion: if the gap at `k` lies inside an interval,
insert `k` in that interval; if it lies at an interval boundary, insert the
singleton interval `{k}`. Consequently the image is all `C_(a-1)`.

For `k <= a-t+1`, accessibility is impossible unless `k` is its interval's
minimum. Write that interval `[k,u]`. Its position is `a-u<t`, so
`u >= u_0 = a-t+1`. Deleting `k` leaves arbitrary interval-partition orders on
the values above `u`, followed by the descending string `u,...,k+1`, followed
by arbitrary interval-partition orders below `k`. Thus for fixed `u` the image
is the composition

    (a-u, 1^(u-k), k-1).

As `u` ranges from `u_0` to `a`, these sets are all contained in the set for
`u=u_0`: forcing additional singleton cuts inside its highest `C_(t-1)` block
only restricts the set. The union is therefore exactly the `u_0` set, which
is the stated formula. QED.

## 5. Composition states and exact transitions

A composition `c=(a_1,...,a_j)` of `h` denotes the following set `S(c)` of
physical stacks on the currently held ordered values. Divide those values
into intervals of ranks, with the highest interval of size `a_1`, the next
highest of size `a_2`, and so on. Independently select a `C_(a_i)` order inside
each interval, and concatenate the blocks from highest to lowest. The empty
composition denotes the singleton set containing the empty stack.

The complete determinized transition rules are:

**New maximum.** For `N_b`, with `b>=1`,

    (a_1,a_2,...) -> (a_1+b-1,a_2,...)      if c is nonempty,
    ()           -> (b-1)                  if b>1,
    ()           -> ()                     if b=1.

A physical capacity `H` permits this action precisely when `h+b <= H`.

**Held output.** For `H_k`, identify the block `a_i` containing ascending rank
`k`. Let `p=a_1+...+a_(i-1)` be the number of values in the higher blocks,
let `q=h-p-a_i` be the number in lower blocks, and put `k'=k-q`.

- If `p>=s`, the action is impossible.
- Otherwise replace `a_i` by `D(a_i,k',min(s-p,a_i))`, retaining all the
  other parts in their original order.

Different letters that lead to the same successor remain distinct letters.
They represent different output values and must not be merged when counting.

**Theorem (exact state representation).** For every code prefix, either it is
infeasible, or the set of physical stacks reachable by its normalized histories
is exactly `S(c)`, where `c` is obtained by the preceding deterministic rules.
The statement also holds with any fixed physical capacity `H`.

**Proof.** Initially the assertion holds for the empty composition. Pushing one
new maximum through either of the first two positions enlarges the highest
block from `C_a` to `C_(a+1)`, leaving all lower blocks unchanged. When the
stack is empty it creates `C_1`. The last token of a new-maximum batch was
inserted at position zero or one. Since `s>=2`, it can always be popped;
deleting it gives back exactly the state before its insertion. This proves
the `N_b` rule, including the transient capacity condition `h+b<=H`.

For `H_k`, all higher blocks occupy exactly `p` physical positions, regardless
of their internal orders. The selected block therefore has exactly `s-p`
available pop positions. If there are none, the action is impossible; otherwise
the restricted-deletion lemma gives exactly the claimed replacement. Internal
choices in every other block remain independent and unrestricted. Induction
proves both inclusions in the exact-state assertion. QED.

Together with the normalization lemma and unique coding, this proves exact
recognition and exact permutation counting by the resulting transition graph.
The output generated from increasing input is the inverse of the sortable
input permutation; this inversion is required, not optional.

## 6. Algorithmic consequences and boundaries

To recognize a sortable input, invert it, compute its unique output code while
keeping the sorted held-value list, and apply the deterministic composition
transitions. Reject at an impossible transition and accept after the final
empty composition. Standard list operations use at most linear time per output:
finding a held rank, locating a block, and constructing the new composition all
cost `O(n)`. Thus the total is `O(n^2)` elementary integer operations and `O(n)`
storage. On a bit model, these bounds acquire the usual `O(log n)` factors for
integers of size at most `n`.

Capacity zero accepts only the empty permutation. For finite capacity `H>=1`,
only compositions of totals at most `H-1` occur after
outputs. There are finitely many, so the graph is an exact finite automaton.
Its adjacency matrix counts code letters, not physical histories; if `A` is
that matrix and the empty state is indexed by zero, its ordinary generating
function is `(I-x A)^(-1)[0,0]`. The coefficient of `x^n` counts distinct
sortable permutations, including the empty permutation once.

Atkinson's sorting-dual symmetry transfers the quadratic recognition algorithm
to every `(r,2)` with `r>=2`: test `(pi^rc)^(-1)` using the `(2,r)` algorithm.
Reversing a history preserves its maximum height, so the same transfer applies
with a physical capacity bound.

The lazy-input lemma also gives a uniform capacity corollary for every positive
`r,s`. For a generated permutation `p`, let `M_j=max(p_1,...,p_j)`. Just before
output `j`, every lazy history holds `M_j-j+1` entries. Its maximum is
`1+max_j(p_j-j)`. Any generating history must have read through `M_j` by that
output, so the same quantity is a lower bound. For sortable input `pi` and
generated output `p=pi^(-1)`, this is `1+max_i(i-pi_i)`. Hence every nonempty
sortable input has that exact minimum physical capacity. This is a connection
to the established maximum-drop statistic, not a new-statistic claim.

The unbounded graph remains infinite. No claim of a finite-state or ordinary
pushdown realization is made here, and algebraicity does not follow merely
from the composition encoding.

## Attribution

The `(r,s)` machine, one-sided enumeration, and `(2,2)` greedy normal form are
Atkinson's prior work. The no-pop block class is the familiar
`Av(123,213)` container. Unique output codes, determinization, regular languages
for bounded storage, and rational transfer matrices have older antecedents.
The precise all-`s` composition transition theorem is what requires comparison
with further literature before any novelty statement.

Primary sources:

- M. D. Atkinson, Generalized stack permutations (1998), Sections 2–4.
  https://www.cs.otago.ac.nz/staffpriv/mike/Papers/Genstack/Genstack.pdf
- M. D. Atkinson, M. J. Livesey, D. Tulley, Permutations generated by token
  passing in graphs (1997).
  https://www.cs.otago.ac.nz/staffpriv/mike/Papers/TokenPassing/TokenPassing.pdf
- V. Vatter, An assortment of problems in permutation patterns,
  arXiv:2602.16355v2, Section 5, Problems 5.10–5.13.
  https://arxiv.org/html/2602.16355v2
