# Unequal generalized stacks: infinite bases at the sharp capacity threshold

## 1. Main result

Let `S_(r,s;H)` be the permutations sortable by one top-position `(r,s)`-stack
with maximum physical height `H`. Push and pop slots are zero-based, counted
from the top. The capacity includes the transient height before a new maximum
is popped; there is no free bypass. Let `G_(r,s;H)` denote the outputs generated
from increasing input. Omit `H` for unbounded capacity.

**Theorem.** For all unequal integers `r,s >= 2`:

1. Both unbounded classes have infinite bases.
2. For integer `H >= 0`, their capacity-`H` bases are finite exactly when
   `H <= max(r,s)+1`, and infinite exactly when `H >= max(r,s)+2`.
3. In the finite regime the nonempty sortable inputs are exactly those with
   `max_i(i-pi_i) <= H-1`; the empty permutation is always included. For `H >= 1` its basis consists of the `H!`
   permutations of length `H+1` ending in their least entry. For `H=0`, its
   basis is `{1}` and its only member is the empty permutation.

Thus there is an exact finite/infinite basis transition, not just an example
of infinitude. The generated-output basis in item 3 consists of the inverses
of the displayed sortable-input patterns.

The unbounded assertion extends the repository's `(2,s)` and `(s,2)` result
to **every unequal pair with both widths at least two**. The equal-width cases
`(r,r)`, `r >= 3`, are not settled here. In particular, none of the arguments
below should be presented as a complete answer to Vatter Problem 5.10.

## 2. The explicit family

It suffices first to treat `2 <= r < s`. For `m >= 0`, define

```
Q_i = s+2+2i                  (0 <= i <= r-2),
E_j = s+1+2j                  (0 <= j <= m+r-2),
M_0 = s+2r-2,
A_j = M_0+2+2j                (0 <= j < m),
M   = M_0+2m,
b   = s-r+2,
n   = M+b = 2s+r+2m.
```

The permanent token is `P=r`. Define the generated-output permutation

```
R_(r,s,m) =
   (Q_0,1), (Q_1,2), ..., (Q_(r-2),r-1),
   r+1,r+2,...,s,
   (A_0,E_0), (A_1,E_1), ..., (A_(m-1),E_(m-1)),
   n, P, E_m,E_(m+1),...,E_(m+r-2), M+1,...,n-1.
```

Empty ranges are omitted. The low values are `1,...,s`; the `E` and record
values interleave through `M`; the remaining final values are `M+1,...,n`.
Consequently this is a permutation of `1,...,n`.

**Family theorem.** Every `R_(r,s,m)` is a basis element of `G_(r,s)`, and is a
basis element of `G_(r,s;H)` for every `H >= s+2`. Every single deletion has an
explicit successful history of capacity at most `s+2`.

For `(r,s)=(3,4)`, the first two members are

```
6,1,8,2,4,11,3,5,7,9,10
6,1,8,2,4,10,5,13,3,7,9,11,12
```

At `r=2`, the construction specializes exactly to `rho_(s,m)` in the existing
the two-push specialization; it does not replace or revise that family.
The new family length is `2s+r+2m`, and its length tends to infinity with `m`.

## 3. Mechanical preliminaries

### 3.1 Lazy generation

An increasing-input generating history can be normalized to read nothing
before an already-held requested output, and to read exactly through the
requested value when that output is a new maximum. This does not increase
physical height.

For completeness, swap adjacent operations `push(x), pop(y)` when `x != y`.
The token `y` existed before the push. Pop it first. If `y` lay before the
insertion slot, reduce that insertion slot by one; otherwise keep it. Its old
pop slot can only decrease. The adjusted slots remain valid and within their
respective widths. The final stack agrees, and intermediate height decreases.
Move unnecessary pushes rightward one output at a time. In the resulting
normal form, every maximal run of pushes is immediately followed by the pop of
the last token in that run; otherwise its final push could be swapped past
that pop. This proves the normalization by induction on the output boundaries.

In a normalized record step the new maximum is the last token pushed and is
then popped. Deleting this push/pop pair leaves the stack that existed just
before its insertion. It is legal to realize that pair by push-slot zero,
pop-slot zero, paying for its transient extra slot.

### 3.2 Relative order and heredity

The relative order of tokens already in a stack never changes. If a token is
at depth at least `r-1`, every allowed new insertion is above it.

Erasing a token's push and pop from a successful history, and reducing later
slots when the erased token lay before them, gives a legal history of its
standardized deletion. Height cannot increase. Hence the generated and sortable
classes, with or without capacity bounds, are closed under patterns. Once an
obstruction and all its single deletions are established, minimality follows.

### 3.3 Inversion and sorting duality

Relabelling a sorting history's tokens by their input positions turns its
input into the identity and its output into the inverse permutation. Thus

```
pi in S_(r,s;H)  iff  inverse(pi) in G_(r,s;H).
```

Reverse a sorting history and complement its labels. This produces increasing
input and output `pi^rc`, with push and pop widths exchanged. Thus the standard
sorting duality is

```
D(pi) = inverse(pi^rc),
pi in S_(r,s;H) iff D(pi) in S_(s,r;H).
```

Both transformations preserve pattern containment, and reversal preserves
maximum physical height. These are prior symmetries, not novelty claims.

## 4. Rejection of the entire family

Use lazy normalization. No output precedes the first record `Q_0=s+2`.
After its immediate push/pop is removed, the held tokens are `1,...,s+1`.
Among the first `r` tokens `1,...,r`, let `z` be the bottom one immediately
after those `r` pushes. The subsequent `s+1-r` nonrecord tokens are all inserted
above `z`. After the first record is output, `z` has depth exactly `s`.

Suppose `z=t` with `1 <= t <= r-1`. Each preceding low output `1,...,t-1`
removes a token above `z`. Between successive low outputs a record step reads
one new relay and the new record; after the record is removed, this adds one
held token above `z`. Just before such a step its depth is `s-1 >= r-1`, so
all these new insertions are indeed above it. Therefore, when `t` is requested,
`z` still has depth `s` and cannot be popped from the first `s` slots.

It follows that any history completing the initial low outputs must have
`z=P=r`. After those outputs, `P` has `s-1` entries above it. The next
`s-r` outputs `r+1,...,s` leave exactly the `r-1` initial relays above `P`.
At this boundary the held tokens number `r`, with `P` last, in every surviving
physical stack. No claim about the relays' mutual order is needed.

Each ordinary relay step reads a new relay and a new maximum, outputs the
maximum, then outputs an old relay. Starting at permanent depth `r-1`, both
pushes are above `P`. The two outputs are also above `P`; so it returns to
depth `r-1`. Induction gives the same invariant after all `m` relay steps.

The terminal record jump reads `b=s-r+2` tokens, all above `P`. Removing the
record leaves the permanent at depth

```
(r-1) + b - 1 = s.
```

The next request is `P`. It is impossible. This proves rejection for every
`r,s,m` under the theorem's hypotheses, even with unbounded capacity.

## 5. Constructive acceptance of every single deletion

All labels in this section are the original labels with one deleted value
omitted. Standardization changes neither relative comparisons nor operation
slots. The Python function `deletion_witness` implements the construction;
its output is a literal sequence of physical push/pop slots, not a search.

### 5.1 Common construction rules

The surviving original low tokens in `1,...,r` can first be read in any desired
physical order: at that height all insertion slots are available. This prefill
uses at most `r` slots. After it, read additional input only when the next output
requires it. A requested new maximum is inserted and removed at slot zero.

While some surviving low token in `1,...,r-1` remains to be output, insert other
new values at slot `min(r-1,h)`. All lows placed ahead of that slot remain ahead
of the new higher tokens. After all those low outputs, use the following rule:

- If `P` is held at depth `d <= r-2`, insert immediately below it, at slot `d+1`.
- Otherwise insert at slot `min(r-1,h)`.

Call `P` *protected* when its depth is at most `r-2`. Once protected after the
low phase, these rules never increase its depth at output boundaries. A
requested new maximum passes over it at slot zero, raising its depth by one
only until that maximum is popped immediately, which leaves it at most `r-1 < s`. In an ordinary relay step
there are at most `r+1` held tokens after the record output. Since `s >= r+1`,
any requested old relay is accessible, regardless of the relays' physical order.

Here is a uniform height check, including postponed batches. If a surviving
original record `x` occurs at original output position `j`, the intact lazy
history has `x-j` held entries just after it. In the deletion history the height
is exactly

```
x - 1_(d <= x) - j + 1_(the output d preceded this record).
```

The last indicator is at most the first, because `x` was an original record.
Thus deletion never raises the height at a surviving original record. The
ordinary record heights are `r+1`, and the final record height is `s+1`.
If an ordinary record was deleted, its old relay is already held and is popped
without new input; the next surviving record satisfies the same bound. This
proves the accessibility assertions even when a batch is postponed or a later
relay output is omitted. A protected permanent therefore survives all such
relay suffixes.

Before the final permanent output there are at most `s+1` held tokens. A
protected `P` is accessible; after it is removed, at most `s` tokens remain,
so all remaining requested outputs are accessible. New maxima later in the
suffix simply bypass at slot zero.

### 5.2 Delete a low output `t` in `1,...,r-1`

Arrange the surviving initial lows as `P` first, followed by the others in
increasing order. They number `r-1`, so the higher-token insertions at slot
`r-1` do not obstruct the initial low outputs. Those outputs are all accessible
in the short prefix after `P`. The extra outputs `r+1,...,s` occur with at most
`s` held entries. The low phase ends with `P` first; the protected suffix rules
complete the history.

### 5.3 Delete an initial extra value or an initial relay

Here the deleted value is in `r+1,...,s` or is one of
`E_0,...,E_(r-2)`. Put `z=r-1`, and arrange the initial lows as

```
P, 1,2,...,r-2, z.
```

The first `r-2` low outputs are in the prefix after `P` and are accessible.
Keep inserting higher values at slot `r-1`; this preserves `P` first and puts
those new values before the last low `z`.

By the time `z` is requested, the deleted value would already have been read.
In the intact word the held height at this boundary is `s+1`; deleting this
input reduces it to `s`. Thus the bottom low `z` is now at depth `s-1`, which
is accessible. After its removal and the extra outputs, the permanent is still
first. A missing initial relay simply leaves one fewer held relay until its
omitted output is passed. The protected suffix rule applies throughout.

### 5.4 Delete an initial record `Q_i`

Set `z=i+1`. Arrange the initial lows as `P`, then the other lows in increasing
order, then `z` last. Before the missing record, all earlier low outputs are
in the prefix after `P` and are accessible.

If `i>0`, just before the missing record would be read, the held height is `s`
and `z` is last. Instead of reading that record's batch, output the already-held
`z` immediately, at depth `s-1`. Reading the postponed relay with the next
record never buries `P` or the remaining low prefix, because insertions stay
at slot `r-1`. The permanent remains first.

If `i=0`, the first output is `z=1`. Output it immediately after the low prefill,
from depth `r-1 < s`, without reading the first large record's batch. The next
remaining record can read the postponed higher tokens with `P` and the other
lows in the prefix. When `r=2`, any intervening extra outputs are instead new
maxima and bypass individually. The same protected permanent results.

After the remaining low and extra outputs, the permanent is first. If the
last initial record was deleted, there may be one fewer held relay; the next
record reads the postponed relay as well, and the height argument in 5.1
covers this case. If there is no ordinary relay step, the terminal record
reads the postponed values and `P` is still immediately accessible.

### 5.5 Delete the permanent `P`

Arrange the surviving lows in increasing order. There are only `r-1`, so the
higher-token insertions preserve that low prefix. The low and extra outputs
succeed. Each subsequent relay phase has at most `r` held tokens after the
record is output, and the terminal phase has at most `s`. Therefore every
remaining requested held output is accessible. No protected token is needed.

### 5.6 Delete a relay introduced during the ordinary relay phase

Such a relay has index `j >= r-1`. Use the unmodified initial construction:
initial lows increasing, with `P` last, and higher insertions at slot `r-1`.
The initial low outputs are accessible; after them at most `s` held tokens
remain, so the extra outputs succeed. The permanent reaches depth `r-1`.

At the step that would introduce the deleted relay, only the record is read;
there is no retained new relay. The requested older relay is still present,
because it has index `j-(r-1) < j`. Popping it leaves only `r-1` held entries,
with `P` at depth `r-2`. The permanent is now protected. Later insertions go
below it; when the deleted relay's requested output is eventually skipped,
protection remains intact. The suffix rules complete the history, including
when that skipped output lies in the final flush rather than an ordinary step.

### 5.7 Delete an ordinary relay record `A_j`

Run the unmodified initial construction and the earlier relay steps. The old
relay `E_j` is already held. Output it before reading the missing record's
batch. This again leaves `r-1` held tokens and protects `P` at depth `r-2`.
The next record, if any, reads the postponed relay too, but all new insertions
are below `P`. The suffix bound in 5.1 applies. With no later ordinary step,
the terminal record reads the postponed relay and `P` remains protected.

### 5.8 Delete the final record `n`

After the ordinary relay steps, `P` is at depth `r-1 < s`. Output it immediately,
then the remaining held relays. The final higher values are new maxima in
increasing order and bypass individually. Thus this deletion is generated.

### 5.9 Delete a terminal auxiliary value in `M+1,...,n-1`

The intact initial and relay steps leave `P` last among `r` tokens. The terminal
record batch now has one fewer token. After its record is popped, the total
height is `s`, with `P` at depth `s-1`; output it. Every remaining token is then
accessible. This covers the last deletion category.

The cases exhaust the low values, initial extra values, all relays, all records,
and the terminal auxiliary values. Every single deletion is generated.

## 6. The capacity bound in the constructive histories

For any permutation `p`, let `M_j=max(p_1,...,p_j)` and put

```
w(p) = max_j(M_j-j+1) = 1 + max_j(p_j-j)       (p nonempty).
```

The equality follows because a running maximum attained at an earlier index
has no larger displacement at a later index. Every lazy history generating
`p` has exactly this maximum height. It is also a lower bound on any history,
because the input must have been read through `M_j` before output `j`.

For `p=inverse(pi)`, this becomes `w(p)=1+max_i(i-pi_i)`.
The statistic `max_i(i-pi_i)` is nonincreasing under taking patterns. Here is a
short proof useful for avoiding a hidden heredity assumption: its maximum equals
the largest number of preceding entries larger than one entry. The displacement
at an entry is that number minus the number of smaller entries after it. For the
reverse inequality, choose a suffix minimum at or after an entry attaining the
largest preceding-larger count. It still has all those larger predecessors and
has no smaller successor. This proves equality; deleting entries cannot increase
the largest preceding-larger count.

For `R_(r,s,m)`, the record boundary heights are `s+2` in the initial stage,
`r+2` in ordinary relay steps, and `s+2` at the terminal record. Thus

```
w(R_(r,s,m)) = s+2.
```

Every deletion `q` consequently has `w(q) <= s+2`. The constructive history
above is lazy after a prefill of at most `r` tokens. A prefill before subsequent
lazy reading has maximum height at most `max(r,w(q))`, which is at most `s+2`.
This proves the physical-capacity bound, including postponed batches and the
first-record-deletion case, without treating a bypass as free.

Sections 4--6 prove the family theorem. Heredity supplies minimality and the
unbounded lengths supply infinitely many distinct basis elements. Inversion
and the capacity-preserving sorting duality extend the conclusion to `r>s`.

## 7. Finite side and sharpness

For arbitrary positive widths, suppose `H <= s+1`. Every permutation `p` with
`w(p) <= H` can be generated: perform lazy input, insert all needed new values
at slot zero, and output the requested value. A requested record is immediately
on top. An already-held output is requested from a stack of height at most
`H-1 <= s`, so every held value is accessible. The transient record height is
at most `H`. Necessity of `w(p) <= H` follows from the lower bound above.

For sorting, therefore, this capacity class is precisely
`max_i(i-pi_i) <= H-1`. If the larger width is instead the push width, apply
sorting duality. The displacement bound is invariant under that duality: an
entry `pi_i=v` becomes an entry with index `n+1-v` and value `n+1-i`, whose
drop is again `i-v`. The same classification holds whenever
`H <= max(r,s)+1`.

By the preceding-larger characterization in Section 6, violating the drop
bound is equivalent to containing a length-`H+1` pattern ending in its minimum.
All such patterns are minimal and there are `H!` of them. This proves the
finite side. The family already provides infinitely many minimal obstructions
at `H=max(r,s)+2`, whose every deletion fits that capacity. They remain minimal
at all larger capacities because the intact permutations are unboundedly
rejected. This proves the exact threshold.

As a byproduct, throughout the finite regime,

```
a_(n,H) = n!                     (0 <= n <= H),
a_(n,H) = H! * H^(n-H)            (n >= H >= 1),
a_(0,0) = 1; a_(n,0)=0           (n > 0).
```

To count, fill positions from right to left in a permutation satisfying
`pi_i >= i-H+1`. Until only `H` positions remain, each position has exactly
`H` eligible unused values; the last `H` positions can be filled arbitrarily.
For `H>=1` the generating function is

```
sum_(k=0)^(H-1) k! x^k + H! x^H / (1-Hx).
```

The maximum-drop statistic and basic finite-state counting methods are prior
concepts. The proposed new contribution is their combination here with the
all-unequal obstruction construction and the sharp infinite-basis threshold.

## 8. Verification, attribution, and boundaries

The evidence file and script distinguish three things:

- The all-parameter written proof above.
- Constructed histories replayed by an independent literal machine checker,
  including the repository's unchanged `generalized.replay`.
- Bounded exact physical-state searches and small unrestricted raw-machine
  searches, used to challenge the implementation and orientation.

The evidence is finite and is not substituted for the proof. One exploratory
unrestricted raw search at `(4,5,m=0)` was killed by the execution environment;
no conclusion was inferred from that run. Wider checks use explicitly bounded
state sets or the non-search constructive witnesses.

The exact formal scope is stated in `formal/README.md`. The equal-width negative control `(3,3,m=1)` and additional controls at `(3,3,m)` and `(4,4,m)` for `m=1,2` show that the strict inequality `s>r` is substantive, not cosmetic.

Primary-source positioning: Atkinson, *Generalized stack permutations* (1998),
DOI `10.1017/S096354839800354X`, supplies the model and earlier one-sided and
`(2,2)` results. Vatter, *An assortment of problems in permutation patterns*,
`arXiv:2602.16355v2`, Section 5, Problem 5.10, explicitly asks for general bases
and discusses their finiteness. The repository's
the two-push specialization and `docs/composition-normal-form.md` supply the
immediate starting point. The new rejection and deletion proofs here use
physical histories directly and do not assume a composition normal form for
push widths greater than two. No claim of historical priority is made.
