# Candidate exact decorated-factor normal form for the (3,3)-stack

This concerns one
stack with insertion and removal at zero-based positions 0, 1, or 2, generating
outputs from increasing input 1,2,... . It counts sets of reachable physical
orders, not histories. No generating-function or
algebraicity theorem follows in this note, and no historical novelty is claimed.

## 1. Maximum-insertion coordinates and the exact deletion transducer

For a top-first order pi on held ranks 1,...,h, let c_j be the number of smaller
ranks that precede j in pi. Recover pi by inserting successive maxima j at slot
c_j. Thus pi is obtainable by top-three insertion without removals exactly when
c_1=0, c_2<=1, and c_j in {0,1,2} for j>=3. Every current physical order in the
machine belongs to this class: insertion preserves it, and deleting an entry
can only decrease the number of smaller predecessors of any surviving entry.
The coordinate encoding is a bijection, not a history encoding.

Push of a new maximum appends one freely chosen legal coordinate. To delete
held rank k, delete coordinate c_k and set p=c_k. Process each later input
coordinate a in increasing rank order:

- If a<=p, emit a and replace p by p+1.
- If a>p, emit a-1 and leave p unchanged.
- Reject as soon as p>=3.

Earlier coordinates are unchanged. This is an exact deterministic partial
transducer from a physical order's code to its surviving standardized code.
Indeed, p is the current slot of k in the order restricted to the ranks scanned
so far. Inserting the next maximum above k raises p by one and leaves that
maximum's code unchanged after k is deleted. Inserting below k leaves p fixed
and removes one smaller predecessor of that maximum. The final slot of k is
less than three exactly when its removal is legal; p never decreases.

The live-state transitions (input/output) are

    p=0: 0/0 ->1; 1/0 ->0; 2/1 ->0
    p=1: 0/0 ->2; 1/1 ->2; 2/1 ->1
    p=2: no legal transition.

All three states accept an empty remaining word. In particular, every code
after the removed coordinate is binary. This transducer processes *sets* by
union of images, so duplicate preimages never become multiplicity.

## 2. Proposed state family

Write concatenation of word languages multiplicatively. Define unary factors

    Z={0}, O={1}, B={0,1}, T={0,1,2}

and, for m>=2, define a correlated binary factor

    C_m = {0,1}^m minus {1^m}.

Let K consist of all finite concatenations of these factors, together with the
empty-word language E={epsilon}. We allow the empty language as rejection.
For formulas only, set C_1=Z and C_0=empty language. The claim is:

**Candidate theorem.** After any feasible lazy output-code prefix of a
(3,3)-stack, the set of maximum-insertion coordinate words is exactly one
member of K. Its factorization into Z,O,B,T,C_m (m>=2) is unique. Record and
held-output transitions below preserve the representation exactly.

Only languages consisting of valid coordinate words (c_1=0,c_2<=1) arise.
Closure below holds whenever the input language has those ambient bounds.

## 3. Suffix images

For W in K, let F_p(W) be the set of words emitted by the preceding transducer
started in p. F_p(E)=E for p=0,1,2. F_2(W) is empty for nonempty W.

For nonempty W, F_1(W) is nonempty precisely when W consists of some number
of unary T factors followed by one unary factor A. Equivalently, all but the
last input coordinate must permit the value 2, and only T permits it.
No C_m can occur because it has at least two binary coordinates. If W=T^t A,
then

    F_1(W)=O^t f(A),
    f(Z)=Z, f(O)=O, f(B)=f(T)=B.

For these exceptional tails direct inspection gives

    F_0(T^t Z)=B^t Z,
    F_0(T^t O)=F_0(T^t B)=C_(t+1),
    F_0(T^(t+1))=B^(t+1).                           (1)

For example, in T^t B an output consisting only of ones is impossible: from
state zero it would require input 2 at the final binary position. Any other
binary word is possible. Keep p=0 until its last zero, use input 0 there to
move to p=1, then use input 2 up to the final position and input 1 there. If the
last zero is final, stay in p=0 before it and use final input 0 or 1.
The same reasoning applies to T^t O, using final input 1. The other identities
in (1) follow by staying in state zero until the final position; the possible
output digits give the displayed full product.

Put U(W)=F_0(W) union F_1(W). Thus U(E)=E. If F_1(W) is empty then U(W)=F_0(W).
On exceptional tails:

    U(T^t Z)=B^t Z,
    U(T^t O)=U(T^t B)=B^(t+1),
    U(T^(t+1))=B^(t+1).                            (2)

The exact recursions on the first factor are

    F_0(Z W)=Z F_1(W),
    F_0(O W)=Z F_0(W),
    F_0(B W)=Z U(W),
    F_0(T W)=B F_0(W) union Z F_1(W).              (3)

If F_1(W) is empty, the last line is B F_0(W). If it is nonempty, W is an
exceptional tail or E and formula (1) directly evaluates F_0(T W) in K.

For m>=2 the correlated factor obeys

    F_0(C_m W)=Z^m F_1(W),                if W is nonempty,
    F_0(C_m)=Z^(m-1) B,
    F_1(C_m W)=empty.                             (4)

To prove (4), an input C_m word must contain a zero. Prior to its first zero,
state zero reads ones and emits zeros. At that zero it enters state one.
Only input 2 can keep it there, so among the remaining binary positions at
most one can remain, and that one must be the very last position of the whole
word. If W is nonempty the zero must therefore be the last coordinate of the
C_m factor. If W is empty the zero may instead be penultimate, yielding the
extra possible final output one. State one cannot read two consecutive binary
positions at all, proving the last assertion.

Equations (1)-(4), by induction on factor count, prove that F_0(W), F_1(W),
and U(W) belong to K or are empty. This is an exact language-closure proof;
it does not assume that every syntactically valid K language is reachable.

## 4. Deleting a coordinate

First suppose the selected coordinate is a unary factor A, with factor prefix
P and suffix W. The successor is

    P times union_{p in A} F_p(W).

If W=E this is P. Otherwise it is P F_0(W) for A=Z, P F_1(W) for A=O, and
P U(W) for A=B or T. All cases belong to K or reject.

Now suppose the selected coordinate lies within C_m. Let ell be the number of
coordinates to its left in that factor, r the number to its right, and W the
factor suffix after C_m. The earlier complete-factor prefix P is unchanged.
We describe the remaining part, with P suppressed.

- If r>=2, or if r>=1 and W is nonempty, the image is

      B^ell F_0(B^r W).

  Starting with selected coordinate one would mean starting the transducer in
  state one with either two binary positions or a binary position followed by
  another position. This is impossible. The selected coordinate must be zero,
  which itself satisfies the original C_m condition and frees its other bits.

- If r=1 and W=E, the image is C_(ell+1). A final output one is possible exactly
  when the retained left prefix already contains a zero. Thus only the all-one
  retained word is excluded.

- If r=0 and W=E, the image is B^ell, because selecting zero always realizes
  every retained prefix.

- If r=0 and W is nonempty, the exact image is

      B^ell F_0(W) union C_ell F_1(W).              (5)

  Selecting zero imposes no restriction on the retained prefix; selecting one
  requires that prefix to contain a zero. If F_1(W) is empty, or is contained
  in F_0(W), equation (5) is simply B^ell F_0(W). The only other case is
  W=T^t A with A=O or B. Then (1) shows that (5) is exactly C_(ell+t+1):
  every binary word is allowed except simultaneous all-one prefix and suffix.

This exhausts the deletion positions, proving exact held-output closure.

## 5. Record transitions, induction, and uniqueness

A lazy record N_b inserts b-1 new held maxima. Each append is Z at height zero,
B at height one, and T at height at least two. The record token itself can be
inserted and removed at slot zero and cannot change the order of other tokens.
Thus the displayed record transition is exact, by the prior lazy-normalization
lemma for the top-position machine. The precise prior bridge is
`docs/composition-normal-form.md`, Section 2, "Lazy-input normalization",
including its following unique output-code construction, at repository commit
`0fdef773ff86300c91f9d3a8d480a9f15736d0d2`. That lemma explicitly applies to
every positive pair (r,s), even though the later composition theorem there
is specialized to push width two. Starting at E and applying the preceding
held transitions proves the candidate normal-form assertion by induction.

Every unary factor is Cartesian-indecomposable by length. Each C_m for m>=2
is also indecomposable: projections across any nontrivial cut are full binary
cubes, but C_m omits the all-one word, so it is not their Cartesian product.
Any two Cartesian factorizations of a finite fixed-length language have a
common refinement at the union of their cut positions. Indeed, if cuts i<j
are independent, factorization at i and projection through j imply that the
middle and final coordinate segments are independent as well. Iterating gives
all cuts together. Hence factorization into indecomposable coordinate intervals
is unique. The listed factors are pairwise distinct, proving the claimed
canonical representation.

## 6. A growing obstruction to bounded unions of the old blocks

For each m>=1, the output prefix

    6,1,2,4,m+8,m+6,5

has coordinate language Z C_m. At m=3 this is the previous seven-order state.
After 6,1,2,4 the language is Z Z (the sole stack order is 5,3). The next record
adds m+1 free T coordinates. Deleting the second-largest held rank m+2 gives
Z Z T^(m-1) B. Deleting held rank two then gives Z F_0(T^(m-1) B)=Z C_m.
The two fixed seed coordinates follow by literal application of the proved
transducer to N6 H1 H1 H2; they can also be checked directly.

Any cover of C_m by Cartesian coordinate boxes requires at least m boxes.
For each i, consider the word with a single zero at position i. A box contained
in C_m must force zero in some coordinate, or it would contain the all-one word.
A box containing this particular single-zero word must force zero at i, and
cannot contain any of the other m-1 single-zero words. Hence m boxes are needed.

A product of unrestricted top-three insertion-order blocks on disjoint fixed
rank intervals, concatenated in any fixed block order, is a coordinate box:
for each coordinate its local insertion digit is independent, shifted by the
fixed number of smaller labels in earlier physical blocks. Therefore even a
fixed finite union of such independent block products cannot represent all
reachable (3,3) states. This strengthens the old cardinality-seven obstruction.
It does not rule out decorated factors: C_m itself has a two-state automaton,
remembering whether a zero has occurred.

## 7. What remains for Question 5.12

This candidate theorem gives a canonical exact determinization, finite
factor *types*, and one integer size parameter for a correlated factor. It
is not a finite-state automaton, an ordinary finite-alphabet pushdown theorem,
or an unambiguous first-return specification for permutations.

Held deletion can rewrite an arbitrarily long coordinate suffix. A concrete
next task is to convert these exact rewrite formulas into finite-control
first-return equations and prove their unique output-code interpretation.
Only after that step would a proper DDE/algebraicity theorem be applicable.
Neither bounded experiments nor this state representation closes that gap.

Primary model source checked: Vincent Vatter, An Assortment of Problems in
Permutation Patterns, arXiv:2602.16355v2, Section 5, Question 5.12:
https://arxiv.org/html/2602.16355v2 . The question concerns a single top-position
(r,s)-stack. The no-pop container and generalized stack terminology are due
to Atkinson; the earlier local work supplies lazy normalization and the exact
unique output code. Fork-stack and consecutive-block-push results are different.
