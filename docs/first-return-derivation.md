# A direct first-return derivation for the (2,2)-stack

This note uses the constraint-forest bijection in `canonical-forests.md`, whose prior structural input is Atkinson's canonical sorting algorithm. It does not use the forbidden-pattern basis in the derivation. The target cubic was known in advance.

## 1. Exact quotient of the forest machine

Mark every node of a forest L if it is a leaf and R if it has at least one
child. Read these marks in preorder to get a word w. Keep operation labels
distinct, even if two operations have the same resulting word.

The exact word operations are:

| Operation | Preconditions | Resulting word |
|---|---|---|
| B | none | w |
| P0 | w empty | L |
| P0 | w nonempty | Rw |
| P1 | w = av nonempty, a in {L,R} | RLv |
| O0 | w = av nonempty | v |
| O1 | w = Lav, a in {L,R} | Lv |

As in the forest model, pushes set the can-pop flag to false; B and pops set
it to true; both pops require a true flag. Initial state: empty word, true
flag. Acceptance: empty word. Every B or push has weight x, recording one
input token; pops have weight 1.

**Quotient lemma.** This labelled word system has exactly the same operation
paths from the empty state as the forest system.

**Proof.** A P0 on a nonempty forest adds a nonleaf root before every existing
node; an empty P0 adds a leaf. A P1 makes the existing first root nonleaf and
inserts a new leaf second, leaving every other node's child list unchanged.
For O0, the removed node is a root. None of the surviving nodes loses a child,
so their L/R marks are unchanged. O1 is available precisely when the first
tree is a leaf and a second tree exists; it removes that second root. Again
no surviving node loses a child, so deleting the second letter is exact.

Availability is therefore determined by w and the flag alone. Starting empty,
every valid word path lifts inductively to the uniquely determined forest
path with the same operation labels. Conversely projecting any forest path
gives that word path. If the first letter is L, P0 and P1 have the same target
RLv, but are distinct labelled paths and must both be counted. QED.

Together with the forest bijection this proves that accepted word paths count
sortable permutations, not all sorting histories.

## 2. A finite-control stack formulation

For a nonempty word, store its first letter a in finite control and the rest
as an ordinary top-first suffix stack. The can-pop flag is also finite control.

- B has weight x, preserves a and the suffix, and enables pops.
- P0 has weight x, sets the control letter to R, pushes the old control letter
  a onto the suffix stack, and disables pops.
- P1 has weight x, sets the control letter to R, pushes L onto the suffix
  stack, and disables pops.
- O0 removes the control token and pops the suffix letter into control.
- O1 is possible only from control L with nonempty suffix. It pops the first
  suffix letter and keeps control L.

Both pops enable further pops. When the suffix is empty, only O0 can empty the
whole word. A first push from the empty word has weight x and gives control L,
empty suffix, and disabled pops.

This is an ordinary pushdown mechanism with finite control. We will count it
directly rather than invoke a general algebraicity theorem.

## 3. First-downstep matrices

Let b be L or R. Start with control letter a, suffix stack beginning with b,
and any fixed tail below b. Stop at the first time the suffix stack height
falls below its starting height. At this stop b has just been popped, either
into control by O0 or discarded by O1. The tail has not been touched.

Define two 2-by-2 matrices, rows/columns ordered L,R:

- T_b(a,d) counts these stopped paths starting with pops enabled and ending
  with control d.
- U_b(a,d) counts them starting with pops disabled and ending with control d.

Every such path ends in a pop, so its final flag is enabled. Matrices do not
depend on the fixed tail. The weight is x per newly introduced token.

The immediate terminating pop possibilities form the matrices

    D_L = [[2, 0], [1, 0]],
    D_R = [[1, 1], [0, 1]].

For example, with control L and suffix beginning L, O0 and O1 both leave
control L but remove different tokens, giving multiplicity 2. With control R
only O0 is permitted. These multiplicities count distinct canonical operation
paths, which correspond to different permutations by the established
bijection.

Let V(a,e) count one initial push and the subsequent first return to the old
suffix height, ending with control e. After a push the control is R and pops
are disabled. P0 pushes suffix letter a, and P1 pushes suffix letter L, hence

    V(L,e) = 2*x*U_L(R,e),
    V(R,e) = x*(U_R(R,e) + U_L(R,e)).

A first-downstep path starts with one of three mutually exclusive events:

1. An immediate terminating pop, available only in T_b.
2. B, followed by a T_b path (weight x).
3. A push, its uniquely determined first return to the old suffix height,
   and then a T_b path. The first-return part has matrix V.

Consequently matrix multiplication in chronological order gives

    T_b = D_b + x*T_b + V*T_b,
    U_b =       x*T_b + V*T_b = T_b - D_b.

All these are identities of formal power series. There are no problematic
zero-weight loops: a pop lowers the number of held tokens, and every push/B
has positive x degree. A path with a fixed number of new tokens has bounded
length. Also U_b has zero constant term, so V has zero constant term and

    K = ((1-x)*I - V)^(-1)

exists uniquely as a formal-series matrix. Thus

    T_b = K*D_b,       U_b = (K-I)*D_b.

There is also a direct uniqueness argument for the whole mutually defined
system, rather than merely for the inverse with V held fixed. Its constants
are T_b(0)=D_b and U_b(0)=0. In
U_b=x*T_b+V*T_b, the coefficient of degree n uses T_b only below degree n
except through V(n)*D_b; V(n) itself is x times a linear combination of
U_L(n-1) and U_R(n-1). Thus induction on degree uniquely determines U_b, T_b,
V, and K. The combinatorial path series give their existence. In particular
the algebra below follows the unique combinatorial formal-series solution.

## 4. Reducing the matrices to three series

Write the second row of K-I as (u,v), and put l = 1+v. Direct multiplication
by the two displayed D matrices gives

    U_L(R,*) = (2*u+v, 0),
    U_R(R,*) = (u, u+v).

Therefore

    V = [[2*x*(2*u+l-1),                0],
         [  x*(3*u+l-1), x*(u+l-1)]].

It follows, rather than being assumed, that K is lower triangular. Put

    K = [[k, 0], [u, l]].

Inverting the triangular matrix yields the exact system

    k = 1 / (1+x-4*x*u-2*x*l),
    l = 1 / (1-x*u-x*l),
    u = x*(3*u+l-1)*k*l.                         (1)

The relevant solution has k(0)=l(0)=1 and u(0)=0, since K(0)=I.

Subtracting the reciprocal equations gives

    k-l = k*l*((1/l)-(1/k))
        = x*k*l*(3*u+l-1)
        = u.

Thus k = u+l. Substituting into the l equation gives

    l = 1 + x*k*l.                               (2)

## 5. Empty-to-empty paths

Let f count all complete word paths from the empty state, including the empty
path. To compute the completion of a first push, use a bottom boundary rather
than a real suffix letter. At that boundary an immediate O0 terminates and
O1 is unavailable. Its terminal column is d=(1,1)^T.

Exactly the same first-step decomposition gives the true-flag completion
column K*d and the false-flag completion column (K-I)*d. A first push starts
with control L and false flag, so its completion series is k-1.

A nonempty complete path begins either with B, or with the sole push from
empty followed by its uniquely determined first return to empty. Each is
then followed by an arbitrary complete path. Hence

    f = 1 + x*f + x*(k-1)*f
      = 1 + x*k*f.                               (3)

Equations (2) and (3), both with constant term 1, imply l=f, and thus u=k-f.
The first equation of (1) reduces to

    k = 1 + x*k*(4*k-2*f-1),
    f = 1 + x*k*f.                               (4)

The subtraction in this simplified system is algebraic; no negative-weight
combinatorial objects have been introduced. The nonnegative first-return
matrix construction precedes this simplification.

## 6. Elimination

Using x*k*f=f-1 in the first equation of (4) gives

    (4-3*f)*k = 1+2*f-2*f^2.

Since 4-3*f has constant term 1, division is legitimate. Substitution back into
f=1+x*k*f yields

    (f-1)*(4-3*f) = x*f*(1+2*f-2*f^2),

or, equivalently,

    2*x*f^3 - (2*x+3)*f^2 - (x-7)*f - 4 = 0.

The relevant branch has f(0)=1. The derivative with respect to f of the
polynomial at (x,f)=(0,1) equals 1, so this branch is unique as a formal power
series. Thus, conditional only on the reviewed prior canonical algorithm and
the supplied bijection/first-return arguments, this is a direct derivation
of the known generating function from the sorting mechanism.

## 7. Checks and discovery provenance

- The cubic and its first terms were known before this investigation from
  Vatter Section 5 and OEIS A393395. The project does not claim to have first
  discovered that polynomial or enumeration.
- Atkinson's original source was audited before proposing a new canonical
  sorter. Its orientation was checked using 2341 and then against the
  independent exhaustive recognizer.
- The forest was constructed by recording precisely the comparison imposed
  between the newly pushed token and the old top, then projecting the resulting
  precedence forest to leaf/nonleaf marks. The operation rules were not fitted
  to coefficients.
- The forest recurrence gave the known counts through n=8 without importing
  them. A separate labelled-path enumeration through n=6 checked exact
  membership, no duplicate paths, legal replay, and equality with the prior
  deterministic canonical history.
- The binary quotient was independently checked at n=0..8. The equations above
  were obtained by first-downstep decomposition, not by guessing an equation
  from those values.
- A local SymPy Groebner elimination of system (1) together with
  f*(1-x*k)=1 independently returned the same cubic. This algebra check does
  not validate the combinatorial derivation by itself.

Relevant primary references:

- Atkinson original: https://www.cs.otago.ac.nz/staffpriv/mike/Papers/Genstack/Genstack.pdf
- Vatter's exact open target and known polynomial: https://arxiv.org/html/2602.16355v2
- Published counting sequence: https://oeis.org/A393395
- Prior one-pop canonical-history method: https://arxiv.org/html/1510.00269
