# Independent weighted-PDA derivation

This derives algebra from machine histories, rather than fitting an equation to finite counts.

## Preconditions

Use the forest bijection: leaf/nonleaf status of each preorder node
is L/R. Forest histories project exactly to words, with distinct operation
edges preserved. P0 on a nonempty word prefixes R; P0 on empty inserts L.
P1 replaces the first symbol t by RL. O0 deletes the first symbol. O1 deletes
the second symbol only when the first is L. B leaves the word unchanged.
After a push, pops are disabled until B; they remain enabled after any pop.

## A standard pushdown automaton

Controls A and N mean pops allowed and pops disabled. Add control C meaning a
leading L is temporarily carried during O1. Stack top is on the left. For
t in {L,R}, transitions are:

- A,t -> A,empty (O0), weight 1
- A,L -> C,empty (first half O1), weight 1
- C,t -> A,L (second half O1), weight 1
- A,t or N,t -> A,t (B), weight x
- A,t or N,t -> N,Rt (P0), weight x
- A,t or N,t -> N,RL (P1), weight x

C has no transition at bottom. Thus an incomplete O1 is not accepted. With an
empty stack, A can stop, execute B, or push L and enter N. There are no other
empty-stack moves. Nonempty P0/P1 transitions remain distinct, even when their
rewrites coincide at t=L.

Replacing O1 by its two forced transitions is bijective on complete paths.
Weights count input tokens: each B or push carries x; pop transitions carry 1.
The extra C transition cannot create a zero-input cycle: an A-to-C step
deletes a symbol, and the forced C-to-A replacement preserves height.
Alternatively, contract each forced pair back to one of the bounded original
pops. At fixed input size, complete paths have bounded length.

## First-return matrices

For t=L or R, let X_t[p,q] count paths starting in control p above symbol t
and stopping at the first exposure of the unchanged lower stack, in control q.
These standard first-return pieces never operate on the lower stack.
A length-two replacement ab decomposes uniquely as X_a X_b, summed over the
intermediate control. A one-symbol replacement contributes X_a.

No first-return path ends in N: no transition removes a stack symbol and
enters N. Entries in the N-ending column are consequently zero. Keep only
ending controls A,C. Write the A-row of X_L as ell=(a,c), and of X_R as
r=(b,d). The N-row differs from its A-row only by the available initial
zero-input removals:

    N-row(X_L) = ell - (1,1)
    N-row(X_R) = r - (1,0).

For either t, the C-row of X_t is ell, since its only transition replaces t
with L and goes to A. Thus restricted to starting controls A,C:

    X_L = [[a,c],[a,c]],   X_R = [[b,d],[a,c]].

The first-return equations before simplification are

    ell = (1,1) + x ell + 2x (r-(1,0)) X_L,
    r   = (1,0) + x r + x (r-(1,0)) X_R + x (r-(1,0)) X_L.

The 2 in the first equation is the two distinct push transitions on L.
Their subpaths enter N and first process a leading R. The equations derive
from the disjoint first transition of each path. Subtraction here only
abbreviates the N-row by deleting the explicit direct-pop alternatives;
it does not remove or assign negative weights to actual histories.

Both components of ell satisfy the same equation with constant term 1,
so a=c=u. We obtain

    u = 1 + x u (2b+2d-1),
    b = 1 + x b^2 + x u (b+2d-1),
    d = x b d + x u (b+2d-1).

Initial terms are u(0)=b(0)=1 and d(0)=0. These equations specify unique formal
power series coefficient by coefficient, since every nonconstant term on the
right has an explicit factor x. Their underlying path interpretation has only
nonnegative integer weights and finitely many paths for each input size.

Subtracting the first equation from the second gives

    b-u = x b (b-u).

Since 1-xb is a unit in the formal-power-series ring, b=u. Subtracting the d
equation from the b equation gives

    u-d = 1 + x u (u-d) = 1/(1-xu).

## Empty-stack generating function

Let f count complete paths from empty stack/control A. The first operation is
stop, B followed by a complete path, or P0 followed by an L first-return piece
starting in N and then a complete path. Only end control A is viable at bottom;
C cannot complete its O1 there. The applicable N-to-A first-return series is
u-1. Therefore

    f = 1 + xf + x(u-1)f = 1 + xuf.

It follows that f=1/(1-xu)=u-d. Substitute b=u and d=u-f into the u equation:

    u = 1 + xu(4u-2f-1).

Eliminate u by xu f=f-1. Multiplying the last equation by xf^2 gives

    f(f-1) - xf^2 - 4(f-1)^2 + xf(f-1)(2f+1) = 0,

which expands exactly to

    2xf^3 - (2x+3)f^2 + (7-x)f - 4 = 0.

The path interpretation gives f(0)=1. The derivative in f of this polynomial
at (x,f)=(0,1) is 1, so that constant term picks a unique formal solution.

## Audit obligations

The algebra assumes the Atkinson canonicalization theorem, the forest-path
bijection, and the exact leaf-word projection. Those are the mathematical
bridges to audit, together with the first-return decomposition and bottom
boundary. Matching finite coefficients is a separate check, not a replacement
for any bridge. 

