# Physical capacity and the uniform bounded-height family

The minimum-capacity bridge and exact bounded-cardinality recurrence are covered by the [formal certificate](../formal/README.md). The associated pole-convergence theorem is proved in [capacity-pole-law.md](capacity-pole-law.md).

## Exact memory parameter

For a nonempty sortable permutation pi, let D=max_i(i-pi_i), with one-based
positions. Its minimum required physical stack capacity is D+1. The canonical
sorter attains this minimum.

Lower bound: immediately after the input entry pi_i is pushed and before it
can be popped, at most pi_i-1 entries can have been output. Hence at least
i-pi_i+1 entries are held. Taking the maximum gives D+1.

For the upper bound, in any configuration admitting a successful continuation,
the smallest held entry lies in the first two positions. Otherwise two larger
entries precede it; their order relative to it cannot change, and neither may
exit before it, permanently blocking its removal. Consequently the eager
canonical sorter emits every available initial interval of values before
reading another input. Immediately before reading position i, write v for the
next missing output value. It is still unread, so its input position p>=i.
The next push reaches height i-v+1<=p-v+1<=D+1. Pops do not increase height.
This proves the bound. The empty permutation needs capacity zero.

This is closely related to the known bounded-priority-queue/maxdrop connection
explicitly stated by Vatter, Section 5, and to Chung--Claesson--Dukes--Graham's
bounded-drop classes. Do not advertise the statistic or this short corollary
as new general theory.

## Uniform first-return recursion

A compressed bypass needs a transient extra physical slot. It is forbidden
when the current held height equals the capacity. Thus a state with zero free
slots allows no bypass or push; only an enabled terminating pop can occur.

Let K_j be the first-return resolvent with j free slots above the starting
held height, using the same control, flags, terminal matrices D_L,D_R and
operation labels as the original proof. Then

- K_0=I;
- for j>=1, U_b^(j)=(K_j-I)D_b;
- V_j(L,e)=2x U_L^(j-1)(R,e);
- V_j(R,e)=x[U_R^(j-1)(R,e)+U_L^(j-1)(R,e)];
- K_j=((1-x)I-V_j)^(-1).

The bypass term stays at the same height; a push consumes one free slot and
therefore uses the previous resolvent. Write K_j=[[k_j,0],[u_j,l_j]]. Direct
matrix calculation, valid also at j=0, gives u_j=k_j-l_j, and hence

    k_0=l_0=1,
    k_j=1/(1+x-4x k_(j-1)+2x l_(j-1)),
    l_j=1/(1-x k_(j-1)).

At capacity H>=1 an initial push consumes one slot, so its disabled completion
is k_(H-1)-1. Empty-state decomposition yields

    F_H=1+x F_H+x(k_(H-1)-1)F_H=l_H.

Also F_0=1. This gives the entire rational family using two iterated series,
without constructing an exponentially growing finite automaton. Equivalently,

    F_0=1, F_1=1/(1-x),
    F_(h+1)=1+x F_h/(4-3F_h+2x F_h F_(h-1))   (h>=1).

First examples:

    F_1=1/(1-x)
    F_2=(1-x)/(1-2x)
    F_3=(1-2x-x^2)/(1-3x).

Coefficientwise stabilization to the unbounded series follows because no
history introducing n tokens can exceed height n. The fixed-point equation of
the scalar recursion is exactly the already-proved cubic. Neither stabilization
nor rationality by itself establishes a rate of growth convergence or a limit
law for memory. The pole-convergence rate is established in the linked analytic note; the separately reviewed [typical-capacity proof](capacity-typical-height.md) establishes the random-permutation memory limit law.

## Closest bounded-drop sources

- Vatter, Section 5, sorting versus generating: bounded priority queues,
  maximum drop and avoidance of all length-(k+2) patterns ending in 1:
  https://arxiv.org/html/2602.16355v2
- F. Chung, A. Claesson, M. Dukes, R. Graham, *Descent polynomials for
  permutations with bounded drop size*, European J. Combin. 31 (2010),
  1853--1867: https://arxiv.org/abs/0908.2456
- M. Hyatt and J. Remmel, *The classification of 231-avoiding permutations by
  descents and maximum drop*: https://arxiv.org/abs/1208.1052

These establish prior relevance of bounded-drop statistics; no equivalence
claim to the present capacity recursion is made without inspecting the exact
model and equations. Fixed-capacity rationality is routine finite-state theory.
