# Corollary: every fixed generalized-stack basis has a rational generating function

Status: independently checked consequence of the accepted global-width theorem and the existing bounded-width construction. No new general regular-language theorem or historical-priority claim is made.

## Statement

For every fixed pair of positive integers r,s, the ordinary basis of the generated class G(r,s) has an effectively constructible regular language of unique, length-preserving encodings. Consequently its ordinary length generating function is rational. The same counting conclusion holds for the sortable-input basis by inversion.

## Proof

Put H=2 max(r,s)+1. The accepted global-width theorem says that every ordinary basis element has lazy width at most H.

For a nonempty permutation p, let d_i be the rank of p_i among its suffix p_i,...,p_n. Then

    max_i d_i = 1 + max_i(p_i-i) = w(p).

Indeed, all suffix entries at most p_i have already arrived before the ith lazy output, so d_i is at most the current physical height. The maximal lazy height is achieved at a record, where all preceding outputs are smaller and d_i=p_i-i+1. Thus the width-bounded universe is precisely the classical rank-bounded class Omega_H, whose rank encoding uses the alphabet {1,...,H}. It is pattern closed because deleting entries cannot increase the number of later smaller entries.

The repository's unique N_b/H_k codes and suffix-rank encoding are equivalent by a length-preserving finite-state conversion. If h tokens are held at an output boundary, a rank digit d<=h becomes H_d; a digit d>h becomes N_(d-h). The new height is respectively h-1 or d-1. Conversely H_k has digit k and N_b has digit h+b. The possible heights are 0,...,H-1, and valid complete codes finish at zero.

For arbitrary fixed r,s, the literal recognizer in the bounded-width construction remains finite: a state is a subset of the physical orders on at most H-1 held ranks. On N_b, insert b-1 new nonrecord ranks in all legal top-r slots; the record itself uses slot zero and is immediately removed. On H_k, retain only orders in which that rank lies in a top-s slot, remove it, and standardize. Its language is exactly

    L = E(G(r,s) intersect Omega_H).

The deletion-shadow construction also remains finite for these parameters. Its R/U/D annotations have length at most H, including temporary arrivals; each shadow's literal state ranges over a finite set. A set of shadow types therefore ranges over a finite powerset even when the permutation has unbounded length. Delayed arrivals caused by deleting a record are handled by the U annotations. No (3,3)-specific numerical state count or optional pruning rule is needed.

Equivalently, one may now apply Albert, Atkinson and Ruskuc's one-deletion regularity theorem: for regular L in the rank-bounded universe, the language of words all of whose standardized one-entry deletions lie in L is effectively regular. Intersect it with E(Omega_H) minus L. Because every deletion stays inside Omega_H, this is exactly E(B(G(r,s)) intersect Omega_H), not a capacity-only notion of minimality. The global bound makes the intersection equal to the entire ordinary basis. Unique length-preserving encoding and finite-automaton transfer matrices give a rational length generating function. QED.

## Attribution and scope

The general finite-state deletion principle is established in Albert, Atkinson and Ruskuc, *Regular closed sets of permutations*, Theoretical Computer Science 306 (2003), 85-100, Proposition 4 and Section 2.3; their Theorem 2 relates regular bounded classes and regular bases. The contribution needed here is the global bound that places this particular entire basis in one bounded universe. [Primary author manuscript](https://www.cs.otago.ac.nz/research/publications/oucs-2002-04.pdf); [arXiv version](https://arxiv.org/abs/math/0209022); [published DOI](https://doi.org/10.1016/S0304-3975(03)00212-3).

Do not identify B(G(r,s) intersect Omega_H) with B(G(r,s)): the former can contain additional capacity obstructions outside Omega_H. Restriction to Omega_H is essential in the intermediate argument.

This is rationality of the basis enumeration for each fixed r,s, with an effective but potentially enormous automaton. It is neither a practical small-state bound uniform in r,s nor rationality/algebraicity of the whole generated class. Bounded width alone would not make an arbitrary permutation language regular; the literal finite-state recognizer and deletion theorem are also essential.
