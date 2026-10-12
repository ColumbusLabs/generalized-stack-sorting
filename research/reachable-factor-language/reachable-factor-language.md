# Exact reachable factor language and bounded-capacity state growth

Author theorem, 10 October 2026.This counts exact lazy determinization states, not output permutations.
No algebraicity result for the unrestricted permutation class or priority
claim is made.

## 1. Statement

Use the canonical factorization of reachable (3,3) states into
Z={0}, O={1}, B={0,1}, T={0,1,2}, and C_m={0,1}^m minus {1^m} for m>=2.
The factors are ordered by increasing held label. The height of a word is
its number of coordinates, so C_m contributes m. The empty state is E.

**Reachable-language theorem.** A canonical factor word is reachable after a
lazy output prefix if and only if it is empty or satisfies all three rules:

1. Its first factor is Z.
2. Its second factor, if any, is not T.
3. Every O factor is immediately preceded by Z or O.

Equivalently, each maximal O-run follows a Z, never a B, T, or C_m. This sharpens
the earlier barrier-segment invariant, which had not excluded O after C_m.

Every allowed height-h word has an explicit reachability code using physical
capacity at most h+4. Reachability concerns the standardized remaining labels;
it does not prescribe which original labels remain.

**State inventory.** Let s_h count these states at held height h. Then

    S(z)=sum_(h>=0) s_h z^h
        =1+(z-z^2+z^3)/(1-4z+z^2).

Thus s_0,...,s_7 are 1,1,3,12,45,168,627,2340, and
s_h=4s_(h-1)-s_(h-2) for h>=4. In particular s_h=Theta((2+sqrt(3))^h).
This is a generating function for canonical states, not permutations.

**Capacity-DFA consequence.** Let M_H be the number of states of the minimal
complete DFA recognizing complete unique lazy output codes of the physical-
capacity-H (3,3) machine, over the alphabet specified in Section 6. For H>=4,

    sum_(h=0)^(H-4) s_h <= M_H <= 1+sum_(h=0)^(H-1) s_h.

Consequently M_H=Theta((2+sqrt(3))^H), and
lim_(H->infinity) (M_H)^(1/H)=2+sqrt(3).
The inequality does not assert an exact formula for M_H at finite H.

## 2. Necessity of the factor rules

The first two rules follow from the coordinate bounds c_1=0 and c_2<=1.
A clause at the first coordinate would allow its first digit to be one, so
only unary Z can be the first indecomposable factor. A unary T cannot occupy
the second coordinate. A clause beginning at coordinate two is allowed.

For the third rule, prove preservation by the reviewed normal-form updates.
Records append Z,B,T according to held height and create no O. The suffix maps
F_0 and U can create O only through a terminal call to F_1 after a Z or C_m
factor. That preceding factor becomes one or more Z cells, so every newly
created O-run has a Z immediately before it. The direct exceptional F_0 and U
formulas create no O. No other surviving prefix of an F_0/U image contains O:
O maps to Z, B maps to Z and T maps to B until the terminal exceptional call.

Deleting a selected O instead uses F_1(T^t A)=O^t f(A). If the resulting
suffix starts with O, the unchanged prefix ends in Z or O by the induction
hypothesis at the selected O. Hence the new O-run still has an allowed
predecessor. If the suffix is empty there is no new adjacency on its right.

For an inside-clause deletion, the only changed pieces are a retained free
B-prefix, an F_0 suffix, a shortened terminal clause, or a terminal merged
clause. The F_0 case has just been checked; the clause cases introduce no O.
A newly created or shortened terminal clause has no following old O. Thus
all cases preserve rule 3. The empty initial state satisfies the rules, so
they are necessary at every reachable boundary.

## 3. Exact constructive macros

Use N_b for reading the next b inputs and immediately outputting the last,
thereby appending b-1 held coordinates. Use H_k for outputting ascending rank
k among held labels. All ranks below are evaluated in the current held set.
The normal-form theorem identifies these macro updates exactly with legal
lazy physical histories, including the usual record transient capacity.

If a current state has height k>=2, N_(t+1) appends T^t. At height one its
first new held cell is B and subsequent new cells are T.

### Append B

From any nonempty state A of height k>=1, execute

    N_3, H_(k+1).

For k>=2 the intermediate suffix is TT; at k=1 it is BT. Removing its first
cell applies U(T)=B in either case. The final state is A B.

### Append Z

For height k>=2, execute

    N_5, H_(k+1), H_(k+1), H_(k+2).

The successive suffixes are T^4, B^3, ZB, Z, so the final state is A Z.
For the sole height-one state A=Z, use instead

    N_5, H_1, H_1, H_2.

The successive full states are Z B T^3, Z B^3, Z Z B, Z Z. Thus it too appends
Z at the standardized-state level. This height-one macro may replace the
original held label; no claim of preserving its identity is needed.

### Extend an O-run after a terminal Z

Suppose A ends in Z and has height k>=1. To replace its terminal Z by Z O^a,
where a>=1, first apply the append-Z macro, then execute

    N_(a+2), H_k, H_(k+a+1).

Writing A=P Z, the state before H_k is P Z Z T^(a+1). Removing the older Z
uses F_0(Z T^(a+1))=Z O^a B. Removing the last B gives P Z O^a.
The labels of the retained Z can change; the standardized word is exact.

### Append C_m

From any nonempty A of height k>=1 and m>=2:

1. Append Z by the preceding macro.
2. Execute N_m, appending T^(m-1).
3. Append B by its macro.
4. Execute H_(k+1), deleting the appended Z.

Before the final deletion the state is A Z T^(m-1) B. The exact identity
F_0(T^(m-1) B)=C_m gives A C_m.

### Assemble any allowed word

Produce the initial Z by N_2. Process the remaining factors from left to right.
Append each B or Z with its macro; append T by N_2 (the second-factor rule
ensures current height is at least two); append any C_m with its macro.
Whenever an O-run is next, the previous factor is Z by rule 3 and maximality
of the run, so apply its O-extension macro. This constructs every allowed word.
It proves sufficiency without inferring reachability from a finite census.

## 4. Capacity accounting

At a lazy boundary of held height k, N_b temporarily reaches physical height
k+b before outputting its record. A held output only decreases physical height.

A T append ending at height k+1 uses at most k+2 physical positions; a B append
uses at most k+3; a Z append uses at most k+5, which is final height plus four.
These bounds include the special height-one Z macro.

An O-extension by a>=1 ends at height k+a. Its append-Z submacro uses at most
k+5 positions, and its later N_(a+2) uses k+a+3. Both are at most final height
plus four. A C_m append ends at height k+m; its peaks are bounded by k+5,
k+m+1 and k+m+3, all at most final height plus three because m>=2.

During assembly the current completed target prefix has height at most h.
Every macro therefore uses physical height at most h+4. The initial N_2
also respects that bound. This proves the capacity assertion.

## 5. Rational state inventory

After a factor that cannot be followed by O, an allowed continuation is a
sequence of the following uniquely parsed chunks:

    B, T, C_m (m>=2), Z O^a (a>=0).

Their total coordinate-weight series is

    A(z)=2z+z^2/(1-z)+z/(1-z).

Hence the continuation series is

    F(z)=1/(1-A(z))=(1-z)/(1-4z+z^2).

Ignoring the second-factor restriction, a nonempty word starts with Z O^a
and then such a continuation, for total z F(z)/(1-z). The invalid words
start specifically with Z T and then an arbitrary continuation, of weight
z^2 F(z). Subtracting those words and adding the empty word gives S(z) above.

Uniqueness of canonical factorization ensures distinct words are distinct
state languages, so this enumeration has no representation multiplicity.
The smallest-modulus denominator root is 2-sqrt(3), the numerator of the
nonempty part is positive there, and the pole is simple. Equivalently the
constant-coefficient recurrence gives s_h=Theta((2+sqrt(3))^h).

## 6. DFA alphabet and proof of state complexity

Fix integer H>=1. Use the common finite alphabet

    N_1,...,N_H, H_1,...,H_(H-1),

where H_k uses ascending held rank. Invalid ranks and records violating
current_height+b<=H reject. Accept exactly at the empty held state. These
are the reviewed unique output codes, with one letter per output value;
physical histories themselves are not counted as different words.

Every nonempty lazy output boundary has held height at most H-1, because
its last operation was an output from physical height at most H. The exact
normal-form automaton therefore has at most sum_(h=0)^(H-1) s_h ordinary
states and one rejecting sink. This proves the upper bound, whether or not
all the counted states are reachable within this capacity.

For the lower bound, every allowed state of height h<=H-4 is reachable within
capacity H by Section 4. Distinct states of the same height have distinct
physical-stack sets by the normal-form uniqueness theorem. The already
reviewed top-query construction supplies, for every physical order sigma
on h old labels, a complete continuation accepted from an old physical
order tau exactly when tau=sigma. It uses four fresh inputs per queried old
label and has peak physical height at most h+4. Consequently it distinguishes
any two unequal state sets at height h within the present capacity H.

For completeness, states at unequal heights are also distinguished. From any
normal-form state of height h, its largest held label has insertion digit at
most two and is accessible. Repeating gives the no-new-input completion
H_h H_(h-1)...H_1. A state of any different height cannot accept this word:
it either rejects at a missing rank or finishes with the wrong nonzero held
count. For h=0 the empty word distinguishes the initial empty state.

These are pairwise distinct continuation languages of reachable prefixes.
The elementary Myhill-Nerode lower bound yields the displayed sum through
H-4. The upper and lower sums are both Theta((2+sqrt(3))^H), proving the growth
statement. This is about the minimal DFA of bounded-capacity unique codes,
not an unrestricted finite-state recognizer or permutation counting series.

## 7. Dependencies and priority limits

Dependencies in the accompanying repository are the
`docs/three-three-enumeration/decorated-normal-form.md` and
`docs/three-three-enumeration/top-query-gadget.md`. Section 2 sharpens the prior reachable-segment invariant;
the construction and complete state inventory are proved here separately.

The generalized-stack model and finite-storage language/automaton framework
have prior work by Atkinson and collaborators. Primary context:

- M. D. Atkinson, Generalized stack permutations (1998),
  https://doi.org/10.1017/S096354839800354X .
- M. D. Atkinson, M. J. Livesey, D. Tulley, Permutations generated by token
  passing in graphs (1997), https://doi.org/10.1016/S0304-3975(96)00057-6 .
- V. Vatter, An Assortment of Problems in Permutation Patterns,
  https://arxiv.org/html/2602.16355v2 , Section 5, Question 5.12.

No primary-source audit establishes priority of the sharper exact state
language or the 2+sqrt(3) growth constant. No novelty claim is made.
