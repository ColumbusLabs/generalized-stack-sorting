# An infinite basis for the (3,3)-stack

## 1. Model and results

The model is one generalized top-position `(3,3)`-stack, with the conventions
of `infinite-basis-unequal-draft.md`.
- The stack is written top first. The **depth** of a held token is the number
  of tokens above it.
- A push inserts the next input token at slot `j`, where `j <= 2` and `j` is at
  most the current height.
- A pop outputs a token of depth at most `2`. There is no bypass.
- `G` is the set of outputs generated from increasing input `1..n`; `S` is the
  set of inputs sorted to `1..n`.
- `G_H` and `S_H` impose physical capacity `H`, which counts every visited
  height, including the transient push of a record.

**Theorem 1.** For every `k >= 0`, the permutations `A(k)` (length `16+3k`) and
`B(k)` (length `17+3k`) of Section 2 are basis elements of `G`. Their inverses
are basis elements of `S`. Hence both `G` and `S` have infinite bases.

**Theorem 2.** For integer `H >= 0`, the capacity-`H` bases of `G_H` and `S_H`
are finite exactly when `H <= 4`, and infinite exactly when `H >= 5`.

These results bear on Vatter's question whether all generalized-stack bases are
finite. Atkinson's `(2,2)` basis has eight elements (see
`generalized-literature-audit.md`). So at equal widths the answer changes
between widths two and three. The threshold `H = max(r,s)+2` is the same as in
the unequal-width theorem. Equal widths `r >= 4` are not settled here
(Section 7).

## 2. The families

For `j >= 0`, put

```
x_j = 11+3j,   a_j = 13+3j,   b_j = 14+3j = x_(j+1),   R_j = 15+3j,
PI  = 5,1,7,2,4,10,3,12,9,6.
```

```
A(k) = PI, (R_0,a_0,x_0), ..., (R_(k-1),a_(k-1),x_(k-1)),
       N, a_k, 8, x_k, b_k, c_k          with N = 16+3k, c_k = 15+3k;

B(k) = PI, (R_0,a_0,x_0), ..., (R_(k-1),a_(k-1),x_(k-1)),
       R_k, a_k, N, 8, x_k, b_k, d_k     with N = 17+3k, d_k = 16+3k.
```

These are permutations:
- `PI` uses `{1,...,12} \ {8,11}`.
- The values above `12` come in consecutive blocks `a_j, b_j, R_j`.
- Each `b_j` appears as `x_(j+1)`, and `x_0 = 11`.
- The final segment supplies `8`, the last block, and `N`.

For example:

```
A(0) = 5,1,7,2,4,10,3,12,9,6,16,13,8,11,14,15
A(1) = 5,1,7,2,4,10,3,12,9,6,15,13,11,19,16,8,14,17,18
B(0) = 5,1,7,2,4,10,3,12,9,6,15,13,17,8,11,14,16
B(1) = 5,1,7,2,4,10,3,12,9,6,15,13,11,18,16,20,8,14,17,19
```

`src/stack_sorting/three_three.py` builds `A(k)`, `B(k)` and every deletion
history of Section 5 without search.

## 3. Preliminaries

**(L) Lazy normalization.** Every generated output has a lazy history. This is
§3.1 of `infinite-basis-unequal-draft.md`. It is also the kernel-checked
`generated_rangeLazy` of `formal/generalized`, proved for arbitrary widths. In
a lazy history, consider each output `v` in turn:
- If `v` is held, nothing is read and `v` is popped.
- Otherwise `v` is a new maximum. The unread values below `v` are pushed in
  increasing order, then `v` is pushed and popped at once. This pair leaves the
  stack as it was.

So, between outputs, the stack changes only by:
- inserting the newly read tokens, each at a slot at most `min(2, height)`;
- removing the output token, from depth at most `2`.

**Facts for `(3,3)`.**
- **(D1)** Held tokens never change relative order.
- **(D2)** If a held token `z` has depth at least `2`, every insertion lands
  above `z`, and `z`'s depth grows by one.
- **(D3)** Only a token of depth at most `2` can be output.
- **(D4) Pattern closure.** `G`, `S`, `G_H` and `S_H` are closed under
  patterns. This is §3.2 of the unequal draft, and is kernel-checked as
  `Run.filter` and `RunH.filter`. So a non-member all of whose single deletions
  are members is a basis element.
- **(D5) Inversion.** `p` is a basis element of `G_H` exactly when its inverse
  is one of `S_H`, with or without capacity. This is §3.3 of the unequal draft,
  and is kernel-checked as `MinimalForbidden.toSort`, `SortMinimal.toGen` and
  their capacity versions.

## 4. Rejection

**Lemma 4.1 (prefix).** In every lazy history whose first ten outputs are `PI`,
the stack after the output `6` is exactly `(11,8)`, and the tokens read are
exactly `1,...,12`.

*Proof.*
1. **Output 5.** Read `1,2,3,4`. Token `4` enters a stack of height `3` at slot
   at most `2`, so it is not at the bottom. The bottom token `z` is one of
   `1,2,3`, at depth `3`.
2. **Output 1.** By (D3), `z != 1`. After the pop, `z` has depth `2`.
3. **Output 7.** Read `6`. By (D2), `6` lands above `z`, which now has depth
   `3`.
4. **Output 2.** By (D3), `z != 2`, so `z = 3`. After the pop, the stack holds
   `{3,4,6}` with `3` at the bottom.
5. **Output 4.** The stack becomes `(6,3)`.
6. **Output 10.** Read `8`, then `9`. If `8` went above `3`, then `3` would
   have depth `2`. Then `9` would land above it (D2), giving it depth `3`, and
   the next output `3` would be impossible. So `8` is inserted below `3`, at
   slot `2`, and is the bottom token. Wherever `9` goes, `8` stays at the
   bottom.
7. **Output 3.** The pop leaves `8` at the bottom, at depth `2`.
8. **Output 12.** Read `11`. By (D2), `11` lands above `8`, which now has depth
   `3`.
9. **Outputs 9 and 6.** These pops leave exactly `(11,8)`. ∎

**Lemma 4.2 (triple).** Suppose the stack is `(x_j,8)` and the next unread
token is `a_j`. Then every lazy history that next outputs `R_j, a_j, x_j`
leaves the stack `(x_(j+1),8)`, with next unread token `a_(j+1)`.

*Proof.*
1. `R_j` is a new maximum, so `a_j` and `b_j` are read.
2. Suppose `a_j` were inserted below `8`, at slot `2`. Then `b_j` would land
   above it (D2), giving it depth `3`. But `a_j` is output right after `R_j`, a
   contradiction (D3).
3. So `a_j` lies above `8`, and `8` has depth `2`. By (D2), `b_j` lands above
   `8`.
4. Exactly `{x_j,a_j,b_j}` lie above `8`. The outputs `a_j` and `x_j` leave
   `(b_j,8) = (x_(j+1),8)`. ∎

**Lemma 4.3 (final of A).** From `(x_k,8)`, with `a_k` next unread, no history
outputs `N, a_k, 8, x_k, b_k, c_k`.

*Proof.*
1. `N` is a new maximum, so `a_k`, `b_k` and `c_k` are read.
2. As in Lemma 4.2, `a_k` must lie above `8`. Otherwise the later insertions
   would bury it at depth at least `3` before its output.
3. Then `b_k` and `c_k` land above `8` (D2).
4. After `a_k` is output, `x_k`, `b_k` and `c_k` lie above `8`. By (D1) they
   remain there, since all of them are output after `8`. So `8` has depth `3`
   when it must be output, contradicting (D3). ∎

**Lemma 4.4 (final of B).** From `(x_k,8)`, with `a_k` next unread, no history
outputs `R_k, a_k, N, 8, x_k, b_k, d_k`.

*Proof.*
1. `R_k` is a new maximum, so `a_k` and `b_k` are read.
2. As before, `a_k` lies above `8`, and then `b_k` lands above `8`.
3. After `a_k` is output, `8` has depth `2`, with `x_k` and `b_k` above it.
4. `N` is a new maximum, so `d_k` is read. By (D2) it lands above `8`, which
   now has depth `3`.
5. `x_k`, `b_k` and `d_k` are all output after `8`, so `8` cannot be output
   (D1, D3). ∎

**Proposition 4.5.** `A(k)` and `B(k)` are not in `G`, for every `k`. Hence
they are not in `G_H` for any `H`.

*Proof.*
1. By (L), it suffices to consider lazy histories.
2. Lemma 4.1 gives the stack `(x_0,8)`, with next unread token `a_0 = 13`.
3. Induction with Lemma 4.2 gives `(x_k,8)` before the final segment.
4. Lemmas 4.3 and 4.4 then give a contradiction. ∎

## 5. Every single deletion is generated

Deleting a value `v` keeps the labels. The input is the remaining values in
increasing order, and the target is the family member with `v` omitted. This is
the generated class after standardization.

Histories are lazy and are written output by output:
- `x@j` means the newly read token `x` is inserted at slot `j`.
- After the colon, the stack after that output is given, top first.
- A record is pushed at slot `0` and popped at once.
- Operations on the deleted token are simply absent.

To check a step, verify that each `x@j` has `j <= min(2, height)` and that each
held output has depth at most `2`. `deletion_witness` implements exactly these
histories.

### 5.1 The prefix

The standard history, with no deletion in the prefix, is:

```
5: 1@0,2@1,3@2,4@2 (1,2,4,3) | 1: (2,4,3) | 7: 6@2 (2,4,6,3) | 2: (4,6,3)
4: (6,3) | 10: 8@2,9@2 (6,3,9,8) | 3: (6,9,8) | 12: 11@2 (6,9,11,8)
9: (6,11,8) | 6: (11,8)
```

It ends in **regime S**, with stack `(x_0,8)`.

When the deleted value is in `PI` or is one of `8` and `11`, use the following
tables.

```
del 5 : 1: () | 7: 2@0,3@1,4@2,6@2 (2,3,6,4) | 2: (3,6,4) | 4: (3,6)
        10: 8@1,9@2 (3,8,9,6) | 3: (8,9,6) | 12: 11@2 (8,9,11,6) | 9: (8,11,6) | 6: (8,11)
del 1 : 5: 2@0,3@1,4@2 (2,3,4) | 7: 6@2 (2,3,6,4) | 2: (3,6,4) | 4: (3,6)
        10: 8@1,9@2 (3,8,9,6) | 3: (8,9,6) | 12: 11@2 (8,9,11,6) | 9: (8,11,6) | 6: (8,11)
del 7 : 5: 1@0,2@1,3@2,4@2 (1,2,4,3) | 1: (2,4,3) | 2: (4,3) | 4: (3)
        10: 6@1,8@1,9@2 (3,8,9,6) | 3: (8,9,6) | 12: 11@2 (8,9,11,6) | 9: (8,11,6) | 6: (8,11)
del 2 : 5: 1@0,3@1,4@2 (1,3,4) | 1: (3,4) | 7: 6@2 (3,4,6) | 4: (3,6)
        10: 8@1,9@2 (3,8,9,6) | 3: (8,9,6) | 12: 11@2 (8,9,11,6) | 9: (8,11,6) | 6: (8,11)
del 4 : 5: 1@0,2@1,3@2 (1,2,3) | 1: (2,3) | 7: 6@2 (2,3,6) | 2: (3,6)
        10: 8@1,9@2 (3,8,9,6) | 3: (8,9,6) | 12: 11@2 (8,9,11,6) | 9: (8,11,6) | 6: (8,11)
del 10: standard through 4: (6,3) | 3: (6) | 12: 8@0,9@1,11@2 (8,9,11,6) | 9: (8,11,6) | 6: (8,11)
del 3 : 5: 1@0,2@1,4@2 (1,2,4) | 1: (2,4) | 7: 6@2 (2,4,6) | 2: (4,6) | 4: (6)
        10: 8@0,9@1 (8,9,6) | 12: 11@2 (8,9,11,6) | 9: (8,11,6) | 6: (8,11)
del 12: standard through 3: (6,9,8) | 9: (6,8) | 6: (8)            [11 still unread]
del 9 : standard through 4: (6,3) | 10: 8@2 (6,3,8) | 3: (6,8) | 12: 11@2 (6,8,11) | 6: (8,11)
del 6 : 5: 1@0,2@1,3@2,4@2 (1,2,4,3) | 1: (2,4,3) | 7: (2,4,3) | 2: (4,3) | 4: (3)
        10: 8@1,9@2 (3,8,9) | 3: (8,9) | 12: 11@2 (8,9,11) | 9: (8,11)
del 11: standard through 3: (6,9,8) | 12: (6,9,8) | 9: (6,8) | 6: (8)
del 8 : standard through 4: (6,3) | 10: 9@2 (6,3,9) | 3: (6,9) | 12: 11@2 (6,9,11)
        9: (6,11) | 6: (11)
```

How each table ends:
- Every case except `8` ends in **regime T**. Here `8` is on top, and the stack
  is `(8,x_0)`, or `(8)` with `x_0` unread (`del 12`) or absent (`del 11`).
- Deleting `8` ends in **regime Z**, with stack `(x_0)`.

### 5.2 Steps through a triple (`j < k`)

- **S-step** (no value of triple `j` deleted):

  ```
  (x_j,8) -> a_j@1, b_j@2 (x_j,a_j,b_j,8) -> R_j -> a_j (x_j,b_j,8) -> x_j (x_(j+1),8)
  ```

- **T-step:**

  ```
  (8,x_j) -> a_j@1, b_j@2 (8,a_j,b_j,x_j) -> R_j -> a_j (8,b_j,x_j) -> x_j (8,x_(j+1))
  ```

  - If `x_j` is still unread, `R_j` first reads `x_j@1` into `(8)`.
  - If `x_j` was deleted, the same steps run without it:
    `(8) -> (8,a_j,b_j) -> (8,b_j)`.
- **Z-step** (`8` deleted):

  ```
  (x_j) -> a_j@1, b_j@2 (x_j,a_j,b_j) -> R_j -> a_j (x_j,b_j) -> x_j (x_(j+1))
  ```

In each step, the popped tokens have depth `1`, then `0`, or `1`, then `2`, so
every pop is legal.

### 5.3 A deletion inside triple `j < k`

Regime S holds on arrival, with stack `(x_j,8)`. Afterwards regime T holds.

- **Delete `R_j`.** `a_j` is now a new maximum with nothing to read:
  `(x_j,8) -> a_j -> x_j (8)`. Then `x_(j+1)` is unread.
- **Delete `a_j`.** `R_j` reads `b_j@2`:
  `(x_j,8,b_j) -> R_j -> x_j (8,x_(j+1))`.
- **Delete `x_(j+1) = b_j`.** `R_j` reads `a_j@2`:
  `(x_j,8,a_j) -> R_j -> a_j` (depth `2`) `(x_j,8) -> x_j (8)`. Then `x_(j+1)`
  is absent.

### 5.4 The final segment

**A, regime T.** Stack `(8,x_k)`. If `x_k` is unread, it is first read at
`@1`; if it is absent, omit it below.

```
a_k@1, b_k@2, c_k@2 (8,a_k,c_k,b_k,x_k) -> N -> a_k (8,c_k,b_k,x_k) -> 8
-> x_k (depth 2) -> b_k (depth 1) -> c_k
```

**A, regime Z.**

```
(x_k) -> a_k@1, b_k@2, c_k@2 (x_k,a_k,c_k,b_k) -> N -> a_k -> x_k -> b_k -> c_k
```

**A, regime S** (stack `(x_k,8)`; the deleted value is in the final segment):

| Deleted | History |
|---|---|
| `N` | `a_k` (record) `-> 8` (depth 1) `-> x_k -> b_k` (record) `-> c_k` (record) |
| `a_k` | `b_k@2, c_k@2 (x_k,8,c_k,b_k) -> N -> 8 -> x_k -> b_k -> c_k` |
| `b_k` | `a_k@1, c_k@2 (x_k,a_k,c_k,8) -> N -> a_k -> 8` (depth 2) `-> x_k -> c_k` |
| `c_k` | `a_k@1, b_k@2 (x_k,a_k,b_k,8) -> N -> a_k -> 8` (depth 2) `-> x_k -> b_k` |

**B, regime T.** Stack `(8,x_k)`, with the same conventions for an unread or
absent `x_k`.

```
a_k@1, b_k@2 (8,a_k,b_k,x_k) -> R_k -> a_k (8,b_k,x_k) -> d_k@2 (8,b_k,d_k,x_k)
-> N -> 8 -> x_k (depth 2) -> b_k -> d_k
```

**B, regime Z.**

```
(x_k) -> a_k@1, b_k@2 (x_k,a_k,b_k) -> R_k -> a_k -> d_k@2 (x_k,b_k,d_k) -> N -> x_k -> b_k -> d_k
```

**B, regime S:**

| Deleted | History |
|---|---|
| `R_k` | `a_k` (record) `-> b_k@2, d_k@2 (x_k,8,d_k,b_k) -> N -> 8 -> x_k -> b_k -> d_k` |
| `a_k` | `b_k@2 (x_k,8,b_k) -> R_k -> d_k@2 (x_k,8,d_k,b_k) -> N -> 8 -> x_k -> b_k -> d_k` |
| `N` | `a_k@1, b_k@2 (x_k,a_k,b_k,8) -> R_k -> a_k -> 8` (depth 2) `-> x_k -> b_k -> d_k` (record) |
| `b_k` | `a_k@1 (x_k,a_k,8) -> R_k -> a_k -> d_k@2 (x_k,8,d_k) -> N -> 8 -> x_k -> d_k` |
| `d_k` | `a_k@1, b_k@2 (x_k,a_k,b_k,8) -> R_k -> a_k -> N -> 8` (depth 2) `-> x_k -> b_k` |

### 5.5 Coverage

Each value of `A(k)` falls in exactly one of these classes:
- `PI ∪ {8,11}`: Section 5.1, then T- or Z-steps, then the T or Z final.
- `{R_j, a_j, x_(j+1)}` for `j < k`: S-steps, then Section 5.3, then T-steps
  and the T final. This includes `x_k = x_((k-1)+1)` when `k >= 1`.
- `{N, a_k, b_k, c_k}`: S-steps, then Section 5.4 regime S.

For `B(k)` the last class is `{R_k, a_k, N, b_k, d_k}`. The counts match the
lengths: `10+2+3k+4 = 16+3k` and `10+2+3k+5 = 17+3k`.

*Proof of Theorem 1.*
1. By Proposition 4.5 the members are not generated.
2. By Section 5, every single deletion is generated.
3. By (D4) they are basis elements. By (D5) their inverses are basis elements
   of `S`.
4. The lengths are pairwise distinct, so both bases are infinite. ∎

## 6. Capacity

The visited heights can be read off the stacks above: each record adds one
transient slot. For every deletion of `B(k)`, every record is pushed onto at
most four held tokens. So every history in Section 5 for `B(k)` has maximum
height at most `5`.

The `A` histories can reach height `6`, in the A final of regime T. `B(k)` has
`w = 5`, where `w(p) = 1 + max_j(p_j - j)` (one-based), while `A(k)` has
`w = 6`. This is consistent with the kernel-checked fact (`RunH.bounded`) that
`w(p)` is a lower bound on the height of any history generating `p`.

*Proof of Theorem 2.*
- **`H >= 5`.** `B(k)` is not in `G_H` (Proposition 4.5). Each of its single
  deletions is in `G_5`, which is contained in `G_H`. By the kernel-checked
  pattern closure of `G_H` (`RunH.filter`), `B(k)` is a capacity-`H` basis
  element. Infinitely many lengths occur.

  For `S_H`, use the capacity-preserving inversion (`MinimalForbiddenH.toSort`).
- **`H <= 4 = max(3,3)+1`.** Apply the kernel-checked `finite_basis_gen` and
  `finite_basis_sort` of `formal/unequal`. They are stated for all positive
  widths, so they include `r = s = 3`. Every capacity-`H` basis element then
  has length `H+1`, so the bases are finite. ∎

## 7. Scope and open questions

- `(r,r)` for `r >= 4` is not settled. Bounded computations only (Section 8):
  - The unequal formula at `r = s` with `m = 0`, and one relay-swapped variant,
    give basis elements of lengths `3r` and `3r+2` for `r = 3,4,5`.
  - The `(4,4)` basis has `576, 3456, 5184` elements at lengths `9, 10, 11`.
  - No `(4,4)` family is known.
- The `(3,3)` basis is not classified. For example, it also has elements of
  lengths divisible by three, such as `12` and `18`. No general statement about
  them is made.
- No enumeration, priority or algebraicity claim is made.

How the families were found: exhaustive bases through length `13`, then
targeted prefix searches, then a period-three pattern. This history is
recorded for transparency only; the proof above does not depend on it.

## 8. Finite checks (not part of the proof)

- **Exhaustive `(3,3)` bases**. The
  enumerator is in `scripts/equal_width/`; it needs a C compiler with OpenMP.

  | Length | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
  |---|---|---|---|---|---|---|---|
  | Basis elements | 36 | 108 | 72 | 216 | 324 | 288 | 720 |

  The controls reproduce Atkinson's eight `(2,2)` elements and the known
  `(2,3)` growth.
- **Family checks** (`scripts/verify_three_three.py`; specify a scratch output file):
  - rejection by an exhaustive pruned lazy search;
  - every Section 5 history replayed by the repository's unchanged
    `generalized.replay`;
  - heights and `w`.
- **Bounded checks during development:**
  - The C checker `scripts/equal_width/check.c` and a second Python checker
    confirmed both families for `k <= 30` (lengths up to `107`).
  - Correction: the first committed `check.c` had 64-entry buffers and no
    input-length check, so its development runs covered only lengths up to
    `62`. The corrected checker validates its input and accepts lengths up to
    `127`. It was rerun under AddressSanitizer and UndefinedBehaviorSanitizer
    on all 62 members with `k <= 30`, and reported nothing
   .
  - The repository's unpruned `sorting_witness` confirmed that `A(0)` is
    rejected (about 90 s, under a 6 GB address-space limit).
  - The same check on `B(0)` stopped at that limit and carries no conclusion.
