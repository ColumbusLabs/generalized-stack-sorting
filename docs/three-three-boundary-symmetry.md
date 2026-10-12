# Proposed all-length boundary-disjointness lemma

This lemma is independent of the width-seven automaton theorem.

Let p be an input/output permutation relation for a top-position (r,s) stack, with at least r+s entries. Suppose token z is among the first r input tokens and among the final s output tokens. If deleting z leaves a feasible input/output relation, then the original relation is feasible.

Proof. Take a history of the deletion relation. Stop immediately after consuming its first r-1 input tokens, which are exactly the original first r tokens other than z. Let E be the sequence of outputs already emitted and let T be the current top-first stack. Every token of E and T belongs to those first r-1 inputs. There are at most r-1 entries in E. Since the original final s outputs start strictly after at least n-s >= r preceding outputs, the entries of E occur strictly before that final output segment.

In the original machine, consume its first r inputs with no intervening pop, arranging their final stack as E followed by T followed by z. This is possible because top-r insertion realizes every ordering of r tokens: each new token can be inserted at its target position within the already-read tokens, a slot below r. Pop E from the top. The stack is now T followed by z, and the original input is positioned immediately after its first r tokens.

Continue the chosen deletion history until the original prefix of n-s outputs has been emitted. Replay each push and pop at exactly the same numerical slot. Token z stays strictly beneath every other held token: when the deletion stack has height h and inserts at slot h, this same slot in the augmented stack is directly above z, so the invariant still holds. All other insertion slots and removal slots are unchanged and remain legal. Physical capacity is unbounded in this lemma.

At this point exactly s original tokens remain, including z and any unread tokens. Read all unread tokens at the top and pop all remaining tokens in the original requested order; each lies in a stack of at most s tokens and is accessible. This proves feasibility.

Consequently a basis element of the generated class has no value among 1,...,r in its final s output positions. Indeed, shortest-basis length is r+s+1 by the existing first-forbidden-layer theorem, while every single deletion of a basis element is feasible. The preceding lemma would contradict its rejection.

Combining this with the free boundary symmetries in the main note gives a free S_r times S_s action on the entire generated basis: relabel values 1,...,r and independently permute the final s positions. The two supports are disjoint. Each nonidentity relabelling changes an early small value, and each nonidentity tail permutation changes a tail value, so the action is free and every orbit has r!s! elements. In particular the full (3,3) basis, and every length sublayer, decomposes into 36-element orbits. This conclusion is all-length and does not depend on a width bound.

Width remark. In the generated orientation neither operation changes lazy width on a basis element. A small value <=r cannot increase the width beyond r, while every forbidden element has width at least max(r,s)+2 by the previously proved finite-capacity threshold theorem. Tail positions have displacement at most s-1, below this maximum. Thus the same free action preserves each fixed-width basis slice. For the (3,3) case the threshold gives width at least5, whereas small-value positions contribute at most3 and the final three positions at most3.
