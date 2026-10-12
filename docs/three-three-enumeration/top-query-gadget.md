# A top-query gadget and a growing labelled-state obstruction

This concerns the exact generalized top-position (3,3) machine and distinct labelled output words. It does not imply nonalgebraicity or rule out a pushdown/word representation.

## 1. Exact gadget

Let sigma be a physical top-first stack of already-read tokens, and let x be one of them. Let u,u+1,u+2,u+3 be the next four unread input labels; all are larger than the old tokens. The requested output block is

    (u+3, x, u, u+1, u+2).

Its lazy execution first reads the four new tokens. The token u+3 is the new record and is immediately output. Its insertion/removal at any legal slot leaves the other tokens in the same order, so it may be ignored when analysing the three preceding new insertions.

**Gadget lemma.** The block is feasible from sigma if and only if x is physically on top of sigma. When feasible, the complete set of possible residual old stacks is the singleton consisting of sigma with its top token x removed. Every fresh token has been output.

### Proof: sufficiency

If sigma=(x,tail), insert u at slot 1, u+1 at slot 2, and u+2 at slot 2, using zero-based top positions. This gives

    (x,u,u+2,u+1,tail).

Insert/output u+3 at the top. Then output x,u,u+1,u+2 at slots 0,0,1,0. The residual stack is tail. All slots are among the first three.

### Proof: necessity

The relative order of old tokens never changes. If x initially has at least three predecessors, it cannot be the first old token output. If it has exactly two predecessors, the very first fresh insertion must be at a slot above x, since inserting immediately below x would require slot 3; x then becomes inaccessible and cannot be output first.

Suppose instead x initially has exactly one old predecessor a. For x to remain accessible after the three fresh insertions, at most one fresh token may precede it. The first fresh token u cannot precede x: that would put x at depth 2, and each subsequent legal insertion would precede x as well, making it inaccessible. Thus u is inserted immediately below x at slot 2. Each of u+1 and u+2 is then inserted before u, since u already has at least two predecessors and every insertion slot is at most 2. After x is output, u still has the three predecessors a,u+1,u+2, so the required next output u is impossible.

Every non-top case is excluded. Since the block outputs x and all four fresh labels, while old-token relative order is unchanged, the only possible residual old stack is sigma minus x. QED.

## 2. Exact set filtering and complete order tests

For any initial set L of possible physical stacks on the same old labels, the gadget's deterministic set image is

    {tail : (x,tail) belongs to L}.

This is a set operation; different insertion histories do not give multiplicities.

Given a target initial order sigma=(x_1,...,x_h), concatenate h such gadgets, with fresh consecutive labels for each block and old query targets x_1,...,x_h. Induction on the gadget lemma shows that this complete output word is feasible from an initial physical order tau if and only if tau=sigma. It uses exactly 4h fresh tokens and outputs all 5h old/fresh tokens.

For the original machine, arbitrary early input consumption does not invalidate this argument: the reviewed lazy-normalization theorem supplies an equivalent history in which each record reads only through its own label. Alternatively, the lemma for one block uses exactly four available future labels and is literal without that bridge.

It follows that distinct initial stack-order sets L and L' always have different **labelled continuation languages**. Choose an order in their symmetric difference and use its complete order test. This is stronger than simply finding unequal cardinalities of the two sets.

### No dominant physical representative

For two different physical orders sigma and tau on the same old labels, their labelled continuation languages are incomparable: the complete test for sigma is admitted only from sigma, and the complete test for tau only from tau. More generally, no proper subset of a finite physical-stack set L has the same future continuation language as L.

Thus selecting one canonical *physical* stack at a prefix cannot preserve every possible future output when the true state contains multiple orders. An explicit representative-list determinization cannot discard any represented order either. For example, the reachable state Z B T^(h-2) contains exactly 2 times 3^(h-2) physical orders, and every one has an exclusive continuation test. A compressed symbolic relation can still represent all these orders, as the reviewed normal form does.

## 3. An explicit exponential family of distinguishable reachable states

For each height h>=2, all states Z B w with w in {B,T}^(h-2) are reachable: begin with N3, append T by N2, and append B at current height a by N3 H_(a+1). There are 2^(h-2) different state languages. If two words differ at coordinate j, a code with digit 2 at j and digit 0 everywhere else belongs to the state allowing T there and not to the one allowing only B (choose a differing coordinate oriented in that direction).

At old height a and target old numerical rank k, each gadget has the standardized output code N4 H_k H_a H_a H_a. Thus a fixed target order on standardized held ranks gives the same continuation code for all compared height-h states, even if their reachability prefixes used different actual labels or maxima.

The order-testing construction therefore makes these 2^(h-2) states pairwise continuation-distinguishable. Any deterministic online recognizer that merges whole held-state languages into finitely many literal continuation-equivalence states must retain at least this many distinguishable configurations at height h.

For a machine with an explicit physical capacity H, the same argument applies whenever h+4<=H: the test's maximal transient height occurs when inserting the record token in its first gadget. The reachability macros need no greater height. In particular, for H>=6 this gives at least 2^(H-6) distinguishable configurations by choosing h=H-4.

## 4. Scope

This lower bound does not rule out a finite control attached to an unbounded stack word: the normal form stores exponentially many states in linearly many symbols. It does not rule out matrix/grammar counting identities that combine states using justified weighted relations, or the equality of some univariate completion counts under old-label relabelling. The fixed orders (1,2) and (2,1), for example, have equal total counts but are distinguished by the gadget.

Its use is to prevent an unjustified collapse from equal small counts or equal port projections to equal labelled continuation behaviour. A proposed first-return decomposition still needs an explicit treatment of the bulk and its correlations.

## 5. Finite literal corroboration

`evidence/three-three-enumeration/top-query/check_top_query_gadget.py` uses no normal-form transition code. It explicitly inserts the four fresh labels in all legal top-three positions, outputs the prescribed five labels when legal, and unions residual stacks. It checks all 5,039 physical-stack/target pairs through initial height six. Every image is exactly the one in the gadget lemma. The test took about 0.25 seconds and is supporting evidence, not the proof.
