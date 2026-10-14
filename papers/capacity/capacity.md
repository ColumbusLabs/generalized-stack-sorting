# Physical capacity in a generalized stack: exact series and a Brownian limit

**Columbus Labs** · [info@columbus-labs.com](mailto:info@columbus-labs.com)  
12 October 2026

[PDF](capacity.pdf) · [LaTeX source](capacity.tex) · [Back to papers](../../README.md#papers)

© 2026 Columbus Labs. Licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).

<a name="abstract"></a>

## Abstract

For permutations sortable by a single generalized $`(2,2)`$-stack, we study the minimum number of physical storage positions. Starting from the canonical operation language, we derive a two-series recurrence for every capacity bound. Its dominant poles approach the unbounded singularity at an explicit inverse-square rate. For a uniformly chosen sortable permutation of length $`n`$, minimum capacity divided by $`\sqrt n`$ converges to an explicit multiple of the maximum of a standard Brownian excursion, with convergence of all positive moments and a uniform Gaussian upper tail. The probabilistic step uses an existing reducible multitype-tree theorem: adding sterile leaves converts the token-mass conditioning into the required type-count conditioning. The underlying maximum-drop statistic, fixed-state rationality, saddle-node method and Brownian universality are established theory. The results here specialize them to the exact physical-capacity family of this machine.

**Contents**

- [1 Model, scope and main results](#section-1)
- [2 Minimum memory and the bounded recurrence](#section-2)
- [3 Positive iteration, poles and the critical point](#section-3)
- [4 A discrete saddle-node passage estimate](#section-4)
- [5 A size-conditioned tree proof of the capacity limit](#section-5)
- [6 Verification and limitations](#section-6)
- [References](#references)

<a name="section-1"></a>

## 1 Model, scope and main results

A generalized $`(2,2)`$-stack reads its input from left to right, inserts a single entry in either of its top two positions, and removes a single entry from either of those positions. Empty or singleton configurations have only the positions actually available. We write stacks top first and require output $`1,\ldots,n`$. Let $`\mathcal S_n`$ be the sortable permutations. Physical capacity counts every held token, including a token inserted and immediately removed. In particular capacity zero sorts only the empty permutation.

Atkinson's canonical sorting rule and the companion mechanism-based enumeration \[[1](#reference-1),[2](#reference-2)\] give a unique compressed operation history for each sortable input. The companion derives the already-known unbounded cubic, displayed immediately before Vatter's Problem 5.11 and in OEIS A393395 \[[3](#reference-3),[4](#reference-4)\]. We use its exact canonical language, recalled in Section [2](#section-2), rather than the forbidden-pattern basis. Its unbounded enumeration theorem has a separate Lean certificate. None of the analytic or probabilistic claims below is covered by that certificate.

For $`\pi\in\mathcal S_n`$, write $`c(\pi)`$ for its minimum physical capacity and let

```math
F_H(x)=\sum_{n\ge0}|\{\pi\in\mathcal S_n:c(\pi)\le H\}|x^n.
```

The empty permutation has capacity zero. The maximum-drop statistic uses one-based positions:

```math
D(\pi)=\max_{1\le i\le n}(i-\pi_i).
```

<a name="theorem-1"></a>

**Theorem 1 (exact capacity family).** For every nonempty sortable input, $`c(\pi)=D(\pi)+1`$, attained by the canonical sorter. The series $`F_H`$ are rational: put $`k_0=F_0=1`$, and for $`H\ge1`$ use

<a name="equation-1"></a>

```math
k_H=\frac1{1+x-4xk_{H-1}+2xF_{H-1}},\qquad
 F_H=\frac1{1-xk_{H-1}}.                                      \qquad\text{(1)}
```

Here and below all counting functions denote formal power series at zero; when evaluating at a positive real argument we explicitly stay before their first poles. Let $`t`$ be the unique root of $`6t^3+2t^2-5t+1=0`$ in $`(0,1/3)`$, and set

```math
\rho=\frac{t(1-3t)}{(1+t)(1-2t-2t^2)},\quad
 L=1+t,\quad K=\frac{t}{\rho L},\quad d=1-2t^2,
```

<a name="equation-2"></a>

```math
A=\frac{K(K-1)/\rho-2\rho K^3L^2}{d},\qquad
 B=\frac{1-2t^3}{Kd}.                                         \qquad\text{(2)}
```

Both constants are positive. Numerically $`\rho=0.1338790671510627\ldots`$.

<a name="theorem-2"></a>

**Theorem 2 (capacity poles).** For $`H\ge1`$, $`F_H`$ has a unique dominant pole $`\rho_H`$, which is positive and simple. As $`H\to\infty`$,

<a name="equation-3"></a>

```math
\rho_H-\rho\sim\frac{\pi^2}{ABH^2},\qquad
 \rho^{-1}-\rho_H^{-1}\sim\frac{\pi^2}{\rho^2ABH^2}.             \qquad\text{(3)}
```

The numerator constant $`\pi^2/(AB)`$ is $`3.246197810318\ldots`$.

<a name="theorem-3"></a>

**Theorem 3 (typical physical capacity).** Choose $`\pi`$ uniformly from $`\mathcal S_n`$ and put $`C_n=c(\pi)`$. If $`M`$ is the maximum of a standard normalized Brownian excursion on $`[0,1]`$, then

<a name="equation-4"></a>

```math
\frac{C_n}{\sqrt n}\ \xrightarrow{\ d\ }\ \beta M,\qquad
 \beta=\sqrt{\frac2{\rho AB}}=2.216645668588593\ldots .          \qquad\text{(4)}
```

Every positive real moment converges. There are constants $`c_0,C_0>0`$ such that

<a name="equation-5"></a>

```math
\Pr(C_n>y)\le C_0\exp(-c_0y^2/n)\quad(n\ge1,\ y>0).          \qquad\text{(5)}
```

Maximum drop has the same scaled limit. Theorem [3](#theorem-3) is proved by a separate size-and-height correspondence, not inferred from the pole asymptotic.

<a name="relation-to-prior-work"></a>

### Relation to prior work

Maximum drop and its relation to bounded priority queues are prior \[[3](#reference-3),[5](#reference-5)\]; the first part of Theorem [1](#theorem-1) is a short machine-specific corollary. Finite-capacity rationality is standard finite-state theory. Height asymptotics for classical trees and ordinary stacks have a substantial literature \[[6](#reference-6),[7](#reference-7)\]. Atkinson and Tulley already used canonical computations and bounded-height forests for binary priority-queue input/output pairs \[[9](#reference-9)\]. The general probability theorem used in Theorem [3](#theorem-3) is due to Addario-Berry, Beltran, Stufler and Thevenin \[[8](#reference-8)\], whose discussion also explicitly considers an additional infertile type. The potential contribution is the precise top-two stack family [(1)](#equation-1), its physical interpretation and class-specific constants and limits. A bounded primary-source audit found no matching family in the inspected sources; this is not a priority certificate. In particular, unpublished details of Pantone's basis-derived unbounded enumeration, cited by Vatter as personal communication, have not been compared.

<a name="section-2"></a>

## 2 Minimum memory and the bounded recurrence

<a name="section-2-1"></a>

### 2.1 Capacity equals maximum drop plus one

Immediately after input entry $`\pi_i`$ is inserted and before it is removed, at most $`\pi_i-1`$ entries can have been output. At least $`i-\pi_i+1`$ entries must therefore be held. This gives $`c(\pi)\ge D(\pi)+1`$ for every sorting history.

In any configuration admitting a successful continuation, the smallest held entry must lie in the first two positions. Otherwise two larger entries precede it. Their relative order with it cannot change, and neither can exit before it, so it can never be removed. By the companion \[[2](#reference-2), Proposition 4\], the eager canonical sorter preserves a successful continuation. It consequently emits every available initial interval of output values before reading another input.

Immediately before it reads position $`i`$, let $`v`$ be the next missing output value. This value is unread, with input position $`p\ge i`$. Exactly $`v-1`$ entries have exited, so the next insertion reaches height

```math
i-v+1\le p-v+1\le D(\pi)+1.
```

Pops never increase height. This proves the upper bound and the canonical sorter's optimality.

<a name="section-2-2"></a>

### 2.2 The canonical word model

For clarity we recall the exact operation-labelled model established in the companion \[[2](#reference-2)\]. It stores a word in letters $`L,R`$ and a Boolean flag saying whether a pop is allowed. The letters encode leaf/nonleaf marks in preorder in the canonical comparison forest. A bypass $`B`$ consumes one new input and leaves the word unchanged. The remaining operations are

```math
\begin{array}{c|c}
\text{operation and condition}&\text{new word}\\\hline
P_0\text{ on the empty word}&L\\
P_0\text{ on }w\ne\varnothing&Rw\\
P_1\text{ on }av\ (a\in\{L,R\})&RLv\\
O_0\text{ on }av&v\\
O_1\text{ on }Lav&Lv.
\end{array}
```

Pushes disable pops; bypasses and pops enable them. A pop requires an enabled flag. Start and finish with the empty word, initially enabled. Each push or bypass has weight $`x`$; pops have weight one. Equal targets do not identify labels: for example the two pushes on a word beginning with $`L`$ remain distinct.

The companion \[[2](#reference-2), Lemmas 6 and 8, Proposition 7\] proves that these complete labelled paths are in size-preserving bijection with sortable permutations. [Lemma 6](../enumeration/main.md#lemma-6) identifies forest preorder with physical stack order; the leaf-word projection keeps one letter per held token. Thus word length equals the canonical held height. A bypass expands physically to an insertion followed by a removal. It therefore requires one extra transient slot even though the compressed word does not grow.

<a name="section-2-3"></a>

### 2.3 First returns with a free-slot parameter

For a nonempty word, hold its first letter in finite control and regard the rest as a suffix stack. Let $`j`$ be the free capacity above the starting held height. Stop a first-downstep path at the first decrease of suffix-stack height. At that step the initial top suffix letter is moved into control by $`O_0`$ or discarded by $`O_1`$; the suffix below it remains untouched. For suffix letter $`b\in\{L,R\}`$, let $`T_b^{(j)}`$ and $`U_b^{(j)}`$ be its $`2\times2`$ counting matrices from an enabled or disabled flag respectively; rows and columns are the initial and final control letters, ordered $`L,R`$.

Immediate terminating pops have matrices

<a name="equation-6"></a>

```math
D_L=\begin{pmatrix}2&0\\1&0\end{pmatrix},\qquad
 D_R=\begin{pmatrix}1&1\\0&1\end{pmatrix}.                     \qquad\text{(6)}
```

The entry two retains the distinct $`O_0,O_1`$ labels. At zero free capacity only an enabled immediate pop is possible. Thus $`T_b^{(0)}=D_b`$, $`U_b^{(0)}=0`$, and $`K_0=I`$.

For $`j\ge1`$, a bypass stays at the same held height; a push uses a slot and invokes a first-downstep with $`j-1`$ free slots. Define the push-excursion matrix $`V_j`$ by

```math
\begin{aligned}
 V_j(L,e)&=2xU_L^{(j-1)}(R,e),\\
 V_j(R,e)&=x\bigl(U_R^{(j-1)}(R,e)+U_L^{(j-1)}(R,e)\bigr).
\end{aligned}
```

First-step decomposition gives

```math
T_b^{(j)}=D_b+xT_b^{(j)}+V_jT_b^{(j)},\qquad
 U_b^{(j)}=T_b^{(j)}-D_b.
```

Consequently

<a name="equation-7"></a>

```math
K_j=((1-x)I-V_j)^{-1},\quad T_b^{(j)}=K_jD_b,\quad
 U_b^{(j)}=(K_j-I)D_b.                                      \qquad\text{(7)}
```

These formal inverses exist because $`V_j(0)=0`$. The first-return decomposition is unambiguous; bounded token count also bounds path length, so zero-weight cycles do not arise.

Write $`K_j=\left(\begin{smallmatrix}k_j&0\\u_j&l_j\end{smallmatrix}\right)`$. Multiplication of [(6)](#equation-6)--[(7)](#equation-7), followed by induction from $`K_0=I`$, yields

<a name="equation-8"></a>

```math
u_j=k_j-l_j,\qquad
 k_j=\frac1{1+x-4xk_{j-1}+2xl_{j-1}},\qquad
 l_j=\frac1{1-xk_{j-1}}.                                    \qquad\text{(8)}
```

For completeness, the two diagonal denominators are those displayed in [(8)](#equation-8), while the lower-left entry is $`x(3u_{j-1}+l_{j-1}-1)k_jl_j`$; subtracting the diagonal reciprocals gives $`k_j-l_j`$ equal to that entry.

An initial push at capacity $`H\ge1`$ leaves $`H-1`$ free slots; its disabled completion is $`k_{H-1}-1`$. Decomposing a complete empty-to-empty path gives

```math
F_H=1+xF_H+x(k_{H-1}-1)F_H=l_H,
```

which proves [(1)](#equation-1). Equivalently,

```math
F_0=1,\quad F_1=\frac1{1-x},\quad
 F_{h+1}=1+\frac{xF_h}{4-3F_h+2xF_hF_{h-1}}\quad(h\ge1).
```

For example $`F_2=(1-x)/(1-2x)`$ and $`F_3=(1-2x-x^2)/(1-3x)`$. Every size-$`n`$ history has physical height at most $`n`$, so $`F_H`$ stabilizes coefficientwise to the unbounded series. Its fixed-point equation is the known cubic. No rate or random-capacity limit follows from stabilization alone.

<a name="section-3"></a>

## 3 Positive iteration, poles and the critical point

Set $`a_h=F_h-1`$, $`b_h=k_h-F_h`$. Equation [(1)](#equation-1) becomes $`y_h=G_x(y_{h-1})`$, $`y_0=(0,0)`$, with

<a name="equation-9"></a>

```math
G_x(a,b)=\left(\frac{x(1+a+b)}{1-x(1+a+b)},\quad
 \frac{x(a+3b)}{[1-x(1+2a+4b)][1-x(1+a+b)]}\right).             \qquad\text{(9)}
```

It has nonnegative Taylor coefficients and is componentwise increasing on

```math
\Omega_x=\{(a,b)\ge0:x(1+2a+4b)<1\}.
```

The orbit from zero increases until it leaves this domain.

Let $`\kappa_h`$ be the first positive pole of $`k_h`$ and $`\rho_h`$ that of $`F_h`$, with $`\kappa_0=\infty`$. Initially $`\kappa_1=\rho_1=1`$. Before the preceding $`k`$-pole, the new denominators

```math
1-x(1+2a_{h-1}+4b_{h-1}),\qquad 1-x(1+a_{h-1}+b_{h-1})
```

strictly decrease from one and cross zero once. The first denominator crosses earlier, and each zero has negative derivative. The previous $`k`$-series diverges before either denominator could stay positive indefinitely. Therefore the new singularities are genuine simple poles and

<a name="equation-10"></a>

```math
\kappa_h<\rho_h<\kappa_{h-1}\quad(h\ge2).                    \qquad\text{(10)}
```

Positivity bounds the corresponding complex moduli before these zeros, proving that the functions are analytic there. For $`h\ge2`$, the denominator of $`F_h`$ is $`1-xk_{h-1}`$, with strictly positive coefficients of both $`x`$ and $`x^2`$ in the subtracted series. Equality in the triangle inequality on $`|x|=\rho_h`$ forces $`x=\rho_h`$. Thus this is the unique dominant pole. In particular,

<a name="equation-11"></a>

```math
[x^n]F_h\sim c_h\rho_h^{-n},\qquad
 c_h=\frac1{1+\rho_h^2k'_{h-1}(\rho_h)}>0.                    \qquad\text{(11)}
```

For $`x>0`$, every nonnegative fixed point of [(9)](#equation-9) in $`\Omega_x`$ has

<a name="equation-12"></a>

```math
a=s\in(0,1/3),\quad b=\frac{s^2}{1-3s},\quad
 x=\frac{s(1-3s)}{(1+s)(1-2s-2s^2)}.                         \qquad\text{(12)}
```

The last expression is Atkinson's conjectured parametric form \[[1](#reference-1), p. 8 of the author manuscript\], with its parameter denoted here by $`s`$ and $`F=1+s`$; it also underlies Howroyd's series reversion in \[[4](#reference-4)\]. It has a unique maximum $`\rho`$ at $`s=t`$: its derivative has numerator proportional to $`(s-1)(6s^3+2s^2-5s+1)`$, and the cubic decreases strictly on $`(0,1/3)`$. At $`x=\rho`$ the increasing orbit from zero is strictly below

```math
y_*=(t,t^2/(1-3t))
```

and converges to it; its bounded limit must be the unique nonnegative fixed point. For $`x>\rho`$ there is no such fixed point and the positive orbit has finite lifetime. Otherwise the domain inequality bounds the orbit; an interior limit is a forbidden fixed point and a boundary limit makes the next iterate unbounded.

It follows that $`\kappa_h\downarrow\rho`$: the critical fixed point bounds every iterate at $`\rho`$, while any larger proposed limit would allow an infinite orbit at some $`x>\rho`$. Interlacing gives $`\rho_h\downarrow\rho`$.

<a name="section-4"></a>

## 4 A discrete saddle-node passage estimate

We give the details needed for the constant in [(3)](#equation-3), including control of entry and exit. In the linearly related coordinates $`(k,f)`$, iteration is

```math
T_x(k,f)=\bigl((1+x-4xk+2xf)^{-1},(1-xk)^{-1}\bigr).
```

At $`(x,k,f)=(\rho,K,L)`$ its Jacobian is

```math
J=\begin{pmatrix}4\rho K^2&-2\rho K^2\\\rho L^2&0\end{pmatrix}.
```

Its eigenvalues are $`1`$ and $`r=2t^2\in(0,1)`$. Normalized right and left eigenvectors for eigenvalue one are

```math
v=(1,\rho L^2),\qquad \ell=(1,-2\rho K^2)/d,\qquad \ell v=1.
```

The projected parameter derivative $`\ell\,\partial_xT`$ and half-Hessian $`\ell D^2T[v,v]/2`$ are respectively $`A,B`$ in [(2)](#equation-2). In positive $`(a,b)`$ coordinates the corresponding vectors are

```math
v_+=(\rho L^2,1-\rho L^2),\qquad \ell_+=(1/2,1/d).
```

Both are strictly positive and pair to one, so positivity of derivatives of $`G`$ also proves $`A,B>0`$.

Choose a stable eigenvector and its dual coordinate $`w`$, and put $`z=\ell_+(y-y_*)`$, $`\delta=x-\rho`$. Taylor expansion in a fixed small box gives

<a name="equation-13"></a>

```math
\begin{aligned}
 z'&=z+A\delta+Bz^2+
 O(|z|^3+\delta|z|+\delta^2+|zw|+w^2+\delta|w|),\\
 w'&=rw+O(\delta+z^2+|zw|+w^2).
\end{aligned}                                                \qquad\text{(13)}
```

There is no linear $`w`$ term in the first line because $`\ell_+`$ is a left eigenvector.

<a name="section-4-1"></a>

### 4.1 The incoming critical orbit

At $`\delta=0`$, the orbit lies componentwise below $`y_*`$. Positivity of $`\ell_+`$ gives $`|w_n|\le C|z_n|`$, while $`z_n<0`$ increases to zero. Thus [(13)](#equation-13) gives $`z_{n+1}=z_n+O(z_n^2)`$ and $`z_{n+1}/z_n\to1`$. After absorbing mixed terms in a slightly larger $`r_1<1`$,

```math
|w_{n+1}|\le r_1|w_n|+Cz_n^2.
```

Choose $`\eta>0`$ with $`r_1/(1-\eta)^2<1`$. Eventually $`|z_{n+1}|\ge(1-\eta)|z_n|`$. Iterating the stable inequality gives $`|w_n|=O(z_n^2)`$: the previous squared coordinates are bounded by $`z_n^2(1-\eta)^{-2j}`$, so the resulting geometric sum converges, and the initial stable term divided by $`z_n^2`$ tends to zero. This uses the incoming positive cone and excludes pure stable-direction approach.

<a name="section-4-2"></a>

### 4.2 A uniform tracking strip

Fix a Taylor box and a bound $`C_*`$ for [(13)](#equation-13), before choosing a strip width. Let $`C_{\rm in}`$ bound $`|w_n|/z_n^2`$ on the late critical orbit. Choose

```math
M>\max\{2C_{\rm in},4C_* /(1-r)\},
```

and only then choose $`\epsilon>0`$ sufficiently small. Consider

```math
|w|\le M(\delta+z^2),\quad |z|\le\epsilon,\quad0\le\delta\le\epsilon^2.
```

Require $`2M\epsilon^2\le\epsilon`$. With $`h=\delta+z^2`$, the center remainder divided by $`h`$ is at most

```math
C_*[2\epsilon+\epsilon^2+M\epsilon+2M^2\epsilon^2+M\epsilon^2].
```

Shrink $`\epsilon`$ so this is at most one. Then, with $`C_1=\max(A,B)+1`$ independent of $`M`$,

```math
|z'-z|\le C_1h,\qquad \delta+(z')^2\ge(1-2C_1\epsilon)h.
```

The stable estimate gives

```math
|w'|\le[(r+2C_*\epsilon)M+C_*]h.
```

Further require $`r+C_*/M+2(C_*+C_1)\epsilon<1`$. These inequalities show that the same strip is invariant until the center coordinate exits the neighborhood. All constants have been chosen in noncircular order: Taylor box, $`C_*`$, $`C_{\rm in}`$, $`M`$, then $`\epsilon`$.

After this choice, take one fixed late critical iterate $`N`$ with $`-\epsilon/2<z_N(0)<0`$. It has strict margin $`|w_N(0)|<(M/2)z_N(0)^2`$. Continuity of finitely many iterates puts the perturbed orbit inside the same strip at time $`N`$ for all sufficiently small positive $`\delta`$, still with a negative, nonzero entry coordinate. In particular its width ratio stays below $`3M/4`$. The incoming time is uniformly bounded.

Inside the strip [(13)](#equation-13) now implies, with a fixed constant $`C`$ after $`M`$ is chosen,

<a name="equation-14"></a>

```math
(A-C\epsilon)\delta+(B-C\epsilon)z^2
 \le z'-z\le
 (A+C\epsilon)\delta+(B+C\epsilon)z^2.                        \qquad\text{(14)}
```

Take $`\epsilon`$ small enough that all four coefficients are positive.

<a name="section-4-3"></a>

### 4.3 Counting steps and controlling exit

For $`q(z)=\alpha\delta+\gamma z^2`$, $`\alpha,\gamma>0`$, its relative change across a step of length $`O(\delta+z^2)`$ in $`|z|\le\epsilon`$ is $`O(\epsilon)`$, by expanding $`q(z+s)-q(z)=2\gamma zs+\gamma s^2`$. To display the comparison, put $`q_\pm(z)=(A\pm C\epsilon)\delta+(B\pm C\epsilon)z^2`$. First choose a fixed upper bound on $`\epsilon`$ so the coefficients $`A\pm C\epsilon`$ and $`B\pm C\epsilon`$ stay in compact positive intervals. For consecutive orbit points in the box, $`\Delta=z_{j+1}-z_j\le C_1(\delta+z_j^2)`$. Expanding $`q_\pm(z_j+t)-q_\pm(z_j)`$ for $`0\le t\le\Delta`$ bounds its absolute value divided by $`q_\pm(z_j)`$ by $`K_0\epsilon`$, uniformly in $`0<\delta\le\epsilon^2`$. Thus [(14)](#equation-14) gives a constant $`K`$, independent of both sufficiently small $`\epsilon`$ and $`0<\delta\le\epsilon^2`$, such that

```math
\int_{z_j}^{z_{j+1}}\frac{dz}{q_+(z)}\le1+K\epsilon,
 \qquad
 \int_{z_j}^{z_{j+1}}\frac{dz}{q_-(z)}\ge1-K\epsilon.
```

Choose $`\epsilon`$ smaller if necessary so $`K\epsilon<1`$. Summing over the $`N`$ steps from $`z_{\rm in}<0`$ to $`z_{\rm out}>0`$ gives

```math
\frac1{1+K\epsilon}\int_{z_{\rm in}}^{z_{\rm out}}\frac{dz}{q_+(z)}
 \le N\le
 \frac1{1-K\epsilon}\int_{z_{\rm in}}^{z_{\rm out}}\frac{dz}{q_-(z)}.
```

For fixed negative and positive endpoints, or endpoints converging to strictly negative and positive limits as $`\delta\downarrow0`$,

```math
\sqrt\delta\int\frac{dz}{\alpha\delta+\gamma z^2}\longrightarrow\frac\pi{\sqrt{\alpha\gamma}}.
```

Endpoint overshoots contribute $`O(1)`$ steps for fixed $`\epsilon`$. First let $`\delta\downarrow0`$, then $`\epsilon\downarrow0`$, to obtain

<a name="equation-15"></a>

```math
N_{\rm pass}(\delta)\sim\frac\pi{\sqrt{AB\delta}}.            \qquad\text{(15)}
```

This is a discrete sum comparison, not an unquantified replacement by an ODE.

At positive exit, $`y-y_*=\epsilon v_++O(\epsilon^2+\delta)`$ is componentwise at least $`(\epsilon/2)v_+`$. At $`x=\rho`$, start a comparison orbit at $`y_*+(\epsilon/2)v_+`$. Nonnegative Taylor coefficients imply that it increases; its quadratic term is nonzero. It must exit $`\Omega_\rho`$ in finitely many steps: a bounded interior limit would be a fixed point above $`y_*`$, and a boundary limit is again impossible. Monotonicity bounds the actual remaining lifetime by this finite number depending only on $`\epsilon`$. Together with the entry bound, [(15)](#equation-15) gives the total lifetime asymptotic.

<a name="section-4-4"></a>

### 4.4 Lifetime and pole indexing

Call $`h`$ steps successful when $`y_1,\ldots,y_h`$ are finite nonnegative iterates obtained by applying $`G_x`$ only to inputs in $`\Omega_x`$. Zero steps are always successful. Inductively, $`h-1`$ steps are successful exactly for $`0<x<\kappa_{h-1}`$. On this interval the next denominator

```math
Q_h(x)=1-x(1+2a_{h-1}(x)+4b_{h-1}(x))
```

strictly decreases and has its unique zero at $`\kappa_h`$. The other denominator is positive whenever $`Q_h>0`$. Hence $`h`$ steps are successful if and only if $`x<\kappa_h`$; rational continuation past an earlier pole is irrelevant.

For $`x>\rho`$ define $`N(x)=\max\{h\ge0:x<\kappa_h\}`$. The state $`y_N`$ is the first one outside $`\Omega_x`$, possibly on its boundary. Applying $`G_x`$ once more would fail. Therefore $`N(\kappa_H)=H-1`$ exactly. The passage estimate yields

```math
H-1\sim\frac\pi{\sqrt{AB(\kappa_H-\rho)}},
```

so $`\kappa_H-\rho\sim\pi^2/(ABH^2)`$. Interlacing [(10)](#equation-10) squeezes $`\rho_H`$ to the same leading asymptotic, and reciprocation proves Theorem [2](#theorem-2).

<a name="section-5"></a>

## 5 A size-conditioned tree proof of the capacity limit

<a name="section-5-1"></a>

### 5.1 A literal decorated specification

The positive map [(9)](#equation-9) defines two types of ordered decorated trees. An $`A`$-vertex has a nonempty ordered list of $`m`$ slots, each empty or occupied by an $`A`$- or $`B`$-child; its token mass is $`m`$. A $`B`$-vertex has $`p`$ prefix slots, one distinguished central child, and $`q`$ suffix slots. A prefix slot is empty or holds an $`A`$-child in two colors or a $`B`$-child in four colors. The central child is an $`A`$-child or a $`B`$-child in three colors. A suffix slot is empty or holds an uncolored $`A`$- or $`B`$-child. Its mass is $`1+p+q`$. Children follow slot order, and all colors and empty slots remain part of the decoration.

Every vertex has positive mass. Tree height counts $`A/B`$ vertices along a longest root-to-vertex path. Induction in [(9)](#equation-9) says that $`(a_H,b_H)`$ counts these trees of height at most $`H`$. Their total vertices and slots are bounded by total mass, so every fixed-size set is finite. For $`n\ge1`$, a uniform mass-$`n`$ $`A`$-rooted tree has exactly the capacity distribution:

```math
\Pr(C_n\le H)=\frac{[x^n]a_H}{[x^n]a},\qquad a=\lim_Ha_H.
```

Equality of cumulative counts suffices; we do not assert an additional explicit metric-tree bijection on permutations.

<a name="section-5-2"></a>

### 5.2 Converting mass to a type count

Put $`\tau=(\tau_A,\tau_B)=(t,t^2/(1-3t))`$. At each mass-$`m`$ vertex append $`m`$ sterile type-$`C`$ leaf children after the existing ordered children. Keep the original decoration as a mark. The expanded tree has $`n`$ sterile vertices exactly when the original mass is $`n`$. Its edge-height is exactly the original node-height: a deepest $`A/B`$ vertex at depth $`H-1`$ has a sterile child at depth $`H`$, and no longer path exists.

Assign an $`i`$-vertex decoration of mass $`m`$ and ordered $`A/B`$ offspring $`j_1,\ldots,j_r`$ probability

```math
\frac{\rho^m\prod_{l=1}^r\tau_{j_l}}{\tau_i}.
```

These probabilities sum to one because $`G_i(\rho,\tau)=\tau_i`$. Sum probabilities of decorations with identical ordered offspring, then forget marks. This gives an ordinary three-type ordered Bienayme process with offspring probability-generating functions

<a name="equation-16"></a>

```math
\phi_i(s_A,s_B,s_C)=\frac{G_i(\rho s_C,\tau_As_A,\tau_Bs_B)}{\tau_i}
 \quad(i=A,B),\qquad \phi_C=1.                               \qquad\text{(16)}
```

Multiplying the marked probabilities over a finite $`A`$-rooted tree telescopes to $`\rho^n/\tau_A`$. Conditional on having $`n`$ sterile vertices, all mass-$`n`$ decorated trees are therefore equally likely. Forgetting marks preserves height and sterile count. This resolves the conditioning mismatch: conditioning on the number of $`A/B`$ vertices instead would not model token size.

<a name="section-5-3"></a>

### 5.3 Checking the probability theorem

We apply Theorem 1.5 of \[[8](#reference-8)\], the reducible multitype Bienayme-tree limit theorem, with conditioning weight vector $`(0,0,1)`$. At $`(\rho,\tau)`$ the two denominators of $`G`$ are positive, respectively

```math
\frac1{1+t},\qquad \frac{1-3t}{1-2t-2t^2}.
```

Thus [(16)](#equation-16) is finite near $`(1,1,1)`$ and the offspring laws have exponential moments. With $`D=\mathop{\mathrm{diag}}\nolimits(\tau_A,\tau_B)`$, the core mean matrix is

```math
M_0=D^{-1}G_y(\rho,\tau)D.
```

All entries are positive and its eigenvalues are $`1,2t^2`$. It is irreducible and critical. The full mean matrix is

```math
\begin{pmatrix}M_0&m\\0&0\end{pmatrix},\qquad
 m_i=\rho G_{i,x}(\rho,\tau)/\tau_i>0.
```

The extra type is sterile, hence subcritical. Nondegeneracy holds because an $`A`$-vertex has positive probability both of no core children and of two $`A`$-children. Every $`n\ge1`$ is admissible: an $`A`$-root with $`n`$ empty slots has mass $`n`$. These verify the critical-core, subcritical attachment, moment, conditioning and nondegeneracy hypotheses of the cited theorem without a subsequence restriction.

<a name="section-5-4"></a>

### 5.4 The scaling factor

Let $`p,q`$ be positive left and right eigenvectors of $`M_0`$, with $`p_A+p_B=1`$ and $`p\cdot q=1`$. Define

<a name="equation-17"></a>

```math
\mu=\sum_i p_im_i,\qquad
 \sigma^2=\sum_{i,j,k}p_iq_jq_k\frac{\tau_j\tau_k}{\tau_i}
 G_{i,y_jy_k}(\rho,\tau),                                    \qquad\text{(17)}
```

where indices run over $`A,B`$. The full left and right vectors are $`(p,\mu)`$ and $`(q,0)`$. The cited theorem normalizes the left vector on its core coordinates, as here. It gives metric scaling $`\sigma\sqrt\mu/(2\sqrt n)`$ toward the Brownian continuum random tree. Sterile leaves contribute to the conditioned mass but not the variance in the critical direction.

Put $`\ell=pD^{-1}`$ and $`v=Dq`$, so $`\ell v=1`$. In the positive coordinates the center coefficients are $`A_*=\ell G_x`$, $`B_*=\ell G_{yy}[v,v]/2`$. Equation [(17)](#equation-17) gives $`\mu=\rho A_*`$ and $`\sigma^2=2B_*`$. Rescaling dual eigenvectors changes the two coefficients inversely; their product is also invariant under the invertible linear coordinate change to $`(k,f)`$. Hence $`A_*B_*=AB`$ and

```math
\frac2{\sigma\sqrt\mu}=\sqrt{\frac2{\rho AB}}=\beta.
```

For comparison, direct derivative evaluation gives $`\mu=1.530393748010960\ldots`$ and $`\sigma^2=0.531941967577447\ldots`$. The factor is derived symbolically, not fitted to pole or census data.

<a name="section-5-5"></a>

### 5.5 Heights, tails and moments

Root-height is continuous under rooted Gromov--Hausdorff convergence. The continuum random tree coded by a standard normalized excursion has root-height $`M=\max e`$. Exact height equality from Section [5.2](#section-5-2) therefore gives [(4)](#equation-4).

The theorem also bounds the height tail by $`C\exp(-cy^2/n)+C\exp(-cy)`$. Deterministically $`C_n\le n`$, because each vertex on a longest original path has positive mass. For $`y\le n`$ the second exponential is bounded by the first after adjusting constants, and for $`y>n`$ the probability is zero. This proves [(5)](#equation-5). Integrating the uniform scaled Gaussian tail gives uniform integrability of every fixed positive power of $`C_n/\sqrt n`$, and hence convergence of all positive moments. Theorem [1](#theorem-1) transfers the same limit to maximum drop.

<a name="verification-provenance-and-limitations"></a>

<a name="section-6"></a>

## 6 Verification and limitations

The implementation compares independent original push/pop reachability, minimax physical capacity, expanded canonical peak and maximum drop on all 46,234 permutations of lengths zero through eight. Bounded word counts agree with [(1)](#equation-1) for capacities through eight and series degree sixteen. These are finite validation bounds, not proofs of the theorems. An optional SymPy check in the cubic number field verifies the critical fixed point, eigenvalues and identity $`\sigma^2\mu=2\rho AB`$ exactly.

The source distribution records component-source hashes, reproducible commands and the formal scope. The original $`25`$-module Lean certificate proves unbounded enumeration through the unique cubic branch. The combined $`38`$-module certificate additionally proves minimum physical capacity, the exact bounded grammar/permutation cardinalities, recurrence [(1)](#equation-1), uniqueness of that family, and coefficient stabilization. It does not formalize the analytic passage estimates or the probability theorem application.

The Brownian conclusion is a specialization of established probability machinery. The invariant-strip estimate is a direct discrete version of a standard saddle-node mechanism. The known cubic and its unbounded coefficient asymptotic are prior \[[3](#reference-3),[4](#reference-4)\]. No general universality, maximum-drop statistic or new analytic method is claimed here. A complete assessment of class-specific priority requires broader literature and expert comparison than the bounded audit provided with the repository.

<a name="references"></a>

## References

<a name="reference-1"></a>

\[1\] M. D. Atkinson, *Generalized Stack Permutations*, Combinatorics, Probability and Computing 7 (1998), 239--246. [Author manuscript](https://www.cs.otago.ac.nz/staffpriv/mike/Papers/Genstack/Genstack.pdf), DOI [10.1017/S096354839800354X](https://doi.org/10.1017/S096354839800354X).

<a name="reference-2"></a>

\[2\] *A direct enumeration of permutations sortable by a generalized (2,2)-stack*. Companion manuscript, 12 October 2026. Supplied in the accompanying source distribution at `papers/enumeration/`. See Proposition 4, Lemmas 6 and 8, and Proposition 7.

<a name="reference-3"></a>

\[3\] V. Vatter, *An Assortment of Problems in Permutation Patterns*, arXiv:2602.16355v2 (2026), Section 5, especially Problem 5.11. [Version 2](https://arxiv.org/html/2602.16355v2).

<a name="reference-4"></a>

\[4\] OEIS Foundation, [A393395](https://oeis.org/A393395). The known cubic, Andrew Howroyd's series reversion and Vaclav Kotesovec's unbounded asymptotic are credited there.

<a name="reference-5"></a>

\[5\] F. Chung, A. Claesson, M. Dukes and R. Graham, *Descent polynomials for permutations with bounded drop size*, European Journal of Combinatorics 31 (2010), 1853--1867. [Preprint](https://arxiv.org/abs/0908.2456).

<a name="reference-6"></a>

\[6\] P. Flajolet and A. Odlyzko, *The average height of binary trees and other simple trees*, Journal of Computer and System Sciences 25 (1982), 171--213. [Author-hosted paper](https://algo.inria.fr/flajolet/Publications/FlOd82height.pdf).

<a name="reference-7"></a>

\[7\] P. Flajolet and R. Sedgewick, *Analytic Combinatorics*, Cambridge University Press (2009). [Author-hosted book](https://algo.inria.fr/flajolet/Publications/book.pdf).

<a name="reference-8"></a>

\[8\] L. Addario-Berry, P. Beltran, B. Stufler and P. Thevenin, *Scaling limits of multitype Bienayme trees*, arXiv:2507.23241v2 (12 June 2026), Theorem 1.5 and Section 1.2.6. [Full theorem](https://arxiv.org/html/2507.23241v2#S1.SS4). Extended abstract, AofA 2026, Article 4 (13 July 2026), [DOI 10.4230/LIPIcs.AofA.2026.4](https://doi.org/10.4230/LIPIcs.AofA.2026.4), Theorem 9.

<a name="reference-9"></a>

\[9\] M. D. Atkinson and D. Tulley, *Bounded capacity priority queues*, Theoretical Computer Science 182 (1997), 145--157, Theorem 3.2. [Author-hosted paper](https://www.cs.otago.ac.nz/staffpriv/mike/Papers/PriorityQueues/BoundedPQs.pdf), DOI [10.1016/S0304-3975(96)00149-1](https://doi.org/10.1016/S0304-3975(96)00149-1).
