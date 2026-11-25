# Optimal Mean Costs of Three-Pass Shellsort

**Abstract.** We study three-pass Shellsort on uniform random permutations, with the gap sequence fixed before the input is read. For each of two cost measures—the number of successful right shifts and the number of actual key comparisons—we prove that the optimal mean cost is $\Theta(n^{3/2})$ and give explicit nonasymptotic bounds. The upper bounds are obtained using the family $(q^2+1,q,1)$, $q=\lfloor n^{1/4}\rfloor$, while the lower bounds hold for every admissible three-pass gap sequence. The proof uses the local net displacement $F_k$ to connect sorting costs with global displacement, combining a two-pass displacement upper bound for coprime gaps with two fluctuation lower bounds.

**Keywords.** Shellsort; average-case complexity; three-pass sorting; displacement estimates.

### Sharp leading coefficient

For either counter the optimized mean is $(\kappa+o(1))n^{3/2}$ with $0.60822153\le\kappa<0.60827485406$. Order optimality is equivalent to $h=\Theta(\sqrt n)$, $g=\Theta(n^{1/4})$ and bounded $\gcd(h,g)$. At a fixed divisor $d$ and positive limiting gap coordinates $(a,b)$, the executed mean divided by $n^{3/2}$ tends to the explicit $K_d(a,b)$. Attaining $\kappa$ requires and suffices that the gaps be eventually coprime and the normalized pair approach the full minimizing set. [Integral kernels](../Shellsort/F09CertificateFunctions.lean) · [Proof and reproduction guide](../README.md) · [Final declarations](../Shellsort/F09Verified.lean)

## 1. Model and Cost Measures

The input consists of $n$ distinct keys, which we equivalently represent as a uniform random permutation of $\{0,1,\dots,n-1\}$. A gap sequence $(h,g,1)$ is chosen in advance, where $n>h>g\ge2$ are integers. A pass with gap $k$ applies ordinary insertion sort with linear scanning to each chain of positions $r,r+k,r+2k,\dots$.

We use two cost measures:

- $M_i$ is the number of times a larger preceding key is shifted one position to the right within its chain during pass $i$. We call these operations successful right shifts and write $M=M_1+M_2+M_3$.
- $C_i$ is the number of key comparisons in pass $i$, including the comparison that terminates a scan, when it exists; $C=C_1+C_2+C_3$.

Each right shift corresponds to one successful comparison, and each insertion incurs at most one additional terminating comparison. Thus, for every input,

$$
M\le C\le M+(n-h)+(n-g)+(n-1)\le M+3n.
$$

We study the two minima over the finite set of admissible gap sequences:

$$
\min_{n>h>g\ge2}\mathbb E\,M(h,g,1),
\qquad
\min_{n>h>g\ge2}\mathbb E\,C(h,g,1).
$$

The gap sequence may depend on $n$ and is fixed before the input is read. The two objectives are minimized separately.

## 2. Main Theorems

**Theorem A (Optimal mean costs of three-pass Shellsort).** For every integer $n\ge16$,

$$
\frac{n\sqrt n}{65536}\le
\min_{n>h>g\ge2}\mathbb E\,M
\le4n\sqrt n,
\qquad
\frac{n\sqrt n}{65536}\le
\min_{n>h>g\ge2}\mathbb E\,C
\le5n\sqrt n.
$$

Thus, the optimal mean shift count and the optimal mean comparison count are both $\Theta(n^{3/2})$. The same explicit gap sequence $(q^2+1,q,1)$, $q=\lfloor n^{1/4}\rfloor$, gives both upper bounds, while the lower bounds hold for every admissible gap sequence.

**Theorem B (Two-pass displacement upper bound for coprime gaps).** For a uniform random input, if $1\le g<h<n$ and $\gcd(h,g)=1$, then

$$
\mathbb E\,F(S_gS_hA)
\le
\frac{n(g-1)\sqrt{h+3}}{2}.
$$

Here $S_kA$ denotes the array obtained by sorting each chain of positions with the same residue modulo $k$. The global displacement, or Spearman footrule, is defined by

$$
F(A)=\sum_x|P_x-R_x|,
$$

where $P_x$ and $R_x$ are the position and rank of key $x$, respectively, both indexed from $0$.

## 3. Notation and Randomization Convention

| Notation | Meaning |
|---|---|
| $I_k(A)$ | Within-chain inversion count for gap $k$: $\#\{(i,j):i<j,\ i\equiv j\pmod k,\ A_i>A_j\}$ |
| $F(A)$ | Global footrule displacement $\sum_x\lvert P_x-R_x\rvert$ |
| $F_k(A)$ | Local net displacement $\frac1k\sum_x\lvert P_x-Q_{k,x}\rvert$, where $Q_{k,x}$ is the position of key $x$ in $S_kA$; $F_1=F$ |
| $S_kA$ | State obtained by sorting each chain modulo $k$ |
| $M_i,C_i$ | Numbers of successful right shifts and key comparisons in pass $i$ |
| $L_s$ | Length of the $s$th $h$-chain; if $n=mh+r$, then $L_s=m+1$ for $s<r$ and $L_s=m$ for $s\ge r$ |
| $t$ | Value of a key (the pivot) specified by its original position |
| $Y_s$ | Number of keys in source chain $s$ that are smaller than the pivot, excluding the pivot itself |
| $D_{hg}$ | Position minus rank of the pivot after two passes |
| $m$ | $\lfloor n/h\rfloor$, the base chain length in the lower-bound lemmas |
| $s$ | $\sqrt n$, used in the upper-bound construction and the four-case lower bound |

**Randomization convention.** Place independent uniform $[0,1]$ random real numbers at the original positions, then replace them by their ranks to obtain a uniform random permutation. Specify the pivot by its original position. Conditional on its value $t$, the indicators that the keys at the other original positions are smaller than the pivot are independent $\mathrm{Bernoulli}(t)$ variables.

## 4. Proof Outline and Organization

The deterministic part connects the cost of a single pass with global displacement through

$$
I_k(A)\le F_k(A)\le2I_k(A)
$$

and

$$
|F(A)-F(S_kA)|
\le kF_k(A)
\le F(A)+F(S_kA)
$$

For the upper bound, the first-pass estimate and Theorem B control the mean shift counts in the second and third passes. We then choose $(h,g)=(q^2+1,q)$. The relation $M\le C\le M+3n$ gives both upper bounds in Theorem A.

For the lower bound, the first-pass displacement fluctuations in Lemma 3.1 and the arc-count fluctuations in Lemma 3.2 are combined with the displacement–cost inequalities. We successively consider $h^2\le n$, $g^2\le h$, $\gcd(h,g)>1$, and the remaining coprime case, obtaining a uniform lower bound for all admissible gap sequences.

| Chapter | Contents |
|---|---|
| [01 Cost and Displacement: Deterministic Lemmas](01_Cost_and_Displacement_Deterministic_Lemmas.md) | Insertion-sort costs, bounds on local displacement, and displacement relations between passes |
| [02 First-Pass Estimates and the Two-Pass Displacement Theorem](02_First_Pass_Estimates_and_the_Two_Pass_Displacement_Theorem.md) | First-pass expectation estimates and the proof of Theorem B |
| [03 Two Fluctuation Lower Bounds](03_Two_Fluctuation_Lower_Bounds.md) | Lower bounds from global displacement and arc counts |
| [04 Upper-Bound Construction and Four-Case Lower Bound](04_Upper_Bound_Construction_and_Four_Case_Lower_Bound.md) | Proof of Theorem A |
| [05 Related Work and References](05_Related_Work_and_References.md) | Literature, attribution, and contributions |
| [06 Appendix A](06_Analytic_Proof_and_Lean_Formalization.md) | Correspondence and differences between the analytic proof and the Lean formalization |

## 5. Contributions and Related Work

Janson–Knuth's three-pass analysis established the arc-counting structure and obtained an $O(n^{23/15})$ mean upper bound at a particular gap scale. Vitányi's gap-ratio lower bound gives $\Omega(n^{3/2})$ when $h\asymp\sqrt n$ and $g\asymp n^{1/4}$; a uniform lower bound for general three-pass gap sequences requires further fluctuation estimates.

We give a uniform nonasymptotic upper bound on two-pass displacement and apply first-pass displacement fluctuations and arc-count fluctuations to all admissible three-pass gap sequences. An explicit family gives the upper bounds, and every admissible gap sequence satisfies the uniform lower bounds, determining the order of the optimal mean cost under both cost measures. The deterministic part uses the classical relation between footrule and inversion count, and the arc-counting structure follows the construction of Janson–Knuth. Detailed connections to the literature and the contribution statement appear in [Related Work and References](05_Related_Work_and_References.md).
