# Related Work and References

The study of the average complexity of three-pass Shellsort involves combinatorial counting of per-pass costs, lower bounds depending on the gap sequence, and the relation between displacement and inversion count. This section explains the connections between the present paper and these results.

## 1. Combinatorial Analysis of the Average Cost of Three Passes

Yao [Yao80] studied the average cost of $(h,k,1)$-Shellsort, deriving asymptotic formulas through a combinatorial interpretation of the third-pass cost and giving an exact expression for the fixed gap sequence $(3,2,1)$.

Janson–Knuth [JK97] further developed the counting analysis of three-pass sorting. Their Sections 1–2 and Lemma 1 use the numbers $Y_s$ of keys smaller than a specified key in the source chains, the endpoint phases modulo $g$ given by $(s+hY_s)\bmod g$, and arcs defined along the $h$-step order to express the contribution of inversions between chains as the absolute value of the difference between an occupancy count and a rounding term. Equation (3.3) of the present paper adopts this counting structure and expresses it in a symmetric form that sums over every key and every arc.

At the scales $h\asymp n^{7/15}$ and $g\asymp n^{1/5}$, Section 9 of Janson–Knuth obtains an average upper bound of $O(n^{23/15})$. The additive error term in their asymptotic formula is $O(g^3h^2)$; when $h\asymp\sqrt n$ and $g\asymp n^{1/4}$, this error bound does not suffice to obtain $O(n^{3/2})$. Section 10 of that paper discusses these scales, studies $h=g^2+1$ experimentally, and proposes a more refined conjecture for the additive error and a one-sided inequality conjecture.

The present paper uses Theorem B to estimate directly the actual displacement of a specified key after two passes. This yields, for the family of gap sequences $(q^2+1,q,1)$, an $O(n^{3/2})$ upper bound on the average cost.

## 2. Lower Bounds in Terms of the Number of Passes and the Gap Sequence

Jiang–Li–Vitányi [JLV00] gave a lower bound on average complexity in terms of the number of passes. For each fixed number of passes $p$, this lower bound is $\Omega(p\,n^{1+1/p})$; taking $p=3$ gives $\Omega(n^{4/3})$.

Vitányi [V18] further expressed the lower bound as a function of the gap sequence. For a gap sequence $h_1,\dots,h_p=1$, with $h_0=n$, Theorem 1 of that paper gives

$$
\Omega\!\left(n\sum_{k=1}^{p}\frac{h_{k-1}}{h_k}\right).
$$

For a three-pass gap sequence $(h,g,1)$, this expression is

$$
\Omega\!\left(n\left(\frac nh+\frac hg+g\right)\right).
$$

This result does not require the gaps to be coprime. At the scales $h\asymp\sqrt n$ and $g\asymp n^{1/4}$, it gives $\Omega(n^{3/2})$. Vitányi also observed that, if the corresponding upper-bound conjecture of Janson–Knuth holds, the average cost at these scales is $\Theta(n^{3/2})$.

Optimizing the preceding expression in gap ratios over all admissible three-pass gap sequences yields only a uniform guarantee of order $n^{4/3}$. Lemmas 3.1 and 3.2 of the present paper control, respectively, displacement fluctuations after the first pass and arc-count fluctuations after two passes with coprime gaps. They thereby establish a lower bound of order $n^{3/2}$ for every admissible three-pass gap sequence, with explicit finite constants.

## 3. Footrule and Inversion Count

Diaconis–Graham [DG77] studied the relation between Spearman's footrule and the degree of disorder of a permutation. Their Theorem 2 gives

$$
I+T\le F\le2I,
$$

where $I$ is the inversion count, $F$ is the footrule, and $T$ is the minimum number of arbitrary transpositions required to sort the permutation.

Lemma 1.1 of the present paper gives a self-contained exchange proof of the required inequality $I\le F$, and application chain by chain then gives $I_k\le F_k\le2I_k$. The local net displacement $F_k$ connects this classical relation to the triangle inequality for global displacement, providing a common deterministic tool for bounding costs from above and charging displacement to costs in lower bounds.

## 4. Main Contributions of This Paper

The analysis in this paper consists of the following three parts:

1. **Two-pass displacement upper bound.** For coprime gaps, we give the uniform nonasymptotic estimate

   $$
   \mathbb E F(S_gS_hA)\le\frac{n(g-1)\sqrt{h+3}}2.
   $$

2. **Uniform fluctuation lower bounds.** Using first-pass displacement fluctuations, a sum of variances on the circle, subtraction of the variance of a single phase, and Poisson-binomial deviations, we establish a lower bound on the average cost for all admissible three-pass gap sequences.
3. **Optimal order of average cost.** The explicit family of gap sequences $(q^2+1,q,1)$, $q=\lfloor n^{1/4}\rfloor$, attains an upper bound of the same order, establishing that the optimal average costs for the number of successful right shifts and the number of key comparisons are both $\Theta(n^{3/2})$.

To the best of our knowledge, this paper is the first to establish the uniform nonasymptotic upper bound on two-pass displacement stated above and to prove that the optimal average cost among all admissible predetermined three-pass gap sequences is $\Theta(n^{3/2})$. Theorem A gives both a uniform lower bound valid for every admissible gap sequence and an upper bound attained by an explicit family of gap sequences.

## 5. References

**[DG77]** P. Diaconis and R. L. Graham. Spearman's footrule as a measure of disarray. *Journal of the Royal Statistical Society, Series B (Methodological)*, **39**(2):262–268, 1977. [DOI: 10.1111/j.2517-6161.1977.tb01624.x](https://doi.org/10.1111/j.2517-6161.1977.tb01624.x).

**[Yao80]** A. C. Yao. An analysis of $(h,k,1)$-Shellsort. *Journal of Algorithms*, **1**(1):14–50, 1980. [DOI: 10.1016/0196-6774(80)90003-6](https://doi.org/10.1016/0196-6774(80)90003-6).

**[JK97]** S. Janson and D. E. Knuth. Shellsort with three increments. *Random Structures & Algorithms*, **10**(1–2):125–142, 1997. [arXiv:cs/9608105](https://arxiv.org/abs/cs/9608105).

**[JLV00]** T. Jiang, M. Li, and P. M. B. Vitányi. A lower bound on the average-case complexity of Shellsort. *Journal of the ACM*, **47**(5):905–911, 2000. [arXiv:cs/9906008](https://arxiv.org/abs/cs/9906008).

**[V18]** P. M. B. Vitányi. On the average-case complexity of Shellsort. *Random Structures & Algorithms*, **52**(2):354–363, 2018. [arXiv:1501.06461](https://arxiv.org/abs/1501.06461).
