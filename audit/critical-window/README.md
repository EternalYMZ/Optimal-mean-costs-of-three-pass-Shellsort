# Quantitative critical window

For fixed divisor $d$ and normalized gap coordinates in any fixed compact positive rectangle $D$, the actual three-pass means for shifts and key comparisons differ from $n^{3/2}K_d(a,b)$ by $O_{D,d}(n^{11/8})$. In particular the separately optimized costs satisfy $m_n^X=\kappa n^{3/2}+O(n^{11/8})$; with the noncoprimality constraint the same assertion holds with $\kappa_2$. These rates have analytical proofs. The prior Lean roots certify the limiting constants.

The arc counts use the original pivot identity in Janson and Knuth's Lemma 1, with the complementary arc for a wrapped pair. Goldstein's Theorem 1.1 bounds the Wasserstein distance of the sum of independent centered variables to a Gaussian of the same variance by the sum of absolute third moments divided by that variance. The binomial phases and conditional endpoint counts use the same inequality. The fixed-divisor finite window controls the classical second-pass remainder at the critical scales. [Janson and Knuth](https://arxiv.org/pdf/cs/9608105) · [Goldstein](https://doi.org/10.1214/10-AOP527)

From the repository root run:

~~~sh
python audit/critical-window/check_arc_orientations.py
~~~

The checker executes both orientations of the incident inversion counts on 55,104 permutation/table pairs. The finite test covers 309,288 forward and 225,408 wrapped counts.
