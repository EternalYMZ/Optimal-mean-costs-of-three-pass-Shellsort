# Quantitative critical window

For fixed divisor $d$ and normalized gaps in a compact positive rectangle $D$, the mean shifts and comparisons differ from $n^{3/2}K_d(a,b)$ by $O_{D,d}(n^{5/4})$. The two separately optimized costs are $\kappa n^{3/2}+O(n^{5/4})$ over all tables and $\kappa_2 n^{3/2}+O(n^{5/4})$ over noncoprime ones. These are analytical error bounds. Existing end-to-end Lean roots certify the limits, and the new module checks the same-class averaging estimate used in the quantitative proof.

The arc counts use the original pivot identity in Janson and Knuth's Lemma 1, with the complementary arc for a wrapped pair. Goldstein's Theorem 1.1 bounds the Wasserstein distance of the sum of independent centered variables to a Gaussian of the same variance by the sum of absolute third moments divided by that variance. The binomial phases and conditional endpoint counts use the same inequality. The fixed-divisor finite window controls the classical second-pass remainder at the critical scales. [Janson and Knuth](https://arxiv.org/pdf/cs/9608105) · [Goldstein](https://doi.org/10.1214/10-AOP527)

From the repository root run:

~~~sh
python audit/critical-window/check_arc_orientations.py
python audit/critical-window/check_arc_averaging.py
lake build Shellsort.F09ArcAveraging
lake env python audit/divisor-two/replay.py Shellsort/F09ArcAveraging.lean Shellsort.F09.ArcAveraging.average_width_inv_sqrt Shellsort.F09.ArcAveraging.sqrt_variance_error Shellsort.F09.ArcAveraging.heat_variance_floor Shellsort.F09.ArcAveraging.window_width_floor Shellsort.F09.ArcAveraging.averaged_heat_error
~~~

The orientation checker executes 55,104 permutation/table pairs, including 309,288 forward and 225,408 wrapped counts. The [width checker](check_arc_averaging.py) compares discrete means with integrals on 324 exact binomial phase profiles. Run it using Python 3 and its standard library.

For a nonzero arc of width $x=j/G$, the inverse square root of $\min(x,1-x)$ has grid average at most four. The [Lean module](../../Shellsort/F09ArcAveraging.lean) combines this estimate with the actual F09 heat kernel $V$ to sum square-root perturbations. At $s=t(1-t)>0$, an absolute variance error $\epsilon$ gives a mean square-root error at most $4\epsilon/\sqrt{(1-\exp(-4\pi^2\lambda_0))s/2}$ for $\lambda\ge\lambda_0>0$. Its threshold integral is finite. The cross-class term uses a separate variance lower bound and a small-threshold interval in the analytical proof. Compactness and lattice rounding transfer the estimate to both minimization problems. [Five kernel-checked roots and hashes](arc_averaging_kernel.json)
