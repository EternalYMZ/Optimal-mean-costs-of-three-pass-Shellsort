# The Janson–Knuth error and the executed last pass

For uniform input and positive coprime gaps, let $M_3$ count the actual shifts in the last insertion pass and let $\psi(h,g)$ be the classical binomial reference function. The analytical argument gives $|\mathbb E M_3-n\psi(h,g)|\le \pi^2g^3h^{3/2}/(2\sqrt3)$, the first conjecture of Janson and Knuth. On compact windows $h\asymp\sqrt n$, $g\asymp n^{1/4}$ the deficit $n\psi-\mathbb E M_3$ is positive for sufficiently large $n$ and has order $n^{3/2}$. The all-size upper-sign conjecture for arbitrary coprime pairs remains open. [Janson and Knuth, §10](https://arxiv.org/pdf/cs/9608105#page=15)

The Lean proof identifies the signed error with the sum of the actual permutation arc errors, matches the reference arc with the binomial sum, and proves the finite Bernoulli product coupling. For legal gaps it transfers a bound on the integrated actual arc discrepancies to both the finite and uniform cost bounds. The conditional source laws, their mean balance and their integrated Fourier estimate are combined analytically. [Precise theorem statements](theorem-types-jk.txt) · [Lean sources](../../ReviewJK/Review.lean)

Run from the repository root with the pinned toolchain. Kernel replay uses the same external checker tools as the other Project S proof exports.

~~~sh
lake build ReviewJK.Review
lake env lean ReviewJK/Review.lean
node audit/replay-f09.mjs ReviewJK.Review
python audit/inversion-error/check_jk_error.py
python audit/inversion-error/check_lift.py
~~~

Nanoda checked 18,790 declarations. Lean's default kernel accepted the same export from an empty environment. The exact threshold-integral computation agrees with 477,624 direct executions and supplies rational means for the original experimental sizes 20, 90 and 272. [Kernel fingerprints](jk-kernel.json) · [Exact results](jk-exact-results.txt)

The second Python program checks exact mean shifts and key comparisons for four-pass tables $(dH,dG,d,1)$ and the rational bounds on their coefficients. For $d=2$, the explicit table $(2q^2+2,2q,2,1)$ with $q=\lfloor(n/2)^{1/4}\rfloor$ has coefficient below $0.59880$. Optimizing this restricted four-pass family yields $(\kappa+\sqrt\pi/8)/\sqrt2$, between $0.5867418$ and $0.5867796$. Both statements concern uniform permutations and ordinary chain insertion. [Finite and rational checks](check_lift.py)
