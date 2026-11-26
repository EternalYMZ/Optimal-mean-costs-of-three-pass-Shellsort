# Signed final-pass deficit

For a uniform permutation and coprime gaps let $D=n\psi(h,g)-\mathbb E M_3$, with $M_3$ the number of final insertion shifts. Put $m=\lfloor n/h\rfloor$ and $H=\min(1,g^2/(m+1))$. The analytical bounds give

$$
 ng\sqrt h H/16384<D<2ng\sqrt h H
$$

for every $n\ge1$, $g\ge2$, and $h\ge2^{21}$. They follow from the exact source variance and a Fourier estimate of its loss relative to the binomial reference. For fixed pivot value and owner count, the true arc variance lies within $25/4$ of the circular average with the actual proportions of short and long chains. This bound also handles empty chains. For arbitrary $h,g$ the one-sided excess satisfies $\mathbb E M_3-n\psi\le\pi^2 g^3h/6$. [Original conjecture, §10](https://arxiv.org/pdf/cs/9608105#page=15)

If $h,g\to\infty$ and $n/(hg^2)\to\infty$, then $D/(g^3h^{3/2})$ converges to a positive universal constant. Directed rational quadrature gives $0.002804727333<\mathcal B<0.002821272543$. The integrand is the difference between the fully mixed and finite-time arc standard deviations. At fixed spatial coordinate the difference is convex in time. The verifier bounds its integral by midpoint and trapezoid rules and an explicit exponential tail. The rational certificate records both outward endpoints and the hash of the shared integer kernel. [Certificate](deep_constant.json) · [Calculation](deep_constant.py)

At fixed coprime $h,g$, the unnormalized long-array deficit converges to a rational value computed by a finite Poisson equation for phase occupancy counts. The stationary distribution is multinomial. Exact substitution verifies the answer on every state, including the equation replaced by the stationary centering condition. All 32 pairs selected by the state-space budget in the checker have positive limits. For $(4,3)$ the limit is $55/81$. [Exact results and state-space sizes](poisson_witness.json)

## Formal scope and replay

The new Lean code proves the signed variance identity, finite convex comparison and its quantitative gain, the physical owner/nonowner integral, and the transfer from a sufficient local sign bound to the executed last-pass cost. The large-gap sign, its profile and the deep coefficient use the analytical estimates above. Both Nanoda and Lean's default kernel accepted the proof export for 14 theorem roots. [Theorem statements](theorem-types.txt) · [Kernel record](kernel.json) · [Lean entry point](../../JKSign/Review.lean)

Run from the repository root after installing its pinned Lean dependencies. The kernel replay program uses the executables described in the main audit guide. The two exact integer checkers require Python 3.9 or newer. The directed quadrature also uses NumPy.

~~~sh
lake build JKSign.Review
lake env lean JKSign/Review.lean
node audit/replay-f09.mjs JKSign.Review
python audit/signed-deficit/variance_check.py
python audit/signed-deficit/deep_constant.py
python audit/signed-deficit/poisson_witness.py
~~~
