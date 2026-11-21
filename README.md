# Project S · P01 · Optimal mean costs of three-pass Shellsort

**Miaozhen Yu (俞缪臻)** · [Project S](https://github.com/users/EternalYMZ/projects/1) · [Paper and repository directory](PROJECT-S.md)

How much can an ordinary Shellsort save by choosing its three gaps well? Fix $n$ distinct keys, take their initial order uniformly at random, and choose the gaps $(h,g,1)$ before reading the input, with $n>h>g\ge 2$. Each pass runs linear insertion on its gap chains and passes the resulting permutation to the next pass. Let $M$ count successful right shifts and $C$ count key comparisons, including the unsuccessful comparison that stops a scan whenever it occurs.

For $n\ge16$, Lean proves the following bounds on the two minima, each taken separately over all legal three-pass tables.

$$
\frac{n\sqrt n}{65536}\le \min_{h,g}\mathbb E[M]\le 4n\sqrt n,
\qquad
\frac{n\sqrt n}{65536}\le \min_{h,g}\mathbb E[C]\le 5n\sqrt n.
$$

Every legal table satisfies both lower bounds, including tables whose first two gaps share a divisor. With $q=\lfloor n^{1/4}\rfloor$, the single table $(q^2+1,q,1)$ witnesses both upper bounds. Thus both optimal mean costs have order $\Theta(n^{3/2})$.

| Part of the proof | Declaration in the `Shellsort` namespace |
|---|---|
| Natural family, including its sharper lower bound $n\sqrt n/8$ | [`uniform_naturalThreePassInsertionCost_bounds`](Shellsort/NaturalThreePass.lean) and [`uniform_naturalThreePassComparisonCost_bounds`, `uniform_naturalThreePassComparisonCost_scaled`](Shellsort/NaturalComparisonBounds.lean) |
| Lower bounds for every legal pair | [`uniform_threePass_cost_lower`](Shellsort/UniformThreePassLower.lean) |
| Bounds on both finite minima | [`optimal_threePass_mean_bounds`](Shellsort/ThreePassOptimalMean.lean) |

## Reproduce

Install Git and [elan](https://github.com/leanprover/elan). From the repository root run

```sh
lake exe cache get
lake build
lake env lean Verify.lean
```

[lean-toolchain](lean-toolchain) selects Lean 4.36.0. The [Lake configuration](lakefile.lean) and [manifest](lake-manifest.json) pin the dependencies. The first command fetches compiled dependencies from the mathlib cache. [Verify.lean](Verify.lean) prints the quantified statements and their transitive axioms. The expected axioms for the cost theorems are `propext`, `Classical.choice`, and `Quot.sound`.

The 2026-11-20 independent kernel check of `Shellsort.optimal_threePass_mean_bounds` accepted the exported proof and its 46,598 declarations, including dependencies. The SHA-256 of that Lean export is `e0abc4b2e83aeef62913ff15b4943665a365b4155e4702a10fe1f56c31a13b2a`.

The [original public version](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/tree/318307acb46089a3fc74f4528d0a461eb69a1dd5) contains the natural-family result. For public review of P01, cite the commit and the declaration you checked. This repository uses the [Apache License 2.0](LICENSE).

Additional executable check: after the build, run `lake env lean ExecutionBridge.lean`. See [ExecutionBridge.lean](ExecutionBridge.lean).

## Proof guide

[Read the proof guide](brief.md). The guide explains the mathematical claim and the scope of the Lean results linked above.
