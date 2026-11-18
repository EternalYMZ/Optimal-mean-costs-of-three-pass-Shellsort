# Three-pass Shellsort in Lean

For each integer $n\ge16$, let $q=\lfloor n^{1/4}\rfloor$. Run ordinary Shellsort with gaps $(q^2+1,q,1)$ on a uniformly random permutation of $n$ distinct keys. Let $M$ count successful right shifts and $C$ count key comparisons in linear insertion, including a final unsuccessful key comparison whenever one occurs. Lean verifies

$$
\frac{n\sqrt n}{8}\le \mathbb E[M]\le 4n\sqrt n,
\qquad
\frac{n\sqrt n}{8}\le \mathbb E[C]\le 4n\sqrt n+3n\le 5n\sqrt n.
$$

Thus both expected counts are $\Theta(n^{3/2})$ for this gap family. The quantifier ranges over input sizes for the displayed family. Each pass uses the actual output of the preceding pass, and the average is taken once over the initial permutation.

| Quantity | Theorem in the `Shellsort` namespace |
|---|---|
| Right shifts | [`uniform_naturalThreePassInsertionCost_bounds`](Shellsort/NaturalThreePass.lean) |
| Key comparisons | [`uniform_naturalThreePassComparisonCost_bounds`, `uniform_naturalThreePassComparisonCost_scaled`](Shellsort/NaturalComparisonBounds.lean) |

## Reproduce

With Git and [elan](https://github.com/leanprover/elan) installed, run the following in the repository root using Bash or PowerShell 7. The first line creates the local toolchain selector. For Windows PowerShell 5.1 use `Set-Content -Encoding ascii lean-toolchain 'leanprover/lean4:v4.36.0'` for that line.

```sh
echo leanprover/lean4:v4.36.0 > lean-toolchain
lake update
lake build
lake env lean Verify.lean
```

The build uses Lean **4.36.0**. [The Lake configuration](lakefile.lean) pins mathlib to commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. [Verify.lean](Verify.lean) prints the theorem statements and their transitive axioms. For each cost theorem the expected list is `[propext, Classical.choice, Quot.sound]`.
