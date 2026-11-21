# Optimal mean costs of three-pass Shellsort

Choose $n>h>g\ge2$ before reading a uniform permutation of $n$ distinct keys. Run linear insertion with gaps $(h,g,1)$. Let $M$ count successful right shifts and $C$ actual key comparisons. For $n\ge16$ the theorem gives
$$
\frac{n^{3/2}}{65536}\le\min_{h,g}\mathbb E M\le4n^{3/2},\qquad
\frac{n^{3/2}}{65536}\le\min_{h,g}\mathbb E C\le5n^{3/2}.
$$

**One table suffices for both upper bounds.** Put $q=\lfloor n^{1/4}\rfloor$ and choose $(h,g)=(q^2+1,q)$. Count first-pass inversions directly. Mark the keys smaller than a tagged key. After the first pass each chain's marks form a prefix. Conditional on the tagged key's original slot and continuous random value, the other chains have independent binomial prefix lengths. Coprimality makes complete residue cycles cancel when counting prefix contributions to the next chains. Bounding the remaining fluctuations controls displacement after two passes and hence the final insertion work.

**The lower bound covers every table.** If $h^2\le n$, first-pass inversions suffice. If $g^2\le h$, the first pass leaves enough mean displacement: a later elementary exchange can correct at most $2g$ units. If $\gcd(h,g)>1$, both passes preserve the keys in each residue class of their common divisor. Even the best arrangement within these classes leaves substantial work.

In the remaining coprime range, inversions between a tagged key and another chain are an absolute deviation of a prefix-endpoint count on a circular arc. Central arc lengths have sufficient fluctuations. Subtracting an independent copy removes the mean bias; second and fourth moments bound the mean absolute deviation from below. Summing counts each inversion twice. Every successful shift requires a key comparison. The two minima are separate; the bounds leave the exact optimizers and leading constants undetermined.

[UniformThreePassLower.lean](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/f83ba5cca0512e1406e71107487a9034cdf5bda1/Shellsort/UniformThreePassLower.lean) · [ThreePassOptimalMean.lean](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/f83ba5cca0512e1406e71107487a9034cdf5bda1/Shellsort/ThreePassOptimalMean.lean)
