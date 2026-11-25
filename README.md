# Project S · P01 · Optimal Mean Costs of Three-Pass Shellsort

**Miaozhen Yu (俞缪臻)** · [Project S](https://github.com/users/EternalYMZ/projects/1) · [Paper and repository directory](PROJECT-S.md)

**[English manuscript](Shellsort-P01_en/README.md)** · **[中文文稿](Shellsort-P01_cn/README.md)** · **[Main Lean theorem](Shellsort/ThreePassOptimalMean.lean)**

This repository contains the analytic proofs and Lean formalization of the optimal mean costs of three-pass Shellsort. For uniform random permutations, both the optimal mean number of successful right shifts and the optimal mean number of key comparisons are $\Theta(n^{3/2})$ when the gap sequence is fixed before the input is read.

## Main Result

Fix $n$ distinct keys, take their initial order uniformly at random, and choose integer gaps $(h,g,1)$ before reading the input, with $n>h>g\ge2$. Each pass uses ordinary insertion sort with linear scanning on its gap chains and passes the resulting permutation to the next pass. Let $M$ count successful right shifts and $C$ count key comparisons, including the unsuccessful comparison that terminates a scan whenever one occurs.

For every integer $n\ge16$, the two minima, taken separately over all admissible three-pass gap sequences, satisfy

$$
\frac{n\sqrt n}{65536}\le \min_{n>h>g\ge2}\mathbb E[M]\le 2n\sqrt n,
\qquad
\frac{n\sqrt n}{65536}\le \min_{n>h>g\ge2}\mathbb E[C]\le \tfrac52 n\sqrt n.
$$

Every admissible gap sequence satisfies both lower bounds, including sequences whose first two gaps are not coprime. With $q=\lfloor n^{1/4}\rfloor$, the single sequence $(q^2+1,q,1)$ gives both upper bounds.

The revised upper bounds charge the second pass using the footrule before and after it. The formalization also proves that the two optimal means differ by at most $3n$. If a legal table has mean shifts at most $Kn\sqrt n$, every common divisor $d\ge2$ of its first two gaps satisfies $\sqrt d\le2048K$. The sharper all-table lower coefficient $1/64$ is proved in the manuscript. [Finite formal bounds](Shellsort/ThreePassRefinedUpper.lean)

A legal deterministic family has mean shifts of order at most $n^{3/2}$ exactly when $h=\Theta(\sqrt n)$, $g=\Theta(n^{1/4})$ and $\gcd(h,g)=O(1)$. The same equivalence holds for key comparisons. Restricting to a largest residue class proves necessity. For sufficiency, a finite displacement bound accounts separately for the order of the sorted classes and the work inside each class. [All-gap order criterion](Shellsort/F09OrderFinite.lean)

Fix $d=\gcd(h,g)$. For positive limiting coordinates $a=h/\sqrt n$, $b=g/n^{1/4}$, both executed means divided by $n\sqrt n$ tend to $K_d(a,b)$. The critical approximation holds uniformly on each compact set of positive coordinates. It includes the actual second-pass contribution $\sqrt{\pi}\sqrt a/(8b)$, the within-class last-pass term and the contributions of the other $d-1$ classes. Minimizing over all legal tables gives the same attained variational infimum for the two separately optimized counters. [Uniform law](Shellsort/F09CriticalResults.lean) · [Variational infimum and original-slot proof](Shellsort/F09PhaseIntegrationFinal.lean) · [Integral definitions](Shellsort/F09CertificateFunctions.lean)

Nanoda replayed six second-pass declarations and their dependencies (46,051 declarations), and a second export connecting the actual within-class and cross-class incidences to the two global minima (59,329 declarations). The manifest provides the roots, allowlist and export fingerprints. After installing the compatible `leanexport` and `nanoda_bin` executables in the Lean toolchain, run `node audit/replay-f09.mjs` from this repository. [Replay manifest](audit/f09-replays.json) · [Reproduction script](audit/replay-f09.mjs)

## Manuscripts

The complete analytic proof is available in English and Chinese. Both versions use the same organization: a README followed by Chapters 01–06. The proof connects costs to displacement through the local net displacement $F_k$, then combines a two-pass displacement upper bound with two fluctuation lower bounds.

| Section | English | 中文 |
|---|---|---|
| Overview, main theorems, and proof outline | [README](Shellsort-P01_en/README.md) | [README](Shellsort-P01_cn/README.md) |
| 01 · Cost and displacement: deterministic lemmas | [Read](Shellsort-P01_en/01_Cost_and_Displacement_Deterministic_Lemmas.md) | [阅读](Shellsort-P01_cn/01_成本与位移_确定性引理.md) |
| 02 · First-pass estimates and the two-pass displacement theorem | [Read](Shellsort-P01_en/02_First_Pass_Estimates_and_the_Two_Pass_Displacement_Theorem.md) | [阅读](Shellsort-P01_cn/02_首趟估计与两趟位移定理.md) |
| 03 · Two fluctuation lower bounds | [Read](Shellsort-P01_en/03_Two_Fluctuation_Lower_Bounds.md) | [阅读](Shellsort-P01_cn/03_两个波动下界引理.md) |
| 04 · Upper-bound construction and four-case lower bound | [Read](Shellsort-P01_en/04_Upper_Bound_Construction_and_Four_Case_Lower_Bound.md) | [阅读](Shellsort-P01_cn/04_上界构造与四情形装配.md) |
| 05 · Related work and references | [Read](Shellsort-P01_en/05_Related_Work_and_References.md) | [阅读](Shellsort-P01_cn/05_相关工作与参考文献.md) |
| 06 · Appendix A: analytic proof and Lean formalization | [Read](Shellsort-P01_en/06_Analytic_Proof_and_Lean_Formalization.md) | [阅读](Shellsort-P01_cn/06_解析证明与Lean形式化的对应及差异.md) |

Appendix A explains the correspondence between the analytic proof and the Lean formalization, including differences in definitions, proof methods, and estimate strength. A shorter overview is available in the [proof guide](brief.md).

## Lean Formalization

The principal declarations are in the `Shellsort` namespace.

| Result | Declaration |
|---|---|
| Bounds on both optimal mean costs | [`optimal_threePass_mean_bounds`](Shellsort/ThreePassOptimalMean.lean) |
| Revised upper bounds for the natural table and for both minima | [`uniform_naturalThreePass_refined_upper` and `optimal_threePass_mean_refined_upper`](Shellsort/ThreePassRefinedUpper.lean) |
| Difference of optimal means and the common-divisor restriction | [`optimal_threePass_mean_difference` and `threePass_common_divisor_budget`](Shellsort/ThreePassRefinedUpper.lean) |
| Lower bounds for every admissible gap pair | [`uniform_threePass_cost_lower`](Shellsort/UniformThreePassLower.lean) |
| Two-pass displacement upper bound for coprime gaps | [`uniform_twoPass_footrule_bound`](Shellsort/TaggedUpper.lean) |
| Shift-cost bounds for the explicit family | [`uniform_naturalThreePassInsertionCost_bounds`](Shellsort/NaturalThreePass.lean) |
| Comparison-cost bounds for the explicit family | [`uniform_naturalThreePassComparisonCost_bounds`](Shellsort/NaturalComparisonBounds.lean) and [`uniform_naturalThreePassComparisonCost_scaled`](Shellsort/NaturalComparisonBounds.lean) |

## Reproduce

Install Git and [elan](https://github.com/leanprover/elan), clone the repository, and run the following commands from its root:

```sh
lake exe cache get
lake build
lake env lean Verify.lean
```

The [toolchain file](lean-toolchain) pins Lean 4.36.0. The [Lake configuration](lakefile.lean) and [manifest](lake-manifest.json) pin the dependencies. The first command fetches compiled dependencies from the mathlib cache. [Verify.lean](Verify.lean) prints the theorem types and their transitive axiom dependencies.

For the additional executable check, run

```sh
lake env lean ExecutionBridge.lean
```

See [ExecutionBridge.lean](ExecutionBridge.lean) for this check.

On 2026-11-25, Nanoda replayed the four declared results from `ThreePassRefinedUpper` listed in the table, together with their dependencies. It checked 46,361 declarations with the axiom allowlist `propext`, `Classical.choice`, and `Quot.sound`. The joint Lean export had SHA-256 `f5f4e9ae03d0b32394147d521bc59b090101517622e151f15cc9cf9c610d834c`.

## Project Information

The [original public version](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/tree/318307acb46089a3fc74f4528d0a461eb69a1dd5) presents the natural-family result. When citing the formalization, specify the repository commit and the relevant theorem declaration. The [Project S directory](PROJECT-S.md) lists the related papers and repositories.

This repository uses the [Apache License 2.0](LICENSE).
