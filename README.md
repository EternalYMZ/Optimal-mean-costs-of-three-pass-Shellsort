# Project S · P01 · Optimal Mean Costs of Three-Pass Shellsort

**Miaozhen Yu (俞缪臻)** · [Project S](https://github.com/users/EternalYMZ/projects/1) · [Paper and repository directory](PROJECT-S.md)

**[English manuscript](Shellsort-P01_en/README.md)** · **[中文文稿](Shellsort-P01_cn/README.md)** · **[Sharp three-pass theorem](Shellsort/F09Verified.lean)**

On uniform random permutations, ordinary three-pass Shellsort with the best predetermined gaps uses $(\kappa+o(1))n^{3/2}$ successful shifts or key comparisons in expectation, with each mean minimized separately. Lean proves $0.60822153\le\kappa<0.60827485406$ and characterizes every gap family attaining this coefficient.

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

For $d\ge2$, the critical cost satisfies $K_d(a,b)\ge0.61546$ at every positive scale. Hence a family attains the leading coefficient precisely when its gaps are eventually coprime and their normalized coordinates approach the compact set of minimizing pairs. This set comprises $(a,z/\sqrt a)$ with $a=\tfrac12\sqrt{z/c}$ and $z$ minimizing $\sqrt{c/z}+zJ(1/z^2)$, where $c=\sqrt{\pi}/8$. All thirteen signed quadratures, including the upper witness at $z=291/200$, are proved in Lean. [Enclosure and divisor separation](Shellsort/F09CertificateKnots.lean) · [Optimal families and shape formula](Shellsort/F09Verified.lean)

Nanoda replayed six second-pass declarations and their dependencies (46,051 declarations), and a second export connecting the actual within-class and cross-class incidences to the two global minima (59,329 declarations). The compact-shape argument and the numerical separation conditional on the thirteen integral bounds have independent Nanoda replays of 46,905 and 47,760 declarations, respectively. The full upper quadrature witness has an additional replay from an empty environment using the Lean kernel. The manifest names the checker and proof roots for each export. The finite all-gap classification replay checked 46,739 declarations. After installing the compatible `leanexport` and `nanoda_bin` executables in the Lean toolchain, run `node audit/replay-f09.mjs` from this repository. [Replay manifest](audit/f09-replays.json) · [Reproduction script](audit/replay-f09.mjs)

For an independent integer recomputation of the row scores, run the following commands from the repository root. They exercise both the half-angle recurrence and the certified sine lookup table.

~~~sh
python audit/f09_quadrature.py --output .lake/f09-integers
python audit/f09_quadrature.py --sine-table Shellsort/F09CertificateSinTableData.lean --compare .lake/f09-integers --output .lake/f09-lookup
~~~

The complete kernel export covers ten roots, including both cost limits, both family criteria and the numerical separation. To check it from an empty environment, run `node audit/replay-f09.mjs Shellsort.F09Verified`. The script checks the SHA-256, theorem names and permitted axioms before replay. The full export is approximately 519 MB. [Proof roots and exact fingerprint](audit/f09-replays.json)

For each counter separately, every noncoprime legal table eventually exceeds its finite-size optimum by strictly more than $0.00718514594\,n\sqrt n$. This follows uniformly from the lower limit $0.61546$ for noncoprime tables and the strict upper bound for $\kappa$. Consequently **every** exact minimizer, including tied minimizers, is coprime at all sufficiently large sizes. The size threshold is existential. [Three unconditional corollaries](Shellsort/F09NoncoprimeCost.lean)

To inspect the input law, executed counters, minimization domains, complete theorem types and transitive axioms together, run `lake env lean audit/Review.lean` after the build. As an independent finite check of the second-pass estimate, `python audit/check_second_pass.py` compares two-chain interleaving probabilities with all 158,323 input/table executions through size seven, then checks 11,480 inequalities through size forty. [Model and root inspection](audit/Review.lean) · [Exact finite check](audit/check_second_pass.py)

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

The finite theorems are in `Shellsort`, and the sharp coefficient and family theorems are in `Shellsort.F09`.

| Result | Declaration |
|---|---|
| Sharp limits for the actual shifts and comparisons | [`verified_three_pass_optimum`](Shellsort/F09Verified.lean) |
| Optimal families and compact set of minimizing shapes | [`verified_optimal_gap_families` and `verified_variational_shapes`](Shellsort/F09Verified.lean) |
| Strict numerical enclosure and uniform divisor separation | [`verified_kappa_precise` and `verified_noncoprime_separation`](Shellsort/F09CertificateKnots.lean) |
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
python audit/replay_knots.py --jobs 2
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
