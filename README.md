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

For coprime gaps, the formal bounds now characterize all order-optimal families. A mean-shift budget of order $n^{3/2}$ forces the two critical scales, and those scales suffice for shifts and comparisons. For arbitrary gaps with the same cost budget, Lean bounds the gcd and both normalized gaps above and below. The proof restricts the actual execution to a residue class and transfers the uniform input law to its relative ranks. [Arbitrary-divisor budget theorem](Shellsort/F09ResidueRestriction.lean) [Scale bounds and near-optimal costs](Shellsort/ThreePassGapScales.lean)

At critical scales Lean also proves the actual first-pass coefficient, constructs integer gaps realizing any fixed positive pair of scales and any prescribed positive gcd, and eliminates one variable from the variational problem. For all legal gap sequences with $h/\sqrt n\to a>0$ and $g/n^{1/4}\to b>0$, the executed second-pass mean divided by $n\sqrt n$ tends to $\sqrt{\pi}\sqrt a/(8b)$, for every gcd. Nanoda replayed the six declarations from the original-slot mixture through this limit and their dependencies (46,051 declarations, export SHA-256 `626d5cb242cebc20765f87912901a7defb85f9cf34168f9db7b23badcfa1056e`). The final-pass cost and the global leading coefficient have separate proof obligations. [Second-pass critical limit](Shellsort/F09SecondCritical.lean) [Integer realization and variational minimization](Shellsort/CriticalGapApproximation.lean)

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
