# Appendix A. Correspondence and Differences between the Analytic Proof and the Lean Formalization

This appendix describes the correspondence and differences between the main text and the Lean formalization in their definitions, the strength of their estimates, and their proof methods.

The corresponding version is [fixed commit d2e146f81dc50e87b062088ebf3d514c4ece7040 of the Optimal-mean-costs-of-three-pass-Shellsort repository][repo]. We use the notation of the main text: $F$ denotes global displacement, $F_k$ the within-chain net displacement in one pass with gap $k$, $I_k$ the within-chain inversion count, and $M_k$, $C_k$ the numbers of successful right shifts and key comparisons in that pass; in the discussion of a three-pass gap sequence, $M_2$, $M_3$ denote the numbers of successful right shifts in the second and third passes, respectively.

## A.1 Correspondence of the Main Theorems

The source declaration [optimal_threePass_mean_bounds][lean-main] for Theorem A takes the minima over admissible gap sequences separately for the average number of right shifts and the average number of comparisons. Its condition $n\ge16$ and constants $65536$, $4$, $5$ are the same as in the main text. The gap sequence is chosen before the random input, and the two objectives are minimized separately.

Theorem B corresponds to [uniform_twoPass_footrule_bound][lean-two]. This declaration requires only that the two gaps be positive and coprime; its scope includes $1\le g<h<n$ as used in the main text. The main text adopts the range required by the three-pass algorithm.

The refinement of the constant in the first-pass displacement estimate is discussed in A.2; the remaining differences concern equivalent expressions of definitions, elementary simplifications, special cases of general theorems, and proof methods.

## A.2 Precision of the First-Pass Displacement Estimate

Equation (2.2) in the main text gives

$$
\mathbb E F(S_hA)
\le
n\left(h-1+\frac{\pi}{8}\sqrt{nh}\right).
$$

The Lean declaration [uniform_onePass_footrule_bound][lean-first] gives

$$
\mathbb E F(S_hA)
\le
n\left(h-1+\frac12\sqrt{nh}\right).
$$

Since $\pi/8<1/2$, the analytic estimate in the main text is stronger. The Lean declaration above gives the $1/2$ version and does not include the $\pi/8$ refinement.

The derivation of the upper bound in Theorem A uses only the $1/2$ version. Thus neither the constant $4$ for the average number of right shifts nor the constant $5$ for the average number of comparisons depends on this refinement.

## A.3 Equivalent Expressions for Local Displacement and Comparison Cost

### A.3.1 Definition of Local Displacement

The main text defines local displacement in terms of the actual positions of each key before and after a pass:

$$
F_k(A)
=
\frac1k\sum_x
\left|P_A(x)-P_{S_kA}(x)\right|.
$$

In Lean, [chainFootrule][lean-chain] sums the absolute differences between each key's relative rank within its chain and its original chain coordinate. For $k>0$, [gapSort_transport_eq_mul_chainFootrule][lean-chain] proves that the sum of the actual positional distances is exactly $k$ times this quantity. Together with reindexing the sum over keys as a sum over original positions, this shows that the two definitions agree.

The two sides of $I_k\le F_k\le2I_k$ correspond, respectively, to [gapInversions_le_chainFootrule][lean-invchain] and [chainFootrule_le_twice_gapInsertionCost][lean-weighted]; the latter yields the right-hand inequality when combined with [gapInsertionCost_eq_gapInversions][lean-cost].

### A.3.2 Comparison Overhead in Terms of Chain Lengths

For $1\le k\le n$, the main text writes

$$
I_k(A)\le C_k(A)\le I_k(A)+n-k.
$$

Let $L_s$ be the length of chain $s$. The Lean declaration [gapComparisonCost_upper_chains][lean-comparison] uses the chain-length form

$$
C_k(A)
\le
M_k(A)+\sum_{s=0}^{k-1}(L_s-1).
$$

In the range considered in the main text, every chain is nonempty, and [sum_actual_chain_lengths][lean-comparison] gives $\sum_sL_s=n$. Hence

$$
\sum_{s=0}^{k-1}(L_s-1)=n-k.
$$

Combining this with $M_k=I_k$ and [gapComparisonCost_lower][lean-comparison] gives the two-sided comparison bound in the main text. These are two expressions of the same sharp bound. The repository also contains a coarser upper bound with an additive $n$, for use over a more general range of positive gaps.

## A.4 The Displacement–Cost Inequality as a Special Case of a General Theorem

Equation (1.8) in the main text states the one-pass relation

$$
F(A)\le2kI_k(A)+F(S_kA),
$$

and applies it to the remaining two passes to obtain equation (1.10):

$$
F(S_hA)\le2gM_2+2M_3.
$$

The Lean declaration [footrule_le_wordShiftDistance][lean-weighted] proves a weighted displacement–cost inequality for an arbitrary sequence of positive gaps: the initial displacement is at most the final displacement plus twice the sum, over all passes, of the gap multiplied by the actual number of successful right shifts. The cost of each pass is evaluated on the actual input state of that pass.

Applying this relation to one pass and substituting $M_k=I_k$ gives equation (1.8). Set $B=S_hA$ and apply the relation to the remaining gap sequence $[g,1]$. Since the final pass fully sorts the array, the final displacement is zero, and hence

$$
F(B)\le2(gM_2+M_3).
$$

Thus equation (1.10) is a direct special case of this general theorem. The proof of [threePass_checkpoint_transport][lean-checkpoint] uses this sharp form and then relaxes it to a bound in terms of the total cost. The main text derives the result by successive applications of the one-pass relation, whereas the Lean formalization gives a unified statement for general gap sequences.

## A.5 Proof Methods and Summation Notation

Lemma 1.1 in the main text proves $I\le F$ by an exchange procedure that places keys in their correct positions in increasing order of rank, computing the decreases in inversion count and displacement at each step. The Lean declaration [ordinaryInversions_le_footrule][lean-inversion] uses a counting and charging proof. The two approaches prove the same inequality by different methods.

Equation (3.3) in the main text and [two_mul_lastCost_eq_sum_taggedArc][lean-arc] both sum over indices that include arcs of zero length; the terms of zero length contribute zero.

[repo]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/tree/d2e146f81dc50e87b062088ebf3d514c4ece7040
[lean-main]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/ThreePassOptimalMean.lean
[lean-two]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/TaggedUpper.lean
[lean-first]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/FirstPassUpper.lean
[lean-chain]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/ChainTransport.lean
[lean-invchain]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/ChainInversionBound.lean
[lean-weighted]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/WordShiftDistance.lean
[lean-cost]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/GapInsertionBridge.lean
[lean-comparison]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/GapComparisonBridge.lean
[lean-checkpoint]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/AllGapThreePassLower.lean
[lean-inversion]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/InversionFootrule.lean
[lean-arc]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/PivotArcCostBridge.lean
