import Shellsort.PivotChainInversions
import Shellsort.TaggedBernoulli

/-! Exact final-pass cost from original marked positions for all positive
gaps. A physical target in a different greatest-common-divisor class uses
the same observable as a target in the pivot's own class. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Incident inversions after both preliminary passes, read from the marked
positions before either pass and the original position of the pivot. -/
def finalPivotPrefixCost {n : ℕ} (h g r : ℕ) (i : Fin n) (B : TaggedSubset i) : ℝ :=
  let b := chainLowerCount B.val h
  let owner := i.val % h
  let j := (owner + h * b owner) % g
  let N := fun a => ∑ s ∈ Finset.range h, sourcePrefixCount h g a s (b s)
  |((N j + if r < j then 1 else 0 : ℕ) : ℝ) - (N r : ℝ)|

/-- The selected target includes the true smaller-key count of the owner. -/
theorem finalPivotPrefixCost_eq_actual {n : ℕ} (p : RankPlacement n) (h g r : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hr : r < g) (i : Fin n) :
    (pivotChainInversions (gapSort (gapSort p h) g) g r (p.symm i) : ℝ) =
      finalPivotPrefixCost h g r i (tagLowerState p i) := by
  have H := twoPass_pivotChainInversions p h g r hh hg hr (p.symm i)
  dsimp only at H
  simp only [Equiv.apply_symm_apply] at H
  unfold finalPivotPrefixCost
  dsimp only [tagLowerState]
  exact_mod_cast H

/-- Every inversion is counted at both endpoints, including inversions
between two different classes modulo the common divisor. -/
theorem two_mul_lastCost_eq_original_prefixes {n : ℕ} (p : RankPlacement n)
    (h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    2 * (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ) =
      ∑ i : Fin n, ∑ r ∈ Finset.range g, finalPivotPrefixCost h g r i (tagLowerState p i) := by
  let q := gapSort (gapSort p h) g
  have count := sum_pivotChainInversions_eq_twice_shifts q g hg
  have realCount : 2 * (gapInsertionCost q 1 (by decide) : ℝ) =
      ∑ x : Fin n, ∑ r ∈ Finset.range g, (pivotChainInversions q g r x : ℝ) := by
    exact_mod_cast count.symm
  rw [realCount, ← Equiv.sum_comp p.symm (fun x =>
    ∑ r ∈ Finset.range g, (pivotChainInversions q g r x : ℝ))]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r hr =>
    finalPivotPrefixCost_eq_actual p h g r hh hg (Finset.mem_range.mp hr) i

/-- The mean for the *executed* final pass on uniform rank permutations is
the integral of independent original smaller-key bits, omitting the pivot.
There is no coprimality assumption and the selected target remains random. -/
theorem uniform_lastCost_original_prefix_mixture (n h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    2 * uniformAverage (fun p : RankPlacement n =>
      (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ)) =
      ∑ i : Fin n, ∫ t : ℝ in 0..1,
        mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
          (fun x => ∑ r ∈ Finset.range g,
            finalPivotPrefixCost h g r i ((omittedBitsSubsetEquiv i) x)) := by
  let F := fun (i : Fin n) (B : TaggedSubset i) =>
    ∑ r ∈ Finset.range g, finalPivotPrefixCost h g r i B
  have path := fun p : RankPlacement n => two_mul_lastCost_eq_original_prefixes p h g hh hg
  calc
    _ = uniformAverage (fun p : RankPlacement n =>
          2 * (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ)) := by
            unfold uniformAverage
            rw [← Finset.mul_sum]
            ring
    _ = uniformAverage (fun p : RankPlacement n => ∑ i : Fin n, F i (tagLowerState p i)) := by
          simp_rw [path]; rfl
    _ = ∑ i : Fin n, uniformAverage (fun p : RankPlacement n => F i (tagLowerState p i)) := by
          unfold uniformAverage
          rw [Finset.sum_comm, Finset.sum_div]
    _ = _ := Finset.sum_congr rfl fun i _ => uniform_tagged_bernoulli_mixture i (F i)

end Shellsort
end
