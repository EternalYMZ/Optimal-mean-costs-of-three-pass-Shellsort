import Shellsort.UniformThreePassLower
import Shellsort.NaturalComparisonBounds

/-! The gap pair is selected before the uniform permutation is sampled.
Both optima are minima over exactly the strictly decreasing three-pass words. -/
noncomputable section
namespace Shellsort

abbrev LegalThreePassPair (n : ℕ) :=
  {w : Fin n × Fin n // 2 ≤ w.2.val ∧ w.2.val < w.1.val}

private def naturalGapPair (n : ℕ) (hn : 16 ≤ n) : LegalThreePassPair n :=
  let ok := natural_gap_legal n hn
  ⟨(⟨fourthRoot n ^ 2 + 1, ok.2.2⟩, ⟨fourthRoot n, ok.2.1.trans ok.2.2⟩), ok.1, ok.2.1⟩

private theorem pair_pos {n : ℕ} (w : LegalThreePassPair n) :
    0 < w.val.1.val ∧ 0 < w.val.2.val := by
  have := w.property
  omega

def threePassPairMeanShifts {n : ℕ} (w : LegalThreePassPair n) : ℝ :=
  uniformAverage fun p : RankPlacement n =>
    (threePassInsertionCost p w.val.1.val w.val.2.val (pair_pos w).1 (pair_pos w).2 : ℝ)

def threePassPairMeanComparisons {n : ℕ} (w : LegalThreePassPair n) : ℝ :=
  uniformAverage fun p : RankPlacement n =>
    (threePassComparisonCost p w.val.1.val w.val.2.val (pair_pos w).1 (pair_pos w).2 : ℝ)

def optimalThreePassMeanShifts (n : ℕ) (hn : 16 ≤ n) : ℝ :=
  Finset.univ.inf' ⟨naturalGapPair n hn, Finset.mem_univ _⟩ threePassPairMeanShifts

def optimalThreePassMeanComparisons (n : ℕ) (hn : 16 ≤ n) : ℝ :=
  Finset.univ.inf' ⟨naturalGapPair n hn, Finset.mem_univ _⟩ threePassPairMeanComparisons

/-- Uniform absolute constants for both finite minima, with no source-law hypotheses. -/
theorem optimal_threePass_mean_bounds (n : ℕ) (hn : 16 ≤ n) :
    ((n : ℝ) * Real.sqrt n / 65536 ≤ optimalThreePassMeanShifts n hn ∧
      optimalThreePassMeanShifts n hn ≤ 4 * (n : ℝ) * Real.sqrt n) ∧
    ((n : ℝ) * Real.sqrt n / 65536 ≤ optimalThreePassMeanComparisons n hn ∧
      optimalThreePassMeanComparisons n hn ≤ 5 * (n : ℝ) * Real.sqrt n) := by
  have every (w : LegalThreePassPair n) := uniform_threePass_cost_lower
    n w.val.1.val w.val.2.val w.val.1.isLt w.property.2 w.property.1
  constructor
  · constructor
    · exact Finset.le_inf' _ _ (fun w _ => (every w).1)
    · exact (Finset.inf'_le threePassPairMeanShifts (Finset.mem_univ (naturalGapPair n hn))).trans
        (uniform_naturalThreePassInsertionCost_bounds n hn).2
  · constructor
    · exact Finset.le_inf' _ _ (fun w _ => (every w).2)
    · exact (Finset.inf'_le threePassPairMeanComparisons (Finset.mem_univ (naturalGapPair n hn))).trans
        (uniform_naturalThreePassComparisonCost_scaled n hn).2

end Shellsort
end
