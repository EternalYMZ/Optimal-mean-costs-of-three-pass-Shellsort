import Shellsort.F09Verified

/-! The cost of restricting the first two gaps to have a common factor.
Both statements are uniform over the original, finite sets of legal tables. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology

private theorem normCost_le_comparisons {n : ℕ} (w : LegalThreePassPair n) :
    normCost w ≤ normComparisons w := by
  have legal := w.property
  have h := uniform_threePassComparisonCost_bounds n w.val.1.val w.val.2.val
    (by omega) (by omega)
  exact div_le_div_of_nonneg_right h.1 (by positivity)

/-- Uniform form of the lower limit 0.61546 for the best noncoprime table.
The threshold may depend on the requested lower bound. -/
theorem verified_noncoprime_cost_floor (t : ℝ) (ht : t < 61546 / 100000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ w : LegalThreePassPair n, 2 ≤ divisor w →
      t ≤ normCost w ∧ t ≤ normComparisons w := by
  suffices floor : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ w : LegalThreePassPair n,
      2 ≤ divisor w → t ≤ normCost w by
    obtain ⟨n₀, lower⟩ := floor
    exact ⟨n₀, fun n hn w hd => ⟨lower n hn w hd, (lower n hn w hd).trans (normCost_le_comparisons w)⟩⟩
  by_contra! bad
  choose N ge w noncoprime cheap using bad
  obtain ⟨d,a,b,φ,hd,ha,hb,inc,gd,al,bl⟩ :=
    budget_convergent_subsequence N w 1 zero_lt_one
      (fun i => by linarith [cheap i])
  have grow : Tendsto N atTop atTop := tendsto_atTop_mono ge tendsto_id
  have limit := actual_threePass_critical_law (N ∘ φ) (fun i => w (φ i)) d a b
    (grow.comp inc.tendsto_atTop) hd ha hb gd al bl
  have two : 2 ≤ d := by
    obtain ⟨i, eq⟩ := gd.exists
    exact eq ▸ noncoprime (φ i)
  have small : K d a b ≤ t := le_of_tendsto' limit (fun i => (cheap (φ i)).le)
  linarith [verified_noncoprime_separation two ha hb]

/-- Every noncoprime table pays a fixed excess over each counter's own global
minimum at all sufficiently large sizes. The excess is in units of n sqrt n. -/
theorem verified_noncoprime_cost_penalty :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (hn : 16 ≤ n) (w : LegalThreePassPair n), 2 ≤ divisor w →
      (718514594 : ℝ) / 100000000000 <
        (threePassPairMeanShifts w - optimalThreePassMeanShifts n hn) / (n * Real.sqrt n) ∧
      (718514594 : ℝ) / 100000000000 <
        (threePassPairMeanComparisons w - optimalThreePassMeanComparisons n hn) / (n * Real.sqrt n) := by
  let δ : ℝ := 718514594 / 100000000000
  obtain ⟨t, large, small⟩ := exists_between
    (show kappa + δ < 61546 / 100000 by dsimp [δ]; linarith [verified_kappa_precise.2])
  obtain ⟨n₁, floor⟩ := verified_noncoprime_cost_floor t small
  by_contra! bad
  choose N ge lo w noncoprime fail using bad
  have grow : Tendsto N atTop atTop := tendsto_atTop_mono ge tendsto_id
  obtain ⟨ms,mc,_⟩ := verified_three_pass_optimum N lo grow
  have gap : kappa < t - δ := by linarith
  obtain ⟨i, big, sh, co⟩ := ((grow.eventually_ge_atTop n₁).and
    ((ms.eventually_lt_const gap).and (mc.eventually_lt_const gap))).exists
  obtain ⟨s, c⟩ := floor (N i) big (w i) (noncoprime i)
  dsimp [normCost, normComparisons] at s c
  have hs : δ < (threePassPairMeanShifts (w i) - optimalThreePassMeanShifts _ (lo i)) /
      (N i * Real.sqrt (N i)) := by rw [sub_div]; linarith
  have hc : δ < (threePassPairMeanComparisons (w i) - optimalThreePassMeanComparisons _ (lo i)) /
      (N i * Real.sqrt (N i)) := by rw [sub_div]; linarith
  exact (not_lt_of_ge (fail i hs)) hc

/-- Every exact minimizer is coprime for all sufficiently large sizes,
including ties and minima taken separately for the two counters. -/
theorem verified_exact_minimizers_coprime :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (hn : 16 ≤ n) (w : LegalThreePassPair n),
      threePassPairMeanShifts w = optimalThreePassMeanShifts n hn ∨
        threePassPairMeanComparisons w = optimalThreePassMeanComparisons n hn →
      divisor w = 1 := by
  obtain ⟨n₀, penalty⟩ := verified_noncoprime_cost_penalty
  refine ⟨n₀, fun n large hn w optimal => ?_⟩
  by_contra bad
  have legal := w.property
  have pos : 0 < divisor w := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨sh, co⟩ := penalty n large hn w (by omega)
  rcases optimal with eq | eq
  · rw [eq, sub_self, zero_div] at sh
    norm_num at sh
  · rw [eq, sub_self, zero_div] at co
    norm_num at co

end Shellsort.F09
end
