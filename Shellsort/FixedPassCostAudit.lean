import Shellsort.PredeterminedOptimum

/-! Transport a fixed-pass shift bound to ordinary key comparisons, even if
    minimizing the two costs selects different gap words. -/
noncomputable section
namespace Shellsort.PredeterminedOptimum
open HarvestBlockIteration

def meanShifts (n : ℕ) (w : PositiveWord) : ℝ :=
  uniformAverage fun p : RankPlacement n => (ordinaryWordShifts p w : ℝ)

private theorem word_scan_le_length (n : ℕ) (w : PositiveWord) :
    (w.map (fun h => n - h.val)).sum ≤ w.length * n := by
  induction w with
  | nil => simp
  | cons h rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem comparison_shift_mean_bounds (n : ℕ) (w : PositiveWord) :
    meanShifts n w ≤ mean n w ∧ mean n w ≤ meanShifts n w + (w.length * n : ℕ) := by
  constructor
  · apply uniformAverage_mono
    intro p
    exact_mod_cast (max_le_iff.mp (ordinaryWord_scan_bounds p w).1).1
  · let g := fun p : RankPlacement n =>
      (ordinaryWordShifts p w : ℝ) + ((w.length*n : ℕ) : ℝ)
    have h : mean n w ≤ uniformAverage g := by
      apply uniformAverage_mono
      intro p
      have hu := (ordinaryWord_scan_bounds p w).2.trans
        (Nat.add_le_add_left (word_scan_le_length n w) _)
      dsimp [g]
      exact_mod_cast hu
    simpa only [g, uniformAverage_add, uniformAverage_const, meanShifts] using h

/-- These hypotheses just say that u and v win the two optimizations. -/
theorem fixed_pass_winners_cost_bounds (n p : ℕ) (u v : PositiveWord)
    (hu : Legal n u) (hup : u.length = p) (hv : Legal n v) (hvp : v.length = p)
    (huBest : ∀ z, Legal n z → z.length = p → meanShifts n u ≤ meanShifts n z)
    (hvBest : ∀ z, Legal n z → z.length = p → mean n v ≤ mean n z) :
    meanShifts n u ≤ mean n v ∧ mean n v ≤ meanShifts n u + (p * n : ℕ) := by
  constructor
  · exact (huBest v hv hvp).trans (comparison_shift_mean_bounds n v).1
  · simpa only [hup] using
      (hvBest u hu hup).trans (comparison_shift_mean_bounds n u).2

#print axioms fixed_pass_winners_cost_bounds
end Shellsort.PredeterminedOptimum
