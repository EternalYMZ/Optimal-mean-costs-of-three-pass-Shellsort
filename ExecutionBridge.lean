import Shellsort.OrdinaryWordComparisons
import Shellsort.ThreePassOptimalMean

/-! Independent consumer of the two cost interfaces, on every physical input. -/
namespace Shellsort.FixedPassRecheck

theorem same_comparisons {n : ℕ} (p : RankPlacement n)
    (h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    ordinaryWordComparisons p [⟨h, hh⟩, ⟨g, hg⟩, ⟨1, by decide⟩] =
      threePassComparisonCost p h g hh hg := by
  simp [ordinaryWordComparisons, threePassComparisonCost, Nat.add_assoc]

theorem same_shifts {n : ℕ} (p : RankPlacement n)
    (h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    ordinaryWordShifts p [⟨h, hh⟩, ⟨g, hg⟩, ⟨1, by decide⟩] =
      threePassInsertionCost p h g hh hg := by
  simp [ordinaryWordShifts, threePassInsertionCost, Nat.add_assoc]

#print axioms same_comparisons
#print axioms same_shifts
#print axioms uniform_naturalThreePassInsertionCost_bounds
#print axioms uniform_naturalThreePassComparisonCost_bounds
#print axioms uniform_naturalThreePassComparisonCost_scaled
#print axioms uniform_threePass_cost_lower
#print axioms optimal_threePass_mean_bounds

end Shellsort.FixedPassRecheck
