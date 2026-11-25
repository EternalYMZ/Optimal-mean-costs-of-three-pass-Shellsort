import Shellsort.F09PhaseIntegrationSameLimit
import Shellsort.F09PhasePhysicalCross

noncomputable section
namespace Shellsort.F09
open Filter
open scoped Topology

/-- The original uniform-permutation law of all target phases, arbitrary
fixed positive gcd, both true chain lengths, and all limiting endpoints. -/
theorem actual_moving_phase_rows : MovingPhysicalPhaseRows := by
  intro N H G d lam dp lp np hp gp cop Gn Hn GH heat t ell T X ht hel tl width
  apply phase_row_limit_of_tagged_classes d dp np t lam T X
  intro i c
  by_cases zero : c.val=0
  · simpa only [zero] using actual_tag_same_class_limit d dp hp gp cop Gn Hn GH heat t ht tl hel width i
  · apply actual_tag_cross_class_limit <;> assumption

/-- The complete mathematical critical law from executed insertion costs on
uniform permutations, without a probabilistic, quadrature or cost-law premise. -/
theorem actual_threePass_critical_law : CriticalCostLaw :=
  criticalCostLaw_of_physicalPhaseRows (physicalPhaseRows_of_moving actual_moving_phase_rows)

/-- The separately optimized, actual three-pass shifts and comparisons
converge to the attained variational minimum over all fixed positive divisors
and real critical coordinates. -/
theorem actual_optimal_threePass_limits (N : ℕ → ℕ) (lo : ∀ i, 16≤N i) (grow : Tendsto N atTop atTop) :
    Tendsto (fun i => optimalThreePassMeanShifts (N i) (lo i) / (N i * Real.sqrt (N i)))
      atTop (𝓝 (sInf criticalValues)) ∧
    Tendsto (fun i => optimalThreePassMeanComparisons (N i) (lo i) / (N i * Real.sqrt (N i)))
      atTop (𝓝 (sInf criticalValues)) ∧ sInf criticalValues ∈ criticalValues :=
  optimal_cost_limits_of_critical_law actual_threePass_critical_law N lo grow

end Shellsort.F09
