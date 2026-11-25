import Shellsort.F09SharpConsequences
import Shellsort.F09CertificateKnots

/-! The sharp leading term and its minimizing families for ordinary three-pass
Shellsort on the uniform permutation, with both counters optimized separately. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology Set

/-- The two optimized means have the same sharp leading coefficient. -/
theorem verified_three_pass_optimum (N : ℕ → ℕ) (lo : ∀ i, 16 ≤ N i)
    (grow : Tendsto N atTop atTop) :
    Tendsto (fun i => optimalThreePassMeanShifts (N i) (lo i) / (N i * Real.sqrt (N i))) atTop (𝓝 kappa) ∧
    Tendsto (fun i => optimalThreePassMeanComparisons (N i) (lo i) / (N i * Real.sqrt (N i))) atTop (𝓝 kappa) ∧
    (6082 : ℝ) / 10000 < kappa ∧ kappa < (608275 : ℝ) / 1000000 :=
  actual_sharp_limits_of_quadrature verifiedQuadratureBounds N lo grow

/-- Eventual coprimality and approach to the full minimizing set characterize
asymptotic optimality for either actual counter, including oscillating families. -/
theorem verified_optimal_gap_families {N : ℕ → ℕ} (w : ∀ i, LegalThreePassPair (N i))
    (grow : Tendsto N atTop atTop) :
    (Tendsto (fun i => normCost (w i)) atTop (𝓝 kappa) ↔
      (∀ᶠ i in atTop, divisor (w i) = 1) ∧
        Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0)) ∧
    (Tendsto (fun i => normComparisons (w i)) atTop (𝓝 kappa) ↔
      (∀ᶠ i in atTop, divisor (w i) = 1) ∧
        Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0)) :=
  optimal_family_for_both_costs verifiedQuadratureBounds w grow

/-- The same criterion applies to the excess over the actual optimum at each size. -/
theorem verified_optimal_regret {N : ℕ → ℕ} (lo : ∀ i, 16 ≤ N i)
    (grow : Tendsto N atTop atTop) (w : ∀ i, LegalThreePassPair (N i)) :
    (Tendsto (fun i => (threePassPairMeanShifts (w i) - optimalThreePassMeanShifts _ (lo i)) /
        ((N i : ℝ) * Real.sqrt (N i))) atTop (𝓝 0) ↔
      (∀ᶠ i in atTop, divisor (w i) = 1) ∧
        Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0)) ∧
    (Tendsto (fun i => (threePassPairMeanComparisons (w i) - optimalThreePassMeanComparisons _ (lo i)) /
        ((N i : ℝ) * Real.sqrt (N i))) atTop (𝓝 0) ↔
      (∀ᶠ i in atTop, divisor (w i) = 1) ∧
        Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0)) :=
  optimal_regret_of_quadrature verifiedQuadratureBounds lo grow w

/-- Every minimizing pair is parametrized by a global one-dimensional
minimizer, and the set of these parameters is nonempty and compact. -/
theorem verified_variational_shapes :
    optimalParameters.Nonempty ∧ IsCompact optimalParameters ∧
      ∀ a b : ℝ, (a, b) ∈ optimalShapes ↔
        ∃ z ∈ optimalParameters, a = scaleAt z ∧ b = z / Real.sqrt a :=
  ⟨optimal_parameters_nonempty verifiedQuadratureBounds, compact_optimal_parameters,
    fun _ _ => optimal_shape_formula⟩

end Shellsort.F09
end
