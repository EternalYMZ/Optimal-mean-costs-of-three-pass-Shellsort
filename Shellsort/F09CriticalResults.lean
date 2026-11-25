import Shellsort.F09PhaseIntegrationFinal
import Shellsort.F09FixedDivisorUniform
import Shellsort.F09OrderFinite
import Shellsort.F09SecondComparisons

/-! Uniform permutation input, deterministic three-pass tables and actual linear
insertion counters. These results are independent of the numerical quadrature. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology Set

/-- Uniform fixed-divisor critical law for both executed counters on every
compact positive window. No probabilistic or analytic assumptions on the costs. -/
theorem actual_critical_uniform (d : ℕ) (hd : 0<d)
    (D : Set (ℝ × ℝ)) (compact : IsCompact D) (positive : ∀ p ∈ D, 0<p.1 ∧ 0<p.2)
    (ε : ℝ) (he : 0<ε) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ w : LegalThreePassPair n,
      divisor w=d → (scaleA w,scaleB w) ∈ D →
      |normCost w - K d (scaleA w) (scaleB w)| < ε ∧
      |normComparisons w - K d (scaleA w) (scaleB w)| < ε :=
  critical_compact_uniform actual_threePass_critical_law d hd D compact positive ε he

end Shellsort.F09
end
