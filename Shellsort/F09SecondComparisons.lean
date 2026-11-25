import Shellsort.F09SecondCritical
import Shellsort.NaturalComparisonBounds

noncomputable section
namespace Shellsort.F09Second
open Filter
open scoped Topology

/-- For ordinary linear insertion, at most one terminating comparison per
slot separates the actual second-pass comparison count from its right shifts. -/
theorem critical_secondPass_comparison_limit (N h g : ℕ → ℕ) (grow : Tendsto N atTop atTop)
    (hh : ∀ i, 0<h i) (hg : ∀ i, 0<g i) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (first : Tendsto (fun i => (h i:ℝ)/Real.sqrt (N i)) atTop (𝓝 a))
    (second : Tendsto (fun i => (g i:ℝ)/Real.sqrt (Real.sqrt (N i))) atTop (𝓝 b)) :
    Tendsto (fun i => uniformAverage (fun p : RankPlacement (N i) =>
      (gapComparisonCost (gapSort p (h i)) (g i) (hg i) : ℝ)) / ((N i:ℝ)*Real.sqrt (N i)))
      atTop (𝓝 (Real.sqrt Real.pi * Real.sqrt a / (8*b))) := by
  have lim := critical_secondPass_limit N h g grow hh hg a b ha hb first second
  have error : Tendsto (fun i => 1/Real.sqrt (N i:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp grow))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lim (by simpa only [add_zero] using lim.add error)
  · apply Eventually.of_forall; intro i
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply uniformAverage_mono; intro p
    exact_mod_cast gapComparisonCost_lower (gapSort p (h i)) (g i) (hg i)
  · filter_upwards [grow.eventually_ge_atTop 1] with i hi
    have np : (0:ℝ)<N i := by exact_mod_cast hi
    have sp := Real.sqrt_pos.2 np
    have up := uniformAverage_mono
      (fun p : RankPlacement (N i) => (gapComparisonCost (gapSort p (h i)) (g i) (hg i):ℝ))
      (fun p => (gapInsertionCost (gapSort p (h i)) (g i) (hg i):ℝ)+N i)
      (fun p => by exact_mod_cast gapComparisonCost_upper (gapSort p (h i)) (g i) (hg i))
    rw [uniformAverage_add,uniformAverage_const] at up
    change _ / ((N i:ℝ)*Real.sqrt (N i)) ≤ _ / ((N i:ℝ)*Real.sqrt (N i))+1/Real.sqrt (N i)
    rw [show 1/Real.sqrt (N i:ℝ) = (N i:ℝ)/((N i:ℝ)*Real.sqrt (N i)) by field_simp,← add_div]
    exact div_le_div_of_nonneg_right up (by positivity)

end Shellsort.F09Second
