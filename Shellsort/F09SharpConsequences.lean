import Shellsort.F09CriticalResults
import Shellsort.F09OptimalFamilies

/-! Final transfer from certified inequalities for the actual integrals to
the two separately optimized counters and all asymptotically optimal families. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology Set

def optimalParameters : Set ℝ := {z | 0<z ∧ H z=kappa}
def scaleAt (z : ℝ) := Real.sqrt (z/c)/2

theorem optimal_shape_formula {a b : ℝ} : (a,b) ∈ optimalShapes ↔
    ∃ z ∈ optimalParameters, a=scaleAt z ∧ b=z/Real.sqrt a := by
  constructor
  · rintro ⟨ha,hb,v⟩
    let z := shape 1 a b
    have zp : 0<z := shape_pos (by decide) ha hb
    obtain ⟨minimum,balance⟩ := (coprime_minimizer_iff ha hb).1 v
    have sa := Real.sqrt_pos.mpr ha
    have beq : b=4*a*(c*Real.sqrt a) := by
      field_simp at balance
      linarith only [balance]
    have zval : z=4*c*a^2 := by
      dsimp [z,shape]; rw [beq]; push_cast
      nlinarith [show 4*a*(c*Real.sqrt a)*Real.sqrt a = 4*c*a*(Real.sqrt a)^2 by ring,
        show 4*c*a*(Real.sqrt a)^2=4*c*a*a by rw [Real.sq_sqrt ha.le]]
    refine ⟨z,⟨zp,minimum⟩,?_,?_⟩
    · unfold scaleAt
      have p : z/c = (2*a)^2 := by rw [zval]; field_simp [c_pos.ne']; ring
      rw [p,Real.sqrt_sq (by positivity)]; ring
    · apply (eq_div_iff sa.ne').2
      simp [z,shape]
  · rintro ⟨z,⟨zp,he⟩,ha',hb'⟩
    have ap : 0<a := ha' ▸ div_pos (Real.sqrt_pos.2 (div_pos zp c_pos)) (by norm_num)
    have sap := Real.sqrt_pos.mpr ap
    have bp : 0<b := hb' ▸ div_pos zp sap
    have shapeEq : shape 1 a b = z := by simp [shape,hb',sap.ne']
    have bal : 4*c*a^2=z := by
      rw [ha']; unfold scaleAt
      have eq := Real.sq_sqrt (div_nonneg zp.le c_pos.le)
      field_simp [c_pos.ne'] at eq ⊢
      linarith only [eq]
    refine ⟨ap,bp,(coprime_minimizer_iff ap bp).2 ⟨shapeEq ▸ he,?_⟩⟩
    rw [hb']
    field_simp [sap.ne',ap.ne',zp.ne']
    nlinarith [show c*Real.sqrt a*Real.sqrt a = c*a by rw [mul_assoc,← sq,Real.sq_sqrt ap.le],
      show c*Real.sqrt a*Real.sqrt a*a = c*a*a by rw [mul_assoc c,← sq,Real.sq_sqrt ap.le]]

theorem optimalParameters_eq_image :
    optimalParameters = (fun p : ℝ × ℝ => shape 1 p.1 p.2) '' optimalShapes := by
  ext z
  constructor
  · intro hz
    let a := scaleAt z
    have ap : 0<a := div_pos (Real.sqrt_pos.mpr (div_pos hz.1 c_pos)) (by norm_num)
    let b := z/Real.sqrt a
    refine ⟨(a,b),optimal_shape_formula.2 ⟨z,hz,rfl,rfl⟩,?_⟩
    simp [shape,b,(Real.sqrt_pos.mpr ap).ne']
  · rintro ⟨⟨a,b⟩,hm,rfl⟩
    exact ⟨shape_pos (by decide) hm.1 hm.2.1,((coprime_minimizer_iff hm.1 hm.2.1).1 hm.2.2).1⟩

theorem compact_optimal_parameters : IsCompact optimalParameters := by
  rw [optimalParameters_eq_image]
  apply (optimalShapes_compact actual_threePass_critical_law).image
  unfold shape
  fun_prop

theorem optimal_parameters_nonempty (q : QuadratureBounds) : optimalParameters.Nonempty := by
  rw [optimalParameters_eq_image]
  exact (optimalShapes_nonempty actual_threePass_critical_law (divisorSeparation_of_quadrature q)).image _

theorem actual_sharp_limits_of_quadrature (q : QuadratureBounds)
    (N : ℕ → ℕ) (lo : ∀ i, 16≤N i) (grow : Tendsto N atTop atTop) :
    Tendsto (fun i => optimalThreePassMeanShifts (N i) (lo i)/(N i*Real.sqrt (N i))) atTop (𝓝 kappa) ∧
    Tendsto (fun i => optimalThreePassMeanComparisons (N i) (lo i)/(N i*Real.sqrt (N i))) atTop (𝓝 kappa) ∧
    (6082:ℝ)/10000 < kappa ∧ kappa < (608275:ℝ)/1000000 := by
  have ⟨sh,co,_⟩ := actual_optimal_threePass_limits N lo grow
  rw [inf_critical_eq_kappa (divisorSeparation_of_quadrature q)] at sh co
  exact ⟨sh,co,by linarith [(kappa_enclosure q).1],(kappa_enclosure q).2⟩

theorem optimal_family_for_both_costs (q : QuadratureBounds) {N : ℕ → ℕ} (w : ∀ i, LegalThreePassPair (N i))
    (grow : Tendsto N atTop atTop) :
    (Tendsto (fun i => normCost (w i)) atTop (𝓝 kappa) ↔
      (∀ᶠ i in atTop, divisor (w i)=1) ∧
        Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0)) ∧
    (Tendsto (fun i => normComparisons (w i)) atTop (𝓝 kappa) ↔
      (∀ᶠ i in atTop, divisor (w i)=1) ∧
        Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0)) := by
  have sh := asymptotically_optimal_iff actual_threePass_critical_law (divisorSeparation_of_quadrature q) N w grow
  refine ⟨sh, Iff.trans ⟨?_,?_⟩ sh⟩
  · intro c
    simpa only [sub_zero,sub_sub_cancel] using c.sub (comparisons_minus_shifts w grow)
  · intro s
    simpa only [zero_add,sub_add_cancel] using (comparisons_minus_shifts w grow).add s

/-- Vanishing normalized excess over the actual finite minimum characterizes
the same gap families, even if the optimal finite gaps change with size. -/
theorem optimal_regret_of_quadrature (q : QuadratureBounds) {N : ℕ → ℕ}
    (lo : ∀ i, 16 ≤ N i) (grow : Tendsto N atTop atTop) (w : ∀ i, LegalThreePassPair (N i)) :
    (Tendsto (fun i => (threePassPairMeanShifts (w i) - optimalThreePassMeanShifts _ (lo i)) /
        ((N i : ℝ) * Real.sqrt (N i))) atTop (𝓝 0) ↔
      (∀ᶠ i in atTop, divisor (w i) = 1) ∧
        Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0)) ∧
    (Tendsto (fun i => (threePassPairMeanComparisons (w i) - optimalThreePassMeanComparisons _ (lo i)) /
        ((N i : ℝ) * Real.sqrt (N i))) atTop (𝓝 0) ↔
      (∀ᶠ i in atTop, divisor (w i) = 1) ∧
        Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0)) := by
  have opt := (actual_sharp_limits_of_quadrature q N lo grow).1
  have shifts := (optimal_family_for_both_costs q w grow).1
  have diff :
      Tendsto (fun i => (threePassPairMeanShifts (w i) - optimalThreePassMeanShifts _ (lo i)) /
        ((N i : ℝ) * Real.sqrt (N i))) atTop (𝓝 0) ↔
      Tendsto (fun i => normCost (w i)) atTop (𝓝 kappa) := by
    constructor
    · intro lim
      simpa only [sub_div, sub_add_cancel, zero_add, normCost] using lim.add opt
    · intro lim
      simpa only [sub_div, sub_self, normCost] using lim.sub opt
  exact ⟨diff.trans shifts, (threePass_nearOptimal_cost_iff N lo grow w).trans (diff.trans shifts)⟩

end Shellsort.F09
end
