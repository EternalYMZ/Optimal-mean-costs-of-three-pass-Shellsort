import Shellsort.F09SecondCost

noncomputable section
open Filter Finset
open scoped Topology
namespace Shellsort.F09Second

/-- Finite, gcd-free enclosure of the true, uniform second insertion-pass mean. -/
theorem uniform_second_bounds (n h g : ℕ) (hh : 0<h) (hg : 0<g) (gh : g≤h) :
    let H := (h:ℝ)/g
    let P := integratedDifference (n/h)/2
    let C := uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort p h) g hg : ℝ))
    n*((H-1)*P-2*H) ≤ C ∧ C ≤ n*(H*P+2*H) := by
  dsimp only
  let H := (h:ℝ)/g
  let D := countDifference (n/h) (n/h)
  have Dcont : Continuous D := by
    change Continuous (countDifference (n/h) (n/h))
    unfold countDifference
    simp_rw [countAverage_eq_sum]
    unfold countMass
    fun_prop
  have A (a b : ℝ) :
      (∫ t : ℝ in 0..1, a*(D t/2)+b) = a*(integratedDifference (n/h)/2)+b := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div, intervalIntegral.integral_const]
    · simp [D,integratedDifference]
    · exact (continuous_const.mul (Dcont.div_const _)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  rw [uniform_second_source_integral n h g hh hg]
  have tag (i : Fin n) := tagSourceMean_bounds n h g hh hg gh i
  have cont (i : Fin n) : Continuous (tagSourceMean n h g hh i) := by
    simp_rw [show tagSourceMean n h g hh i = fun t =>
      mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
        (fun z => (predecessorReward h g i ((omittedBitsSubsetEquiv i) z).val : ℝ)) from
          funext fun t => (tagIntegral_source_mean n h g hh i t).symm]
    exact bernoulli_product_mean_continuous _
  have each (i : Fin n) :
      (H-1)*(integratedDifference (n/h)/2)-2*H ≤ (∫ t : ℝ in 0..1, tagSourceMean n h g hh i t) ∧
      (∫ t : ℝ in 0..1, tagSourceMean n h g hh i t) ≤ H*(integratedDifference (n/h)/2)+2*H := by
    rw [sub_eq_add_neg ((H-1)*_)]
    rw [← A, ← A]
    constructor
    · apply intervalIntegral.integral_mono_on zero_le_one
        (((continuous_const.mul (Dcont.div_const _)).add continuous_const).intervalIntegrable _ _)
        ((cont i).intervalIntegrable _ _)
      intro t ht
      change (H-1)*(D t/2)+-(2*H) ≤ _
      rw [← sub_eq_add_neg]
      exact (tag i t ht).1
    · apply intervalIntegral.integral_mono_on zero_le_one ((cont i).intervalIntegrable _ _)
        (((continuous_const.mul (Dcont.div_const _)).add continuous_const).intervalIntegrable _ _)
      intro t ht; exact (tag i t ht).2
  have l := sum_le_sum (s:=univ) (fun i _ => (each i).1)
  have u := sum_le_sum (s:=univ) (fun i _ => (each i).2)
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,H] using And.intro l u

/-- Whenever both the short first-chain length and the gap ratio diverge, the
true second-pass shifts have coefficient sqrt(pi)/8 in their intrinsic scale. -/
theorem uniform_second_limit (N h g : ℕ → ℕ) (hh : ∀ i, 0<h i) (hg : ∀ i, 0<g i)
    (chains : Tendsto (fun i => N i / h i) atTop atTop)
    (ratio : Tendsto (fun i => (h i:ℝ) / g i) atTop atTop) :
    Tendsto (fun i => uniformAverage (fun p : RankPlacement (N i) =>
      (gapInsertionCost (gapSort p (h i)) (g i) (hg i) : ℝ)) /
      ((N i:ℝ)*((h i:ℝ)/g i)*Real.sqrt (N i / h i : ℕ))) atTop (𝓝 (Real.sqrt Real.pi/8)) := by
  let H i := (h i:ℝ)/g i
  let m i := N i/h i
  let S i := Real.sqrt (m i)
  let D i := integratedDifference (m i)
  have main : Tendsto (fun i => D i/S i/2) atTop (𝓝 (Real.sqrt Real.pi/8)) := by
    rw [show Real.sqrt Real.pi/8 = (Real.sqrt Real.pi/4)/2 by ring]
    exact (integratedDifference_limit.comp chains).div_const 2
  have vanish : Tendsto (fun i => 2/S i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp chains))
  have lost : Tendsto (fun i => D i/S i/2/H i) atTop (𝓝 0) := main.div_atTop ratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using (main.sub lost).sub vanish)
    (by simpa only [add_zero] using main.add vanish)
  all_goals
    filter_upwards [chains.eventually_ge_atTop 1, ratio.eventually_ge_atTop 1] with i mi hi
    have mi' : 0 < m i := mi
    have np : 0 < (N i:ℝ) := by
      exact_mod_cast (lt_of_lt_of_le mi' (Nat.div_le_self _ _))
    have sp : 0 < S i := Real.sqrt_pos.2 (by exact_mod_cast mi')
    have hp : 0 < H i := lt_of_lt_of_le zero_lt_one hi
    have gp : (0:ℝ) < g i := by exact_mod_cast hg i
    have gh : g i ≤ h i := by exact_mod_cast (one_le_div gp).1 hi
    have b := uniform_second_bounds (N i) (h i) (g i) (hh i) (hg i) gh
    have denom : 0 < (N i:ℝ)*H i*S i := by positivity
  · change D i/S i/2-D i/S i/2/H i-2/S i ≤ _ / ((N i:ℝ)*H i*S i)
    apply (le_div_iff₀ denom).2
    convert b.1 using 1
    change _ = (N i:ℝ)*((H i-1)*(D i/2)-2*H i)
    field_simp
  · change _ / ((N i:ℝ)*H i*S i) ≤ D i/S i/2+2/S i
    apply (div_le_iff₀ denom).2
    convert b.2 using 1
    change _ = (N i:ℝ)*(H i*(D i/2)+2*H i)
    field_simp

end Shellsort.F09Second
