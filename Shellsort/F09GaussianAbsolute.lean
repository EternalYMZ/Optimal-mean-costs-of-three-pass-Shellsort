import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Absolute first moments from triangular-array weak limits, also when the
limit variance is zero. Bounds are in terms of second moments alone. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology MeasureTheory ProbabilityTheory Set Real
open scoped BoundedContinuousFunction NNReal

private def clip (R : ℝ) (pos : 0 < R) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ℝ => min |x| R)
    (by fun_prop) R (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) pos.le)]
      exact min_le_right ..)

private theorem tail_bound (μ : ProbabilityMeasure ℝ) (R : ℝ) (pos : 0 < R)
    (absInt : Integrable (fun x : ℝ => |x|) (μ : Measure ℝ))
    (sqInt : Integrable (fun x : ℝ => x^2) (μ : Measure ℝ)) :
    |(∫ x, |x| ∂(μ : Measure ℝ)) - ∫ x, clip R pos x ∂(μ : Measure ℝ)| ≤
      (∫ x : ℝ, x^2 ∂(μ : Measure ℝ))/R := by
  have clipInt := (clip R pos).integrable (μ := (μ : Measure ℝ))
  have order := integral_mono clipInt absInt (fun x => min_le_left |x| R)
  rw [abs_of_nonneg (sub_nonneg.mpr order), ← integral_sub absInt clipInt, ← integral_div]
  apply integral_mono (absInt.sub clipInt) (sqInt.div_const _)
  intro x
  change |x| - min |x| R ≤ x^2/R
  apply (le_div_iff₀ pos).2
  rcases le_total |x| R with lo | hi
  · rw [min_eq_left lo]; nlinarith [sq_nonneg x]
  · rw [min_eq_right hi]
    nlinarith only [sq_abs x, sq_nonneg R, mul_le_mul_of_nonneg_left hi (abs_nonneg x)]

theorem abs_moment_tendsto_of_charFun
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (weak : ∀ t : ℝ, Tendsto (fun i => charFun (μ i : Measure ℝ) t) atTop
      (𝓝 (charFun (ν : Measure ℝ) t)))
    (absInt : ∀ i, Integrable (fun x : ℝ => |x|) (μ i : Measure ℝ))
    (sqInt : ∀ i, Integrable (fun x : ℝ => x^2) (μ i : Measure ℝ))
    (limitAbs : Integrable (fun x : ℝ => |x|) (ν : Measure ℝ))
    (limitSq : Integrable (fun x : ℝ => x^2) (ν : Measure ℝ))
    (C : ℝ) (bound : ∀ i, (∫ x : ℝ, x^2 ∂(μ i : Measure ℝ)) ≤ C) :
    Tendsto (fun i => ∫ x : ℝ, |x| ∂(μ i : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, |x| ∂(ν : Measure ℝ))) := by
  have weak' : Tendsto μ atTop (𝓝 ν) := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr weak
  rw [Metric.tendsto_nhds]
  intro ε ep
  let S := max C (∫ x : ℝ, x^2 ∂(ν : Measure ℝ))
  have s0 : 0 ≤ S := (integral_nonneg (fun x : ℝ => sq_nonneg x)).trans (le_max_right ..)
  let R := (4*S+1)/ε
  have rp : 0 < R := div_pos (by linarith) ep
  have frac : S/R < ε/4 := by
    apply (div_lt_iff₀ rp).2
    dsimp [R]; field_simp; linarith
  have lim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp weak' (clip R rp)
  filter_upwards [Metric.tendsto_nhds.mp lim (ε/2) (by linarith)] with i close
  have ta := (tail_bound (μ i) R rp (absInt i) (sqInt i)).trans_lt
    ((div_le_div_of_nonneg_right ((bound i).trans (le_max_left ..)) rp.le).trans_lt frac)
  have tb := (tail_bound ν R rp limitAbs limitSq).trans_lt
    ((div_le_div_of_nonneg_right (le_max_right ..) rp.le).trans_lt frac)
  rw [Real.dist_eq] at close ⊢
  have tri := abs_sub_le (∫ x : ℝ, |x| ∂(μ i : Measure ℝ))
    (∫ x : ℝ, clip R rp x ∂(μ i : Measure ℝ)) (∫ x : ℝ, |x| ∂(ν : Measure ℝ))
  have last := abs_sub_le (∫ x : ℝ, clip R rp x ∂(μ i : Measure ℝ))
    (∫ x : ℝ, clip R rp x ∂(ν : Measure ℝ)) (∫ x : ℝ, |x| ∂(ν : Measure ℝ))
  rw [abs_sub_comm (∫ x : ℝ, clip R rp x ∂(ν : Measure ℝ))] at last
  linarith

/-- The absolute moment of a centered Gaussian includes its degenerate limit. -/
theorem integral_abs_gaussian (s : ℝ≥0) :
    ∫ x : ℝ, |x| ∂gaussianReal 0 s = Real.sqrt (2/Real.pi)*Real.sqrt s := by
  by_cases zero : s = 0
  · simp [zero]
  have sp : 0 < (s:ℝ) := by exact_mod_cast (pos_iff_ne_zero.2 zero)
  let b : ℝ := (2*(s:ℝ))⁻¹
  have bp : 0 < b := by dsimp [b]; positivity
  have I := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (by norm_num) (by norm_num) bp
  norm_num [Real.Gamma_one] at I
  rw [integral_gaussianReal_eq_integral_smul zero]
  calc (∫ x : ℝ, gaussianPDFReal 0 s x • |x|) =
      (Real.sqrt (2*Real.pi*s))⁻¹ * ∫ x : ℝ, |x| * Real.exp (-b * |x| ^ 2) := by
        rw [← integral_const_mul]; apply integral_congr_ae
        filter_upwards with x
        simp only [gaussianPDFReal, smul_eq_mul, sub_zero, sq_abs]
        rw [show -(x^2)/(2*(s:ℝ)) = -b*x^2 by dsimp [b]; ring]; ring
       _ = (Real.sqrt (2*Real.pi*s))⁻¹ * (2 * ∫ x in Ioi (0:ℝ), x*Real.exp (-b*x^2)) := by
         rw [integral_comp_abs (f := fun x : ℝ => x*Real.exp (-b*x^2))]
       _ = Real.sqrt (2/Real.pi)*Real.sqrt s := by
         simp only [← neg_mul, Real.rpow_neg_one] at I
         rw [I]
         simp [b, Real.sqrt_mul, Real.sqrt_div, Real.pi_pos.le, sp.le, Real.sq_sqrt,
           Real.sqrt_ne_zero'.mpr sp, Real.sqrt_ne_zero'.mpr Real.pi_pos]
         field_simp
         nlinarith [Real.sq_sqrt sp.le,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

end Shellsort.F09
end
