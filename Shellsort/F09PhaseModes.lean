import Shellsort.BernoulliCounts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact characteristic modes of two independent source prefixes and their
critical-scale limits, allowing the thresholds themselves to converge. -/
noncomputable section
namespace Shellsort
open Filter Real
open scoped Topology BigOperators

private theorem fourierMean_scale {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => a*f x) = a*mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

/-- Test a function of the signed difference of two independent binomial
counts. This handles degenerate thresholds and zero source lengths. -/
def binomialDifferenceMean (m : ℕ) (t : ℝ) (F : ℝ → ℝ) : ℝ :=
  mean (bernoulliVectorWeight t m) (fun x =>
    mean (bernoulliVectorWeight t m) (fun y => F ((bitCount x : ℝ)-bitCount y)))

theorem binomialDifferenceMean_succ (m : ℕ) (t : ℝ) (F : ℝ → ℝ) :
    binomialDifferenceMean (m+1) t F = binomialDifferenceMean m t (fun z =>
      (1-t)*((1-t)*F z+t*F (z-1)) + t*((1-t)*F (z+1)+t*F z)) := by
  let w := bernoulliVectorWeight t m
  let H (a b : ℕ) := F ((a:ℝ)-b)
  have split (a : ℕ) := bernoulli_count_succ_mean t m (H a)
  change mean (bernoulliVectorWeight t (m+1)) (fun x =>
    mean (bernoulliVectorWeight t (m+1)) (fun y => H (bitCount x) (bitCount y))) = _
  simp_rw [split]
  rw [bernoulli_count_succ_mean t m (fun a =>
    (1-t)*mean w (fun y => H a (bitCount y)) + t*mean w (fun y => H a (bitCount y+1)))]
  simp only [binomialDifferenceMean, mean_add, fourierMean_scale, H, w, Nat.cast_add, Nat.cast_one]
  simp only [sub_add_eq_sub_sub, add_sub_right_comm, sub_add_cancel]

/-- Exact cosine transform at every frequency and finite source length. -/
theorem binomialDifference_cos_mode (m : ℕ) (t θ : ℝ) :
    binomialDifferenceMean m t (fun z => Real.cos (θ*z)) =
      (1 - 4*t*(1-t)*Real.sin (θ/2)^2)^m := by
  induction m with
  | zero => simp [binomialDifferenceMean, bitCount, mean_const _ (bernoulliVectorWeight_sum t 0)]
  | succ m ih =>
    have double : Real.cos θ = 1 - 2*Real.sin (θ/2)^2 := by
      have := Real.cos_two_mul (θ/2)
      rw [show 2*(θ/2) = θ by ring] at this
      nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
    have step (z : ℝ) : (1-t)*((1-t)*Real.cos (θ*z) + t*Real.cos (θ*(z-1))) +
        t*((1-t)*Real.cos (θ*(z+1))+t*Real.cos (θ*z)) =
        (1-4*t*(1-t)*Real.sin (θ/2)^2)*Real.cos (θ*z) := by
      rw [show θ*(z-1) = θ*z - θ by ring, show θ*(z+1) = θ*z + θ by ring,
        Real.cos_sub, Real.cos_add, double]
      ring
    rw [binomialDifferenceMean_succ]
    simp only [step, binomialDifferenceMean, fourierMean_scale] at ih ⊢
    rw [ih, pow_succ]
    ring

private theorem criticalPower_limit {u : ℕ → ℝ} {m : ℕ → ℕ} {L : ℝ}
    (hu : Tendsto u atTop (𝓝 0)) (hmu : Tendsto (fun n => (m n:ℝ)*u n) atTop (𝓝 L)) :
    Tendsto (fun n => (1+u n)^(m n)) atTop (𝓝 (Real.exp L)) := by
  have hu1 : Tendsto (fun n => 1+u n) atTop (𝓝 1) := by simpa using tendsto_const_nhds.add hu
  have hd : ContinuousAt (dslope Real.log 1) 1 := continuousAt_dslope_same.mpr (Real.differentiableAt_log (by norm_num))
  have hs : Tendsto (fun n => dslope Real.log 1 (1+u n)) atTop (𝓝 1) := by
    simpa [Function.comp_def, dslope_same, Real.deriv_log] using hd.tendsto.comp hu1
  have hlog (n : ℕ) : u n * dslope Real.log 1 (1+u n) = Real.log (1+u n) := by
    simpa only [add_sub_cancel_left, smul_eq_mul, Real.log_one, sub_zero] using
      sub_smul_dslope Real.log (1:ℝ) (1+u n)
  have prod : Tendsto (fun n => (m n:ℝ)*Real.log (1+u n)) atTop (𝓝 L) := by
    simpa only [mul_assoc, hlog, mul_one] using hmu.mul hs
  apply (Real.continuous_exp.continuousAt.tendsto.comp prod).congr'
  filter_upwards [hu1.eventually (lt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn
  change Real.exp ((m n:ℝ)*Real.log (1+u n)) = _
  rw [← Real.log_pow, Real.exp_log (pow_pos hn _)]

/-- For m/G² tending to lam and a convergent threshold, the exact binomial
cosine transform approaches the wrapped normal heat multiplier at each fixed
frequency. No lower bound on the limiting threshold variance is required. -/
theorem binomialDifference_critical_mode_limit {G m : ℕ → ℕ} {t : ℕ → ℝ} {lam T : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop)
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (r : ℕ) :
    Tendsto (fun n => binomialDifferenceMean (m n) (t n)
      (fun z => Real.cos ((2*Real.pi*r/(G n:ℝ))*z))) atTop
      (𝓝 (Real.exp (-4*Real.pi^2*(r:ℝ)^2*(lam*(T*(1-T)))))) := by
  let k := Real.pi*(r:ℝ)
  let X := fun n => k/(G n:ℝ)
  let v := fun n => -4*t n*(1-t n)
  have hx : Tendsto X atTop (𝓝 0) := by
    simpa only [X, div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_const_nhds (x := k)).mul (tendsto_inv_atTop_zero.comp hG)
  have hv : Tendsto v atTop (𝓝 (-4*T*(1-T))) :=
    (tendsto_const_nhds.mul ht).mul (tendsto_const_nhds.sub ht)
  have hsin : Tendsto (fun n => Real.sin (X n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_sin.continuousAt.tendsto.comp hx
  have hsinc : Tendsto (fun n => Real.sinc (X n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_sinc.continuousAt.tendsto.comp hx
  have sinEq (z : ℝ) : Real.sin z = z * Real.sinc z := by
    by_cases hz : z=0
    · simp [hz]
    · rw [Real.sinc_of_ne_zero hz]; field_simp
  let u := fun n => v n * Real.sin (X n)^2
  have hu : Tendsto u atTop (𝓝 0) := by simpa only [zero_pow (by decide : 2≠0), mul_zero] using hv.mul (hsin.pow 2)
  have hmU : Tendsto (fun n => (m n:ℝ)*u n) atTop (𝓝 (-4*Real.pi^2*(r:ℝ)^2*(lam*(T*(1-T))))) := by
    have H := ((hm.mul hv).mul (tendsto_const_nhds (x:=k^2))).mul (hsinc.pow 2)
    convert H using 1
    · funext n; dsimp [u, X]; rw [sinEq]; simp only [div_eq_mul_inv]; ring
    · dsimp [k]; ring
  have eq (n : ℕ) : binomialDifferenceMean (m n) (t n) (fun z => Real.cos ((2*Real.pi*r/(G n:ℝ))*z)) =
      (1+u n)^(m n) := by
    rw [binomialDifference_cos_mode]
    have ang : 2*Real.pi*r/(G n:ℝ)/2 = X n := by dsimp [X,k]; ring
    rw [ang]
    dsimp only [u,v]
    congr 1
    ring
  simpa only [eq] using criticalPower_limit hu hmU

end Shellsort
end
