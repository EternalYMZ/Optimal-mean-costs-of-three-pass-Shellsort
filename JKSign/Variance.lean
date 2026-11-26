import Shellsort.FirstPassMoments
import ReviewJK.ArcAssembly

/-! Exact loss of Bernoulli count variance relative to a fixed reference probability.
The term linear in the drift is retained because an actual conditioned pivot can shift the mean. -/
noncomputable section
namespace Shellsort.JK
open scoped BigOperators

/-- Exact variance decomposition for independent indicators of arbitrary marginals. -/
theorem bernoulli_variance_drift_defect {m : ℕ} (p : Fin m → ℝ) (q : ℝ) :
    centeredSecond (productWeight (fun i => bernoulliWeight (p i)))
      (fun z => (bitCount z : ℝ)) =
      (m : ℝ)*q*(1-q) + (1-2*q)*(∑ i, (p i-q)) - ∑ i, (p i-q)^2 := by
  let trial := fun (_ : Fin m) (z : Bool) => if z then (1 : ℝ) else 0
  have h := productWeight_variance_sum (fun i => bernoulliWeight (p i)) trial
    (fun i => bernoulliWeight_sum (p i))
  have hc (z : Fin m → Bool) : (bitCount z : ℝ) = ∑ i, trial i (z i) := by
    simp only [bitCount, trial, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [hc]
  rw [h]
  simp only [trial, bernoulli_scaled_variance, one_pow, mul_one]
  calc
    _ = ∑ i, (q*(1-q) + (1-2*q)*(p i-q) - (p i-q)^2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- An absolute drift bound leaves a variance deficit equal to the squared marginal
heterogeneity, modulo the displayed linear allowance. -/
theorem bernoulli_variance_budget {m : ℕ} (p : Fin m → ℝ) (q A : ℝ)
    (hq : q ∈ Set.Icc 0 1) (hdrift : |∑ i, (p i-q)| ≤ A) :
    centeredSecond (productWeight (fun i => bernoulliWeight (p i)))
      (fun z => (bitCount z : ℝ)) + ∑ i, (p i-q)^2 ≤ (m : ℝ)*q*(1-q)+A := by
  rw [bernoulli_variance_drift_defect p q]
  have hq' : |1-2*q| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2], by linarith [hq.1]⟩
  have hh : (1-2*q)*(∑ i, (p i-q)) ≤ A := by
    calc
      _ ≤ |(1-2*q)*(∑ i, (p i-q))| := le_abs_self _
      _ = |1-2*q| * |∑ i, (p i-q)| := abs_mul _ _
      _ ≤ 1 * A := mul_le_mul hq' hdrift (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  linarith

/-- The tangent bound keeps the squared defect when passing from a variance to its square root.
Here B is the positive reference standard deviation. -/
theorem standardDeviation_loss_of_budget {V B A D : ℝ} (hV : 0 ≤ V) (hB : 0 < B)
    (h : V+D ≤ B^2+A) :
    Real.sqrt V ≤ B+(A-D)/(2*B) := by
  have hmul : (2*B) * (Real.sqrt V - B) ≤ A-D := by
    nlinarith [sq_nonneg (Real.sqrt V-B),Real.sq_sqrt hV]
  have hp : 0 < 2*B := by positivity
  have := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hmul :
    (Real.sqrt V-B)*(2*B) ≤ A-D)
  linarith


/-- The expected number of hits in the same finite product. -/
theorem bernoulli_count_mean {m : ℕ} (p : Fin m → ℝ) :
    mean (productWeight (fun i => bernoulliWeight (p i))) (fun z => (bitCount z : ℝ)) = ∑ i, p i := by
  let trial := fun (_ : Fin m) (z : Bool) => if z then (1 : ℝ) else 0
  have hc (z : Fin m → Bool) : (bitCount z : ℝ) = ∑ i, trial i (z i) := by
    simp only [bitCount, trial, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [hc]
  rw [productWeight_mean_sum (fun i => bernoulliWeight (p i)) trial
    (fun i => bernoulliWeight_sum (p i))]
  simp [trial,bernoulli_scaled_mean]

/-- Matching the mean removes the drift and turns the variance gap into exactly
the same gap of the two noncentered second moments. -/
theorem bernoulli_second_moment_gap {m : ℕ} (p : Fin m → ℝ) (q : ℝ)
    (hs : ∑ i, p i = (m : ℝ)*q) :
    mean (bernoulliVectorWeight q m) (fun z => (bitCount z : ℝ)^2) -
      mean (productWeight (fun i => bernoulliWeight (p i))) (fun z => (bitCount z : ℝ)^2) =
      ∑ i, (p i-q)^2 := by
  let count := fun z : Fin m → Bool => (bitCount z : ℝ)
  let w := fun (p : Fin m → ℝ) => productWeight (fun i => bernoulliWeight (p i))
  let u := fun _ : Fin m => q
  have norm (t : Fin m → ℝ) := productWeight_sum (fun i => bernoulliWeight (t i))
    (fun i => bernoulliWeight_sum (t i))
  have drift : ∑ i, (p i-q)=0 := by simp [Finset.sum_sub_distrib,hs]
  have v1 := bernoulli_variance_drift_defect p q
  have v2 := bernoulli_variance_drift_defect u q
  rw [centeredSecond_identity _ _ (norm p), bernoulli_count_mean p, hs, drift] at v1
  rw [centeredSecond_identity _ _ (norm u), bernoulli_count_mean u] at v2
  simp only [u, sub_self, Finset.sum_const_zero, sub_zero, mul_zero, add_zero,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at v2
  change secondMoment (w u) count - secondMoment (w p) count = _
  change secondMoment (w p) count - ((m:ℝ)*q)^2 = _ at v1
  change secondMoment (w u) count - ((m:ℝ)*q)^2 = _ at v2
  linarith

end Shellsort.JK
end
