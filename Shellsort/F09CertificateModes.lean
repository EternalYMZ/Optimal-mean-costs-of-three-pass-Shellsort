import Shellsort.F09CertificateFourier

/-! Uniform bounds for the neglected heat modes after the finite dot product. -/
noncomputable section
namespace Shellsort.F09
open Real Set
open scoped BigOperators

theorem V_truncated_upper {δ : ℝ} (hd : 0 ≤ δ) (x : ℝ) (n : ℕ) :
    V δ x ≤ v x-2/Real.pi^2*∑ i ∈ Finset.range n, mode i δ x := by
  have h := (mode_sum hd x).sum_le_tsum (Finset.range n) (fun i _ => mode_nonneg i δ x)
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left h (by positivity)) _

theorem V_truncated_lower {δ : ℝ} (hd0 : 0 ≤ δ) (x : ℝ) (m : ℕ)
    (cap : 59 ≤ 36*δ*((m:ℝ)+1)^2) :
    v x-2/Real.pi^2*(∑ i ∈ Finset.range m, mode i δ x) - 1/(2:ℝ)^59 ≤ V δ x := by
  have p : 9 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have e : Real.exp (-59) ≤ 1/(2:ℝ)^59 := by
    rw [Real.exp_neg,← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    calc
      (2:ℝ)^59 ≤ (Real.exp 1)^59 := by gcongr; linarith [Real.add_one_le_exp 1]
      _ = Real.exp 59 := by rw [← Real.exp_nat_mul]; norm_num
  have b (k : ℕ) : mode (k+m) δ x ≤ (1/(2:ℝ)^59)*weight k := by
    have hk : (m:ℝ)+1 ≤ ((k+m:ℕ):ℝ)+1 := by push_cast; linarith [Nat.cast_nonneg k (α:=ℝ)]
    have hk2 : ((m:ℝ)+1)^2 ≤ (((k+m:ℕ):ℝ)+1)^2 := by gcongr
    have ex := mul_le_mul_of_nonneg_right
      (mul_le_mul p hk2 (sq_nonneg _) (sq_nonneg _)) hd0
    have coeff : (59:ℝ) ≤ 4*Real.pi^2*(((k+m:ℕ):ℝ)+1)^2*δ := by nlinarith only [cap,ex]
    have he : Real.exp (-4*Real.pi^2*(((k+m:ℕ):ℝ)+1)^2*δ) ≤ 1/(2:ℝ)^59 :=
      (Real.exp_le_exp.mpr (by linarith only [coeff])).trans e
    unfold mode weight
    have hprod := mul_le_mul he (Real.sin_sq_le_one (Real.pi*(((k+m:ℕ):ℝ)+1)*x))
      (sq_nonneg _) (by norm_num)
    rw [mul_one] at hprod
    calc
      _ ≤ (1/(2:ℝ)^59)/(((k+m:ℕ):ℝ)+1)^2 := div_le_div_of_nonneg_right hprod (sq_nonneg _)
      _ ≤ (1/(2:ℝ)^59)/((k:ℝ)+1)^2 := by apply div_le_div_of_nonneg_left (by norm_num) (by positivity); gcongr <;> norm_num
      _ = _ := by ring
  have h := mode_sum hd0 x
  have hs := ((summable_nat_add_iff m).mpr h).tsum_le_tsum b
    (weight_sum.summable.mul_left (1/(2:ℝ)^59))
  rw [tsum_mul_left,weight_sum.tsum_eq] at hs
  have eq := h.sum_add_tsum_nat_add m
  change _ ≤ v x-2/Real.pi^2*(∑' i, mode i δ x)
  rw [← eq]
  have hp : 0 < Real.pi^2 := by positivity
  field_simp
  nlinarith only [hs,hp]

end Shellsort.F09

