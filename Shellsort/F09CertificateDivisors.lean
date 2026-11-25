import Shellsort.F09CertificateAnalysis
import Shellsort.F09CertificateReduction

/-! Divisors for which the semicircle estimate alone suffices. -/
noncomputable section
namespace Shellsort.F09
open Real Set

/-- All divisors from ten onward are excluded without Fourier quadrature. -/
theorem reduced_large_divisor {d : ℕ} (hd : 10 ≤ d) {z : ℝ} (hz : 0 < z) :
    (63:ℝ)/100 ≤ reduced d z := by
  have dr : (10:ℝ) ≤ d := by exact_mod_cast hd
  have dp : (0:ℝ) < d := by linarith
  have hs := Real.sq_sqrt dp.le
  have ht : (316:ℝ)/100 ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith)
  have hc : (22155:ℝ)/100000 ≤ B z := by linarith [c_lower,c_le_B hz]
  have he := mul_le_mul_of_nonneg_left hc (show 0 ≤ (d:ℝ)-1 by linarith)
  have hquad := mul_nonneg (show 0 ≤ Real.sqrt d-316/100 by linarith)
    (show 0 ≤ (22155:ℝ)/100000*(Real.sqrt d+316/100)-63/100 by linarith)
  unfold reduced
  rw [le_div_iff₀ (Real.sqrt_pos.mpr dp)]
  nlinarith [H_nonneg hz]

theorem K_large_divisor {d : ℕ} (hd : 10 ≤ d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (63:ℝ)/100 ≤ K d a b :=
  (K_lowerBounds (by omega : 0 < d) _).mpr (fun _ hz => reduced_large_divisor hd hz) _ _ ha hb

/-- The coprime one-dimensional lower bound excludes every divisor at least four. -/
theorem reduced_from_four {d : ℕ} (hd : 4 ≤ d) {z : ℝ} (hz : 0 < z)
    (hH : (6082:ℝ)/10000 ≤ H z) : (6364:ℝ)/10000 ≤ reduced d z := by
  have dr : (4:ℝ) ≤ d := by exact_mod_cast hd
  have dp : (0:ℝ) < d := by linarith
  have hs := Real.sq_sqrt dp.le
  have ht : (2:ℝ) ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by linarith)
  have hc : (22155:ℝ)/100000 ≤ B z := by linarith [c_lower,c_le_B hz]
  have he := mul_le_mul_of_nonneg_left hc (show 0 ≤ (d:ℝ)-1 by linarith)
  have hquad := mul_nonneg (show 0 ≤ Real.sqrt d-2 by linarith)
    (show 0 ≤ (22155:ℝ)/100000*(Real.sqrt d+2)-6364/10000 by linarith)
  unfold reduced
  rw [le_div_iff₀ (Real.sqrt_pos.mpr dp)]
  nlinarith

end Shellsort.F09

