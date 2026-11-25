import Shellsort.F09WitnessUpper
import Shellsort.F09CertificateReduction

/-! The numerical upper witness lifted to the actual scale functional. -/
noncomputable section
namespace Shellsort.F09
open Real Set

theorem H_witness_upper : H (291/200) < (60827485406:ℝ)/100000000000 := by
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hc := Real.sq_sqrt c_pos.le
  have hp : Real.sqrt Real.pi < (177245385090552:ℝ)/100000000000000 := by
    nlinarith [Real.pi_lt_d20,Real.sqrt_nonneg Real.pi]
  have eq : c=Real.sqrt Real.pi/8 := rfl
  have cU : Real.sqrt c < (47069813188836:ℝ)/100000000000000 := by
    nlinarith [Real.sqrt_nonneg c]
  have sL : (120623380818148:ℝ)/100000000000000 ≤ Real.sqrt (291/200) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have q : Real.sqrt c/Real.sqrt (291/200) ≤
      (47069813188836/100000000000000:ℝ)/(120623380818148/100000000000000) :=
    (div_le_div_of_nonneg_right cU.le (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) sL)
  unfold H
  rw [Real.sqrt_div c_pos.le]
  linarith only [q,witness_upper_tight]

theorem kappa_witness_upper : kappa < (60827485406:ℝ)/100000000000 := by
  have lb : BddBelow (H '' Ioi 0) := ⟨0,by rintro _ ⟨z,hz,rfl⟩; exact H_nonneg hz⟩
  exact (csInf_le lb (show H (291/200) ∈ H '' Ioi 0 from ⟨_,by norm_num,rfl⟩)).trans_lt H_witness_upper

theorem K_witness_upper : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ shape 1 a b = 291/200 ∧
    K 1 a b < (60827485406:ℝ)/100000000000 := by
  obtain ⟨a,b,ha,hb,hz,he⟩ := (K_slice (d:=1) (z:=291/200) (by norm_num) (by norm_num)).1
  rw [reduced_one] at he
  exact ⟨a,b,ha,hb,hz,he ▸ H_witness_upper⟩

end Shellsort.F09

