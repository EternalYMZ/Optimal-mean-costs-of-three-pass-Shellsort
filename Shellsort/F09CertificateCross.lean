import Shellsort.F09CertificateAnalysis

/-! Direct lower rectangular sums for the cross integral, using only the
first Fourier decay rate. All finite certificate arithmetic is rational. -/
noncomputable section
namespace Shellsort.F09
open Real Set MeasureTheory
open scoped BigOperators

private def mesh (k : ℕ) : ℚ := (k:ℚ)/64
private def vertex (k : ℕ) : ℚ := mesh k*(1-mesh k)
private def base (k : ℕ) : ℚ := min (vertex k) (vertex (k+1))
private def envelope (z : ℚ) (k : ℕ) : ℚ :=
  let w := base k
  w + z^2*((1-1/(1+18*w/z^2)^2)/12)

private def height (z : ℚ) (k : ℕ) : ℚ :=
  ((Nat.sqrt (Int.toNat ⌊(10^8:ℚ)*envelope z k⌋) : ℕ):ℚ)/10000

private def Sound (z b : ℚ) : Prop :=
  (∀ i : Fin 64, (height z i)^2 ≤ envelope z i) ∧
  b*(177246/100000) ≤ (∑ k ∈ Finset.range 64, height z k)/64

private instance (z b : ℚ) : Decidable (Sound z b) := by unfold Sound; infer_instance

set_option maxHeartbeats 1500000 in
private theorem integrate {z b : ℚ} (hzq : 0 < z) (hbq : 0 ≤ b) (cert : Sound z b) :
    (b:ℝ) ≤ B z := by
  have hz : 0 < (z:ℝ) := by exact_mod_cast hzq
  have hb : 0 ≤ (b:ℝ) := by exact_mod_cast hbq
  let a := fun (k : ℕ) => (mesh k:ℝ)
  have ga (k : ℕ) : a k = (k:ℝ)/64 := by simp [a,mesh]
  have step (k : ℕ) : a (k+1)-a k = 1/64 := by simp [ga]; ring
  have order (k : ℕ) : a k ≤ a (k+1) := by linarith [step k]
  have lo (k : ℕ) : 0 ≤ a k := by rw [ga]; positivity
  have hi {k : ℕ} (hk : k < 64) : a (k+1) ≤ 1 := by
    rw [ga]; push_cast; have he : (k:ℝ) ≤ 63 := by exact_mod_cast (show k ≤ 63 by omega)
    linarith
  have intg (k : ℕ) (hk : k < 64) :
      IntervalIntegrable (scaled z) volume (a k) (a (k+1)) := by
    apply (scaled_integrable hz).mono_set
    rw [uIcc_of_le (order k),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (lo k) (hi hk)
  have piece (k : ℕ) (hk : k < 64) :
      (height z k:ℝ)/64 ≤ ∫ t in (a k)..(a (k+1)), scaled z t := by
    have e (j : ℕ) : (vertex j:ℝ) = v (a j) := by simp [vertex,a,v]
    have eb : (base k:ℝ) = min (v (a k)) (v (a (k+1))) := by simp [base,e]
    have hpoint (t : ℝ) (ht : t ∈ Icc (a k) (a (k+1))) : (height z k:ℝ) ≤ scaled z t := by
      have bt : (base k:ℝ) ≤ v t := by
        rw [eb]
        by_cases h : t ≤ 1/2
        · apply le_trans (min_le_left _ _)
          unfold v; nlinarith only [mul_nonneg (sub_nonneg.mpr ht.1)
            (show 0 ≤ 1-t-a k by linarith only [h,ht.1])]
        · apply le_trans (min_le_right _ _)
          unfold v; nlinarith only [mul_nonneg (sub_nonneg.mpr ht.2)
            (show 0 ≤ t+a (k+1)-1 by linarith only [h,ht.2])]
      have bn : 0 ≤ (base k:ℝ) := by
        rw [eb]
        exact le_min (mul_nonneg (lo k) (sub_nonneg.mpr ((order k).trans (hi hk))))
          (mul_nonneg (lo (k+1)) (sub_nonneg.mpr (hi hk)))
      have vv : 0 ≤ v t := bn.trans bt
      have dw := W_rational_lower (x:=1/(z:ℝ)^2*v t) (u:=18*(base k:ℝ)/z^2)
        (mul_nonneg (by positivity) vv) (by positivity) (by
          rw [show (18:ℝ)*(1/(z:ℝ)^2*v t) = 18*v t/z^2 by ring]
          gcongr)
      have num : (height z k:ℝ)^2 ≤ (envelope z k:ℝ) := by
        exact_mod_cast cert.1 ⟨k,hk⟩
      rw [scaled_eq hz]
      apply Real.le_sqrt_of_sq_le
      apply num.trans
      unfold envelope
      push_cast
      linarith only [bt,mul_le_mul_of_nonneg_left dw (sq_nonneg (z:ℝ))]
    have hh := intervalIntegral.integral_mono_on (order k) intervalIntegrable_const (intg k hk) hpoint
    rw [intervalIntegral.integral_const,step,smul_eq_mul] at hh
    linarith
  have hsum := Finset.sum_le_sum (s:=Finset.range 64) (fun i hi => piece i (Finset.mem_range.mp hi))
  rw [intervalIntegral.sum_integral_adjacent_intervals intg,← Finset.sum_div] at hsum
  have e0 : a 0 = 0 := by norm_num [ga]
  have e1 : a 64 = 1 := by norm_num [ga]
  rw [e0,e1] at hsum
  have chk : (b:ℝ)*(177246/100000) ≤ (∑ k ∈ Finset.range 64,(height z k:ℝ))/64 := by
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_sum] using
      (Rat.cast_le (K:=ℝ)).mpr cert.2
  have hp : Real.sqrt Real.pi ≤ (177246:ℝ)/100000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith [Real.pi_lt_d6]⟩
  unfold scaled at hsum
  rw [intervalIntegral.integral_const_mul] at hsum
  unfold B L
  rw [← mul_div_assoc,le_div_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
  exact (mul_le_mul_of_nonneg_left hp hb).trans (chk.trans hsum)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem sound_three_quarters : Sound (3/4) (246/1000) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem sound_one : Sound 1 (264/1000) := by decide +kernel

theorem B_three_quarters : (246:ℝ)/1000 ≤ B (3/4) := by
  simpa only [Rat.cast_div,Rat.cast_ofNat] using
    integrate (z:=(3/4:ℚ)) (b:=(246/1000:ℚ)) (by norm_num) (by norm_num) sound_three_quarters

theorem B_one : (264:ℝ)/1000 ≤ B 1 := by
  simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using
    integrate (z:=(1:ℚ)) (b:=(264/1000:ℚ)) (by norm_num) (by norm_num) sound_one

end Shellsort.F09

