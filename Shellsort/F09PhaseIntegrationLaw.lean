import Shellsort.F09PhaseIntegrationPhysical
import Shellsort.F09PhaseIntegrationScales
import Shellsort.ThreePassGapScales
import Shellsort.F09CertificateFourier

noncomputable section
namespace Shellsort.F09
open Filter Real Set MeasureTheory
open scoped Topology

/-- The conditional incidence limit for the d targets attached to one width.
Each same-class inversion contributes at two pivots. The d-1 other classes
have twice the reference visit variance. -/
def phase_incident_kernel (d : ℕ) (lam t x : ℝ) :=
  2/Real.sqrt (2*π)*Real.sqrt (V (lam*v t) x) +
    ((d:ℝ)-1)*(2/Real.sqrt π)*Real.sqrt (lam*v t+W (lam*v t))

private theorem kernel_integral (d : ℕ) (lam : ℝ)
    (inner : ∀ t ∈ Icc (0:ℝ) 1, IntervalIntegrable (fun x => Real.sqrt (V (lam*v t) x)) volume 0 1)
    (outer : IntervalIntegrable (fun t => ∫ x : ℝ in 0..1, Real.sqrt (V (lam*v t) x)) volume 0 1)
    (cross : IntervalIntegrable (fun t => Real.sqrt (lam*v t+W (lam*v t))) volume 0 1) :
    (∫ t : ℝ in 0..1, ∫ x : ℝ in 0..1, phase_incident_kernel d lam t x)/2 = J lam+((d:ℝ)-1)*L lam := by
  let A := 2/Real.sqrt (2*π)
  let B := ((d:ℝ)-1)*(2/Real.sqrt π)
  have inside (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      (∫ x : ℝ in 0..1, phase_incident_kernel d lam t x) =
        A*(∫ x : ℝ in 0..1, Real.sqrt (V (lam*v t) x))+B*Real.sqrt (lam*v t+W (lam*v t)) := by
    unfold phase_incident_kernel
    rw [intervalIntegral.integral_add ((inner t ht).const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
    simp [A,B]
  rw [intervalIntegral.integral_congr (fun t ht => inside t (by simpa only [uIcc_of_le zero_le_one] using ht)),
    intervalIntegral.integral_add (outer.const_mul A) (cross.const_mul B),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  unfold J L A B
  ring

/-- Local normalized phase laws for the true pivot ensemble imply the whole
final-pass law after the original threshold integral and the changing phase sum. -/
theorem actual_last_phase_limit (N H G : ℕ → ℕ) (d : ℕ) (dp : 0<d)
    (np : ∀ n, 0<N n) (hp : ∀ n, 0<H n) (gp : ∀ n, 0<G n) (cop : ∀ n, (H n).Coprime (G n))
    (grow : Tendsto (fun n => (G n:ℝ)) atTop atTop) (lam : ℝ) (hlam : 0≤lam)
    (envelope : ℝ → ℝ) (bound_int : IntervalIntegrable envelope volume 0 1)
    (bound : ∀ n t, t∈Ioo (0:ℝ) 1 → ∀ k, k<G n → |actualPhaseRow (N n) d (H n) (G n) k t| ≤ envelope t)
    (rows : ∀ t ∈ Ioo (0:ℝ) 1, ∀ x ∈ Ioo (0:ℝ) 1, ∀ k : ℕ → ℕ, (∀ n, k n<G n) →
      Tendsto (fun n => (k n:ℝ)/(G n:ℝ)) atTop (𝓝 x) →
      Tendsto (fun n => actualPhaseRow (N n) d (H n) (G n) (k n) t)
        atTop (𝓝 (phase_incident_kernel d lam t x))) :
    Tendsto (fun n => uniformAverage (fun p : RankPlacement (N n) => (gapInsertionCost
      (gapSort (gapSort p (d*H n)) (d*G n)) 1 (by decide):ℝ)) /
      ((N n:ℝ)*G n*Real.sqrt (H n))) atTop (𝓝 (J lam+((d:ℝ)-1)*L lam)) := by
  have ⟨inner,outer⟩ := phase_profile_integrable hlam
  have hv : Continuous v := by unfold v; fun_prop
  have hc : Continuous (fun t => lam*v t) := continuous_const.mul hv
  have map : MapsTo (fun t => lam*v t) (Icc 0 1) (Ici 0) :=
    fun _ ht => mul_nonneg hlam (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
  have cross : IntervalIntegrable (fun t => Real.sqrt (lam*v t+W (lam*v t))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact Real.continuous_sqrt.continuousOn.comp (hc.continuousOn.add (W_continuousOn.comp hc.continuousOn map)) (mapsTo_univ _ _)
  have lim := (phase_threshold_grid_limit gp grow (fun n t k => actualPhaseRow (N n) d (H n) (G n) k t)
    (phase_incident_kernel d lam) envelope (fun n k _ => actualPhaseRow_continuous _ _ _ _ _) bound_int bound rows).div_const 2
  rw [kernel_integral d lam inner outer cross] at lim
  exact lim.congr (fun n => (actual_last_as_phase_grid (N n) d (H n) (G n) (np n) dp (hp n) (gp n) (cop n)).symm)

end Shellsort.F09
