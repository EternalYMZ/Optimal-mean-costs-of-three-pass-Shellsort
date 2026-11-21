import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! Scale comparison for the true two-pass residual estimate. These statements
    do not assume independence of chains or assert the probabilistic estimate. -/
noncomputable section
namespace Shellsort.TwoGapResidualScales

/-- Square of the two-pass displacement scale, divided by the last gap squared. -/
def scaleSquared (n h g d : ℝ) : ℝ :=
  n*(d-1)/g^2 + min (h/d) (Real.sqrt (n*h)/g)

private theorem sparse_le_dense_plus_base {n h g d : ℝ}
    (nn : 0 ≤ n) (hn : 0 ≤ h) (gp : 0 < g) (dd : 2 ≤ d) :
    Real.sqrt (n*h)/g ≤ n*(d-1)/g^2 + h/d := by
  have dp : 0<d := by linarith
  have hnroot := Real.sq_sqrt (mul_nonneg nn hn)
  have an : 0 ≤ n*(d-1) := mul_nonneg nn (by linarith)
  have A : 0 ≤ n*(d-1)*d := mul_nonneg an dp.le
  have B : 0 ≤ h*g^2 := mul_nonneg hn (sq_nonneg _)
  have prod : n*h*d ≤ 4*(n*h)*(d-1) := by
    nlinarith only [mul_nonneg (mul_nonneg nn hn) (show 0≤3*d-4 by linarith)]
  have D : (Real.sqrt (n*h)*g*d)^2 ≤ (n*(d-1)*d+h*g^2)^2 := by
    calc
      _ = (n*h*d)*(g^2*d) := by rw [mul_pow,mul_pow,hnroot]; ring
      _ ≤ (4*(n*h)*(d-1))*(g^2*d) :=
        mul_le_mul_of_nonneg_right prod (mul_nonneg (sq_nonneg g) dp.le)
      _ ≤ _ := by nlinarith only [sq_nonneg (n*(d-1)*d-h*g^2)]
  have step : Real.sqrt (n*h)*g*d ≤ n*(d-1)*d+h*g^2 :=
    le_of_sq_le_sq D (add_nonneg A B)
  field_simp [gp.ne',dp.ne']
  nlinarith only [step]

theorem noncoprime_sandwich {n h g d : ℝ} (nn : 0 ≤ n) (hn : 0 ≤ h)
    (gp : 0 < g) (dd : 2 ≤ d) :
    scaleSquared n h g d ≤ n*(d-1)/g^2 + Real.sqrt (n*h)/g ∧
    n*(d-1)/g^2 + Real.sqrt (n*h)/g ≤ 2*scaleSquared n h g d := by
  have base : 0 ≤ n*(d-1)/g^2 := div_nonneg (mul_nonneg nn (by linarith)) (sq_nonneg _)
  have dens : 0 ≤ h/d := div_nonneg hn (by linarith)
  have sp : 0 ≤ Real.sqrt (n*h)/g := div_nonneg (Real.sqrt_nonneg _) gp.le
  have q := sparse_le_dense_plus_base nn hn gp dd
  unfold scaleSquared
  constructor
  · exact add_le_add_right (min_le_right _ _) _
  · by_cases hh : h/d ≤ Real.sqrt (n*h)/g
    · rw [min_eq_left hh]; linarith
    · rw [min_eq_right (le_of_not_ge hh)]; linarith

private theorem sparse_floor {n h g : ℝ} (np : 0<n) (gp : 0<g) (gh : g≤h) :
    Real.sqrt (n/g) ≤ Real.sqrt (n*h)/g := by
  apply (le_div_iff₀ gp).2
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  rw [mul_pow,Real.sq_sqrt (div_nonneg np.le gp.le),Real.sq_sqrt (mul_nonneg np.le (gp.le.trans gh))]
  calc
    n/g*g^2 = n*g := by field_simp
    _ ≤ n*h := mul_le_mul_of_nonneg_left gh np.le

/-- Every source regime pays for one of two logarithms: either the last gap
    itself, or the chain length at that gap. -/
theorem root_floor {n h g d : ℝ} (np : 0<n) (gp : 0<g) (gh : g≤h)
    (dg : d=1 ∨ 2≤d) :
    min (Real.sqrt g) (Real.sqrt (Real.sqrt (n/g))) ≤ Real.sqrt (scaleSquared n h g d) := by
  rw [←Real.sqrt_monotone.map_min]
  apply Real.sqrt_le_sqrt
  have sf := sparse_floor np gp gh
  rcases dg with rfl|dd
  · simp only [scaleSquared,sub_self,mul_zero,zero_div,div_one,zero_add]
    exact min_le_min gh sf
  · have q := sparse_le_dense_plus_base np.le (gp.le.trans gh) gp dd
    have base : 0≤n*(d-1)/g^2 := div_nonneg (mul_nonneg np.le (by linarith)) (sq_nonneg _)
    apply (min_le_right _ _).trans
    apply sf.trans
    unfold scaleSquared
    by_cases hh : h/d ≤ Real.sqrt (n*h)/g
    · simpa only [min_eq_left hh] using q
    · rw [min_eq_right (le_of_not_ge hh)]; linarith

private theorem logb_one {x : ℝ} (hx : 1≤x) :
    Real.logb 2 x ≤ 2*(x-1) := by
  have xp : 0<x := by linarith
  have half := Real.log_le_sub_one_of_pos (show (0:ℝ)<(2:ℝ)⁻¹ by norm_num)
  rw [Real.log_inv] at half
  have ltwo : (1:ℝ)/2 ≤ Real.log 2 := by linarith
  have lin := Real.log_le_sub_one_of_pos xp
  unfold Real.logb
  apply (div_le_iff₀ (Real.log_pos (show (1:ℝ)<2 by norm_num))).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr ltwo),lin]

/-- Given a finite entropy bound after both sorting passes and the normalized
    scale charge, the log of the final allowed gap is also paid. -/
theorem absorb_gap_log {n h g d e : ℝ} (gp : 1≤g) (gh : g≤h) (gn : g≤n)
    (dg : d=1 ∨ 2≤d) (ep : 0≤e)
    (entropy : Real.logb 2 g ≤ e+Real.logb 2 (n/g)) :
    Real.logb 2 g ≤ e+8*Real.sqrt (scaleSquared n h g d) := by
  have gp' : 0<g := by linarith
  have np : 0<n := gp'.trans_le gn
  have yg : 1≤n/g := (one_le_div gp').2 gn
  have sg : 1≤Real.sqrt g := by simpa using Real.sqrt_le_sqrt gp
  have sy : 1≤Real.sqrt (n/g) := by simpa using Real.sqrt_le_sqrt yg
  have ry : 1≤Real.sqrt (Real.sqrt (n/g)) := by simpa using Real.sqrt_le_sqrt sy
  have choice := root_floor np gp' gh dg
  by_cases den : Real.sqrt g ≤ Real.sqrt (Real.sqrt (n/g))
  · rw [min_eq_left den] at choice
    have b := logb_one sg
    rw [Real.logb,Real.log_sqrt gp'.le] at b
    unfold Real.logb
    linarith [show Real.log g / 2 / Real.log 2 = (Real.log g / Real.log 2)/2 by ring]
  · rw [min_eq_right (le_of_not_ge den)] at choice
    have b := logb_one ry
    rw [Real.logb,Real.log_sqrt (Real.sqrt_nonneg _),Real.log_sqrt (div_nonneg np.le gp'.le)] at b
    unfold Real.logb at entropy ⊢
    linarith [show Real.log (n/g) / 2 / 2 / Real.log 2 = (Real.log (n/g) / Real.log 2)/4 by ring]

#print axioms noncoprime_sandwich
#print axioms absorb_gap_log
end Shellsort.TwoGapResidualScales
