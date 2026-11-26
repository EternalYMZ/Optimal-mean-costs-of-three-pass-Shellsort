import Shellsort.F09CertificateReduction

/-! Exact excess of the critical coefficient over its minimum at fixed shape.
After building the anonymous review project, run from its root:
  lake env lean /path/to/F09ScalePenalty.lean
-/

noncomputable section
namespace Shellsort.F09

/-- At fixed divisor and shape, the scale ratio is r = 2 a s with
s = sqrt(c / (d z)); the optimal scale is 1 / (2 s). -/
theorem fixed_shape_scale_penalty {d : ℕ} (hd : 0 < d) {a b z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hz : shape d a b = z) :
    let s := Real.sqrt (c / ((d : ℝ) * z))
    let r := 2 * a * s
    K d a b - reduced d z = s / 2 * ((r - 1)^2 / r) := by
  have dp : 0 < (d : ℝ) := by exact_mod_cast hd
  have zp : 0 < z := hz ▸ shape_pos hd ha hb
  have shape_eq : (d : ℝ) * z = b * Real.sqrt a := by
    rw [← hz, shape]; field_simp
  have arg : (d : ℝ)^2 / (a * b^2) = 1 / z^2 := by
    rw [← hz, shape]
    field_simp
    nlinarith [Real.sq_sqrt ha.le]
  let s := Real.sqrt (c / ((d : ℝ) * z))
  have sp : 0 < s := Real.sqrt_pos.mpr (div_pos c_pos (mul_pos dp zp))
  have sqs : s^2 = c / ((d : ℝ) * z) :=
    Real.sq_sqrt (div_pos c_pos (mul_pos dp zp)).le
  have first : c * Real.sqrt a / b = a * s^2 := by
    rw [sqs, shape_eq]
    field_simp [hb.ne', (Real.sqrt_pos.mpr ha).ne']
    linear_combination c * Real.sq_sqrt ha.le
  have split : Real.sqrt (c / z) / Real.sqrt d = s := by
    dsimp [s]
    rw [← Real.sqrt_div (div_nonneg c_pos.le zp.le)]
    congr 1
    ring
  change K d a b - reduced d z = s / 2 * ((2 * a * s - 1)^2 / (2 * a * s))
  have sd := Real.sqrt_pos.mpr dp
  calc
    _ = 1 / (4 * a) + a * s^2 - s := by
      unfold K reduced H B
      dsimp only
      rw [arg, first, ← shape_eq, (div_eq_iff sd.ne').mp split]
      field_simp [ha.ne', dp.ne', sd.ne']
      ring
    _ = _ := by
      field_simp [ha.ne', sp.ne']
      ring

/-- A scale at least t-fold too large or too small incurs the same guaranteed
excess. Equality is attained at each of the two reciprocal thresholds. -/
theorem fixed_shape_scale_penalty_lower {d : ℕ} (hd : 0 < d) {a b z t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hz : shape d a b = z) (ht : 1 ≤ t) :
    let s := Real.sqrt (c / ((d : ℝ) * z))
    let r := 2 * a * s
    (t ≤ r ∨ r ≤ 1 / t) → s / 2 * ((t - 1)^2 / t) ≤ K d a b - reduced d z := by
  let s := Real.sqrt (c / ((d : ℝ) * z))
  let r := 2 * a * s
  have zp : 0 < z := hz ▸ shape_pos hd ha hb
  have dp : 0 < (d : ℝ) := by exact_mod_cast hd
  have sp : 0 < s := Real.sqrt_pos.mpr (div_pos c_pos (mul_pos dp zp))
  have rp : 0 < r := by dsimp [r]; positivity
  have tp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  change (t ≤ r ∨ r ≤ 1 / t) → s / 2 * ((t - 1)^2 / t) ≤ K d a b - reduced d z
  intro outside
  rw [fixed_shape_scale_penalty hd ha hb hz]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ s / 2)
  change (t - 1)^2 / t ≤ (r - 1)^2 / r
  apply (div_le_div_iff₀ tp rp).2
  have signed : 0 ≤ (r - t) * (r * t - 1) := by
    rcases outside with large | small
    · exact mul_nonneg (sub_nonneg.mpr large)
        (sub_nonneg.mpr (one_le_mul_of_one_le_of_one_le (ht.trans large) ht))
    · have rt := (le_div_iff₀ tp).mp small
      have one_over : 1 / t ≤ 1 := (div_le_iff₀ tp).2 (by simpa using ht)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (small.trans (one_over.trans ht)))
        (sub_nonpos.mpr rt)
  nlinarith only [signed]

#print axioms fixed_shape_scale_penalty
#print axioms fixed_shape_scale_penalty_lower

end Shellsort.F09
