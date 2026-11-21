import Shellsort.ProductWeights

/-! Equal total mass forces a coordinate change to be balanced at other
coordinates. For a random subset of fixed size this bounds each membership
variance by the sum of the other membership variances. -/

namespace Shellsort
open scoped BigOperators

theorem equal_mass_coordinate_abs_le {ι : Type*} [Fintype ι] (u v : ι → ℝ)
    (i : ι) (hs : ∑ j, u j = ∑ j, v j) :
    2 * |u i - v i| ≤ ∑ j, |u j - v j| := by
  classical
  have sumzero : ∑ j, (u j - v j) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have comp : ∑ j ∈ Finset.univ.erase i, (u j - v j) = -(u i - v i) := by
    have := Finset.sum_erase_add Finset.univ (fun j => u j - v j) (Finset.mem_univ i)
    linarith
  have bound := Finset.abs_sum_le_sum_abs (fun j => u j - v j) (Finset.univ.erase i)
  rw [comp, abs_neg] at bound
  have := Finset.sum_erase_add Finset.univ (fun j => |u j - v j|) (Finset.mem_univ i)
  linarith

/-- The probability of one occupied phase under an explicit finite law. -/
noncomputable def phaseMarginal {α ι : Type*} [Fintype α] [DecidableEq ι]
    (w : α → ℝ) (mask : α → Finset ι) (j : ι) : ℝ :=
  mean w fun x => if j ∈ mask x then 1 else 0

private theorem mean_scale_phase {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => a*f x) = a * mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

private theorem mean_le_on_support {α : Type*} [Fintype α] {w f g : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (h : ∀ x, w x ≠ 0 → f x ≤ g x) : mean w f ≤ mean w g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hz : w x = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_left (h x hz) (hw x)

private theorem two_copies_mismatch {α ι : Type*} [Fintype α] [DecidableEq ι]
    (w : α → ℝ) (hw : ∑ x, w x = 1) (mask : α → Finset ι) (j : ι) :
    (mean w fun x => mean w fun y =>
      |(if j ∈ mask x then (1:ℝ) else 0) - (if j ∈ mask y then 1 else 0)|) =
      2 * (phaseMarginal w mask j * (1-phaseMarginal w mask j)) := by
  let f (x : α) : ℝ := if j ∈ mask x then 1 else 0
  let p := mean w f
  have point (x y : α) : |f x - f y| = (f x + f y) - (2 * f x)*f y := by
    by_cases hx : j ∈ mask x <;> by_cases hy : j ∈ mask y <;> norm_num [f, hx, hy]
  have inner (x : α) : (mean w fun y => |f x - f y|) = f x + p - (2*p)*f x := by
    simp only [point, mean_sub, mean_add, mean_const w hw, mean_scale_phase, p]
    ring
  change (mean w fun x => mean w fun y => |f x - f y|) = 2*(p*(1-p))
  simp only [inner, mean_sub, mean_add, mean_const w hw, mean_scale_phase, p]
  ring

/-- No independence is assumed between different sites of a sampled mask.
Only masks of nonzero weight must satisfy the cardinality constraint. -/
theorem fixed_card_phase_variance {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (w : α → ℝ) (mask : α → Finset ι) (hw0 : ∀ x, 0 ≤ w x) (hw : ∑ x, w x = 1)
    (hs : ∀ x y, w x ≠ 0 → w y ≠ 0 → (mask x).card = (mask y).card) (i : ι) :
    2 * (phaseMarginal w mask i * (1 - phaseMarginal w mask i)) ≤
      ∑ j, phaseMarginal w mask j * (1-phaseMarginal w mask j) := by
  let f (x : α) (j : ι) : ℝ := if j ∈ mask x then 1 else 0
  have mass (x : α) : ∑ j, f x j = ((mask x).card : ℝ) := by
    simp [f]
  have path (x y : α) (hx : w x ≠ 0) (hy : w y ≠ 0) :=
    equal_mass_coordinate_abs_le (f x) (f y) i (by rw [mass, mass, hs x y hx hy])
  have bound : (mean w fun x => mean w fun y => 2*|f x i-f y i|) ≤
      (mean w fun x => mean w fun y => ∑ j, |f x j-f y j|) :=
    mean_le_on_support hw0 fun x hx => mean_le_on_support hw0 fun y hy => path x y hx hy
  simp only [mean_scale_phase, mean_sum, f, two_copies_mismatch w hw mask,
    ← Finset.mul_sum] at bound
  linarith

end Shellsort
