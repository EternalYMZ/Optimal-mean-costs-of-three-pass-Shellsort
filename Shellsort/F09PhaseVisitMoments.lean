import Shellsort.F09PhaseCross
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul

/-! Third moments of single-source visits stay bounded at critical lengths.
This also covers targets chosen by an independent reference owner. -/
noncomputable section
namespace Shellsort
open Set Real
open scoped BigOperators

theorem binomialDifference_fourth (m : ℕ) (t : ℝ) :
    binomialDifferenceMean m t (fun z => z^4) =
      12*(m:ℝ)*(m-1)*(t*(1-t))^2 + 2*m*(t*(1-t)) := by
  induction m with
  | zero => simp [binomialDifferenceMean,bitCount,mean_const _ (bernoulliVectorWeight_sum t 0)]
  | succ m ih =>
    let v := t*(1-t)
    have a (z : ℝ) : (1-t)*((1-t)*z^4+t*(z-1)^4)+t*((1-t)*(z+1)^4+t*z^4) =
        (z^4+(12*v)*z^2)+2*v := by dsimp [v]; ring
    have sec : binomialDifferenceMean m t (fun z => z^2) = 2*((m:ℝ)*t*(1-t)) := by
      unfold binomialDifferenceMean
      rw [phase_two_copy_square _ _ (bernoulliVectorWeight_sum t m), phase_bitCount_exact_variance]
    rw [binomialDifferenceMean_succ]
    simp only [a, binomialDifferenceMean, mean_add, phaseMean_scale, mean_const _ (bernoulliVectorWeight_sum t m)] at ih sec ⊢
    rw [ih,sec]; dsimp only [v]; push_cast; ring

private theorem fourth_centered_le_pair {α : Type*} [Fintype α] (w f : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (h1 : ∑ x, w x = 1) :
    mean w (fun x => (f x-mean w f)^4) ≤ mean w (fun x => mean w (fun y => (f x-f y)^4)) := by
  apply phaseMean_mono w hw; intro x
  have cv : ConvexOn ℝ Set.univ (fun z : ℝ => z^4) := (by decide : Even 4).convexOn_pow
  have j := cv.map_sum_le (t:=Finset.univ) (p:=fun y => f x-f y) (w:=w)
    (fun y _ => hw y) h1 (fun _ _ => Set.mem_univ _)
  change (mean w (fun y => f x-f y))^4 ≤ _ at j
  simp only [mean_sub, mean_const w h1] at j
  exact j

private theorem add_fourth_cap (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)^4 ≤ 8*(a^4+b^4) := by
  nlinarith [mul_nonneg (sq_nonneg (a-b))
    (show 0 ≤ 7*a^2+10*a*b+7*b^2 by positivity)]

/-- Absolute centered third moment of the actual number of visits from one
binomial prefix to a single physical target. The bound is uniform in s,j,t. -/
theorem source_visit_third_centered_bound (h g j s m : ℕ) (t : ℝ)
    (hg : 0 < g) (hc : Nat.Coprime h g) (hj : j < g) (ht : t ∈ Icc 0 1) :
    let w := bernoulliVectorWeight t m
    let F := fun x => (sourcePrefixCount h g j s (bitCount x):ℝ)
    mean w (fun x => |F x - mean w F|^3) ≤ 9 + 8*(12*(m:ℝ)^2+2*m)/(g:ℝ)^4 := by
  let w := bernoulliVectorWeight t m
  let F := fun x : Fin m → Bool => (sourcePrefixCount h g j s (bitCount x):ℝ)
  let B := fun x : Fin m → Bool => (bitCount x:ℝ)
  let v := t*(1-t)
  have gp : (0:ℝ) < g := by exact_mod_cast hg
  have w0 := bernoulliVectorWeight_nonneg t ht m
  have w1 := bernoulliVectorWeight_sum t m
  have bound (x y : Fin m → Bool) :
      (g:ℝ)^4 * (F x-F y)^4 ≤ 8*((B x-B y)^4+(g:ℝ)^4) := by
    have de := source_prefix_pair_scaled h g j s (bitCount x) (bitCount y) hg hc hj
    change |(g:ℝ)*(F x-F y)-(B x-B y)| ≤ g at de
    let a := (g:ℝ)*(F x-F y)
    let b := B x-B y
    have tri : |a| ≤ |b|+g := by
      have T := abs_add_le (a-b) b
      rw [sub_add_cancel] at T
      linarith
    have P := (pow_le_pow_left₀ (abs_nonneg _) tri 4).trans (add_fourth_cap _ _ (abs_nonneg _) gp.le)
    simpa only [Even.pow_abs (by decide : Even 4), a, b, mul_pow] using P
  have E := phaseMean_mono w w0 (fun x => phaseMean_mono w w0 (bound x))
  simp only [phaseMean_scale,mean_add,mean_const w w1] at E
  change (g:ℝ)^4 * mean w (fun x => mean w fun y => (F x-F y)^4) ≤
    8 * (binomialDifferenceMean m t (fun z => z^4)+(g:ℝ)^4) at E
  rw [binomialDifference_fourth] at E
  have cap4 : mean w (fun x => (F x-mean w F)^4) ≤ 8+8*(12*(m:ℝ)^2+2*m)/(g:ℝ)^4 := by
    apply (fourth_centered_le_pair w F w0 w1).trans
    rw [← sub_le_iff_le_add', le_div_iff₀ (pow_pos gp 4)]
    have lo : 0 ≤ v := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    have hi : v ≤ 1 := by dsimp [v]; nlinarith [sq_nonneg (t-1/2)]
    have A : v^2 ≤ 1 := pow_le_one₀ lo hi
    have A1 := mul_le_mul_of_nonneg_left A (sq_nonneg (m:ℝ))
    have A2 := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg m)
    change (g:ℝ)^4 * _ ≤ 8*(12*(m:ℝ)*(m-1)*v^2 + 2*m*v + (g:ℝ)^4) at E
    nlinarith [mul_nonneg (Nat.cast_nonneg m) (sq_nonneg v)]
  have cube (z : ℝ) : |z|^3 ≤ 1+z^4 := by
    by_cases h : |z| ≤ 1
    · exact (pow_le_one₀ (abs_nonneg z) h (n:=3)).trans (le_add_of_nonneg_right (by positivity))
    · have h' := pow_le_pow_right₀ (le_of_not_ge h) (by decide : 3 ≤ 4)
      rw [Even.pow_abs (by decide : Even 4)] at h'
      linarith
  have upper := phaseMean_mono w w0 (fun x => cube (F x-mean w F))
  rw [mean_add, mean_const w w1] at upper
  change mean w (fun x => |F x-mean w F|^3) ≤ _
  linarith

end Shellsort
end
