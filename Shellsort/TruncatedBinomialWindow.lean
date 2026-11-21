import Shellsort.BernoulliCounts
import Mathlib.Data.Nat.Dist

/-! Finite walk estimates for the difference of two independent binomial
counts, with explicit truncation and rounding constants. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

private def walk (k : ℕ) (t : ℝ) (F : ℝ → ℝ) : ℝ :=
  mean (bernoulliVectorWeight t k) (fun x => mean (bernoulliVectorWeight t k)
    (fun y => F ((bitCount x : ℝ) - (bitCount y : ℝ))))

private lemma mean_walk_scale {α : Type*} [Fintype α] (w f : α → ℝ) (c : ℝ) :
    mean w (fun x => c*f x) = c * mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

private lemma walk_add (k : ℕ) (t : ℝ) (F G : ℝ → ℝ) :
    walk k t (fun x => F x + G x) = walk k t F + walk k t G := by
  simp only [walk, mean_add]

private lemma walk_scale (k : ℕ) (t c : ℝ) (F : ℝ → ℝ) :
    walk k t (fun x => c * F x) = c * walk k t F := by
  simp only [walk, mean_walk_scale]

private lemma walk_const (k : ℕ) (t c : ℝ) : walk k t (fun _ => c) = c := by
  simp only [walk, mean_const _ (bernoulliVectorWeight_sum t k)]

private lemma walk_zero (t : ℝ) (F : ℝ → ℝ) : walk 0 t F = F 0 := by
  simp [walk, bitCount, mean_const _ (bernoulliVectorWeight_sum t 0)]

private lemma walk_succ (k : ℕ) (t : ℝ) (F : ℝ → ℝ) :
    walk (k+1) t F = walk k t (fun z =>
      (1-t)*((1-t)*F z + t*F (z-1)) + t*((1-t)*F (z+1) + t*F z)) := by
  let w := bernoulliVectorWeight t k
  let H (a b : ℕ) := F ((a:ℝ)-b)
  have split (a : ℕ) := bernoulli_count_succ_mean t k (H a)
  change mean (bernoulliVectorWeight t (k+1)) (fun x =>
    mean (bernoulliVectorWeight t (k+1)) (fun y => H (bitCount x) (bitCount y))) = _
  simp_rw [split]
  rw [bernoulli_count_succ_mean t k (fun a =>
    (1-t)*mean w (fun y => H a (bitCount y)) + t*mean w (fun y => H a (bitCount y+1)))]
  simp only [walk, mean_add, mean_walk_scale, H, w, Nat.cast_add, Nat.cast_one]
  simp only [sub_add_eq_sub_sub, add_sub_right_comm, sub_add_cancel]

private lemma walk_mono (k : ℕ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    {F G : ℝ → ℝ} (h : ∀ z, F z ≤ G z) : walk k t F ≤ walk k t G := by
  let hw := bernoulliVectorWeight_nonneg t ht k
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h _) (hw y)) (hw x)

/-- Exact second moment and fourth-moment upper bound before truncation. -/
private theorem walk_moments (k : ℕ) (t : ℝ) :
    walk k t (fun z => z^2) = 2*k*(t*(1-t)) ∧
    walk k t (fun z => z^4) ≤ 2*k*(t*(1-t))+12*((k:ℝ)*(t*(1-t)))^2 := by
  induction k with
  | zero => simp [walk_zero]
  | succ k ih =>
    obtain ⟨two,four⟩ := ih
    let u := t*(1-t)
    have two' (z : ℝ) : (1-t)*((1-t)*z^2+t*(z-1)^2)+t*((1-t)*(z+1)^2+t*z^2) =
        z^2 + 2*u := by dsimp [u]; ring
    have four' (z : ℝ) : (1-t)*((1-t)*z^4+t*(z-1)^4)+t*((1-t)*(z+1)^4+t*z^4) =
        (z^4+(12*u)*z^2)+2*u := by dsimp [u]; ring
    constructor
    · rw [walk_succ]
      simp only [two', walk_add, walk_const, two, Nat.cast_succ, u]
      ring
    · rw [walk_succ]
      simp only [four', walk_add, walk_const, walk_scale, two, Nat.cast_succ, u]
      nlinarith [sq_nonneg (t*(1-t))]

private theorem walk_abs_central (k : ℕ) (t : ℝ) (hk : 0 < k)
    (htl : 1/4 ≤ t) (htu : t ≤ 3/4) :
    Real.sqrt k / 4 ≤ walk k t abs := by
  have ht : 0 ≤ t ∧ t ≤ 1 := ⟨by linarith,by linarith⟩
  let v := (k:ℝ)*(t*(1-t))
  have kv : 3/16*(k:ℝ) ≤ v := by
    rw [mul_comm (3/16)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    nlinarith [mul_nonneg (sub_nonneg.mpr htl) (sub_nonneg.mpr htu)]
  have k1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hv : 0 < v := by linarith
  let q := Real.sqrt (1+6*v)
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have qsq : q^2 = 1+6*v := Real.sq_sqrt (by positivity)
  have point (z : ℝ) : 3*q^2*z^2 ≤ 2*q^3*|z|+z^4 := by
    have h := mul_nonneg (mul_nonneg (abs_nonneg z) (show 0 ≤ |z|+2*q by positivity))
      (sq_nonneg (|z|-q))
    have h2 := sq_abs z
    nlinarith only [h, congrArg (fun x : ℝ => x^2) h2,
      congrArg (fun x : ℝ => q^2*x) h2]
  have pol := walk_mono k t ht point
  obtain ⟨m2,m4⟩ := walk_moments k t
  have h2 : walk k t (fun z => z^2) = 2*v := by dsimp [v]; linarith
  have h4 : walk k t (fun z => z^4) ≤ 2*v+12*v^2 := by dsimp [v]; linarith
  simp only [walk_add, walk_scale, h2] at pol
  have absbound : 2*v ≤ q*walk k t abs := by
    apply le_of_mul_le_mul_left (a := 2*q^2) _ (by positivity)
    nlinarith only [pol,h4,congrArg (fun w : ℝ => 2*v*w) qsq]
  have nq : (k:ℝ)*(1+6*v) ≤ (8*v)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 16*v-3*k by linarith) (show 0 ≤ 1+6*v by positivity),
      mul_nonneg hv.le (show 0 ≤ 6*v-1 by linarith)]
  have sq : Real.sqrt k * q ≤ 8*v := by
    apply le_of_sq_le_sq _ (by positivity)
    rwa [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), qsq]
  apply le_of_mul_le_mul_left (a := q) _ hq
  linarith

private def clipped (r : ℕ) (z : ℝ) : ℝ := if |z| ≤ (r:ℝ) then |z| else 0

private lemma clipped_large (k r : ℕ) (t : ℝ) (hk : 0 < k) (hr : 0 < r)
    (hsize : 4 * Real.sqrt k ≤ (r:ℝ)) (htl : 1/4 ≤ t) (htu : t ≤ 3/4) :
    Real.sqrt k / 8 ≤ walk k t (clipped r) := by
  have ht : 0 ≤ t ∧ t ≤ 1 := ⟨by linarith,by linarith⟩
  have rr : 0 < (r:ℝ) := by exact_mod_cast hr
  have point (z : ℝ) : (r:ℝ)*|z| ≤ r*clipped r z+z^2 := by
    unfold clipped
    split_ifs with hz
    · nlinarith [sq_nonneg z]
    · nlinarith [mul_nonneg (abs_nonneg z) (sub_nonneg.mpr (le_of_not_ge hz)), sq_abs z]
  have h := walk_mono k t ht point
  simp only [walk_add,walk_scale,(walk_moments k t).1] at h
  have hab := mul_le_mul_of_nonneg_left (walk_abs_central k t hk htl htu) rr.le
  have hu := mul_le_mul_of_nonneg_left (show t*(1-t) ≤ 1/4 by nlinarith [sq_nonneg (t-1/2)])
    (show 0 ≤ 2*(k:ℝ) by positivity)
  have hk2 := Real.sq_sqrt (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  apply le_of_mul_le_mul_left (a := (r:ℝ)) _ rr
  nlinarith [mul_le_mul_of_nonneg_right hsize (Real.sqrt_nonneg (k:ℝ))]

private theorem real_count_dist (a b : ℕ) : |(a:ℝ)-b| = (Nat.dist a b : ℕ) := by
  rcases le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h, abs_of_nonpos (by exact_mod_cast sub_nonpos.mpr (show (a:ℝ) ≤ b by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h,Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

/-- A bounded initial segment of independent Bernoulli trials retains a
definite contribution even after differences larger than r are discarded. -/
theorem truncated_binomial_window_lower (m r : ℕ) (t : ℝ) (hm : 0 < m) (hr : 0 < r)
    (htl : 1/4 ≤ t) (htu : t ≤ 3/4) : ∃ k ≤ m,
    min (r:ℝ) (Real.sqrt m)/48 ≤
      mean (bernoulliVectorWeight t k) (fun x => mean (bernoulliVectorWeight t k)
        (fun y => if Nat.dist (bitCount x) (bitCount y) ≤ r then
          (Nat.dist (bitCount x) (bitCount y) : ℝ) else 0)) := by
  suffices H : ∃ k ≤ m, min (r:ℝ) (Real.sqrt m)/48 ≤ walk k t (clipped r) by
    simpa only [walk,clipped,real_count_dist,Nat.cast_le] using H
  by_cases small : r < 4
  · refine ⟨1,hm,?_⟩
    have rr : (1:ℝ) ≤ r := by exact_mod_cast hr
    have rr' : (r:ℝ) ≤ 3 := by exact_mod_cast (by omega : r ≤ 3)
    rw [show 1 = 0+1 by rfl,walk_succ,walk_zero]
    have htwo : 3/8 ≤ 2*t*(1-t) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr htl) (sub_nonneg.mpr htu)]
    norm_num [clipped,rr, Nat.cast_nonneg]
    nlinarith [min_le_left (r:ℝ) (Real.sqrt m)]
  · let k := min m (r^2/16)
    have rd : 16 ≤ r^2 := by nlinarith [show 4 ≤ r by omega, sq_nonneg (r:ℤ)]
    have kp : 0 < k := lt_min hm ((Nat.le_div_iff_mul_le (by decide)).mpr (by simpa using rd))
    have ks : k * 16 ≤ r^2 :=
      (Nat.mul_le_mul_right 16 (min_le_right m (r^2/16))).trans (Nat.div_mul_le_self _ _)
    have rsq : 4*Real.sqrt k ≤ (r:ℝ) := by
      apply le_of_sq_le_sq _ (Nat.cast_nonneg _)
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      have h := (show (k:ℝ)*16 ≤ (r:ℝ)^2 by exact_mod_cast ks)
      linarith
    refine ⟨k,min_le_left _ _,le_trans ?_ (clipped_large k r t kp hr rsq htl htu)⟩
    rcases le_total m (r^2/16) with h | h
    · have heq : k=m := min_eq_left h
      rw [heq]
      linarith [min_le_right (r:ℝ) (Real.sqrt m), Real.sqrt_nonneg (m:ℝ)]
    · have heq : k=r^2/16 := min_eq_right h
      have trunc : r^2 < (k+1)*16 := by
        rw [heq]; omega
      have coarse : r^2 ≤ 36*k := by omega
      have rs : (r:ℝ) ≤ 6*Real.sqrt k := by
        apply le_of_sq_le_sq _ (by positivity)
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        have v : (r:ℝ)^2 ≤ 36*k := by exact_mod_cast coarse
        linarith
      linarith [min_le_left (r:ℝ) (Real.sqrt m)]

end Shellsort
end
