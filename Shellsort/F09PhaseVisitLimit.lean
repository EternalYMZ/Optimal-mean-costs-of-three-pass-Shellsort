import Shellsort.F09PhaseVisits
import Shellsort.F09PhaseModes
import Shellsort.F09CertificateFunctions
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Normed.Group.Tannery

/-! The complete-block physical visit variance in the critical limit,
through the Bernoulli polynomial Fourier series and the true binomial modes. -/
noncomputable section
namespace Shellsort
open Real Set Filter
open scoped BigOperators Topology

theorem phase_quadratic_cos_series {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    HasSum (fun k : ℕ => Real.cos (2*π*((k:ℝ)+1)*q)/((k:ℝ)+1)^2)
      (π^2*(q^2-q+1/6)) := by
  have H := hasSum_one_div_nat_pow_mul_cos (k := 1) (by decide) hq
  change HasSum _ (_ * bernoulliFun (2*1) q) at H
  simp only [Nat.mul_one, bernoulliFun_two] at H
  have A := (hasSum_nat_add_iff' 1).mpr H
  convert A using 1
  · funext k; push_cast; ring
  · norm_num [Nat.factorial]; ring_nf; tauto

theorem phase_cos_mod (g x y r : ℕ) (hg : 0 < g) :
    Real.cos (2*π*(r:ℝ)*(|((x%g:ℕ):ℝ)-(y%g:ℕ)| /g)) =
    Real.cos ((2*π*(r:ℝ)/g)*((x:ℝ)-y)) := by
  have gp : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  let z : ℝ := 2*π*(r:ℝ)/g
  have eqx : ((x%g:ℕ):ℝ) + (g:ℝ)*((x/g:ℕ):ℝ) = x := by exact_mod_cast Nat.mod_add_div x g
  have eqy : ((y%g:ℕ):ℝ) + (g:ℝ)*((y/g:ℕ):ℝ) = y := by exact_mod_cast Nat.mod_add_div y g
  let shifts : ℤ := (r:ℤ) * (((x/g:ℕ):ℤ) - ((y/g:ℕ):ℤ))
  have decomp : z*((x:ℝ)-y) = z*(((x%g:ℕ):ℝ)-(y%g:ℕ)) + (shifts:ℝ)*(2*π) := by
    dsimp only [z, shifts]; simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast]
    field_simp [gp]
    linear_combination r*eqy - r*eqx
  change _ = Real.cos (z*((x:ℝ)-y))
  rw [decomp, Real.cos_add_int_mul_two_pi]
  rcases le_total (((y%g:ℕ):ℝ)) (((x%g:ℕ):ℝ)) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]; congr 1; dsimp [z]; ring
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]; rw [← Real.cos_neg (z*_)]
    congr 1; dsimp [z]; ring

private theorem visit_series_at_counts (g x y : ℕ) (hg : 0 < g) :
    HasSum (fun k : ℕ => Real.cos ((2*π*((k:ℝ)+1)/g)*((x:ℝ)-y)) / ((k:ℝ)+1)^2)
      (π^2*(1/6 - visitRoundingNumerator g x y/(g:ℝ)^2)) := by
  let a := |((x%g:ℕ):ℝ)-(y%g:ℕ)|
  have gp : (0:ℝ) < g := by exact_mod_cast hg
  have ax := Nat.mod_lt x hg
  have ay := Nat.mod_lt y hg
  have ha : a ≤ g := by
    apply abs_le.mpr
    have hx : ((x%g:ℕ):ℝ) < g := by exact_mod_cast ax
    have hy : ((y%g:ℕ):ℝ) < g := by exact_mod_cast ay
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (x%g), Nat.cast_nonneg (α := ℝ) (y%g)]
  have hq : a/(g:ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (abs_nonneg _) gp.le, (div_le_one gp).mpr ha⟩
  have H := phase_quadratic_cos_series hq
  have pt (k : ℕ) :
      Real.cos (2*π*((k:ℝ)+1)*(a/g)) = Real.cos ((2*π*((k:ℝ)+1)/g)*((x:ℝ)-y)) := by
    simpa only [Nat.cast_succ, a] using phase_cos_mod g x y (k+1) hg
  simp only [pt] at H
  convert H using 2
  unfold visitRoundingNumerator
  change 1/6 - a*(g-a)/(g:ℝ)^2 = _
  field_simp
  ring

theorem phase_mean_hasSum {α : Type*} [Fintype α] (w : α → ℝ)
    (f : ℕ → α → ℝ) (S : α → ℝ) (hf : ∀ x, HasSum (fun k => f k x) (S x)) :
    HasSum (fun k => mean w (f k)) (mean w S) := by
  exact hasSum_sum fun x _ => (hf x).mul_left (w x)

theorem phaseMean_scale {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => a*f x) = a*mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

theorem phaseMean_div {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => f x/a) = mean w f/a := by simp only [mean, Finset.sum_div, mul_div_assoc]

/-- The finite binomial multiplier in the positive integer mode k+1. -/
def phaseHeatCoeff (g m : ℕ) (t : ℝ) (k : ℕ) :=
  binomialDifferenceMean m t (fun z => cos ((2*π*((k:ℝ)+1)/g)*z))

theorem phaseHeatCoeff_unit (g m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) (k : ℕ) :
    0 ≤ phaseHeatCoeff g m t k ∧ phaseHeatCoeff g m t k ≤ 1 := by
  unfold phaseHeatCoeff
  rw [binomialDifference_cos_mode]
  have hv : 0 ≤ 4*t*(1-t) := by have := ht.1; have := ht.2; positivity
  have hu : 4*t*(1-t) ≤ 1 := by nlinarith [sq_nonneg (2*t-1)]
  have scale (z : ℝ) : 0 ≤ 1-4*t*(1-t)*sin z^2 ∧ 1-4*t*(1-t)*sin z^2 ≤ 1 :=
    ⟨sub_nonneg.mpr (by simpa using mul_le_mul hu (sin_sq_le_one z) (sq_nonneg _) zero_le_one),
      sub_le_self _ (mul_nonneg hv (sq_nonneg _))⟩
  exact ⟨pow_nonneg (scale _).1 _, pow_le_one₀ (scale _).1 (scale _).2⟩

theorem phaseHeatCoeff_limit {G m : ℕ → ℕ} {t : ℕ → ℝ} {lam T : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop)
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (k : ℕ) :
    Tendsto (fun n => phaseHeatCoeff (G n) (m n) (t n) k) atTop
      (𝓝 (exp (-4*π^2*((k:ℝ)+1)^2*(lam*F09.v T)))) := by
  simpa only [phaseHeatCoeff, F09.v, Nat.cast_succ] using
    binomialDifference_critical_mode_limit hG hm ht (k+1)

private theorem visitModeSeries (g m : ℕ) (t : ℝ) (hg : 0 < g) :
    let w := bernoulliVectorWeight t m
    (∑' k, phaseHeatCoeff g m t k/((k:ℝ)+1)^2) =
      π^2*(1/6 - (mean w (fun x => mean w (fun y =>
        visitRoundingNumerator g (bitCount x) (bitCount y))))/(g:ℝ)^2) := by
  let w := bernoulliVectorWeight t m
  let F := fun (k : ℕ) (x y : Fin m → Bool) =>
    cos ((2*π*((k:ℝ)+1)/g)*((bitCount x:ℝ)-bitCount y))/((k:ℝ)+1)^2
  let S := fun (x y : Fin m → Bool) =>
    π^2 * (1/6-visitRoundingNumerator g (bitCount x) (bitCount y)/(g:ℝ)^2)
  have H := phase_mean_hasSum w (fun k x => mean w (F k x)) (fun x => mean w (S x))
      (fun x => phase_mean_hasSum w (fun k => F k x) (S x)
        (fun y => visit_series_at_counts g (bitCount x) (bitCount y) hg))
  have eq := H.tsum_eq
  dsimp only [F, S] at eq
  simp only [phaseMean_scale, mean_sub, mean_const w (bernoulliVectorWeight_sum t m), phaseMean_div] at eq
  exact eq

/-- The phase-averaged visit variance of one physical source block has an
exact finite-frequency representation for arbitrary binomial source length. -/
theorem source_block_visit_variance_fourier (h g j start m : ℕ) (t : ℝ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hj : j < g) :
    (∑ s : Fin g, centeredSecond (bernoulliVectorWeight t m)
      (fun x => (sourcePrefixCount h g j (start+s.val) (bitCount x) : ℝ)))/(g:ℝ) =
      (m:ℝ)/(g:ℝ)^2 * F09.v t + 1/12 -
      1/(2*π^2)*(∑' k, phaseHeatCoeff g m t k/((k:ℝ)+1)^2) := by
  have eq := source_block_visit_variance h g j start m t hg hc hj
  rw [visitModeSeries g m t hg]
  dsimp only [F09.v]
  have gp : (g:ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  field_simp [gp, Real.pi_pos.ne']
  linear_combination 72*eq

theorem phase_weight_summable : Summable (fun k : ℕ => 1/((k:ℝ)+1)^2) := by
  have h : HasSum (fun k : ℕ => 1/((k:ℝ)+1)^2) (π^2/6) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  exact h.summable

/-- The normalized variance of an actual physical block converges to
λv+W(λv), including thresholds 0 and 1. The target and initial source
label may change arbitrarily with n. -/
theorem source_block_visit_critical_limit {G H m j start : ℕ → ℕ} {t : ℕ → ℝ} {lam T : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop)
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (ht01 : ∀ n, t n ∈ Icc 0 1)
    (hc : ∀ n, Nat.Coprime (H n) (G n)) (hj : ∀ n, j n < G n) :
    Tendsto (fun n =>
      (∑ s : Fin (G n), centeredSecond (bernoulliVectorWeight (t n) (m n))
        (fun x => (sourcePrefixCount (H n) (G n) (j n) (start n+s.val) (bitCount x) : ℝ))) / (G n:ℝ))
      atTop (𝓝 (lam*F09.v T+F09.W (lam*F09.v T))) := by
  let f := fun n k => phaseHeatCoeff (G n) (m n) (t n) k/((k:ℝ)+1)^2
  let S := fun k : ℕ => exp (-4*π^2*((k:ℝ)+1)^2*(lam*F09.v T))/((k:ℝ)+1)^2
  have bounded (n k : ℕ) : ‖f n k‖ ≤ 1/((k:ℝ)+1)^2 := by
    have H := phaseHeatCoeff_unit (G n) (m n) (t n) (ht01 n) k
    dsimp [f]; rw [abs_of_nonneg (div_nonneg H.1 (sq_nonneg _))]
    exact div_le_div_of_nonneg_right H.2 (sq_nonneg _)
  have series : Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, S k)) :=
    tendsto_tsum_of_dominated_convergence phase_weight_summable
      (fun k => (phaseHeatCoeff_limit hG hm ht k).div_const _) (.of_forall bounded)
  have hv : Tendsto (fun n => F09.v (t n)) atTop (𝓝 (F09.v T)) := ht.mul (tendsto_const_nhds.sub ht)
  have bound := ((hm.mul hv).add (tendsto_const_nhds (x:=1/12))).sub
    ((tendsto_const_nhds (x:=1/(2*π^2))).mul series)
  have limit : lam*F09.v T+F09.W (lam*F09.v T) =
      lam*F09.v T+1/12-1/(2*π^2)*(∑' k, S k) := by dsimp [F09.W,S]; ring
  rw [limit]
  exact bound.congr fun n => (source_block_visit_variance_fourier
    (H n) (G n) (j n) (start n) (m n) (t n) (by have := hj n; omega) (hc n) (hj n)).symm

end Shellsort
end
