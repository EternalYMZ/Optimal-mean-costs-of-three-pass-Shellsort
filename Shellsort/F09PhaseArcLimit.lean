import Shellsort.F09PhaseVisitLimit
import Shellsort.F09PhaseArc

/-! The complete physical source block for a same-class arc, including
wrapping and moving arc widths and thresholds, converges to the kernel V. -/
noncomputable section
namespace Shellsort
open Real Set Filter
open scoped BigOperators Topology

private def phaseB2 (u : ℝ) := u^2-u+1/6
private def phaseB2ext (u : ℝ) :=
  if u < 0 then phaseB2 (u+1) else if 1 < u then phaseB2 (u-1) else phaseB2 u

private theorem phaseB2_series {u : ℝ} (hl : -1 ≤ u) (hr : u ≤ 2) :
    HasSum (fun k : ℕ => Real.cos (2*π*((k:ℝ)+1)*u)/((k:ℝ)+1)^2)
      (π^2*phaseB2ext u) := by
  have perPlus (k : ℕ) : cos (2*π*((k:ℝ)+1)*(u+1)) = cos (2*π*((k:ℝ)+1)*u) := by
    convert Real.cos_add_nat_mul_two_pi (2*π*((k:ℝ)+1)*u) (k+1) using 2; push_cast; ring
  have perMinus (k : ℕ) : cos (2*π*((k:ℝ)+1)*(u-1)) = cos (2*π*((k:ℝ)+1)*u) := by
    convert Real.cos_sub_nat_mul_two_pi (2*π*((k:ℝ)+1)*u) (k+1) using 2; push_cast; ring
  by_cases hn : u < 0
  · have H := phase_quadratic_cos_series (q := u+1) ⟨by linarith,by linarith⟩
    simpa only [phaseB2ext, hn, ite_true, phaseB2, perPlus] using H
  by_cases hp : 1 < u
  · have H := phase_quadratic_cos_series (q := u-1) ⟨by linarith,by linarith⟩
    simpa only [phaseB2ext, hn, hp, ite_false, ite_true, phaseB2, perMinus] using H
  simpa only [phaseB2ext, hn, hp, ite_false, phaseB2] using
    phase_quadratic_cos_series (q := u) ⟨le_of_not_gt hn, le_of_not_gt hp⟩

private theorem arc_quadratic_identity {q w : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) :
    w*(1-w) + (phaseB2ext (q+w) + phaseB2ext (q-w))/2 - phaseB2ext q =
      min (min w (1-w)) (min q (1-q)) := by
  rcases hq with ⟨hq0,hq1⟩
  rcases hw with ⟨hw0,hw1⟩
  simp only [phaseB2ext, not_lt_of_ge hq0, not_lt_of_ge hq1,
    not_lt_of_ge (add_nonneg hq0 hw0), show ¬1 < q-w by linarith, ite_false, phaseB2, min_def]
  split_ifs <;> ring_nf <;> linarith

theorem phase_tent_cos_series {q w : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) :
    HasSum (fun k : ℕ => cos (2*π*((k:ℝ)+1)*q) * sin (π*((k:ℝ)+1)*w)^2 / ((k:ℝ)+1)^2)
      (π^2/2*(w*(1-w)- min (min w (1-w)) (min q (1-q)))) := by
  have plus := phaseB2_series (u := q+w) (by linarith [hq.1,hw.1]) (by linarith [hq.2,hw.2])
  have minus := phaseB2_series (u := q-w) (by linarith [hq.1,hw.2]) (by linarith [hq.2,hw.1])
  have mid := phaseB2_series (u := q) (by linarith [hq.1]) (by linarith [hq.2])
  have H := (mid.sub ((plus.add minus).div_const 2)).div_const 2
  convert H using 1
  · funext k
    let A := 2*π*((k:ℝ)+1)
    change cos (A*q)*sin (π*((k:ℝ)+1)*w)^2 / _ = _
    have double : cos (A*w) = 1-2*sin (π*((k:ℝ)+1)*w)^2 := by
      let z := π*((k:ℝ)+1)*w
      change cos (A*w) = 1-2*sin z^2
      rw [show A*w = 2*z by dsimp [A,z]; ring, cos_two_mul]
      nlinarith [sin_sq_add_cos_sq z]
    change _ = (_- (cos (A*(q+w))/_ + cos (A*(q-w))/_)/2)/2
    rw [mul_add A q w, mul_sub A q w, cos_add, cos_sub, double]
    dsimp [A]; ring
  · rw [← arc_quadratic_identity hq hw]; ring

private theorem cyclicArcLoss_real (g ell x y : ℕ) (hg : 0 < g) (hl : ell ≤ g) :
    (cyclicArcLoss g ell x y:ℝ)/g =
      min (min ((ell:ℝ)/g) (1-(ell:ℝ)/g))
        (min (|((x%g:ℕ):ℝ)-(y%g:ℕ)|/g) (1-|((x%g:ℕ):ℝ)-(y%g:ℕ)|/g)) := by
  let a := x%g
  let b := y%g
  let d := (y+(g-a))%g
  have ha : a < g := Nat.mod_lt _ hg
  have hb : b < g := Nat.mod_lt _ hg
  have hd : d < g := Nat.mod_lt _ hg
  have dEq : d = (b+(g-a))%g := by simp [d,b,Nat.mod_add_mod]
  have gp : (0:ℝ) < g := by exact_mod_cast hg
  have sd : min d (g-d) = min (Nat.dist a b) (g-Nat.dist a b) := by
    rw [dEq]
    by_cases hab : a ≤ b
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show b+(g-a)-g < g by omega)]
      dsimp [Nat.dist]; omega
    · rw [Nat.mod_eq_of_lt (show b+(g-a) < g by omega)]
      dsimp [Nat.dist]; omega
  have dc : Nat.dist a b ≤ g := by dsimp [Nat.dist]; omega
  have cast_dist : ((Nat.dist a b:ℕ):ℝ) = |(a:ℝ)-b| := by
    rcases le_total a b with hab | hba
    · rw [Nat.dist, Nat.sub_eq_zero_of_le hab, Nat.zero_add, Nat.cast_sub hab,
        abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]; ring
    · rw [Nat.dist, Nat.sub_eq_zero_of_le hba, Nat.add_zero, Nat.cast_sub hba,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
  unfold cyclicArcLoss
  change ((min (min ell (g-ell)) (min d (g-d)):ℕ):ℝ)/g = _
  rw [sd]
  simp only [Nat.cast_min, Nat.cast_sub hl, Nat.cast_sub dc, cast_dist, ← min_div_div_right gp.le]
  simp only [sub_div, div_self gp.ne', a, b]

private theorem arc_series_at_counts (g ell x y : ℕ) (hg : 0 < g) (hl : ell ≤ g) :
    let w := (ell:ℝ)/g
    HasSum (fun k : ℕ => sin (π*((k:ℝ)+1)*w)^2 *
      cos ((2*π*((k:ℝ)+1)/g)*((x:ℝ)-y)) / ((k:ℝ)+1)^2)
      (π^2/2*(w*(1-w)-(cyclicArcLoss g ell x y:ℝ)/g)) := by
  let w := (ell:ℝ)/g
  let a := |((x%g:ℕ):ℝ)-(y%g:ℕ)|
  have gp : (0:ℝ) < g := by exact_mod_cast hg
  have ha : a ≤ g := by
    have hx : ((x%g:ℕ):ℝ) < g := by exact_mod_cast Nat.mod_lt x hg
    have hy : ((y%g:ℕ):ℝ) < g := by exact_mod_cast Nat.mod_lt y hg
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (x%g), Nat.cast_nonneg (α := ℝ) (y%g)]
  have hq : a/(g:ℝ) ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (abs_nonneg _) gp.le, (div_le_one gp).mpr ha⟩
  have hw : w ∈ Icc (0:ℝ) 1 := ⟨by dsimp [w]; positivity,
    (div_le_one gp).mpr (by exact_mod_cast hl)⟩
  have H := phase_tent_cos_series hq hw
  have pt (k : ℕ) :
      cos (2*π*((k:ℝ)+1)*(a/g)) = cos ((2*π*((k:ℝ)+1)/g)*((x:ℝ)-y)) := by
    simpa only [Nat.cast_succ, a] using phase_cos_mod g x y (k+1) hg
  simp only [pt] at H
  rw [cyclicArcLoss_real g ell x y hg hl]
  convert H using 1
  funext k; dsimp only [w]; ring

/-- Exact finite multiplier sum for the physical same-class trace,
divided by the number of phases. -/
theorem physical_arc_variance_fourier (h g o ell y m : ℕ) (t : ℝ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hl : ell ≤ g) :
    let w := (ell:ℝ)/g
    fullArcTrace h g o ell y m t /g = w*(1-w) - 2/π^2 *
      (∑' k : ℕ, sin (π*((k:ℝ)+1)*w)^2 * phaseHeatCoeff g m t k / ((k:ℝ)+1)^2) := by
  let w := (ell:ℝ)/g
  let P := bernoulliVectorWeight t m
  let F := fun (k : ℕ) (x z : Fin m → Bool) => sin (π*((k:ℝ)+1)*w)^2 *
    cos ((2*π*((k:ℝ)+1)/g)*((bitCount x:ℝ)-bitCount z))/((k:ℝ)+1)^2
  let S := fun (x z : Fin m → Bool) =>
    π^2/2*(w*(1-w)-(cyclicArcLoss g ell (bitCount x) (bitCount z):ℝ)/g)
  have H := phase_mean_hasSum P (fun k x => mean P (F k x)) (fun x => mean P (S x))
      (fun x => phase_mean_hasSum P (fun k => F k x) (S x)
        (fun z => arc_series_at_counts g ell (bitCount x) (bitCount z) hg hl))
  have eq := H.tsum_eq
  dsimp only [F,S] at eq
  simp only [phaseMean_div, phaseMean_scale, mean_sub, mean_const P (bernoulliVectorWeight_sum t m)] at eq
  change (∑' k : ℕ, sin (π*((k:ℝ)+1)*w)^2 * phaseHeatCoeff g m t k / ((k:ℝ)+1)^2) =
    π^2/2*(w*(1-w) - (mean P fun x => mean P fun z => (cyclicArcLoss g ell (bitCount x) (bitCount z):ℝ))/g) at eq
  change _ = w*(1-w) - 2/π^2 * _
  rw [fullArcTrace_eq_phaseKernel h g o ell y m t hg hc hl, eq]
  field_simp [Real.pi_pos.ne']
  ring

/-- The block variance at a true choice of starting phase and pivot-owner
count converges to the manuscript's heat kernel V. Both the normalized arc
width and the threshold may approach either endpoint. -/
theorem physical_arc_critical_limit {G H o ell y m : ℕ → ℕ} {t : ℕ → ℝ} {lam T X : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop)
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (ht01 : ∀ n, t n ∈ Icc 0 1)
    (hx : Tendsto (fun n => (ell n:ℝ)/(G n:ℝ)) atTop (𝓝 X))
    (hc : ∀ n, Nat.Coprime (H n) (G n)) (hl : ∀ n, ell n ≤ G n) :
    Tendsto (fun n => fullArcTrace (H n) (G n) (o n) (ell n) (y n) (m n) (t n)/(G n:ℝ))
      atTop (𝓝 (F09.V (lam*F09.v T) X)) := by
  let w := fun n => (ell n:ℝ)/(G n:ℝ)
  let f := fun n (k : ℕ) => sin (π*((k:ℝ)+1)*w n)^2 * phaseHeatCoeff (G n) (m n) (t n) k/((k:ℝ)+1)^2
  let S := fun k : ℕ => exp (-4*π^2*((k:ℝ)+1)^2*(lam*F09.v T))*sin (π*((k:ℝ)+1)*X)^2/((k:ℝ)+1)^2
  have bounded (n k : ℕ) : ‖f n k‖ ≤ 1/((k:ℝ)+1)^2 := by
    have A := phaseHeatCoeff_unit (G n) (m n) (t n) (ht01 n) k
    dsimp [f]; rw [abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) A.1) (sq_nonneg _))]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    simpa using mul_le_mul (sin_sq_le_one _) A.2 A.1 zero_le_one
  have mode (k : ℕ) : Tendsto (fun n => f n k) atTop (𝓝 (S k)) := by
    have trig : Tendsto (fun n => sin (π*((k:ℝ)+1)*w n)) atTop (𝓝 (sin (π*((k:ℝ)+1)*X))) :=
      Real.continuous_sin.continuousAt.tendsto.comp (tendsto_const_nhds.mul hx)
    simpa only [f,S,mul_comm (exp _) _] using
      ((trig.pow 2).mul (phaseHeatCoeff_limit hG hm ht k)).div_const (((k:ℝ)+1)^2)
  have series : Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, S k)) :=
    tendsto_tsum_of_dominated_convergence phase_weight_summable mode (.of_forall bounded)
  have limit := (hx.mul ((tendsto_const_nhds (x:=1)).sub hx)).sub
    ((tendsto_const_nhds (x:=2/π^2)).mul series)
  apply limit.congr'
  filter_upwards [hG.eventually_gt_atTop 0] with n hn
  exact (physical_arc_variance_fourier (H n) (G n) (o n) (ell n) (y n) (m n) (t n)
    (by exact_mod_cast hn) (hc n) (hl n)).symm

end Shellsort
end
