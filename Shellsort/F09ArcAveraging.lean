import Shellsort.F09CertificateFourier
import Mathlib.Algebra.BigOperators.Intervals

/-! Quantitative inputs to the fixed-divisor critical-window estimate. -/
noncomputable section
namespace Shellsort.F09.ArcAveraging
open Real Finset

def width (G j : ℕ) : ℝ := min ((j:ℝ)/G) (1 - (j:ℝ)/G)

private theorem reciprocal_roots (k : ℕ) :
    ∑ i ∈ range k, 1 / Real.sqrt ((i+1:ℕ):ℝ) ≤ 2 * Real.sqrt k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have pos : 0 < Real.sqrt ((k+1:ℕ):ℝ) := by positivity
    have diff : 1 / Real.sqrt ((k+1:ℕ):ℝ) ≤
        2 * (Real.sqrt ((k+1:ℕ):ℝ) - Real.sqrt k) := by
      apply (div_le_iff₀ pos).2
      have sq₁ := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (k+1))
      have sq₀ := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)
      push_cast at sq₁ ⊢
      nlinarith only [sq₁, sq₀, sq_nonneg (Real.sqrt ((k:ℝ)+1) - Real.sqrt k)]
    rw [sum_range_succ]
    linarith only [ih, diff]

/-- All positive class arc widths j/G, j=1,...,G-1, with the normalization
1/G used in the last-pass pivot average. G=1 gives the empty sum. -/
theorem average_width_inv_sqrt (G : ℕ) (hG : 0 < G) :
    (∑ i ∈ range (G-1), 1 / Real.sqrt (width G (i+1))) / G ≤ 4 := by
  let u (i : ℕ) := 1 / Real.sqrt ((i+1:ℕ):ℝ)
  have gp : 0 < (G:ℝ) := by exact_mod_cast hG
  have each (i : ℕ) (hi : i ∈ range (G-1)) :
      1 / Real.sqrt (width G (i+1)) ≤ Real.sqrt G * (u i + u (G-1-1-i)) := by
    have cut := mem_range.mp hi
    let j := i+1
    let k := G-j
    have jp : 0 < j := by dsimp [j]; omega
    have kp : 0 < k := by dsimp [k,j]; omega
    have parts : j + k = G := by dsimp [j,k]; omega
    have reflect : G-1-1-i+1 = k := by dsimp [k,j]; omega
    have partsR : (j:ℝ) + (k:ℝ) = G := by exact_mod_cast parts
    have comp : 1 - (j:ℝ)/G = (k:ℝ)/G := by field_simp; linarith
    change 1 / Real.sqrt (min ((j:ℝ)/G) (1-(j:ℝ)/G)) ≤ _
    dsimp only [u]
    rw [reflect, comp]
    change _ ≤ Real.sqrt G * (1 / Real.sqrt (j:ℝ) + 1 / Real.sqrt (k:ℝ))
    rcases le_total ((j:ℝ)/G) ((k:ℝ)/G) with small | small
    · rw [min_eq_left small, Real.sqrt_div (by positivity), one_div_div, mul_add]
      simp only [mul_one_div]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right small, Real.sqrt_div (by positivity), one_div_div, mul_add]
      simp only [mul_one_div]
      exact le_add_of_nonneg_left (by positivity)
  have sums := sum_le_sum each
  rw [← mul_sum, sum_add_distrib, sum_range_reflect] at sums
  have upper : ∑ i ∈ range (G-1), u i ≤ 2 * Real.sqrt G := by
    apply (reciprocal_roots (G-1)).trans
    gcongr
    exact_mod_cast Nat.sub_le G 1
  apply (div_le_iff₀ gp).2
  exact sums.trans (by
    have mult := mul_le_mul_of_nonneg_left (add_le_add upper upper) (Real.sqrt_nonneg G)
    nlinarith only [mult, Real.sq_sqrt gp.le])

/-- A reference variance bounded away from zero trades the square-root
modulus of continuity for a first-order perturbation in the variance. -/
theorem sqrt_variance_error {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a-b| / Real.sqrt b := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hb)).2
  calc
    _ ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg a)) (abs_nonneg _)
    _ = |a-b| := by
      rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), ← abs_mul]
      congr 1
      nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb.le]

/-- Every nonzero Fourier mode decays at least as fast as the first one.
This is a lower bound for the literal F09 heat variance used in J. -/
theorem heat_variance_floor {δ x : ℝ} (hd : 0 ≤ δ) (hx : x ∈ Set.Icc 0 1) :
    (1 - Real.exp (-4*Real.pi^2*δ)) * (x*(1-x)) ≤ V δ x := by
  let decay := Real.exp (-4*Real.pi^2*δ)
  have each (k : ℕ) : mode k δ x ≤ decay * mode k 0 x := by
    have growth : 1 ≤ ((k:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k, sq_nonneg (k:ℝ)]
    have expo : Real.exp (-4*Real.pi^2*((k:ℝ)+1)^2*δ) ≤ decay := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg (sub_nonneg.mpr growth) (mul_nonneg (sq_nonneg Real.pi) hd)]
    unfold mode
    simp only [mul_zero, Real.exp_zero, one_mul]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right expo (by positivity)
  have total := (mode_sum hd x).tsum_le_tsum each ((mode_sum le_rfl x).mul_left decay)
  rw [tsum_mul_left] at total
  have zero := V_zero hx
  change x*(1-x) - 2/Real.pi^2*(∑' k, mode k 0 x) = 0 at zero
  change (1-decay)*(x*(1-x)) ≤ x*(1-x) - 2/Real.pi^2*(∑' k, mode k δ x)
  nlinarith only [mul_le_mul_of_nonneg_left total (by positivity : 0 ≤ 2/Real.pi^2),
    congrArg (fun y : ℝ => decay*y) zero]

/-- The time can approach zero. On a window λ ≥ lam0 > 0 only the factor s
is lost. In the paper s = v(t) = t(1-t). -/
theorem window_width_floor {lam0 lam s x : ℝ} (lp : 0 < lam0) (window : lam0 ≤ lam)
    (hs : s ∈ Set.Icc (0:ℝ) 1) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    ((1 - Real.exp (-4*Real.pi^2*lam0))*s/2) * min x (1-x) ≤ V (lam*s) x := by
  have decay : 0 ≤ 1 - Real.exp (-4*Real.pi^2*lam0) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    nlinarith only [mul_nonneg (sq_nonneg Real.pi) lp.le]
  have spatial : min x (1-x) ≤ 2*(x*(1-x)) := by
    rcases le_total x (1-x) with small | small
    · rw [min_eq_left small]
      nlinarith only [mul_nonneg hx.1 (sub_nonneg.mpr small)]
    · rw [min_eq_right small]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr small)]
  have heat := (V_concave x).2 (show lam0 ∈ Set.Ici 0 from lp.le)
    (show (0:ℝ) ∈ Set.Ici 0 by simp) hs.1 (sub_nonneg.mpr hs.2)
    (show s+(1-s)=1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, V_zero hx] at heat
  have rising := V_heat_monotone x (show lam0*s ∈ Set.Ici 0 from mul_nonneg lp.le hs.1)
    (show lam*s ∈ Set.Ici 0 from mul_nonneg (lp.le.trans window) hs.1)
    (mul_le_mul_of_nonneg_right window hs.1)
  rw [mul_comm s lam0] at heat
  apply le_trans _ (heat.trans rising)
  have base := heat_variance_floor lp.le hx
  nlinarith only [mul_le_mul_of_nonneg_left spatial (mul_nonneg decay hs.1),
    mul_le_mul_of_nonneg_left base hs.1]

/-- Uniform in the period and in λ ≥ lam0: an additive variance error e
costs at most a constant times e / sqrt(s) averaged over nonzero widths.
Here the reference variances are exactly those in the critical law. -/
theorem averaged_heat_error (G : ℕ) (hG : 0 < G) (A : ℕ → ℝ)
    {lam0 lam s e : ℝ} (lp : 0 < lam0) (window : lam0 ≤ lam) (sp : 0 < s) (sh : s ≤ 1)
    (ep : 0 ≤ e) (apos : ∀ j, 0 < j → j < G → 0 ≤ A j)
    (error : ∀ j, 0 < j → j < G → |A j - V (lam*s) ((j:ℝ)/G)| ≤ e) :
    (∑ i ∈ range (G-1), |Real.sqrt (A (i+1)) -
      Real.sqrt (V (lam*s) (((i+1:ℕ):ℝ)/G))|) / G ≤
        4 * (e / Real.sqrt ((1 - Real.exp (-4*Real.pi^2*lam0))*s/2)) := by
  let C := (1 - Real.exp (-4*Real.pi^2*lam0))*s/2
  have decay : 0 < 1 - Real.exp (-4*Real.pi^2*lam0) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    nlinarith only [mul_pos (sq_pos_of_pos Real.pi_pos) lp]
  have cp : 0 < C := by dsimp [C]; positivity
  have each (i : ℕ) (hi : i ∈ range (G-1)) :
      |Real.sqrt (A (i+1)) - Real.sqrt (V (lam*s) (((i+1:ℕ):ℝ)/G))| ≤
        (e / Real.sqrt C) * (1 / Real.sqrt (width G (i+1))) := by
    have ltG : i+1 < G := by have := mem_range.mp hi; omega
    have xleft : 0 < ((i+1:ℕ):ℝ)/G := by positivity
    have xright : ((i+1:ℕ):ℝ)/G < 1 := by
      apply (div_lt_iff₀ (by exact_mod_cast hG : (0:ℝ)<G)).2
      simpa using (Nat.cast_lt.mpr ltG : ((i+1:ℕ):ℝ) < G)
    have wp : 0 < width G (i+1) := lt_min xleft (sub_pos.mpr xright)
    have floor := window_width_floor lp window ⟨sp.le, sh⟩ ⟨xleft.le, xright.le⟩
    change C * width G (i+1) ≤ _ at floor
    have root := sqrt_variance_error (apos _ (Nat.succ_pos _) ltG) ((mul_pos cp wp).trans_le floor)
    apply root.trans
    calc
      _ ≤ e / Real.sqrt (C * width G (i+1)) := by
        apply div_le_div₀ (by exact ep) (error _ (Nat.succ_pos _) ltG)
          (Real.sqrt_pos.mpr (mul_pos cp wp)) (Real.sqrt_le_sqrt floor)
      _ = _ := by rw [Real.sqrt_mul cp.le]; ring
  have total := div_le_div_of_nonneg_right (sum_le_sum each) (Nat.cast_nonneg (α := ℝ) G)
  rw [← mul_sum, mul_div_assoc] at total
  apply total.trans
  rw [mul_comm 4]
  exact mul_le_mul_of_nonneg_left (average_width_inv_sqrt G hG) (div_nonneg ep (Real.sqrt_nonneg C))

#print axioms average_width_inv_sqrt
#print axioms sqrt_variance_error
#print axioms heat_variance_floor
#print axioms window_width_floor
#print axioms averaged_heat_error

end Shellsort.F09.ArcAveraging
