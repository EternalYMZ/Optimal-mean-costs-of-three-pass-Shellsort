import Shellsort.F09CertificateFunctions
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Unconditional estimates for the actual Fourier integral functions of F09. -/
noncomputable section
namespace Shellsort.F09
open Real Set MeasureTheory

def weight (k : ℕ) : ℝ := 1/((k:ℝ)+1)^2
private def term (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-4*Real.pi^2*((k:ℝ)+1)^2*x)/((k:ℝ)+1)^2

theorem weight_sum : HasSum weight (Real.pi^2/6) := by
  change HasSum (fun k : ℕ => 1/((k:ℝ)+1)^2) _
  simpa using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two

private theorem term_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : term k x ≤ weight k := by
  unfold term weight
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ 4*Real.pi^2*((k:ℝ)+1)^2*x := by positivity
  linarith

private theorem term_norm (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : ‖term k x‖ ≤ weight k := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold term; positivity)]
  exact term_le k hx

theorem W_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ W x := by
  have hs := Summable.of_norm_bounded weight_sum.summable (fun i => term_norm i hx)
  have hs' := hs.tsum_le_tsum (fun i => term_le i hx) weight_sum.summable
  rw [weight_sum.tsum_eq] at hs'
  change 0 ≤ 1/12-1/(2*Real.pi^2)*(∑' i, term i x)
  have hp : 0 < Real.pi^2 := by positivity
  rw [sub_nonneg]
  calc
    _ ≤ 1/(2*Real.pi^2)*(Real.pi^2/6) := mul_le_mul_of_nonneg_left hs' (by positivity)
    _ = _ := by field_simp; ring

theorem W_continuousOn : ContinuousOn W (Ici 0) := by
  have hs : ContinuousOn (fun x => ∑' i, term i x) (Ici 0) := by
    refine continuousOn_tsum (fun _ => ?_) weight_sum.summable (fun i _ hx => term_norm i hx)
    unfold term
    fun_prop
  exact continuousOn_const.sub (continuousOn_const.mul hs)

theorem J_nonneg (lam : ℝ) : 0 ≤ J lam := by
  unfold J
  apply div_nonneg _ (Real.sqrt_nonneg _)
  exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ =>
    intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => Real.sqrt_nonneg _))

theorem integral_sqrt_v : (∫ t in (0:ℝ)..1, Real.sqrt (v t)) = Real.pi/8 := by
  have h (t : ℝ) : Real.sqrt (v t) = Real.sqrt (1-(2*t+(-1))^2)/2 := by
    have eq : 1-(2*t+(-1))^2 = 4*v t := by unfold v; ring
    rw [eq, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    norm_num
  simp_rw [h]
  rw [intervalIntegral.integral_div]
  have he := intervalIntegral.integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    (fun x : ℝ => Real.sqrt (1-x^2)) (by norm_num : (2:ℝ) ≠ 0) (-1:ℝ)
  norm_num at he
  rw [he, integral_sqrt_one_sub_sq]
  ring

/-- The semicircle lower bound for the actual Gaussian cross term. -/
theorem c_le_B {z : ℝ} (hz : 0 < z) : c ≤ B z := by
  let lam : ℝ := 1/z^2
  have hl : 0 ≤ lam := by dsimp [lam]; positivity
  have hv : Continuous v := by unfold v; fun_prop
  have hcont := (continuous_const.mul hv : Continuous (fun t => lam*v t))
  have hmap : MapsTo (fun t => lam*v t) (Icc 0 1) (Ici 0) :=
    fun t ht => mul_nonneg hl (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
  have hgi : IntervalIntegrable (fun t => z*Real.sqrt (lam*v t+W (lam*v t))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact continuousOn_const.mul (Real.continuous_sqrt.continuousOn.comp
      (hcont.continuousOn.add (W_continuousOn.comp hcont.continuousOn hmap)) (mapsTo_univ _ _))
  have hfi : IntervalIntegrable (fun t => Real.sqrt (v t)) volume 0 1 :=
    (Real.continuous_sqrt.comp hv).intervalIntegrable _ _
  have hin := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hfi hgi
    (fun t ht => show Real.sqrt (v t) ≤ z*Real.sqrt (lam*v t+W (lam*v t)) from by
      rw [← Real.sqrt_sq hz.le, ← Real.sqrt_mul (sq_nonneg _)]
      apply Real.sqrt_le_sqrt
      have hn := W_nonneg (hmap ht)
      have hcancel : z^2*(lam*v t) = v t := by dsimp [lam]; field_simp
      rw [mul_add, hcancel]
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg z) hn))
  rw [integral_sqrt_v, intervalIntegral.integral_const_mul] at hin
  unfold c B L
  rw [← mul_div_assoc, le_div_iff₀ (Real.sqrt_pos.2 Real.pi_pos)]
  have hs := Real.sq_sqrt Real.pi_pos.le
  change Real.sqrt Real.pi/8 * Real.sqrt Real.pi ≤ z * _
  nlinarith

/-- A positive shape always has a nonnegative reduced one-residue cost. -/
theorem H_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ H z :=
  add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hz.le (J_nonneg _))

theorem c_lower : (22155672:ℝ)/100000000 < c := by
  unfold c
  have hs := Real.sq_sqrt Real.pi_pos.le
  have h : (17724538508:ℝ)/10000000000 < Real.sqrt Real.pi := by
    nlinarith [Real.pi_gt_d20, Real.sqrt_nonneg Real.pi]
  linarith

theorem sqrt_c_bounds : (47069813:ℝ)/100000000 < Real.sqrt c ∧
    Real.sqrt c < (47069814:ℝ)/100000000 := by
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hc := Real.sq_sqrt c_pos.le
  have h1 : (17724538508:ℝ)/10000000000 < Real.sqrt Real.pi := by
    nlinarith [Real.pi_gt_d20, Real.sqrt_nonneg Real.pi]
  have h2 : Real.sqrt Real.pi < (17724538510:ℝ)/10000000000 := by
    nlinarith [Real.pi_lt_d20, Real.sqrt_nonneg Real.pi]
  have cc : c = Real.sqrt Real.pi/8 := rfl
  constructor <;> nlinarith [Real.sqrt_nonneg c]

/-- A contraction of the variance argument scales the heat correction from below. -/
theorem W_scale {θ δ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hδ : 0 ≤ δ) :
    θ*W δ ≤ W (θ*δ) := by
  have hsum {x : ℝ} (hx : 0 ≤ x) : Summable (fun i => term i x) :=
    Summable.of_norm_bounded weight_sum.summable (fun i => term_norm i hx)
  have ht (i : ℕ) : term i (θ*δ) ≤ θ*term i δ+(1-θ)*weight i := by
    let e := -4*Real.pi^2*((i:ℝ)+1)^2*δ
    have he := convexOn_exp.2 (Set.mem_univ e) (Set.mem_univ 0) h0
      (show 0 ≤ 1-θ by linarith) (show θ+(1-θ)=1 by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at he
    have eq : -4*Real.pi^2*((i:ℝ)+1)^2*(θ*δ) = θ*e := by unfold e; ring
    unfold term weight
    rw [eq]
    calc
      _ ≤ (θ*Real.exp e+(1-θ))/((i:ℝ)+1)^2 :=
        div_le_div_of_nonneg_right he (sq_nonneg _)
      _ = _ := by unfold e; ring
  have t := (hsum (mul_nonneg h0 hδ)).tsum_le_tsum ht
    (((hsum hδ).mul_left θ).add (weight_sum.summable.mul_left (1-θ)))
  rw [Summable.tsum_add ((hsum hδ).mul_left θ) (weight_sum.summable.mul_left (1-θ)),
    tsum_mul_left,tsum_mul_left,weight_sum.tsum_eq] at t
  change θ*(1/12-1/(2*Real.pi^2)* (∑' i,term i δ)) ≤
    1/12-1/(2*Real.pi^2)*(∑' i,term i (θ*δ))
  have hp : 0 < Real.pi^2 := by positivity
  field_simp
  nlinarith

def scaled (z t : ℝ) := z*Real.sqrt (1/z^2*v t + W (1/z^2*v t))

theorem scaled_integrable {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (scaled z) volume 0 1 := by
  have hv : Continuous v := by unfold v; fun_prop
  have hc : Continuous (fun t : ℝ => 1/z^2*v t) := continuous_const.mul hv
  have hm : MapsTo (fun t : ℝ => 1/z^2*v t) (Icc 0 1) (Ici 0) :=
    fun t ht => mul_nonneg (by positivity) (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact continuousOn_const.mul (Real.continuous_sqrt.continuousOn.comp
    (hc.continuousOn.add (W_continuousOn.comp hc.continuousOn hm)) (mapsTo_univ _ _))

theorem scaled_eq {z : ℝ} (hz : 0 < z) (t : ℝ) :
    scaled z t = Real.sqrt (v t + z^2 * W (1/z^2*v t)) := by
  unfold scaled
  nth_rw 1 [← Real.sqrt_sq hz.le]
  rw [← Real.sqrt_mul (sq_nonneg _), mul_add]
  congr 2
  field_simp

theorem B_monotone : MonotoneOn B (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have hsq : x^2 ≤ y^2 := by gcongr
  have hscale : ∀ t ∈ Icc (0:ℝ) 1, scaled x t ≤ scaled y t := by
    intro t ht
    have hv : 0 ≤ v t := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    have hw := W_scale (θ:=x^2/y^2) (δ:=1/x^2*v t) (by positivity)
      ((div_le_one (by positivity)).mpr hsq) (mul_nonneg (by positivity) hv)
    have eq : x^2/y^2*(1/x^2*v t) = 1/y^2*v t := by field_simp
    rw [eq,div_mul_eq_mul_div,div_le_iff₀ (by positivity)] at hw
    rw [scaled_eq hx,scaled_eq hy]
    apply Real.sqrt_le_sqrt
    linarith
  have hin := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (scaled_integrable hx) (scaled_integrable hy) hscale
  unfold scaled at hin
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hin
  unfold B L
  rw [← mul_div_assoc,← mul_div_assoc]
  exact div_le_div_of_nonneg_right hin (Real.sqrt_nonneg _)

/-- Every Fourier mode decays at least as fast as the first. -/
theorem W_first_mode {x : ℝ} (hx : 0 ≤ x) :
    (1-Real.exp (-4*Real.pi^2*x))/12 ≤ W x := by
  let e := Real.exp (-4*Real.pi^2*x)
  have ht (i : ℕ) : term i x ≤ e*weight i := by
    have hi : (1:ℝ) ≤ ((i:ℝ)+1)^2 := by nlinarith [sq_nonneg (i:ℝ),Nat.cast_nonneg i (α:=ℝ)]
    have he : -4*Real.pi^2*((i:ℝ)+1)^2*x ≤ -4*Real.pi^2*x := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 4*Real.pi^2*x) (sub_nonneg.mpr hi)]
    unfold term weight
    calc
      _ ≤ e/((i:ℝ)+1)^2 := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr he) (sq_nonneg _)
      _ = _ := by ring
  have t := (Summable.of_norm_bounded weight_sum.summable (fun i => term_norm i hx)).tsum_le_tsum
    ht (weight_sum.summable.mul_left e)
  rw [tsum_mul_left,weight_sum.tsum_eq] at t
  change (1-e)/12 ≤ 1/12-1/(2*Real.pi^2)*(∑' i,term i x)
  have hp : 0 < Real.pi^2 := by positivity
  field_simp
  nlinarith

/-- Elementary outward rational bound using exp(u) ≥ (1 + u/2)^2. -/
theorem W_rational_lower {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) (hux : u ≤ 18*x) :
    (1-1/(1+u)^2)/12 ≤ W x := by
  have hp : 9 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hpow : (1+u)^2 ≤ Real.exp (4*Real.pi^2*x) := by
    calc
      _ ≤ (Real.exp u)^2 := by gcongr; linarith [Real.add_one_le_exp u]
      _ = Real.exp (u+u) := by rw [Real.exp_add]; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hx (sub_nonneg.mpr hp)])
  have hrec := one_div_le_one_div_of_le (by positivity : 0 < (1+u)^2) hpow
  apply le_trans _ (W_first_mode hx)
  rw [show -4*Real.pi^2*x = -(4*Real.pi^2*x) by ring,Real.exp_neg]
  linarith [show (Real.exp (4*Real.pi^2*x))⁻¹ ≤ 1/(1+u)^2 by simpa [one_div] using hrec]

end Shellsort.F09
