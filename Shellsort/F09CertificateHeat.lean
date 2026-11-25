import Shellsort.F09CertificateFourier
import Shellsort.F09PhaseArcLimit
import Shellsort.F09GaussianAbsolute
import Mathlib.MeasureTheory.Function.Floor

/-! Positive heat representation and the signed quadrature hypotheses. -/
noncomputable section
namespace Shellsort.F09
open Real Set MeasureTheory ProbabilityTheory
open scoped NNReal

private def heatLaw (δ : ℝ) := gaussianReal 0 (Real.toNNReal (2*δ))
private instance (δ : ℝ) : IsProbabilityMeasure (heatLaw δ) := by unfold heatLaw; infer_instance

private def orbitDist (y : ℝ) := min (Int.fract y) (1-Int.fract y)
private def tent (x y : ℝ) := min (min x (1-x)) (orbitDist y)
private def wave (k : ℕ) (x y : ℝ) :=
  Real.cos (2*Real.pi*((k:ℝ)+1)*y)*Real.sin (Real.pi*((k:ℝ)+1)*x)^2/((k:ℝ)+1)^2

private theorem wave_sum {x : ℝ} (hx : x ∈ Icc 0 1) (y : ℝ) :
    HasSum (fun k => wave k x y) (Real.pi^2/2*(v x-tent x y)) := by
  have h := Shellsort.phase_tent_cos_series (q:=Int.fract y)
    ⟨Int.fract_nonneg y,(Int.fract_lt_one y).le⟩ hx
  convert h using 1
  funext k
  unfold wave
  have eq : 2*Real.pi*((k:ℝ)+1)*y =
      2*Real.pi*((k:ℝ)+1)*Int.fract y + (((k:ℤ)+1)*⌊y⌋:ℤ)*(2*Real.pi) := by
    push_cast
    rw [Int.fract]
    ring
  rw [eq,Real.cos_add_int_mul_two_pi]
  rfl

private theorem wave_norm (k : ℕ) (x y : ℝ) : ‖wave k x y‖ ≤ weight k := by
  unfold wave weight
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (sq_nonneg (Real.sin _)),
    abs_of_nonneg (sq_nonneg ((k:ℝ)+1))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_one₀ (Real.abs_cos_le_one _) (sq_nonneg _) (Real.sin_sq_le_one _)

private theorem heat_cos {δ : ℝ} (hd : 0 ≤ δ) (w : ℝ) :
    (∫ y, Real.cos (w*y) ∂heatLaw δ) = Real.exp (-δ*w^2) := by
  let f := fun y : ℝ => Complex.exp ((w:ℂ)*(y:ℂ)*Complex.I)
  have fi : Integrable f (heatLaw δ) := by
    apply Integrable.of_bound (by unfold f; fun_prop) 1
    filter_upwards with y
    simp [f,Complex.norm_exp]
  have h := integral_re fi
  have hchar := charFun_gaussianReal (μ:=0) (v:=Real.toNNReal (2*δ)) w
  rw [charFun_apply_real] at hchar
  change (∫ y, f y ∂heatLaw δ) = _ at hchar
  rw [hchar] at h
  simp [f,Complex.exp_re,Real.toNNReal_of_nonneg (by linarith : 0 ≤ 2*δ)] at h
  rw [← Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im] at h
  simp only [mul_zero,zero_div,Real.cos_zero,mul_one] at h
  convert h using 1 <;> congr 1 <;> ring

/-- The Fourier variance is the Gaussian average of the cyclic overlap tent. -/
theorem V_eq_gaussian_tent {δ x : ℝ} (hd : 0 ≤ δ) (hx : x ∈ Icc 0 1) :
    V δ x = ∫ y, tent x y ∂heatLaw δ := by
  have fi (k : ℕ) : Integrable (wave k x) (heatLaw δ) := by
    exact Integrable.of_bound (by unfold wave; fun_prop) (weight k) (ae_of_all _ (wave_norm k x))
  have hnorm (k : ℕ) : ‖∫ y, ‖wave k x y‖ ∂heatLaw δ‖ ≤ weight k := by
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact (integral_mono (fi k).norm (integrable_const (weight k)) (wave_norm k x)).trans_eq (by simp)
  have swap := integral_tsum_of_summable_integral_norm fi (Summable.of_norm_bounded weight_sum.summable hnorm)
  have htme : Measurable (fun y => tent x y) := by unfold tent orbitDist; fun_prop
  have ti : Integrable (fun y => tent x y) (heatLaw δ) := by
    apply Integrable.of_bound htme.aestronglyMeasurable 1
    filter_upwards with y
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ tent x y from le_min
      (le_min hx.1 (sub_nonneg.mpr hx.2)) (le_min (Int.fract_nonneg _) (sub_nonneg.mpr (Int.fract_lt_one _).le)))]
    exact (min_le_left ..).trans ((min_le_left ..).trans hx.2)
  have imode (k : ℕ) : (∫ y, wave k x y ∂heatLaw δ) =
      Real.exp (-4*Real.pi^2*((k:ℝ)+1)^2*δ) * Real.sin (Real.pi*((k:ℝ)+1)*x)^2/((k:ℝ)+1)^2 := by
    unfold wave
    rw [integral_div,integral_mul_const,heat_cos hd]
    congr 3 <;> ring
  simp_rw [imode,fun y => (wave_sum hx y).tsum_eq] at swap
  rw [integral_const_mul,integral_sub (integrable_const _) ti] at swap
  simp only [integral_const,probReal_univ,one_smul] at swap
  unfold V
  change v x - 2/Real.pi^2*_ = _
  rw [swap]
  field_simp
  ring

theorem V_spatial_concave {δ : ℝ} (hd : 0 ≤ δ) : ConcaveOn ℝ (Icc 0 1) (V δ) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hxy : a*x+b*y ∈ Icc 0 1 := convex_Icc (0:ℝ) 1 hx hy ha hb hab
  have hti (x : ℝ) (hx : x ∈ Icc 0 1) : Integrable (fun u => tent x u) (heatLaw δ) := by
    apply Integrable.of_bound (by unfold tent orbitDist; fun_prop) 1
    filter_upwards with u
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ tent x u from le_min
      (le_min hx.1 (sub_nonneg.mpr hx.2)) (le_min (Int.fract_nonneg _) (sub_nonneg.mpr (Int.fract_lt_one _).le)))]
    exact (min_le_left ..).trans ((min_le_left ..).trans hx.2)
  rw [V_eq_gaussian_tent hd hx,V_eq_gaussian_tent hd hy,V_eq_gaussian_tent hd hxy,
    ← integral_const_mul,← integral_const_mul,← integral_add ((hti x hx).const_mul a) ((hti y hy).const_mul b)]
  apply integral_mono (((hti x hx).const_mul a).add ((hti y hy).const_mul b)) (hti _ hxy)
  intro u
  change a*tent x u+b*tent y u ≤ tent (a*x+b*y) u
  have hp (s t : ℝ) (hh : s ≤ t) (v w : ℝ) (hh' : v ≤ w) :=
    add_le_add (mul_le_mul_of_nonneg_left hh ha) (mul_le_mul_of_nonneg_left hh' hb)
  unfold tent
  apply le_min
  · apply le_min
    · exact hp _ _ ((min_le_left ..).trans (min_le_left ..)) _ _ ((min_le_left ..).trans (min_le_left ..))
    · have h := hp (tent x u) (1-x) ((min_le_left ..).trans (min_le_right ..))
        (tent y u) (1-y) ((min_le_left ..).trans (min_le_right ..))
      unfold tent at h
      linarith
  · have h := hp (tent x u) (orbitDist u) (min_le_right ..) (tent y u) (orbitDist u) (min_le_right ..)
    unfold tent at h
    linear_combination h + orbitDist u*hab

private theorem tent_integrable {x : ℝ} (hx : x ∈ Icc 0 1) (δ : ℝ) :
    Integrable (tent x) (heatLaw δ) := by
  apply Integrable.of_bound (by unfold tent orbitDist; fun_prop) 1
  filter_upwards with y
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ tent x y from le_min
    (le_min hx.1 (sub_nonneg.mpr hx.2)) (le_min (Int.fract_nonneg _) (sub_nonneg.mpr (Int.fract_lt_one _).le)))]
  exact (min_le_left ..).trans ((min_le_left ..).trans hx.2)

theorem V_symm {δ x : ℝ} (hd : 0 ≤ δ) (hx : x ∈ Icc 0 1) : V δ (1-x) = V δ x := by
  rw [V_eq_gaussian_tent hd (show 1-x ∈ Icc 0 1 from ⟨by linarith [hx.2],by linarith [hx.1]⟩),
    V_eq_gaussian_tent hd hx]
  simp only [tent,sub_sub_cancel,min_comm (1-x) x]

/-- Gaussian absolute first moment used at small variance quadrature nodes. -/
theorem V_gaussian_upper {δ x : ℝ} (hd : 0 ≤ δ) (hx : x ∈ Icc 0 1) :
    V δ x ≤ 2*Real.sqrt δ/Real.sqrt Real.pi := by
  have dist (y : ℝ) : orbitDist y ≤ |y| := by
    have h : orbitDist y ≤ 1/2 := by
      unfold orbitDist
      rw [min_le_iff]
      by_cases h : Int.fract y ≤ 1/2
      · exact Or.inl h
      · exact Or.inr (by linarith)
    by_cases hy : 1/2 ≤ |y|
    · exact h.trans hy
    unfold orbitDist
    by_cases h0 : 0 ≤ y
    · rw [abs_of_nonneg h0] at *
      rw [Int.fract_eq_self.mpr ⟨h0,by linarith⟩]; exact min_le_left .. 
    · rw [abs_of_neg (lt_of_not_ge h0)] at *
      have eq : Int.fract y = y+1 := by
        rw [← Int.fract_add_one]; exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [eq]
      exact (min_le_right ..).trans (by linarith)
  rw [V_eq_gaussian_tent hd hx]
  have g : Integrable (fun y : ℝ => |y|) (heatLaw δ) := by
    simpa [heatLaw] using ((memLp_id_gaussianReal (μ:=0) (v:=Real.toNNReal (2*δ)) 1).integrable (by simp)).abs
  apply (integral_mono (tent_integrable hx δ) g (fun y => (min_le_right ..).trans (dist y))).trans_eq
  unfold heatLaw
  rw [integral_abs_gaussian,Real.sqrt_div (by norm_num)]
  change Real.sqrt 2/Real.sqrt Real.pi*Real.sqrt ((2*δ).toNNReal:ℝ) = _
  rw [Real.coe_toNNReal _ (by linarith : 0 ≤ 2*δ),Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ))]
  have he := Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))
  field_simp
  linear_combination Real.sqrt δ*he

end Shellsort.F09

