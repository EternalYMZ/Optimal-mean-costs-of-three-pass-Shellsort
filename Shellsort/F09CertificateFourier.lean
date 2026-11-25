import Shellsort.F09CertificateAnalysis
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fourier positivity and shape interpolation for the actual integral J. -/
noncomputable section
namespace Shellsort.F09
open Real Set MeasureTheory

def mode (k : ℕ) (δ x : ℝ) := Real.exp (-4*Real.pi^2*((k:ℝ)+1)^2*δ) *
  Real.sin (Real.pi*((k:ℝ)+1)*x)^2/((k:ℝ)+1)^2

theorem mode_nonneg (k : ℕ) (δ x : ℝ) : 0 ≤ mode k δ x := by unfold mode; positivity

private theorem mode_bound (k : ℕ) {δ : ℝ} (hd : 0 ≤ δ) (x : ℝ) : ‖mode k δ x‖ ≤ weight k := by
  rw [Real.norm_eq_abs,abs_of_nonneg (mode_nonneg ..)]
  unfold mode weight
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hs := Real.sin_sq_le_one (Real.pi*((k:ℝ)+1)*x)
  have he : Real.exp (-4*Real.pi^2*((k:ℝ)+1)^2*δ) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hp : 0 ≤ 4*Real.pi^2*((k:ℝ)+1)^2*δ := by positivity
    linarith)
  exact mul_le_one₀ he (sq_nonneg _) hs

theorem mode_sum {δ : ℝ} (hd : 0 ≤ δ) (x : ℝ) : Summable (fun k => mode k δ x) :=
  Summable.of_norm_bounded weight_sum.summable (fun i => mode_bound i hd x)

theorem V_zero {x : ℝ} (hx : x ∈ Icc 0 1) : V 0 x = 0 := by
  have hc := hasSum_one_div_nat_pow_mul_cos (k:=1) (by decide) hx
  norm_num [Polynomial.bernoulli_def,Finset.sum_range_succ,bernoulli_two,
    Polynomial.eval_monomial,Nat.factorial] at hc
  have hc1 := (hasSum_nat_add_iff' 1).mpr hc
  simp at hc1
  have hs := (weight_sum.sub hc1).mul_left (1/2:ℝ)
  have hid (k : ℕ) : mode k 0 x =
      (1/2)*(weight k - (((k:ℝ)+1)^2)⁻¹ * Real.cos (2*Real.pi*((k:ℝ)+1)*x)) := by
    unfold mode weight
    rw [show 2*Real.pi*((k:ℝ)+1)*x = 2*(Real.pi*((k:ℝ)+1)*x) by ring, Real.cos_two_mul_eq_one_sub]
    simp
    ring
  unfold V
  change x*(1-x)-2/Real.pi^2*(∑' k, mode k 0 x) = 0
  simp_rw [hid]
  rw [hs.tsum_eq]
  field_simp
  ring

theorem V_concave (x : ℝ) : ConcaveOn ℝ (Ici 0) (fun δ => V δ x) := by
  refine ⟨convex_Ici _,?_⟩
  intro δ hδ η hη a b ha hb hab
  simp only [smul_eq_mul]
  have mix : 0 ≤ a*δ+b*η := add_nonneg (mul_nonneg ha hδ) (mul_nonneg hb hη)
  have hterm (k : ℕ) : mode k (a*δ+b*η) x ≤ a*mode k δ x+b*mode k η x := by
    let e := -4*Real.pi^2*((k:ℝ)+1)^2
    have he := convexOn_exp.2 (Set.mem_univ (e*δ)) (Set.mem_univ (e*η)) ha hb hab
    simp only [smul_eq_mul] at he
    rw [show a*(e*δ)+b*(e*η)=e*(a*δ+b*η) by ring] at he
    have m := mul_le_mul_of_nonneg_right he
      (show 0 ≤ Real.sin (Real.pi*((k:ℝ)+1)*x)^2/((k:ℝ)+1)^2 by positivity)
    unfold mode
    unfold e at m
    linear_combination m
  have h := (mode_sum mix x).tsum_le_tsum hterm
    (((mode_sum hδ x).mul_left a).add ((mode_sum hη x).mul_left b))
  rw [Summable.tsum_add ((mode_sum hδ x).mul_left a) ((mode_sum hη x).mul_left b),
    tsum_mul_left,tsum_mul_left] at h
  change a*(x*(1-x)-2/Real.pi^2*(∑' i,mode i δ x))+
    b*(x*(1-x)-2/Real.pi^2*(∑' i,mode i η x)) ≤
    x*(1-x)-2/Real.pi^2*(∑' i,mode i (a*δ+b*η) x)
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2/Real.pi^2 by positivity)
  linear_combination hm + x*(1-x)*hab

theorem V_nonneg {δ x : ℝ} (hd : 0 ≤ δ) (hx : x ∈ Icc 0 1) : 0 ≤ V δ x := by
  have each (i : ℕ) : mode i δ x ≤ mode i 0 x := by
    unfold mode
    simp only [mul_zero,Real.exp_zero,one_mul]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_of_le_one_left (sq_nonneg _)
    apply Real.exp_le_one_iff.mpr
    have hp : 0 ≤ 4*Real.pi^2*((i:ℝ)+1)^2*δ := by positivity
    linarith
  have h := (mode_sum hd x).tsum_le_tsum each (mode_sum le_rfl x)
  rw [← V_zero hx]
  change x*(1-x)-2/Real.pi^2*(∑' i,mode i 0 x) ≤ x*(1-x)-2/Real.pi^2*(∑' i,mode i δ x)
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left h (by positivity)) _

def profile (lam : ℝ) (p : ℝ × ℝ) :=
  Real.sqrt (V (max 0 (lam*v p.1)) p.2)

def average (f : ℝ × ℝ → ℝ) :=
  (∫ t in (0:ℝ)..1, ∫ x in (0:ℝ)..1, f (t,x)) / Real.sqrt (2*Real.pi)

theorem profile_cont (lam : ℝ) : Continuous (profile lam) := by
  have hs : Continuous (fun p : ℝ × ℝ => ∑' k, mode k (max 0 (lam*v p.1)) p.2) := by
    refine continuous_tsum (u:=weight) ?_ weight_sum.summable ?_
    · intro k; unfold mode v; fun_prop
    · intro k p; exact mode_bound k (le_max_left ..) _
  unfold profile V
  apply Real.continuous_sqrt.comp
  exact (continuous_snd.mul (continuous_const.sub continuous_snd)).sub (continuous_const.mul hs)

theorem profile_eq {lam t : ℝ} (hl : 0 ≤ lam) (ht : t ∈ Icc 0 1) (x : ℝ) :
    profile lam (t,x) = Real.sqrt (V (lam*v t) x) := by
  unfold profile
  simp only [max_eq_right (mul_nonneg hl (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) : 0 ≤ lam*v t)]

theorem J_eq {lam : ℝ} (hl : 0 ≤ lam) : J lam = average (profile lam) := by
  unfold J average
  apply congrArg (fun y : ℝ => y/Real.sqrt (2*Real.pi))
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le zero_le_one]
  intro t ht
  simp_rw [profile_eq hl ht]

private theorem inner_cont {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun t : ℝ => ∫ x in (0:ℝ)..1, f (t,x)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f:=fun t x : ℝ => f (t,x)) hf 0 1

private theorem section_cont {f : ℝ × ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    Continuous (fun x : ℝ => f (t,x)) := hf.comp (continuous_const.prodMk continuous_id)

private theorem average_mono {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (le : ∀ t ∈ Icc 0 1, ∀ x ∈ Icc 0 1, f (t,x) ≤ g (t,x)) : average f ≤ average g := by
  unfold average
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply intervalIntegral.integral_mono_on zero_le_one
    ((inner_cont hf).intervalIntegrable _ _) ((inner_cont hg).intervalIntegrable _ _)
  intro t ht
  exact intervalIntegral.integral_mono_on zero_le_one
    ((section_cont hf t).intervalIntegrable _ _) ((section_cont hg t).intervalIntegrable _ _) (le t ht)

private theorem average_mix {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℝ) : average (fun p => a*f p+b*g p) = a*average f+b*average g := by
  unfold average
  have e (t : ℝ) : (∫ x in (0:ℝ)..1, a*f (t,x)+b*g (t,x)) =
      a*(∫ x in (0:ℝ)..1, f (t,x))+b*(∫ x in (0:ℝ)..1, g (t,x)) := by
    rw [intervalIntegral.integral_add (f:=fun x => a*f (t,x)) (g:=fun x => b*g (t,x))
      ((continuous_const.mul (section_cont hf t)).intervalIntegrable _ _)
      ((continuous_const.mul (section_cont hg t)).intervalIntegrable _ _)]
    simp only [intervalIntegral.integral_const_mul]
  simp_rw [e]
  rw [intervalIntegral.integral_add (f:=fun t => a*(∫ x in (0:ℝ)..1, f (t,x)))
    (g:=fun t => b*(∫ x in (0:ℝ)..1, g (t,x)))
    ((continuous_const.mul (inner_cont hf)).intervalIntegrable _ _)
    ((continuous_const.mul (inner_cont hg)).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul]
  ring

set_option maxHeartbeats 1000000 in
theorem J_concave : ConcaveOn ℝ (Ici 0) J := by
  refine ⟨convex_Ici _,?_⟩
  intro u hu w hw a b ha hb hab
  simp only [smul_eq_mul]
  have hm := add_nonneg (mul_nonneg ha hu) (mul_nonneg hb hw)
  rw [J_eq hu,J_eq hw,J_eq hm,← average_mix (profile_cont u) (profile_cont w)]
  apply average_mono ((continuous_const.mul (profile_cont u)).add (continuous_const.mul (profile_cont w)))
    (profile_cont _)
  intro t ht x hx
  change a*profile u (t,x)+b*profile w (t,x) ≤ profile (a*u+b*w) (t,x)
  rw [profile_eq hu ht,profile_eq hw ht,profile_eq hm ht]
  have hv := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have h1 : 0 ≤ u*v t := mul_nonneg hu hv
  have h2 : 0 ≤ w*v t := mul_nonneg hw hv
  have hV := (V_concave x).2 h1 h2 ha hb hab
  have hS := Real.strictConcaveOn_sqrt.concaveOn.2 (V_nonneg h1 hx) (V_nonneg h2 hx) ha hb hab
  simp only [smul_eq_mul] at hV hS
  rw [show a*(u*v t)+b*(w*v t)=(a*u+b*w)*v t by ring] at hV
  exact hS.trans (Real.sqrt_le_sqrt hV)

private theorem averaged_scale {z : ℝ} (hz : 0 < z) :
    average (fun p => z*profile (1/z^2) p) = z*J (1/z^2) := by
  have eq := average_mix (profile_cont (1/z^2)) (profile_cont (1/z^2)) z 0
  simpa only [zero_mul,add_zero,← J_eq (by positivity : 0 ≤ 1/z^2)] using eq

/-- The unnormalized heat contribution is nondecreasing. A single quadrature
at shape ten controls the entire large-shape tail. -/
theorem shape_J_monotone : MonotoneOn (fun z : ℝ => z*J (1/z^2)) (Ioi 0) := by
  intro r hr s hs hrs
  change 0 < r at hr
  change 0 < s at hs
  change r*J (1/r^2) ≤ s*J (1/s^2)
  rw [← averaged_scale hr,← averaged_scale hs]
  apply average_mono (continuous_const.mul (profile_cont _)) (continuous_const.mul (profile_cont _))
  intro t ht x hx
  change r*profile (1/r^2) (t,x) ≤ s*profile (1/s^2) (t,x)
  rw [profile_eq (by positivity : 0 ≤ 1/r^2) ht,profile_eq (by positivity : 0 ≤ 1/s^2) ht]
  have hv : 0 ≤ v t := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  let a := r^2/s^2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (div_le_one (by positivity)).mpr (by gcongr)
  have hV := (V_concave x).2 (show 1/r^2*v t ∈ Ici 0 from mul_nonneg (by positivity) hv)
    (show (0:ℝ) ∈ Ici 0 by simp) ha (sub_nonneg.mpr ha1) (show a+(1-a)=1 by ring)
  simp only [smul_eq_mul,V_zero hx,mul_zero,add_zero] at hV
  have eq : a*(1/r^2*v t) = 1/s^2*v t := by dsimp [a]; field_simp
  rw [eq] at hV
  have he : r^2*V (1/r^2*v t) x ≤ s^2*V (1/s^2*v t) x := by
    convert mul_le_mul_of_nonneg_left hV (sq_nonneg s) using 1
    dsimp [a]; field_simp
  have hsq := Real.sqrt_le_sqrt he
  simpa only [Real.sqrt_mul (sq_nonneg r),Real.sqrt_mul (sq_nonneg s),
    Real.sqrt_sq hr.le,Real.sqrt_sq hs.le] using hsq

theorem J_universal_upper {lam : ℝ} (hl : 0 ≤ lam) :
    J lam ≤ (Real.pi/8)/Real.sqrt (2*Real.pi) := by
  let f := fun (p : ℝ × ℝ) => Real.sqrt (v p.2)
  have hf : Continuous f := by unfold f v; fun_prop
  rw [J_eq hl]
  have hi : average (profile lam) ≤ average f := by
    apply average_mono (profile_cont lam) hf
    intro t ht x hx
    rw [profile_eq hl ht]
    apply Real.sqrt_le_sqrt
    change x*(1-x)-2/Real.pi^2*(∑' i,mode i (lam*v t) x) ≤ x*(1-x)
    have hsum : 0 ≤ ∑' i, mode i (lam*v t) x := tsum_nonneg (fun i => mode_nonneg i _ _)
    exact sub_le_self _ (mul_nonneg (by positivity) hsum)
  unfold average f at hi
  unfold average
  simpa only [integral_sqrt_v,intervalIntegral.integral_const,sub_zero,one_smul] using hi

/-- A fully analytic upper bound, independent of the archived quadrature. -/
theorem kappa_lt_617 : kappa < (617:ℝ)/1000 := by
  have lb : BddBelow (H '' Ioi 0) := by
    refine ⟨0,?_⟩
    rintro _ ⟨z,hz,rfl⟩; exact H_nonneg hz
  apply lt_of_le_of_lt (csInf_le lb (show H (4/3) ∈ H '' Ioi 0 from ⟨_,by norm_num,rfl⟩))
  have h1 : (11547:ℝ)/10000 ≤ Real.sqrt (4/3) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have h2 : (250662:ℝ)/100000 ≤ Real.sqrt (2*Real.pi) :=
    Real.le_sqrt_of_sq_le (by linarith [Real.pi_gt_d6])
  have ju := J_universal_upper (by positivity : 0 ≤ 1/(4/3:ℝ)^2)
  have hp : (Real.pi/8)/Real.sqrt (2*Real.pi) ≤ (15667:ℝ)/100000 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_lt_d6]
  have sq : Real.sqrt c/Real.sqrt (4/3) ≤ (47069814/100000000:ℝ)/(11547/10000) :=
    (div_le_div_of_nonneg_right sqrt_c_bounds.2.le (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1)
  unfold H
  rw [Real.sqrt_div c_pos.le]
  linarith

/-- Integrability of both levels of the source variance integral on the
physical unit interval, including its boundary thresholds. -/
theorem phase_profile_integrable {lam : ℝ} (hl : 0 ≤ lam) :
    (∀ t ∈ Icc (0:ℝ) 1, IntervalIntegrable (fun x => Real.sqrt (V (lam*v t) x)) volume 0 1) ∧
    IntervalIntegrable (fun t => ∫ x : ℝ in 0..1, Real.sqrt (V (lam*v t) x)) volume 0 1 := by
  constructor
  · intro t ht
    simp_rw [← profile_eq hl ht]
    exact (section_cont (profile_cont lam) t).intervalIntegrable _ _
  · apply ((inner_cont (profile_cont lam)).intervalIntegrable 0 1).congr
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    simp only [profile_eq hl ⟨ht.1.le,ht.2⟩]

theorem V_heat_monotone (x : ℝ) : MonotoneOn (fun δ => V δ x) (Ici 0) := by
  intro u hu w _ huw
  have hw : 0 ≤ w := hu.trans huw
  have point (i : ℕ) : mode i w x ≤ mode i u x := by
    unfold mode
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ 4*Real.pi^2*((i:ℝ)+1)^2 := by positivity
    nlinarith [mul_nonneg hp (sub_nonneg.mpr huw)]
  have sum := (mode_sum hw x).tsum_le_tsum point (mode_sum hu x)
  change x*(1-x)-2/Real.pi^2*(∑' i,mode i u x) ≤ x*(1-x)-2/Real.pi^2*(∑' i,mode i w x)
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left sum (by positivity)) _

end Shellsort.F09
