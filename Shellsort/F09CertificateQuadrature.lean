import Shellsort.F09CertificateHeat

/-! Signed quadrature on a quadratic mesh, in the two variables separately. -/
noncomputable section
namespace Shellsort.F09
open Real Set MeasureTheory
open scoped BigOperators

def quadPoint (N i : ℕ) : ℝ := (i:ℝ)^2/(2*(N:ℝ)^2)
def quadRule (upper : Bool) (N : ℕ) (f : ℝ → ℝ) := ∑ i ∈ Finset.range N,
  let a := quadPoint N i
  let b := quadPoint N (i+1)
  (b-a)*(if upper then f ((a+b)/2) else (f a+f b)/2)

private theorem local_quadrature {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (C : Continuous f)
    (conc : ConcaveOn ℝ (Icc a b) f) :
    (b-a)*((f a+f b)/2) ≤ (∫ x in a..b, f x) ∧
    (∫ x in a..b, f x) ≤ (b-a)*f ((a+b)/2) := by
  let m := (f b-f a)/(b-a)
  let k := f a-m*a
  have hl (x : ℝ) (hx : x ∈ Icc a b) : m*x+k ≤ f x := by
    let c := (b-x)/(b-a)
    let d := (x-a)/(b-a)
    have hc : 0 ≤ c := div_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hab.le)
    have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le)
    have vone : c+d = 1 := by dsimp [c,d]; field_simp; ring
    have hmix := conc.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hc hd vone
    have he : c*a+d*b=x := by dsimp [c,d]; field_simp; ring
    simp only [smul_eq_mul,he] at hmix
    convert hmix using 1
    dsimp [m,k,c,d]; field_simp; ring
  have hu (x : ℝ) (hx : x ∈ Icc a b) : f x + f (a+b-x) ≤ 2*f ((a+b)/2) := by
    have hm := conc.2 hx (show a+b-x ∈ Icc a b from ⟨by linarith [hx.2],by linarith [hx.1]⟩)
      (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)
    rw [smul_eq_mul,smul_eq_mul,smul_eq_mul,smul_eq_mul,
      show 1/2*x+1/2*(a+b-x)=(a+b)/2 by ring] at hm
    linarith
  constructor
  · have e := intervalIntegral.integral_mono_on (μ:=volume) hab.le
      (f:=fun x => m*x+k) ((by fun_prop : Continuous (fun x : ℝ => m*x+k)).intervalIntegrable _ _)
      (C.intervalIntegrable _ _) hl
    rw [intervalIntegral.integral_add (f:=fun x => m*x) (g:=fun _ => k)
      ((by fun_prop : Continuous (fun x : ℝ => m*x)).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_id,intervalIntegral.integral_const,smul_eq_mul] at e
    convert e using 1
    dsimp [m,k]; field_simp; ring
  · have cr : Continuous (fun x : ℝ => f (a+b-x)) := C.comp (continuous_const.sub continuous_id)
    have e := intervalIntegral.integral_mono_on (μ:=volume) hab.le
      (f:=fun x => f x+f (a+b-x)) (g:=fun _ => 2*f ((a+b)/2))
      ((C.add cr).intervalIntegrable _ _) intervalIntegrable_const hu
    rw [intervalIntegral.integral_add (f:=f) (g:=fun x => f (a+b-x))
      (C.intervalIntegrable _ _) (cr.intervalIntegrable _ _), intervalIntegral.integral_comp_sub_left,
      add_sub_cancel_right,add_sub_cancel_left,intervalIntegral.integral_const,smul_eq_mul] at e
    linarith

private theorem node_strict (N : ℕ) (hn : 0 < N) (i : ℕ) :
    quadPoint N i < quadPoint N (i+1) := by
  unfold quadPoint; push_cast
  apply div_lt_div_of_pos_right _ (by positivity)
  nlinarith [Nat.cast_nonneg i (α:=ℝ)]

theorem quadRule_bounds {f : ℝ → ℝ} (C : Continuous f) (conc : ConcaveOn ℝ (Icc 0 1) f)
    (symm : ∀ x ∈ Icc 0 1, f (1-x)=f x) (N : ℕ) (hn : 0 < N) :
    2*quadRule false N f ≤ (∫ x in (0:ℝ)..1, f x) ∧
    (∫ x in (0:ℝ)..1, f x) ≤ 2*quadRule true N f := by
  have left : quadPoint N 0=0 := by simp [quadPoint]
  have right : quadPoint N N=1/2 := by unfold quadPoint; field_simp
  have cover (i : ℕ) (hi : i < N) : Icc (quadPoint N i) (quadPoint N (i+1)) ⊆ Icc 0 1 := by
    apply Icc_subset_Icc (by unfold quadPoint; positivity)
    have hI : ((i+1:ℕ):ℝ) ≤ N := by exact_mod_cast (show i+1 ≤ N by omega)
    apply le_trans (b:=quadPoint N N)
    · unfold quadPoint; gcongr
    · rw [right]; norm_num
  have rows (i : ℕ) (hi : i < N) := local_quadrature (node_strict N hn i) C
    (conc.subset (cover i hi) (convex_Icc _ _))
  have lower := Finset.sum_le_sum (s:=Finset.range N)
    (fun i hi => (rows i (Finset.mem_range.mp hi)).1)
  have upper := Finset.sum_le_sum (s:=Finset.range N)
    (fun i hi => (rows i (Finset.mem_range.mp hi)).2)
  have sum := intervalIntegral.sum_integral_adjacent_intervals (μ:=volume) (n:=N) (a:=quadPoint N)
    (fun _ _ => C.intervalIntegrable _ _)
  rw [left,right] at sum
  rw [sum] at lower upper
  have reflected := intervalIntegral.integral_comp_sub_left (a:=(0:ℝ)) (b:=1/2) f 1
  rw [show (1:ℝ)-1/2=1/2 by norm_num,sub_zero] at reflected
  have sub : (∫ x in (0:ℝ)..1/2, f (1-x)) = ∫ x in (0:ℝ)..1/2, f x := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by norm_num)]
    exact fun x hx => symm x ⟨hx.1,by linarith [hx.2]⟩
  have both := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (C.intervalIntegrable 0 (1/2))
    (C.intervalIntegrable (1/2) 1)
  rw [← reflected,sub] at both
  change 2* _ ≤ _ ∧ _ ≤ 2* _
  unfold quadRule
  simp only [Bool.false_eq_true,if_false,if_true]
  constructor <;> linarith

private theorem profile_spatial_concave (lam : ℝ) (t : ℝ) :
    ConcaveOn ℝ (Icc 0 1) (fun x => profile lam (t,x)) := by
  let δ := max 0 (lam*v t)
  have hd : 0 ≤ δ := le_max_left .. 
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have h := (V_spatial_concave hd).2 hx hy ha hb hab
  have sq := Real.strictConcaveOn_sqrt.concaveOn.2 (V_nonneg hd hx) (V_nonneg hd hy) ha hb hab
  exact sq.trans (Real.sqrt_le_sqrt h)

private theorem profile_time_concave {lam x : ℝ} (hl : 0 ≤ lam) (hx : x ∈ Icc 0 1) :
    ConcaveOn ℝ (Icc 0 1) (fun t => profile lam (t,x)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro u hu w hw a b ha hb hab
  have htime : a*u+b*w ∈ Icc 0 1 := convex_Icc (0:ℝ) 1 hu hw ha hb hab
  have u0 := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
  have w0 := mul_nonneg hw.1 (sub_nonneg.mpr hw.2)
  have hdiff : a*v u+b*v w ≤ v (a*u+b*w) := by
    unfold v
    have he : a*u*(1-u)+b*w*(1-w)+a*b*(u-w)^2 = (a*u+b*w)*(1-(a*u+b*w)) := by
      linear_combination (a*u^2+b*w^2)*hab
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (u-w))]
  have v1 := (V_concave x).2 (show lam*v u ∈ Ici 0 from mul_nonneg hl u0)
    (show lam*v w ∈ Ici 0 from mul_nonneg hl w0) ha hb hab
  have v2 := V_heat_monotone x
    (show a*(lam*v u)+b*(lam*v w) ∈ Ici 0 from
      add_nonneg (mul_nonneg ha (mul_nonneg hl u0)) (mul_nonneg hb (mul_nonneg hl w0)))
    (show lam*v (a*u+b*w) ∈ Ici 0 from mul_nonneg hl (mul_nonneg htime.1 (sub_nonneg.mpr htime.2)))
    (by convert mul_le_mul_of_nonneg_left hdiff hl using 1 <;> ring)
  have sq := Real.strictConcaveOn_sqrt.concaveOn.2 (V_nonneg (mul_nonneg hl u0) hx)
    (V_nonneg (mul_nonneg hl w0) hx) ha hb hab
  simp only [smul_eq_mul] at *
  rw [profile_eq hl hu,profile_eq hl hw,profile_eq hl htime]
  exact sq.trans (Real.sqrt_le_sqrt (v1.trans v2))

private theorem quadRule_mono {upper : Bool} {N : ℕ} (hn : 0 < N) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Icc 0 1, f x ≤ g x) : quadRule upper N f ≤ quadRule upper N g := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hstep := node_strict N hn i
  have a0 : 0 ≤ quadPoint N i := by unfold quadPoint; positivity
  have bn : quadPoint N (i+1) ≤ 1 := by
    have hr : ((i+1:ℕ):ℝ) ≤ N := by exact_mod_cast (show i+1 ≤ N by omega)
    have h : quadPoint N (i+1) ≤ quadPoint N N := by unfold quadPoint; gcongr
    have he : quadPoint N N = 1/2 := by unfold quadPoint; field_simp
    linarith
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hstep.le)
  cases upper
  · exact div_le_div_of_nonneg_right (add_le_add (h _ ⟨a0,hstep.le.trans bn⟩)
      (h _ ⟨a0.trans hstep.le,bn⟩)) (by norm_num)
  · exact h _ ⟨by linarith,by linarith⟩

private theorem quadRule_mul (u : Bool) (N : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    quadRule u N (fun x => c*f x) = c*quadRule u N f := by
  unfold quadRule
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases u <;> simp <;> ring

def fourierQuadrature (u : Bool) (N : ℕ) (lam : ℝ) :=
  (4/Real.sqrt (2*Real.pi))*quadRule u N (fun t => quadRule u N (fun x => profile lam (t,x)))

set_option maxHeartbeats 1200000 in
/-- Signed, tensor-product trapezoid and midpoint bounds for the actual
Fourier integral. This rule allows the quadratic grid at any positive size. -/
theorem fourierQuadrature_bounds {lam : ℝ} (hl : 0 ≤ lam) (N : ℕ) (hn : 0 < N) :
    fourierQuadrature false N lam ≤ J lam ∧ J lam ≤ fourierQuadrature true N lam := by
  let f := profile lam
  let F := fun t : ℝ => ∫ x in (0:ℝ)..1, f (t,x)
  have cont := profile_cont lam
  have cs (t : ℝ) : Continuous (fun x : ℝ => f (t,x)) := cont.comp (continuous_const.prodMk continuous_id)
  have cf : Continuous F := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f:=fun t x : ℝ => f (t,x)) cont 0 1
  have ss (t : ℝ) (x : ℝ) (hx : x ∈ Icc 0 1) : f (t,1-x)=f (t,x) := by
    unfold f profile; rw [V_symm (le_max_left ..) hx]
  have st (t : ℝ) (_ : t ∈ Icc 0 1) : F (1-t)=F t := by
    have he : v (1-t)=v t := by unfold v; ring
    simp only [F,f,profile,he]
  have concF : ConcaveOn ℝ (Icc 0 1) F := by
    refine ⟨convex_Icc _ _,?_⟩
    intro t ht s hs a b ha hb hab
    simp only [smul_eq_mul]
    unfold F
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        (f:=fun x => a*f (t,x)) (g:=fun x => b*f (s,x))
        ((continuous_const.mul (cs t)).intervalIntegrable _ _)
        ((continuous_const.mul (cs s)).intervalIntegrable _ _)]
    apply intervalIntegral.integral_mono_on zero_le_one
      (((continuous_const.mul (cs t)).add (continuous_const.mul (cs s))).intervalIntegrable _ _)
      ((cs _).intervalIntegrable _ _)
    intro x hx
    exact (profile_time_concave hl hx).2 ht hs ha hb hab
  have outer := quadRule_bounds cf concF st N hn
  have inner (t : ℝ) := quadRule_bounds (cs t) (profile_spatial_concave lam t) (ss t) N hn
  have l := quadRule_mono (upper:=false) hn (fun t _ => (inner t).1)
  have u := quadRule_mono (upper:=true) hn (fun t _ => (inner t).2)
  rw [quadRule_mul] at l u
  rw [J_eq hl]
  unfold fourierQuadrature average
  have hp : 0 < Real.sqrt (2*Real.pi) := by positivity
  constructor
  · rw [le_div_iff₀ hp]
    field_simp
    linarith [outer.1]
  · rw [div_le_iff₀ hp]
    field_simp
    linarith [outer.2]


end Shellsort.F09

