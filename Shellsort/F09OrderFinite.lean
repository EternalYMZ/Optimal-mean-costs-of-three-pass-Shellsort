import Shellsort.F09OrderClassUpper
import Shellsort.F09OrderFamilies

noncomputable section
namespace Shellsort.F09
open Filter Set
open scoped Topology

/-- A finite scale criterion for the actual uniform insertion mean. Its
extra divisor term accounts for the physical interleaving of the classes. -/
theorem threePass_cost_controlled_scales (n h g : ℕ) (hhn : h<n) (hgh : g<h) (hg : 2≤g)
    (L : ℝ) (bound : 1≤L) (hlo : Real.sqrt n ≤ L*h) (hhi : (h:ℝ) ≤ L*Real.sqrt n)
    (glo : Real.sqrt (Real.sqrt n) ≤ L*g) (ghi : (g:ℝ) ≤ L*Real.sqrt (Real.sqrt n)) :
    uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g (by omega) (by omega):ℝ)) ≤
      (5*L^2+2*(Nat.gcd h g:ℕ))*n*Real.sqrt n := by
  have np : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have gp : (1:ℝ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  have gp' : (0:ℝ) < g := by linarith
  have Lp : 0 ≤ L := by linarith
  let s := Real.sqrt (n : ℝ)
  let t := Real.sqrt s
  have sn : s^2 = n := Real.sq_sqrt np.le
  have ts : t^2 = s := Real.sq_sqrt (Real.sqrt_nonneg _)
  have so : 1 ≤ s := Real.one_le_sqrt.2 (by exact_mod_cast (show 1 ≤ n by omega))
  have Lsq : L ≤ L^2 := by nlinarith [mul_nonneg Lp (sub_nonneg.mpr bound)]
  have hsqrt : Real.sqrt h ≤ L*t := by
    apply (Real.sqrt_le_left (by positivity)).2
    rw [mul_pow, ts]
    exact hhi.trans (mul_le_mul_of_nonneg_right Lsq (Real.sqrt_nonneg _))
  have hplus : Real.sqrt ((h:ℝ)+3) ≤ 2*Real.sqrt h := by
    apply (Real.sqrt_le_left (by positivity)).2
    have hOne : (1:ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
    nlinarith [Real.sq_sqrt hp.le]
  have f : (n:ℝ)^2/(4*h) ≤ L*n*s/4 := by
    apply (div_le_iff₀ (by positivity)).2
    have pay := mul_le_mul_of_nonneg_left hlo (show 0 ≤ n*s by positivity)
    change s ≤ L*h at hlo
    nlinarith [show (n:ℝ)*s*s = n^2 by rw [mul_assoc, ← sq, sn]; ring]
  have m : (2/(g:ℝ))*(n*((h:ℝ)-1+Real.sqrt ((n:ℝ)*h)/2)) ≤
      (2*L + L^2)*n*s := by
    have r : Real.sqrt h ≤ L^2*g := hsqrt.trans (by
      have u := mul_le_mul_of_nonneg_left glo Lp; change L*t ≤ _; nlinarith)
    have u₁ := mul_le_mul_of_nonneg_left gp (show 0 ≤ 2*L*n*s by positivity)
    have u₂ := mul_le_mul_of_nonneg_left hhi (show 0 ≤ 2*(n:ℝ) by positivity)
    have u₃ := mul_le_mul_of_nonneg_left r (show 0 ≤ n*s by positivity)
    rw [Real.sqrt_mul np.le]
    change (2/(g:ℝ))*(n*((h:ℝ)-1+s*Real.sqrt h/2)) ≤ _
    rw [div_mul_eq_mul_div, div_le_iff₀ gp']
    nlinarith
  have last : (n:ℝ)*(((g:ℝ)-1)*Real.sqrt ((h:ℝ)+3)/2) ≤ L^2*n*s := by
    have a := mul_le_mul (show (g:ℝ)-1 ≤ L*t by change (g:ℝ) ≤ L*t at ghi; linarith) hplus
      (Real.sqrt_nonneg _) (show 0 ≤ L*t by positivity)
    have b := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2*L*t by positivity)
    apply (mul_le_mul_of_nonneg_left (b := ((g:ℝ)-1)*Real.sqrt ((h:ℝ)+3)/2)
      (c := L^2*s) ?_ np.le).trans_eq (by ring)
    nlinarith only [a, b, congrArg (fun x : ℝ => L^2*x) ts]
  let d := Nat.gcd h g
  let H := h/d
  let G := g/d
  have dp : 0<d := Nat.gcd_pos_of_pos_left g (by omega)
  have dOne : (1:ℝ) ≤ d := by exact_mod_cast dp
  have ph : 0<H := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left ..)) dp
  have pg : 0<G := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right ..)) dp
  have cop : H.Coprime G := Nat.coprime_div_gcd_div_gcd dp
  have deh : d*H=h := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have deg : d*G=g := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have leH : (H:ℝ) ≤ h := by exact_mod_cast Nat.div_le_self h d
  have rootD : Real.sqrt (d:ℝ) ≤ d := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr dOne) (Nat.cast_nonneg (α:=ℝ) d)]
  have rootH : Real.sqrt ((H:ℝ)+3) ≤ Real.sqrt ((h:ℝ)+3) := Real.sqrt_le_sqrt (by linarith)
  have gapR : (d:ℝ)*((G:ℝ)-1) ≤ (g:ℝ)-1 := by
    have q : (d:ℝ)*G=g := by exact_mod_cast deg
    nlinarith
  have gain := mul_le_mul gapR rootH (Real.sqrt_nonneg _) (by linarith : 0≤(g:ℝ)-1)
  have boundClass : (d:ℝ)*(((G:ℝ)-1)*Real.sqrt ((H:ℝ)+3)/2) ≤
      ((g:ℝ)-1)*Real.sqrt ((h:ℝ)+3)/2 := by linarith only [gain]
  have base : (d:ℝ)-1+Real.sqrt ((n:ℝ)*d)/2 ≤ 2*d*s := by
    rw [Real.sqrt_mul np.le]; change (d:ℝ)-1+s*Real.sqrt d/2 ≤ _
    have nonneg := Real.sqrt_nonneg (n:ℝ)
    have one := mul_le_mul_of_nonneg_right so (Nat.cast_nonneg (α:=ℝ) d)
    nlinarith only [one,mul_le_mul_of_nonneg_left rootD nonneg,dOne]
  have A := uniform_twoPass_footrule_all_divisors n d H G dp ph pg cop
  rw [deh,deg] at A
  have lastCost := (uniformAverage_mono _ _ (fun p : RankPlacement n => ordinaryInsertionCost_le_footrule
    (gapSort (gapSort p h) g))).trans A
  have lastFinal : _ ≤ 2*d*n*s + L^2*n*s :=
    lastCost.trans ((mul_le_mul_of_nonneg_left (add_le_add base boundClass) np.le).trans (by
      rw [mul_add]; nlinarith only [last]))
  have middle := (uniform_secondPassCost_upper n h g (by omega) (by omega)).trans m
  have ini := (uniform_firstPassCost_upper n h (by omega)).trans f
  rw [uniform_threePassInsertionCost_decomposition]
  have scalar := mul_le_mul_of_nonneg_right Lsq (show 0 ≤ n*s by positivity)
  change _ ≤ (5*L^2+2*d)*n*s
  nlinarith only [ini,middle,lastFinal,scalar,show 0≤L^2*(n:ℝ)*s by positivity]

/-- Independent order criterion for arbitrary legal three-pass schedules.
The sufficiency proof uses finite displacement moments and no critical law. -/
theorem order_optimal_iff_finite {N : ℕ → ℕ} (w : ∀ i, LegalThreePassPair (N i)) :
    BddAbove (range fun i => normCost (w i)) ↔ controlledScales w := by
  refine ⟨controlledScales_of_bounded w,?_⟩
  rintro ⟨L,D,lp,bounds⟩
  let A := max 1 L
  have a1 : 1≤A := le_max_left ..
  have al : L≤A := le_max_right ..
  refine ⟨5*A^2+2*(D:ℝ),?_⟩
  rintro _ ⟨i,rfl⟩
  let n := N i
  let h := (w i).val.1.val
  let g := (w i).val.2.val
  let s := Real.sqrt (n:ℝ)
  let t := Real.sqrt s
  have gh : g<h := (w i).property.2
  have hg : 2≤g := (w i).property.1
  have hn : h<n := (w i).val.1.isLt
  have np : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have sp : 0<s := Real.sqrt_pos.2 np
  have tp : 0<t := Real.sqrt_pos.2 sp
  obtain ⟨bd,⟨hlo,hhi⟩,⟨glo,ghi⟩⟩ := bounds i
  change 1/L ≤ (h:ℝ)/s at hlo; change (h:ℝ)/s ≤ L at hhi
  change 1/L ≤ (g:ℝ)/t at glo; change (g:ℝ)/t ≤ L at ghi
  have lower {k : ℕ} {z : ℝ} (zp : 0<z) (u : 1/L ≤ (k:ℝ)/z) :
      z ≤ A*k := by
    have v := (div_le_div_iff₀ lp zp).mp u
    exact (by linarith : z ≤ L*k).trans (mul_le_mul_of_nonneg_right al (Nat.cast_nonneg _))
  have upper {k : ℕ} {z : ℝ} (zp : 0<z) (u : (k:ℝ)/z ≤ L) :
      (k:ℝ) ≤ A*z := (div_le_iff₀ zp).mp (u.trans al)
  have f := threePass_cost_controlled_scales n h g hn gh hg A a1 (lower sp hlo) (upper sp hhi)
    (lower tp glo) (upper tp ghi)
  change _ / ((n:ℝ)*s) ≤ _
  apply (div_le_iff₀ (mul_pos np sp)).mpr
  have ds : (Nat.gcd h g:ℝ) ≤ D := by exact_mod_cast bd
  apply f.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (mul_pos np sp).le
  linarith

/-- The same finite family criterion for actual ordinary linear-insertion
comparisons, using the per-input terminating-comparison bound. -/
theorem comparison_order_optimal_iff_finite {N : ℕ → ℕ} (w : ∀ i, LegalThreePassPair (N i)) :
    BddAbove (range fun i => threePassPairMeanComparisons (w i)/((N i:ℝ)*Real.sqrt (N i))) ↔
      controlledScales w := by
  let C i := threePassPairMeanComparisons (w i)/((N i:ℝ)*Real.sqrt (N i))
  have estimates (i) : normCost (w i) ≤ C i ∧ C i ≤ normCost (w i)+3 := by
    have hg := (w i).property
    have np : (0:ℝ)<N i := by exact_mod_cast (show 0<N i by have := (w i).val.1.isLt; omega)
    have sp := Real.sqrt_pos.2 np
    have one : 1 ≤ Real.sqrt (N i:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1≤N i by
      have := (w i).val.1.isLt; omega))
    have bounds := uniform_threePassComparisonCost_bounds (N i) (w i).val.1.val (w i).val.2.val
      (by omega) (by omega)
    change threePassPairMeanShifts (w i) ≤ threePassPairMeanComparisons (w i) ∧
      threePassPairMeanComparisons (w i) ≤ threePassPairMeanShifts (w i)+3*N i at bounds
    refine ⟨div_le_div_of_nonneg_right bounds.1 (mul_pos np sp).le,?_⟩
    change _ / _ ≤ _ / _+3
    apply (div_le_iff₀ (mul_pos np sp)).mpr
    rw [add_mul,div_mul_cancel₀ _ (mul_pos np sp).ne']
    have scale := mul_le_mul_of_nonneg_left one (show (0:ℝ)≤3*(N i:ℝ) by positivity)
    nlinarith only [bounds.2,scale]
  rw [← order_optimal_iff_finite w]
  constructor
  · rintro ⟨M,upper⟩
    exact ⟨M,fun _ ⟨i,e⟩ => e ▸ (estimates i).1.trans (upper (mem_range_self i))⟩
  · rintro ⟨M,upper⟩
    refine ⟨M+3,?_⟩
    rintro _ ⟨i,rfl⟩
    exact (estimates i).2.trans (add_le_add (upper (mem_range_self i)) le_rfl)

end Shellsort.F09
