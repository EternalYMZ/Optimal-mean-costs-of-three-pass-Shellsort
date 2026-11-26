import Shellsort.F09Verified

/-! Among noncoprime tables, every sufficiently large exact minimizer of either
executed counter has gcd two. The explicit separation uses positive scales,
the existing lower quadrature knots and a coarse elementary upper witness.
All inequalities and both transfers are proved in this file. -/
noncomputable section
namespace Shellsort.F09
open Real Set MeasureTheory Filter Topology

private theorem B_one_upper_coarse : B 1 ≤ (282096:ℝ)/1000000 := by
  have wm (x : ℝ) : W x ≤ 1/12 := by
    unfold W
    exact sub_le_self _ (mul_nonneg (by positivity) (tsum_nonneg (fun _ => by positivity)))
  let f := fun t : ℝ => t - t^2 + 1/3
  have it : IntervalIntegrable f volume 0 1 := (by unfold f; fun_prop : Continuous f).intervalIntegrable _ _
  have upper := intervalIntegral.integral_mono_on (zero_le_one' ℝ) (scaled_integrable (z:=1) zero_lt_one) it
    (fun t ht => show scaled 1 t ≤ f t from by
      rw [scaled_eq (by norm_num)]
      norm_num
      have vv : 0 ≤ v t := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
      have nn := add_nonneg vv (W_nonneg vv)
      have ss := Real.sq_sqrt nn
      dsimp [f]
      have vv' : v t = t-t^2 := by unfold v; ring
      nlinarith only [ss,sq_nonneg (Real.sqrt (v t + W (v t)) - 1/2),wm (v t),vv'])
  have fi : (∫ t in (0:ℝ)..1, f t) = 1/2 := by
    unfold f
    rw [intervalIntegral.integral_add,intervalIntegral.integral_sub,integral_id,integral_pow,
      intervalIntegral.integral_const] <;> norm_num
  rw [fi] at upper
  simp [scaled] at upper
  have hp : (177245:ℝ)/100000 ≤ Real.sqrt Real.pi := Real.le_sqrt_of_sq_le (by linarith [Real.pi_gt_d6])
  unfold B L
  simp only [one_pow,div_one,one_mul]
  rw [div_le_iff₀ (Real.sqrt_pos.2 Real.pi_pos)]
  linarith

theorem divisor_two_coarse_upper : reduced 2 1 < (6431:ℝ)/10000 := by
  have ju := J_universal_upper (lam:=1) (by norm_num)
  have js : (250662:ℝ)/100000 ≤ Real.sqrt (2*Real.pi) := Real.le_sqrt_of_sq_le (by linarith [Real.pi_gt_d6])
  have j : J 1 ≤ 156665/1000000 := ju.trans ((div_le_iff₀ (by positivity)).2 (by linarith [Real.pi_lt_d6]))
  have rt : (141421:ℝ)/100000 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  unfold reduced H
  norm_num only [Nat.cast_ofNat,one_pow,div_one,one_mul,show (2:ℝ)-1=1 by norm_num]
  rw [div_lt_iff₀ (by positivity)]
  linarith [sqrt_c_bounds.2,B_one_upper_coarse]

private theorem B_at_anchor {z k u q : ℝ} (zp : 0 < z) (up : 0 ≤ u) (small : u ≤ 18/(4*z^2))
    (heat : q ≤ (1-1/(1+u)^2)/12) (factor : k^2 ≤ 1+4*z^2*q) :
    k*c ≤ B z := by
  have bound : q ≤ W (1/(4*z^2)) :=
    heat.trans (W_rational_lower (by positivity) up
      (small.trans_eq (show 18/(4*z^2) = 18*(1/(4*z^2)) by ring)))
  let f := fun t : ℝ => k * Real.sqrt (v t)
  have fi : IntervalIntegrable f volume 0 1 := (by unfold f v; fun_prop : Continuous f).intervalIntegrable _ _
  have lower := intervalIntegral.integral_mono_on (zero_le_one' ℝ) fi (scaled_integrable zp)
    (fun t ht => show f t ≤ scaled z t from by
      rw [scaled_eq zp]
      have vv : 0 ≤ v t := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
      have mx : 4*v t ≤ 1 := by unfold v; nlinarith [sq_nonneg (2*t-1)]
      have hs := W_scale (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) vv) mx (by positivity : 0 ≤ 1/(4*z^2))
      have alg : 4*v t*(1/(4*z^2)) = 1/z^2*v t := by ring
      rw [alg] at hs
      have inequality := (mul_le_mul_of_nonneg_left bound (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) vv)).trans hs
      apply Real.le_sqrt_of_sq_le
      simp only [f,mul_pow,Real.sq_sqrt vv]
      nlinarith only [mul_le_mul_of_nonneg_left inequality (sq_nonneg z),
        mul_le_mul_of_nonneg_right factor vv])
  dsimp [f] at lower
  rw [intervalIntegral.integral_const_mul,integral_sqrt_v] at lower
  unfold scaled at lower
  rw [intervalIntegral.integral_const_mul] at lower
  unfold B L
  rw [← mul_div_assoc,le_div_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
  change _ ≤ z * _
  apply le_trans _ lower
  unfold c
  nlinarith only [congrArg (fun x:ℝ => k*x) (Real.sq_sqrt Real.pi_pos.le)]

private theorem B_left_lower : (2295:ℝ)/10000 ≤ B (12/25) := by
  have h := B_at_anchor (z:=12/25) (k:=1036/1000) (u:=18) (q:=83/1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith [c_lower]

private theorem B_half_lower : (2305:ℝ)/10000 ≤ B (1/2) := by
  have h := B_at_anchor (z:=1/2) (k:=10405/10000) (u:=18) (q:=83/1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith [c_lower]

private theorem B_seven_eighths_lower : (2476:ℝ)/10000 ≤ B (7/8) := by
  have h := B_at_anchor (z:=7/8) (k:=11178/10000) (u:=58/10) (q:=815/10000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith [c_lower]

private theorem J_middle {z : ℝ} (hz : (1/2:ℝ) ≤ z) (hr : z ≤ 1) :
    (1536:ℝ)/10000 ≤ J (1/z^2) := by
  have hlo := verifiedQuadratureBounds.j1
  have hhi := verifiedQuadratureBounds.j1_2
  norm_num at hlo hhi
  have zp : 0 < z := by linarith
  have xx : 1/z^2 ∈ Icc (1:ℝ) 4 := by
    constructor
    · rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ 1+z by linarith)]
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ z+1/2 by linarith)]
  rw [← segment_eq_Icc (by norm_num : (1:ℝ) ≤ 4)] at xx
  obtain ⟨a,b,ha,hb,hs,hx⟩ := xx
  have h := J_concave.2 (show (1:ℝ) ∈ Ici 0 by norm_num) (show (4:ℝ) ∈ Ici 0 by norm_num) ha hb hs
  simp only [smul_eq_mul] at h hx
  rw [← hx]
  linarith [mul_le_mul_of_nonneg_left (show (1536:ℝ)/10000 ≤ J 1 by linarith) ha,
    mul_le_mul_of_nonneg_left (show (1536:ℝ)/10000 ≤ J 4 by linarith) hb]

private theorem H_middle {z u k : ℝ} (hz : (1/2:ℝ) ≤ z) (hzu : z ≤ u) (hu : u ≤ 1)
    (kp : 0 ≤ k) (kc : k^2*u ≤ c)
    (margin : 2*k*(1536/10000)+(1536/10000)^2 ≤ k^2) :
    k + (1536/10000)*u ≤ H z := by
  let j : ℝ := 1536/10000
  have jp : 0 ≤ j := by norm_num [j]
  have zp : 0 < z := by linarith
  have zu : 0 ≤ u-z := sub_nonneg.mpr hzu
  have bound : 2*z*k*j + z*j^2*(u-z) ≤ k^2 := by
    calc _ ≤ 2*1*k*j + 1*j^2*1 := by gcongr <;> linarith
         _ ≤ _ := by dsimp [j]; linarith
  have sq : (k+j*(u-z))^2 ≤ c/z := by
    apply (le_div_iff₀ zp).2
    nlinarith only [kc,mul_nonneg zu (sub_nonneg.mpr bound)]
  have root := Real.le_sqrt_of_sq_le sq
  have jbound := mul_le_mul_of_nonneg_left (J_middle hz (hzu.trans hu)) zp.le
  unfold H
  dsimp [j] at root
  linarith

private theorem reduced_cell {d : ℕ} {z h b : ℝ} (hd : 3 ≤ d) (hh : h ≤ H z) (hb : b ≤ B z)
    (bpos : 0 ≤ b) (slope : 646/1000 ≤ (3464/1000)*b)
    (atThree : (646/1000)*(173206/100000) ≤ h+2*b) :
    (646:ℝ)/1000 ≤ reduced d z := by
  have dr : (3:ℝ) ≤ d := by exact_mod_cast hd
  have dp : 0 < (d:ℝ) := by linarith
  let s := Real.sqrt (d:ℝ)
  let u := Real.sqrt 3
  have ss : s^2 = d := Real.sq_sqrt dp.le
  have us : u^2 = 3 := Real.sq_sqrt (by norm_num)
  have usl : (1732:ℝ)/1000 ≤ u := Real.le_sqrt_of_sq_le (by norm_num)
  have usu : u ≤ (173206:ℝ)/100000 := Real.sqrt_le_iff.2 ⟨by norm_num,by norm_num⟩
  have su : u ≤ s := Real.sqrt_le_sqrt dr
  have coef : 0 ≤ b*(s+u)-646/1000 := by linarith [mul_le_mul_of_nonneg_left (show 3464/1000 ≤ s+u by linarith) bpos]
  have inc := mul_nonneg (sub_nonneg.mpr su) coef
  have cb := mul_le_mul_of_nonneg_left hb (show 0 ≤ (d:ℝ)-1 by linarith)
  unfold reduced
  rw [le_div_iff₀ (Real.sqrt_pos.mpr dp)]
  change _ * s ≤ _
  nlinarith only [hh,cb,inc,atThree,usu,congrArg (fun x:ℝ => b*x) ss,
    congrArg (fun x:ℝ => b*x) us]

theorem all_larger_divisors_coarse_lower (d : ℕ) (hd : 3 ≤ d) (z : ℝ) (hz : 0 < z) :
    (646:ℝ)/1000 ≤ reduced d z := by
  by_cases small : z ≤ 12/25
  · have hs : (679:ℝ)/1000 ≤ H z := by
      unfold H
      have sq : ((679:ℝ)/1000)^2 ≤ c/z := (le_div_iff₀ hz).2 (by linarith [c_lower])
      apply (Real.le_sqrt_of_sq_le sq).trans
      exact le_add_of_nonneg_right (mul_nonneg hz.le (J_nonneg _))
    apply reduced_cell hd hs (show (22155:ℝ)/100000 ≤ B z by linarith [c_lower,c_le_B hz]) <;> norm_num
  have bleft := B_left_lower.trans (B_monotone (show (12/25:ℝ) ∈ Ioi 0 by norm_num) hz (le_of_not_ge small))
  by_cases hhalf : z ≤ 1/2
  · apply reduced_cell hd (H_small hz hhalf) bleft <;> norm_num
  have ha : (1/2:ℝ) ≤ z := le_of_not_ge hhalf
  by_cases hmid : z ≤ 3/4
  · have hh := H_middle (k:=5435/10000) ha hmid (by norm_num) (by norm_num) (by linarith [c_lower]) (by norm_num)
    apply reduced_cell hd hh (B_half_lower.trans (B_monotone (by norm_num) hz ha)) <;> norm_num
  have hb : (3/4:ℝ) ≤ z := le_of_not_ge hmid
  by_cases h7 : z ≤ 7/8
  · have hh := H_middle (k:=503/1000) ha h7 (by norm_num) (by norm_num) (by linarith [c_lower]) (by norm_num)
    apply reduced_cell hd hh (B_three_quarters.trans (B_monotone (by norm_num) hz hb)) <;> norm_num
  by_cases hone : z ≤ 1
  · have hh := H_middle (k:=47069/100000) ha hone (by norm_num) (by norm_num) (by linarith [c_lower]) (by norm_num)
    apply reduced_cell hd hh (B_seven_eighths_lower.trans (B_monotone (by norm_num) hz (le_of_not_ge h7))) <;> norm_num
  apply reduced_cell hd (H_lower verifiedQuadratureBounds hz) (B_one.trans
    (B_monotone (by norm_num) hz (le_of_not_ge hone))) <;> norm_num

private theorem divisor_three_floor :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ w : LegalThreePassPair n, 3 ≤ divisor w →
      (6435:ℝ)/10000 ≤ normCost w ∧ (6435:ℝ)/10000 ≤ normComparisons w := by
  suffices sh : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ w : LegalThreePassPair n, 3 ≤ divisor w →
      (6435:ℝ)/10000 ≤ normCost w by
    obtain ⟨n₀, floor⟩ := sh
    refine ⟨n₀, fun n large w hd => ⟨floor n large w hd, (floor n large w hd).trans ?_⟩⟩
    have legal := w.property
    have c := uniform_threePassComparisonCost_bounds n w.val.1.val w.val.2.val
      (by omega) (by omega)
    exact div_le_div_of_nonneg_right c.1 (by positivity)
  by_contra! bad
  choose N ge w large cheap using bad
  obtain ⟨d,a,b,φ,hd,ha,hb,inc,gd,al,bl⟩ := budget_convergent_subsequence N w 1 zero_lt_one
    (fun i => by linarith [cheap i])
  have grow : Tendsto N atTop atTop := tendsto_atTop_mono ge tendsto_id
  have limit := actual_threePass_critical_law (N ∘ φ) (fun i => w (φ i)) d a b
    (grow.comp inc.tendsto_atTop) hd ha hb gd al bl
  obtain ⟨i, eq⟩ := gd.exists
  have big : 3 ≤ d := eq ▸ large (φ i)
  have floor := (K_lowerBounds hd _).2 (all_larger_divisors_coarse_lower d big) a b ha hb
  have upper : K d a b ≤ (6435:ℝ)/10000 := le_of_tendsto' limit (fun j => (cheap (φ j)).le)
  linarith

/-- At every sufficiently large size there is a single divisor-two table
whose two executed means are strictly lower than those of *every* table with
divisor at least three. -/
theorem verified_divisor_two_dominates :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ v : LegalThreePassPair n, divisor v = 2 ∧
      ∀ w : LegalThreePassPair n, 3 ≤ divisor w →
        threePassPairMeanShifts v < threePassPairMeanShifts w ∧
        threePassPairMeanComparisons v < threePassPairMeanComparisons w := by
  obtain ⟨n₁, floor⟩ := divisor_three_floor
  obtain ⟨a,b,ha,hb,_,eq⟩ := (K_slice (d := 2) (z := 1) (by decide) (by norm_num)).1
  let N (i : ℕ) := i + 16
  have grow : Tendsto N atTop atTop := tendsto_atTop_mono (fun i => by dsimp [N]; omega) tendsto_id
  obtain ⟨v,gd,al,bl⟩ := recovery_family N (fun i => by dsimp [N]; omega) grow 2 (by decide) a b ha hb
  have sh := actual_threePass_critical_law N v 2 a b grow (by decide) ha hb gd al bl
  have co := fixed_divisor_comparison_limit actual_threePass_critical_law N v 2 a b grow
    (by decide) ha hb gd al bl
  have gap : K 2 a b < (6435:ℝ)/10000 := by linarith [divisor_two_coarse_upper]
  obtain ⟨i₀, good⟩ := eventually_atTop.1 (gd.and
    ((sh.eventually_lt_const gap).and (co.eventually_lt_const gap)))
  refine ⟨max n₁ (i₀+16), fun n large => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = N i := ⟨n-16, by dsimp [N]; omega⟩
  obtain ⟨gcd,shcheap,cocheap⟩ := good i (by dsimp [N] at large; omega)
  refine ⟨v i, gcd, fun w hd => ?_⟩
  obtain ⟨shfloor,cofloor⟩ := floor (N i) (by omega) w hd
  exact ⟨lt_of_not_ge (fun h => (not_le_of_gt (shcheap.trans_le shfloor))
    (div_le_div_of_nonneg_right h (by positivity))),
    lt_of_not_ge (fun h => (not_le_of_gt (cocheap.trans_le cofloor))
    (div_le_div_of_nonneg_right h (by positivity)))⟩

/-- Includes all ties and minimization of either counter separately. -/
theorem verified_noncoprime_minimizers_divisor_two :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ w : LegalThreePassPair n, 2 ≤ divisor w →
      ((∀ v : LegalThreePassPair n, 2 ≤ divisor v → threePassPairMeanShifts w ≤ threePassPairMeanShifts v) ∨
       (∀ v : LegalThreePassPair n, 2 ≤ divisor v → threePassPairMeanComparisons w ≤ threePassPairMeanComparisons v)) →
      divisor w = 2 := by
  obtain ⟨n₀, dominates⟩ := verified_divisor_two_dominates
  refine ⟨n₀, fun n large w noncoprime minimal => ?_⟩
  obtain ⟨v,gd,wins⟩ := dominates n large
  by_contra ne
  obtain ⟨sh,co⟩ := wins w (by omega)
  rcases minimal with hs | hc
  · exact (not_le_of_gt sh) (hs v gd.ge)
  · exact (not_le_of_gt co) (hc v gd.ge)

#check divisor_two_coarse_upper
#check all_larger_divisors_coarse_lower
#check verified_divisor_two_dominates
#check verified_noncoprime_minimizers_divisor_two
#print axioms divisor_two_coarse_upper
#print axioms all_larger_divisors_coarse_lower
#print axioms verified_divisor_two_dominates
#print axioms verified_noncoprime_minimizers_divisor_two
end Shellsort.F09
end
