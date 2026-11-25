import Shellsort.ThreePassRefinedUpper

/-! Finite versions of the gap-scale tests for a fixed three-pass word, applied
to successful right shifts on the actual uniform process. -/
noncomputable section
namespace Shellsort
open Filter Topology

/-- The first-pass cost and its remaining transport give two necessary scale
bounds even when the two initial gaps share divisors. -/
theorem threePass_gap_lower_scales (n h g : ℕ) (hhn : h < n) (hgh : g < h) (hg : 2 ≤ g)
    (K : ℝ) (budget : uniformAverage (fun p : RankPlacement n =>
      (threePassInsertionCost p h g (by omega) (by omega) : ℝ)) ≤ K*n*Real.sqrt n) :
    Real.sqrt n ≤ (4*K+1)*h ∧ Real.sqrt h ≤ 2048*K*g := by
  have np : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have gp : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have rs := Real.sq_sqrt np.le
  have sone : 1 ≤ Real.sqrt (n:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ n by omega))
  constructor
  · have first := (uniform_threePassInsertionCost_lower n h g (by omega) (by omega)).trans budget
    have f := (div_le_iff₀ (by positivity : 0 < 4*(h:ℝ))).mp (sub_le_iff_le_add.mp first)
    have cancelled : (n:ℝ) ≤ 4*K*Real.sqrt n*h + h := by
      apply le_of_mul_le_mul_left (a := (n:ℝ)) _ np
      linarith
    apply le_of_mul_le_mul_left (a := Real.sqrt (n:ℝ)) _ (Real.sqrt_pos.2 np)
    nlinarith [mul_le_mul_of_nonneg_right sone hp.le]
  · have state := (uniform_onePass_footrule_fluctuation_lower n h (by omega) hhn.le).trans
      (uniform_threePass_checkpoint_transport n h g (by omega) (by omega)).1
    have capped := state.trans (mul_le_mul_of_nonneg_left budget (by positivity))
    rw [Real.sqrt_mul np.le] at capped
    apply le_of_mul_le_mul_left (a := (n:ℝ)*Real.sqrt n) _ (by positivity)
    linarith

/-- For a coprime pair, final-pass fluctuations bound the product
`g * sqrt h` on the same execution that satisfies the cost budget. -/
theorem threePass_coprime_product_budget (n h g : ℕ) (hhn : h < n) (hgh : g < h) (hg : 2 ≤ g)
    (cop : Nat.Coprime h g) (K : ℝ)
    (budget : uniformAverage (fun p : RankPlacement n =>
      (threePassInsertionCost p h g (by omega) (by omega) : ℝ)) ≤ K*n*Real.sqrt n) :
    (g:ℝ)*Real.sqrt h ≤ max (32000*K) ((32000*K)^2)*Real.sqrt n := by
  have np : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (0:ℝ) ≤ h := Nat.cast_nonneg _
  have gp : (0:ℝ) ≤ g := Nat.cast_nonneg _
  have arc := uniform_finalInsertionCost_arc_lower n h g hhn.le hgh.le hg cop
  have final_le := uniformAverage_mono _ _ (fun p : RankPlacement n =>
    (show (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ) ≤
        (threePassInsertionCost p h g (by omega) (by omega) : ℝ) by
      simp only [threePassInsertionCost, Nat.cast_add]
      linarith [Nat.cast_nonneg (α := ℝ) (gapInsertionCost p h (by omega)),
        Nat.cast_nonneg (α := ℝ) (gapInsertionCost (gapSort p h) g (by omega))]))
  have lim := arc.trans (final_le.trans budget)
  have rounded := arc_scale_rounding n h g (by omega) hhn.le (by omega)
  have scaled := mul_le_mul_of_nonneg_left rounded np.le
  have bound : min ((g:ℝ)*Real.sqrt h) (Real.sqrt g * Real.sqrt (Real.sqrt ((n:ℝ)*h))) ≤
      32000*K*Real.sqrt n := by
    apply le_of_mul_le_mul_left (a := (n:ℝ)) _ np
    linarith
  rcases (min_le_iff.mp bound) with small | large
  · exact small.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.sqrt_nonneg _))
  · have squared := mul_self_le_mul_self (by positivity) large
    have ident : (Real.sqrt g * Real.sqrt (Real.sqrt ((n:ℝ)*h)))^2 =
        (g:ℝ)*Real.sqrt n*Real.sqrt h := by
      rw [mul_pow, Real.sq_sqrt gp, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_mul np.le]
      ring
    have b : (g:ℝ)*Real.sqrt h ≤ (32000*K)^2*Real.sqrt n := by
      apply le_of_mul_le_mul_left (a := Real.sqrt (n:ℝ)) _ (Real.sqrt_pos.2 np)
      nlinarith only [ident, squared]
    exact b.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.sqrt_nonneg _))

/-- Explicit compact bounds on both normalized gaps for every coprime word
whose actual uniform shift mean is within the indicated budget. -/
theorem threePass_coprime_gap_scales (n h g : ℕ) (hhn : h < n) (hgh : g < h) (hg : 2 ≤ g)
    (cop : Nat.Coprime h g) (K : ℝ) (kp : 0 < K)
    (budget : uniformAverage (fun p : RankPlacement n =>
      (threePassInsertionCost p h g (by omega) (by omega) : ℝ)) ≤ K*n*Real.sqrt n) :
    let U := max (32000*K) ((32000*K)^2)
    let D := Real.sqrt (4*K+1)
    let t := Real.sqrt (Real.sqrt (n:ℝ))
    Real.sqrt n ≤ (4*K+1)*h ∧ (h:ℝ) ≤ 2048*K*U*Real.sqrt n ∧
      t ≤ D*(2048*K)*g ∧ (g:ℝ) ≤ D*U*t := by
  dsimp only
  have ⟨first, shiftBound⟩ := threePass_gap_lower_scales n h g hhn hgh hg K budget
  have prod := threePass_coprime_product_budget n h g hhn hgh hg cop K budget
  have root := Real.sqrt_le_sqrt first
  rw [Real.sqrt_mul (by positivity : 0 ≤ 4*K+1)] at root
  have hp := Real.sq_sqrt (Nat.cast_nonneg h : (0:ℝ) ≤ h)
  have t2 := Real.sq_sqrt (Real.sqrt_nonneg (n:ℝ))
  have np : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨first, ?_, ?_, ?_⟩
  · have a := mul_le_mul_of_nonneg_right shiftBound (Real.sqrt_nonneg (h:ℝ))
    have b := mul_le_mul_of_nonneg_left prod (show 0 ≤ 2048*K by positivity)
    nlinarith only [hp, a, b]
  · have a := root.trans (mul_le_mul_of_nonneg_left shiftBound (Real.sqrt_nonneg _))
    linarith
  · have a := mul_le_mul_of_nonneg_left root (Nat.cast_nonneg g : (0:ℝ) ≤ g)
    have b := mul_le_mul_of_nonneg_left prod (Real.sqrt_nonneg (4*K+1))
    apply le_of_mul_le_mul_right (a := Real.sqrt (Real.sqrt (n:ℝ))) _ (by positivity)
    rw [mul_assoc, ← sq, t2]
    linarith

/-- Conversely, a single factor bounding both normalized gaps suffices for
the optimal order for every coprime word in that range. -/
theorem threePass_coprime_cost_of_gap_scales (n h g : ℕ) (hhn : h < n) (hgh : g < h) (hg : 2 ≤ g)
    (cop : Nat.Coprime h g) (L : ℝ) (bound : 1 ≤ L)
    (hlo : Real.sqrt n ≤ L*h) (hhi : (h:ℝ) ≤ L*Real.sqrt n)
    (glo : Real.sqrt (Real.sqrt n) ≤ L*g) (ghi : (g:ℝ) ≤ L*Real.sqrt (Real.sqrt n)) :
    uniformAverage (fun p : RankPlacement n =>
        (threePassInsertionCost p h g (by omega) (by omega) : ℝ)) ≤ 5*L^2*n*Real.sqrt n ∧
    uniformAverage (fun p : RankPlacement n =>
        (threePassComparisonCost p h g (by omega) (by omega) : ℝ)) ≤ 8*L^2*n*Real.sqrt n := by
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
  have total := uniform_threePassInsertionCost_upper n h g (by omega) (by omega) cop
  have c := (uniform_threePassComparisonCost_bounds n h g (by omega) (by omega)).2
  have lbudget := mul_le_mul_of_nonneg_right Lsq (show 0 ≤ n*s by positivity)
  have baseline := mul_le_mul_of_nonneg_left so np.le
  have l₁ := mul_le_mul_of_nonneg_right (bound.trans Lsq) (show 0 ≤ n*s by positivity)
  change _ ≤ 5*L^2*n*s ∧ _ ≤ 8*L^2*n*s
  constructor <;> nlinarith only [f, m, last, total, c, lbudget, baseline, l₁]

/-- How much a fixed legal word loses relative to the optimal word can be
measured in either shifts or comparisons. The two regrets differ by at most
three linear scans even if the optimizers are different words. -/
theorem threePass_regret_difference (n : ℕ) (hn : 16 ≤ n) (w : LegalThreePassPair n) :
    |(threePassPairMeanComparisons w - optimalThreePassMeanComparisons n hn) -
      (threePassPairMeanShifts w - optimalThreePassMeanShifts n hn)| ≤ 3*n := by
  have hw := w.property
  have perWord := uniform_threePassComparisonCost_bounds n w.val.1.val w.val.2.val
      (by omega) (by omega)
  change threePassPairMeanShifts w ≤ threePassPairMeanComparisons w ∧
    threePassPairMeanComparisons w ≤ threePassPairMeanShifts w + 3*n at perWord
  obtain ⟨lo, hi⟩ := optimal_threePass_mean_difference n hn
  rw [abs_le]
  constructor <;> linarith [perWord.1, perWord.2]

/-- Asymptotic near-optimality in the critical normalization is identical
for the two separately optimized costs, on any diverging size sequence. -/
theorem threePass_nearOptimal_cost_iff (N : ℕ → ℕ) (hn : ∀ i, 16 ≤ N i)
    (grow : Tendsto N atTop atTop) (w : ∀ i, LegalThreePassPair (N i)) :
    Tendsto (fun i => (threePassPairMeanComparisons (w i)-optimalThreePassMeanComparisons _ (hn i)) /
      ((N i:ℝ)*Real.sqrt (N i))) atTop (𝓝 0) ↔
    Tendsto (fun i => (threePassPairMeanShifts (w i)-optimalThreePassMeanShifts _ (hn i)) /
      ((N i:ℝ)*Real.sqrt (N i))) atTop (𝓝 0) := by
  let C i := (threePassPairMeanComparisons (w i)-optimalThreePassMeanComparisons _ (hn i)) /
    ((N i:ℝ)*Real.sqrt (N i))
  let M i := (threePassPairMeanShifts (w i)-optimalThreePassMeanShifts _ (hn i)) /
    ((N i:ℝ)*Real.sqrt (N i))
  change Tendsto C _ _ ↔ Tendsto M _ _
  have roots : Tendsto (fun i => Real.sqrt (N i:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)
  have err : Tendsto (fun i => C i - M i) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun i => 3/Real.sqrt (N i))
      (fun i => ?_) (tendsto_const_nhds.div_atTop roots)
    have np : 0 < (N i:ℝ) := by exact_mod_cast (show 0 < N i by have := hn i; omega)
    simp only [C, M, ← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos np (Real.sqrt_pos.2 np))]
    calc
      _ ≤ (3*(N i:ℝ))/((N i:ℝ)*Real.sqrt (N i)) :=
        div_le_div_of_nonneg_right (threePass_regret_difference _ (hn i) (w i)) (by positivity)
      _ = _ := by field_simp
  constructor
  · intro h
    simpa using h.sub err
  · intro h
    simpa using err.add h

/-- First term of the critical variational cost. Convergence of the first
normalized gap alone determines its executed first-pass contribution. -/
theorem threePass_critical_firstPass_limit (N h : ℕ → ℕ) (grow : Tendsto N atTop atTop)
    (hh : ∀ i, 0 < h i) (a : ℝ) (ap : 0 < a)
    (scale : Tendsto (fun i => (h i:ℝ)/Real.sqrt (N i)) atTop (𝓝 a)) :
    Tendsto (fun i => uniformAverage (fun p : RankPlacement (N i) =>
      (gapInsertionCost p (h i) (hh i) : ℝ)) / ((N i:ℝ)*Real.sqrt (N i)))
      atTop (𝓝 (1/(4*a))) := by
  let s i := Real.sqrt (N i:ℝ)
  have roots : Tendsto s atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)
  have base : Tendsto (fun i => 1/(4*((h i:ℝ)/s i))) atTop (𝓝 (1/(4*a))) :=
    tendsto_const_nhds.div (scale.const_mul 4) (by positivity)
  have error : Tendsto (fun i => (1/4:ℝ)/s i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop roots
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [sub_zero] using base.sub error) base
  all_goals
    filter_upwards [grow.eventually_ge_atTop 1] with i ni
    have np : (0:ℝ) < N i := by exact_mod_cast ni
    have sp : 0 < s i := Real.sqrt_pos.2 np
    have hp : (0:ℝ) < h i := by exact_mod_cast hh i
    have hp₂ : s i^2 = N i := Real.sq_sqrt np.le
    have b := uniform_firstPassCost_bounds (N i) (h i) (hh i)
    have maxId : (N i:ℝ)^2/(4*h i)/((N i:ℝ)*s i) = 1/(4*((h i:ℝ)/s i)) := by
      field_simp
      nlinarith
    have offset : ((N i:ℝ)/4)/((N i:ℝ)*s i) = (1/4:ℝ)/s i := by field_simp
  · change 1/(4*((h i:ℝ)/s i)) - (1/4:ℝ)/s i ≤ _
    rw [← maxId, ← offset, ← sub_div]
    exact div_le_div_of_nonneg_right b.1 (mul_nonneg np.le sp.le)
  · change _ ≤ 1/(4*((h i:ℝ)/s i))
    rw [← maxId]
    exact div_le_div_of_nonneg_right b.2 (mul_nonneg np.le sp.le)

end Shellsort
end
