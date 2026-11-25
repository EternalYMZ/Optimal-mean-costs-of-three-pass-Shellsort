import Shellsort.OrdinaryWordComparisons
import Shellsort.ThreePassOptimalMean

/-! Finite upper bounds for the genuine three-pass insertion process.
The second pass charges the footrules on both sides of that pass. -/
noncomputable section
namespace Shellsort

/-- Sum of both endpoint footrules bounds the physical transport, hence the shifts. -/
theorem gapInsertionCost_le_endpoint_footrules {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * (gapInsertionCost p k hk : ℝ) ≤ footrule p + footrule (gapSort p k) := by
  rw [gapInsertionCost_eq_gapInversions]
  calc
    _ ≤ (k : ℝ) * chainFootrule p k := by
      gcongr
      exact gapInversions_le_chainFootrule p k hk
    _ = transport p (gapSort p k) := (gapSort_transport_eq_mul_chainFootrule p k hk).symm
    _ ≤ _ := transport_le_footrules _ _

/-- The improved middle-pass estimate uses the actual first and second checkpoints. -/
theorem uniform_threePassInsertionCost_endpoint_upper (n h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hc : Nat.Coprime h g) :
    uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) ≤
      (n : ℝ)^2 / (4*h) +
        (n * ((h : ℝ) - 1 + Real.sqrt ((n : ℝ)*h)/2) +
          n * (((g : ℝ)-1)*Real.sqrt ((h : ℝ)+3)/2)) / g +
        n * (((g : ℝ)-1)*Real.sqrt ((h : ℝ)+3)/2) := by
  have middle := uniformAverage_mono _ _ (fun p : RankPlacement n =>
    gapInsertionCost_le_endpoint_footrules (gapSort p h) g hg)
  rw [uniformAverage_const_mul, uniformAverage_add] at middle
  have d₁ := uniform_onePass_footrule_bound n h hh
  have d₂ := uniform_twoPass_footrule_bound n h g hh hg hc
  rw [uniform_threePassInsertionCost_decomposition]
  refine add_le_add (add_le_add (uniform_firstPassCost_upper n h hh) ?_)
    (uniform_thirdPassCost_upper n h g hh hg hc)
  apply (le_div_iff₀ (by exact_mod_cast hg : 0 < (g : ℝ))).2
  rw [mul_comm]
  exact middle.trans (add_le_add d₁ d₂)

/-- Overhead beyond shifts counts at most one stopping comparison per visited slot. -/
theorem uniform_threePassComparisonCost_scan_upper (n h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) :
    uniformAverage (fun p : RankPlacement n => (threePassComparisonCost p h g hh hg : ℝ)) ≤
      uniformAverage (fun p : RankPlacement n => (threePassInsertionCost p h g hh hg : ℝ)) +
        ((n-h + (n-g) + (n-1) : ℕ) : ℝ) := by
  rw [← uniformAverage_const (n := n) ((n-h + (n-g) + (n-1) : ℕ) : ℝ), ← uniformAverage_add]
  apply uniformAverage_mono
  intro p
  have h₁ := (gapComparisonCost_scan_bounds p h hh).2
  have h₂ := (gapComparisonCost_scan_bounds (gapSort p h) g hg).2
  have h₃ := (gapComparisonCost_scan_bounds (gapSort (gapSort p h) g) 1 (by decide)).2
  unfold threePassComparisonCost threePassInsertionCost
  exact_mod_cast (show _ ≤ _ by omega : _ ≤ _)

private def relativeUpper (q s : ℝ) : ℝ :=
  s / (4*(q^2+1)) + q/s + Real.sqrt (q^2+1)/(2*q) +
    ((q-1)*Real.sqrt (q^2+4)/(2*s))*(1+1/q)

private theorem relativeUpper_large {q s : ℝ} (hq : 3 ≤ q)
    (hs : q^2 ≤ s) (ht : s ≤ (q+1)^2) : relativeUpper q s ≤ 29/15 := by
  have qp : 0 < q := by linarith
  have sp : 0 < s := (sq_pos_of_pos qp).trans_le hs
  have t₁ : s / (4*(q^2+1)) ≤ 2/5 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ 3*q-1) (by linarith : 0 ≤ q-3)]
  have t₂ : q/s ≤ 1/3 := by
    apply (div_le_iff₀ sp).2
    nlinarith [mul_nonneg qp.le (by linarith : 0 ≤ q-3)]
  have t₃ : Real.sqrt (q^2+1)/(2*q) ≤ 8/15 := by
    apply (div_le_iff₀ (by positivity)).2
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 3) hq]
  have hr : Real.sqrt (q^2+4) ≤ q+1 := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith
  have hfactor : (q-1)*Real.sqrt (q^2+4)/(2*s) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ q-1)]
  have hinv : 1/q ≤ 1/3 := (div_le_div_iff₀ qp (by norm_num)).2 (by linarith)
  have t₄ := mul_le_mul hfactor (show 1+1/q ≤ 4/3 by linarith)
    (by positivity) (by norm_num)
  unfold relativeUpper
  linarith

private theorem relativeUpper_two {s : ℝ} (hs : 4 ≤ s) (ht : s ≤ 9) :
    relativeUpper 2 s ≤ 2 ∧ relativeUpper 2 s + 3/s - 8/s^3 ≤ 5/2 := by
  have sp : 0 < s := by linarith
  have h₅ : Real.sqrt 5 ≤ 9/4 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have h₈ : Real.sqrt 8 ≤ 3 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hbound : relativeUpper 2 s ≤ s/20 + 17/4*(1/s) + 9/16 := by
    unfold relativeUpper
    norm_num
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right h₅ sp.le]
  have chord : 1/s ≤ (13-s)/36 := by
    apply (div_le_iff₀ sp).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ht)]
  constructor
  · linarith
  · rw [show 3/s = 3*(1/s) by ring]
    by_cases small : s ≤ 9/2
    · have hpow := pow_le_pow_left₀ sp.le small 3
      have credit : (3/40 : ℝ) ≤ 8/s^3 := by
        apply (le_div_iff₀ (by positivity)).2
        norm_num at hpow
        linarith
      linarith
    · have credit : 0 ≤ 8/s^3 := by positivity
      linarith

/-- Both revised upper constants hold for the same predetermined natural table
on uniform permutations of every size at least 16. -/
theorem uniform_naturalThreePass_refined_upper (n : ℕ) (hn : 16 ≤ n) :
    uniformAverage (fun p : RankPlacement n => (naturalThreePassInsertionCost hn p : ℝ)) ≤
        2 * (n : ℝ) * Real.sqrt n ∧
    uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ)) ≤
        (5/2 : ℝ) * n * Real.sqrt n := by
  let q := fourthRoot n
  let s := Real.sqrt (n : ℝ)
  have hq := fourthRoot_ge_two n hn
  change 2 ≤ q at hq
  have qp : 0 < q := by omega
  have qr : (0 : ℝ) < q := by exact_mod_cast qp
  have np : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have sp : 0 < s := Real.sqrt_pos.2 np
  have sn : s^2 = n := Real.sq_sqrt np.le
  have hₗ : (q : ℝ)^2 ≤ s := by
    have a : (q : ℝ)^4 ≤ n := by exact_mod_cast (fourthRoot_spec n).1
    nlinarith [sq_nonneg (s - (q:ℝ)^2), sq_nonneg (q:ℝ)]
  have hᵤ : s ≤ ((q : ℝ)+1)^2 := by
    have a : (n : ℝ) < ((q : ℝ)+1)^4 := by exact_mod_cast (fourthRoot_spec n).2
    nlinarith [sq_nonneg (s - ((q:ℝ)+1)^2), sq_nonneg ((q:ℝ)+1)]
  let M := uniformAverage (fun p : RankPlacement n => (naturalThreePassInsertionCost hn p : ℝ))
  let C := uniformAverage (fun p : RankPlacement n => (naturalThreePassComparisonCost hn p : ℝ))
  change M ≤ 2 * n * s ∧ C ≤ 5/2 * n * s
  have normalized : M ≤ relativeUpper q s * s^3 := by
    apply (uniform_threePassInsertionCost_endpoint_upper n (q^2+1) q
      (by positivity) qp (natural_gap_coprime q)).trans_eq
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Real.sqrt_mul np.le]
    rw [← show s = Real.sqrt (n : ℝ) from rfl, ← sn]
    unfold relativeUpper
    rw [show (q:ℝ)^2+1+3 = (q:ℝ)^2+4 by ring]
    field_simp
    ring
  have cubic : s^3 = (n : ℝ)*s := by rw [pow_succ, sn]
  have compare := uniform_threePassComparisonCost_scan_upper n (q^2+1) q (by positivity) qp
  change C ≤ M + ((n-(q^2+1) + (n-q) + (n-1) : ℕ) : ℝ) at compare
  by_cases small : q = 2
  · rw [small] at normalized hₗ hᵤ compare
    norm_num at hₗ hᵤ normalized
    have sh := relativeUpper_two hₗ hᵤ
    have scan : (n-(2^2+1) + (n-2) + (n-1) : ℕ) + 8 = 3*n := by omega
    have scanR := congrArg (fun x : ℕ => (x : ℝ)) scan
    push_cast at scanR
    constructor
    · calc
        M ≤ _ := normalized
        _ ≤ 2*s^3 := mul_le_mul_of_nonneg_right sh.1 (by positivity)
        _ = _ := by rw [cubic]; ring
    · have joined := mul_le_mul_of_nonneg_right sh.2 (show 0 ≤ s^3 by positivity)
      have identity : (relativeUpper 2 s + 3/s - 8/s^3)*s^3 =
          relativeUpper 2 s*s^3 + 3*s^2-8 := by field_simp
      rw [identity, sn] at joined
      norm_num at scanR compare
      linarith [cubic]
  · have three : (3 : ℝ) ≤ q := by exact_mod_cast (show 3 ≤ q by omega)
    have nine : 9 ≤ s := by nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 3) three]
    have cap := relativeUpper_large three hₗ hᵤ
    have m := normalized.trans (mul_le_mul_of_nonneg_right cap (show 0 ≤ s^3 by positivity))
    have slots : (n-(q^2+1) + (n-q) + (n-1) : ℕ) ≤ 3*n := by omega
    have slotsR : ((n-(q^2+1) + (n-q) + (n-1) : ℕ):ℝ) ≤ 3*(n:ℝ) := by exact_mod_cast slots
    rw [cubic] at m
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left nine np.le]

/-- The two separately optimized means inherit the revised upper constants. -/
theorem optimal_threePass_mean_refined_upper (n : ℕ) (hn : 16 ≤ n) :
    optimalThreePassMeanShifts n hn ≤ 2 * (n : ℝ) * Real.sqrt n ∧
    optimalThreePassMeanComparisons n hn ≤ (5/2 : ℝ) * n * Real.sqrt n := by
  obtain ⟨hq, hgap, hlen⟩ := natural_gap_legal n hn
  let w : LegalThreePassPair n :=
    ⟨(⟨_, hlen⟩, ⟨_, hgap.trans hlen⟩), hq, hgap⟩
  have cap := uniform_naturalThreePass_refined_upper n hn
  exact ⟨(Finset.inf'_le threePassPairMeanShifts (Finset.mem_univ w)).trans cap.1,
    (Finset.inf'_le threePassPairMeanComparisons (Finset.mem_univ w)).trans cap.2⟩

/-- Distinct minimizing tables for shifts and comparisons incur a difference
of at most three linear scans in their optimal means. -/
theorem optimal_threePass_mean_difference (n : ℕ) (hn : 16 ≤ n) :
    0 ≤ optimalThreePassMeanComparisons n hn - optimalThreePassMeanShifts n hn ∧
    optimalThreePassMeanComparisons n hn - optimalThreePassMeanShifts n hn ≤ 3*n := by
  obtain ⟨hq, hgap, hlen⟩ := natural_gap_legal n hn
  have nonempty : (Finset.univ : Finset (LegalThreePassPair n)).Nonempty :=
    ⟨⟨(⟨_, hlen⟩, ⟨_, hgap.trans hlen⟩), hq, hgap⟩, Finset.mem_univ _⟩
  have perPair (w : LegalThreePassPair n) :
      threePassPairMeanShifts w ≤ threePassPairMeanComparisons w ∧
      threePassPairMeanComparisons w ≤ threePassPairMeanShifts w + 3*n := by
    have := w.property
    exact uniform_threePassComparisonCost_bounds n _ _ (by omega) (by omega)
  unfold optimalThreePassMeanComparisons optimalThreePassMeanShifts
  obtain ⟨w, hw, hbest⟩ := Finset.exists_mem_eq_inf' nonempty threePassPairMeanShifts
  constructor
  · apply sub_nonneg.mpr
    exact Finset.le_inf' _ _ fun v hv => (Finset.inf'_le _ hv).trans (perPair v).1
  · rw [hbest]
    exact sub_le_iff_le_add'.mpr ((Finset.inf'_le _ hw).trans (perPair w).2)

/-- A necessary restriction on all three-pass schedules with a fixed cost budget.
The factor 2048 comes from the previously formalized first-pass fluctuation. -/
theorem threePass_common_divisor_budget (n h g d : ℕ) (hhn : h < n) (hgh : g < h)
    (hg : 2 ≤ g) (hd : 2 ≤ d) (hdh : d ∣ h) (hdg : d ∣ g) (K : ℝ)
    (budget : uniformAverage (fun p : RankPlacement n =>
      (threePassInsertionCost p h g (by omega) (by omega) : ℝ)) ≤ K*n*Real.sqrt n) :
    Real.sqrt d ≤ 2048*K := by
  have dlen := (Nat.le_of_dvd (by omega : 0 < h) hdh).trans hhn.le
  have lower := (uniform_onePass_footrule_fluctuation_lower n d hd dlen).trans
    (uniform_common_gap_footrule_le_twoPass n h g d hdh hdg)
  have transport := (uniform_threePass_checkpoint_transport n h g (by omega) (by omega)).2
  have bound := lower.trans (transport.trans (mul_le_mul_of_nonneg_left budget (by norm_num)))
  rw [Real.sqrt_mul (Nat.cast_nonneg n)] at bound
  have np : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply le_of_mul_le_mul_left (a := (n:ℝ)*Real.sqrt n) _ (by positivity)
  linarith

end Shellsort
end
