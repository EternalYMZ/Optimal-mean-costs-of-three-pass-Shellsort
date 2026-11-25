import Shellsort.F09OptimalLimit

/-! The order criterion for every legal family. A rectangular upper and lower
bound on the normalized coordinates is the usual pair of Θ scale conditions. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology Set
def controlledScales {N : ℕ → ℕ} (w : ∀ i, LegalThreePassPair (N i)) : Prop :=
  ∃ (L : ℝ) (D : ℕ), 0 < L ∧ ∀ i, divisor (w i) ≤ D ∧
    scaleA (w i) ∈ Icc (1/L) L ∧ scaleB (w i) ∈ Icc (1/L) L

theorem controlledScales_of_bounded {N : ℕ → ℕ} (w : ∀ i, LegalThreePassPair (N i))
    (budget : BddAbove (range fun i => normCost (w i))) : controlledScales w := by
  obtain ⟨T,upper⟩ := budget
  let C := max 1 T
  have cp : 0<C := zero_lt_one.trans_le (le_max_left ..)
  obtain ⟨L,one,rect⟩ := threePass_budget_rectangle C cp
  have lp : 0 < L := zero_lt_one.trans_le one
  refine ⟨L,⌈1+(2048*C)^2⌉₊,lp,?_⟩
  intro i
  let n := N i
  let h := (w i).val.1.val
  let g := (w i).val.2.val
  have hn : h<n := (w i).val.1.isLt
  have gh : g<h := (w i).property.2
  have lg : 2≤g := (w i).property.1
  have np : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have sp := Real.sqrt_pos.mpr np
  have rp := Real.sqrt_pos.mpr sp
  have bd : normCost (w i) ≤ C := (upper (mem_range_self _)).trans (le_max_right ..)
  have cost := (div_le_iff₀ (mul_pos np sp)).mp bd
  rw [← mul_assoc] at cost
  obtain ⟨a,b,c,d⟩ := rect n h g hn gh lg cost
  have dc : (Nat.gcd h g:ℝ) ≤ 1+(2048*C)^2 := by
    by_cases two : 2 ≤ Nat.gcd h g
    · have k := threePass_common_divisor_budget n h g (Nat.gcd h g) hn gh lg two
        (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..) C cost
      have sq := mul_self_le_mul_self (Real.sqrt_nonneg _) k
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (Nat.gcd h g))]
    · have le : (Nat.gcd h g:ℝ) ≤ 1 := by exact_mod_cast (show Nat.gcd h g ≤ 1 by omega)
      nlinarith [sq_nonneg (2048*C)]
  exact ⟨by exact_mod_cast dc.trans (Nat.le_ceil _),
    ⟨(div_le_div_iff₀ lp sp).2 (by linarith),(div_le_iff₀ sp).2 b⟩,
    ⟨(div_le_div_iff₀ lp rp).2 (by linarith),(div_le_iff₀ rp).2 d⟩⟩

end Shellsort.F09
end
