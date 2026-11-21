import Shellsort.SourceArcBlocks
import Shellsort.CyclicArcTraceLower

/-! Unconditional lower bounds for ordinary three-pass Shellsort on uniform
permutations. The two-phase fluctuation is needed only in the coprime region. -/
noncomputable section
namespace Shellsort

/-- Actual unequal source lengths and the chosen pivot are permitted. -/
theorem centralSourceVarianceBound_coprime (n h g : ℕ)
    (hhn : h ≤ n) (hgh : g ≤ h) (hg : 2 ≤ g) (hc : Nat.Coprime h g) :
    centralSourceVarianceBound n h g (by omega) := by
  have hh : 0 < h := by omega
  have gp : 0 < g := by omega
  apply centralSourceVarianceBound_of_trace n h g hh hgh hg hc
  · intro ell he t tl tu s
    exact canonicalArcProb_half g ell (n/h) t s gp (centralArcLengths_valid hg he).2.1.le
      ⟨by linarith, by linarith⟩
  · intro ell he t tl tu
    have hm : 0 < n/h := (Nat.le_div_iff_mul_le hh).mpr (by simpa using hhn)
    exact canonicalArcTrace_lower g ell (n/h) t gp (centralArcLengths_valid hg he).1
      (centralArcLengths_valid hg he).2.1 hm tl tu

/-- Actual expected unit-pass shifts after two coprime gaps. -/
theorem uniform_finalInsertionCost_arc_lower (n h g : ℕ)
    (hhn : h ≤ n) (hgh : g ≤ h) (hg : 2 ≤ g) (hc : Nat.Coprime h g) :
    (n:ℝ)*g*Real.sqrt ((h:ℝ)/g*min (g:ℝ) (Real.sqrt (n/h:ℕ)))/25600 ≤
      uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort (gapSort p h) g)
        1 (by decide) : ℝ)) :=
  uniform_lastCost_lower_of_sourceVariance n h g (by omega) hhn hg hgh hc
    (centralSourceVarianceBound_coprime n h g hhn hgh hg hc)

/-- Each legal predetermined three-pass word on uniform permutations incurs
the stated bound in both executed insertion shifts and linear key comparisons. -/
theorem uniform_threePass_cost_lower (n h g : ℕ) (hhn : h < n) (hgh : g < h) (hg : 2 ≤ g) :
    (n:ℝ)*Real.sqrt n/65536 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassInsertionCost p h g (by omega) (by omega) : ℝ)) ∧
    (n:ℝ)*Real.sqrt n/65536 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassComparisonCost p h g (by omega) (by omega) : ℝ)) :=
  uniform_threePass_lower_of_sourceVariance n h g hhn hgh hg
    (fun _ _ hc => centralSourceVarianceBound_coprime n h g hhn.le hgh.le hg hc)

end Shellsort
end