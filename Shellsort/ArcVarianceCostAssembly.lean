import Shellsort.PivotArcCostBridge
import Shellsort.CentralArcAggregation
import Shellsort.OnePassFluctuationLower

/-! Real-cost consequences of a local variance bound on central arcs.
The premise describes finite independent source chains at a central threshold. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

def centralSourceVarianceBound (n h g : ℕ) (hh : 0 < h) : Prop :=
  ∀ i : Fin n, ∀ ell ∈ centralArcLengths g, ∀ t : ℝ, 1/4 ≤ t → t ≤ 3/4 →
    let coord := positionChainEquiv n h hh i
    ∀ a, ((h:ℝ)/g*min ((min ell (g-ell):ℕ):ℝ) (Real.sqrt (n/h:ℕ)))/768 ≤
      sourceArcVariance h g (n/h) (n%h) ell coord.1 t (ownerBitCount coord.2 a)

private theorem uniformAverage_finset_sum {n : ℕ} {α : Type*} (S : Finset α)
    (F : α → RankPlacement n → ℝ) :
    uniformAverage (fun p => ∑ a ∈ S, F a p) = ∑ a ∈ S, uniformAverage (F a) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem uniform_lastCost_lower_of_sourceVariance (n h g : ℕ)
    (hh : 0 < h) (hhn : h ≤ n) (hg : 2 ≤ g) (hgh : g ≤ h) (hc : Nat.Coprime h g)
    (variance : centralSourceVarianceBound n h g hh) :
    (n:ℝ)*g*Real.sqrt ((h:ℝ)/g*min (g:ℝ) (Real.sqrt (n/h:ℕ)))/25600 ≤
      uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort (gapSort p h) g)
        1 (by decide) : ℝ)) := by
  have gp : 0 < g := by omega
  let f := fun (i : Fin n) (ell : ℕ) (p : RankPlacement n) =>
    |(taggedSubsetArcCount h g ell i (tagLowerState p i).val : ℝ) - ((h*ell/g : ℕ) : ℝ)|
  apply centralArc_double_sum_lower n g hg _ _ _ (by positivity) (Real.sqrt_nonneg _)
    (fun i ell => uniformAverage (f i ell))
  · intro i ell
    exact uniformAverage_nonneg _ (fun _ => abs_nonneg _)
  · intro i ell hl
    have valid := centralArcLengths_valid hg hl
    have mpos : 1 ≤ n/h := (Nat.le_div_iff_mul_le hh).mpr (by simpa using hhn)
    have rpos : 1 ≤ min ell (g-ell) := by omega
    have minpos : (1:ℝ) ≤ min ((min ell (g-ell):ℕ):ℝ) (Real.sqrt (n/h:ℕ)) := by
      apply le_min
      · exact_mod_cast rpos
      · exact (Real.one_le_sqrt.mpr (by exact_mod_cast mpos))
    have ratio : (1:ℝ) ≤ (h:ℝ)/g := (one_le_div (by exact_mod_cast gp)).mpr (by exact_mod_cast hgh)
    apply uniform_pivotArc_abs_lower_of_central_variance hh g ell i _ _ _ (variance i ell hl)
    simpa using mul_le_mul ratio minpos (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (h:ℝ)/g)
  · rw [← uniformAverage_const_mul]
    simp_rw [two_mul_lastCost_eq_sum_taggedArc _ h g hh gp hc]
    rw [uniformAverage_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact uniformAverage_finset_sum _ _

/-- For every preselected legal three-pass word, only the central-source
variance in the large coprime case is needed for both actual cost lower bounds. -/
theorem uniform_threePass_lower_of_sourceVariance (n h g : ℕ)
    (hhn : h < n) (hgh : g < h) (hg : 2 ≤ g)
    (variance : n < h^2 → h < g^2 → Nat.Coprime h g →
      centralSourceVarianceBound n h g (by omega)) :
    (n:ℝ)*Real.sqrt n/65536 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassInsertionCost p h g (by omega) (by omega) : ℝ)) ∧
    (n:ℝ)*Real.sqrt n/65536 ≤ uniformAverage
      (fun p : RankPlacement n => (threePassComparisonCost p h g (by omega) (by omega) : ℝ)) := by
  have hh : 0 < h := by omega
  have gp : 0 < g := by omega
  have lower := uniform_threePass_lower_of_coprime_fluctuation n h g (by omega) (by omega) hhn.le gp
    (1/65536) (by norm_num) (by norm_num) (by
      intro large long cop
      have stage := uniform_lastCost_lower_of_sourceVariance n h g hh hhn.le hg hgh.le cop
        (variance large long cop)
      have F := stage.trans (uniformAverage_mono _ _
        (fun p => ordinaryInsertionCost_le_footrule (gapSort (gapSort p h) g)))
      have rounded := mul_le_mul_of_nonneg_left
        (arc_scale_rounding n h g hh hhn.le gp) (Nat.cast_nonneg n)
      have positive : 0 ≤ (n:ℝ)*g*Real.sqrt ((h:ℝ)/g*min (g:ℝ) (Real.sqrt (n/h:ℕ))) := by positivity
      linarith)
  constructor <;> linarith [lower.1,lower.2]

end Shellsort
end
