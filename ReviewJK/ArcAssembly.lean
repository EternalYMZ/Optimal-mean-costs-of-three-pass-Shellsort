import Shellsort.PivotArcCostBridge
import Shellsort.ActualCostComposition
import Shellsort.F09SecondBinomial

/-! The Janson–Knuth reference sum and error aggregation for the executed third pass. -/
noncomputable section
namespace Shellsort
namespace JK
open scoped BigOperators

/-- Expected absolute deviation of the sum of h−1 independent Bernoulli(ℓ/g) variables. -/
def referenceArc (h g ell : ℕ) : ℝ :=
  mean (bernoulliVectorWeight ((ell : ℝ) / g) (h - 1))
    (fun z => |(bitCount z : ℝ) - ((h * ell / g : ℕ) : ℝ)|)

/-- The finite binomial sum appearing in the original Janson–Knuth function. -/
theorem referenceArc_eq_binomial_sum (h g ell : ℕ) :
    referenceArc h g ell =
      ∑ k ∈ Finset.range (h - 1 + 1),
        (((h - 1).choose k : ℝ) * ((ell : ℝ) / g)^k *
          (1 - (ell : ℝ) / g)^(h - 1 - k)) * |(k : ℝ) - ((h * ell / g : ℕ) : ℝ)| := by
  exact F09Second.countAverage_eq_sum (h - 1) ((ell : ℝ) / g)
    (fun k => |(k : ℝ) - ((h * ell / g : ℕ) : ℝ)|)

/-- The Janson–Knuth binomial reference function. -/
def psi (h g : ℕ) : ℝ :=
  (∑ ell ∈ (Finset.range g).erase 0, referenceArc h g ell) / 2

/-- Arc reward at an original slot, averaged over uniform rank placements. -/
def observedArc {n : ℕ} (h g ell : ℕ) (i : Fin n) : ℝ :=
  uniformAverage (fun p => |(taggedSubsetArcCount h g ell i (tagLowerState p i).val : ℝ) -
    ((h * ell / g : ℕ) : ℝ)|)

private theorem average_sum {n : ℕ} {α : Type*} (S : Finset α) (F : α → RankPlacement n → ℝ) :
    uniformAverage (fun p => ∑ j ∈ S, F j p) = ∑ j ∈ S, uniformAverage (F j) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem observedArc_zero {n : ℕ} (h g : ℕ) (i : Fin n) : observedArc h g 0 i = 0 := by
  simp [observedArc, taggedSubsetArcCount, bitCount, pivotArcHit, pivotArcSites, uniformAverage]

/-- Exact signed error, expressed using only the positive widths of arcs. -/
theorem two_mul_lastCost_error {n h g : ℕ} (hh : 0 < h) (hg : 0 < g) (hc : Nat.Coprime h g) :
    2 * (uniformAverage (fun p : RankPlacement n =>
      (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ)) - n * psi h g) =
      ∑ i : Fin n, ∑ ell ∈ (Finset.range g).erase 0,
        (observedArc h g ell i - referenceArc h g ell) := by
  classical
  let widths := (Finset.range g).erase 0
  have realSum : 2 * uniformAverage (fun p : RankPlacement n =>
      (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ)) =
      ∑ i : Fin n, ∑ ell ∈ widths, observedArc h g ell i := by
    rw [← uniformAverage_const_mul]
    simp_rw [two_mul_lastCost_eq_sum_taggedArc _ h g hh hg hc]
    rw [average_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [average_sum]
    change ∑ ell ∈ Finset.range g, observedArc h g ell i = _
    exact (Finset.sum_erase_add _ _ (Finset.mem_range.mpr hg)).symm.trans
      (by simp [widths, observedArc_zero])
  simp_rw [Finset.sum_sub_distrib]
  rw [mul_sub, realSum]
  simp [widths, psi]
  ring

/-- Finite transfer from a uniform local arc bound to the true last-pass expectation. -/
theorem lastCost_error_of_arc_bound {n h g : ℕ} (hh : 0 < h) (hg : 0 < g)
    (hc : Nat.Coprime h g) (B : ℝ)
    (arc : ∀ (i : Fin n) (ell : ℕ), 0 < ell → ell < g →
      |observedArc h g ell i - referenceArc h g ell| ≤ B) :
    |uniformAverage (fun p : RankPlacement n =>
      (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ)) - n * psi h g| ≤
      n * (g - 1 : ℕ) * B / 2 := by
  classical
  let widths := (Finset.range g).erase 0
  let d := fun (i : Fin n) (ell : ℕ) => observedArc h g ell i - referenceArc h g ell
  have localBound (i : Fin n) : |∑ ell ∈ widths, d i ell| ≤ (g - 1 : ℕ) * B := by
    calc
      _ ≤ ∑ ell ∈ widths, |d i ell| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ell ∈ widths, B := Finset.sum_le_sum fun ell he =>
        arc i ell (Nat.pos_of_ne_zero (Finset.mem_erase.mp he).1)
          (Finset.mem_range.mp (Finset.mem_erase.mp he).2)
      _ = _ := by simp [widths, Finset.card_erase_of_mem (Finset.mem_range.mpr hg)]
  have allBound : |∑ i : Fin n, ∑ ell ∈ widths, d i ell| ≤ n * (g - 1 : ℕ) * B := by
    calc
      _ ≤ ∑ i : Fin n, |∑ ell ∈ widths, d i ell| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (g - 1 : ℕ) * B := Finset.sum_le_sum fun i _ => localBound i
      _ = _ := by simp [mul_assoc]
  have identity := congrArg abs (two_mul_lastCost_error (n := n) hh hg hc)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at identity
  linarith


/-- Application with the integrated per-arc estimate in the uniform-error theorem.
The premise is about actual permutation arcs; its Fourier and threshold proof is analytic. -/
theorem lastCost_uniform_error_of_integrated_arcs {n h g : ℕ}
    (hgh : g < h) (hhn : h < n) (hgp : 2 ≤ g) (hc : Nat.Coprime h g)
    (arc : ∀ (i : Fin n) (ell : ℕ), 0 < ell → ell < g →
      |observedArc h g ell i - referenceArc h g ell| ≤
        Real.sqrt 3 * Real.sqrt ((h - 1 : ℕ) : ℝ) *
          min 1 (Real.pi^2 * (g : ℝ)^2 / (6 * ((n/h : ℕ) : ℝ)))):
    let err := |uniformAverage (fun p : RankPlacement n =>
      (gapInsertionCost (gapSort (gapSort p h) g) 1 (by decide) : ℝ)) - n * psi h g|
    err ≤ (n : ℝ) * ((g - 1 : ℕ) : ℝ) * (Real.sqrt 3 * Real.sqrt ((h - 1 : ℕ) : ℝ) *
        min 1 (Real.pi^2 * (g : ℝ)^2 / (6 * ((n/h : ℕ) : ℝ)))) / 2 ∧
      err ≤ Real.pi^2 / (2 * Real.sqrt 3) * (g : ℝ)^3 * (h : ℝ) * Real.sqrt h := by
  have hh : 0 < h := by omega
  have hg : 0 < g := by omega
  have hm : 1 ≤ n/h := (Nat.le_div_iff_mul_le hh).mpr (by simpa using hhn.le)
  have mpos : (0 : ℝ) < ((n/h : ℕ) : ℝ) := by exact_mod_cast hm
  have nbound : (n : ℝ) ≤ 2 * (h : ℝ) * ((n/h : ℕ) : ℝ) := by
    exact_mod_cast (calc
      n ≤ h * (n/h + 1) := (Nat.lt_mul_div_succ n hh).le
      _ ≤ h * (2 * (n/h)) := Nat.mul_le_mul_left h (by omega)
      _ = 2 * h * (n/h) := by ring)
  have gs : ((g - 1 : ℕ) : ℝ) ≤ g := by exact_mod_cast Nat.sub_le g 1
  have hs : Real.sqrt ((h - 1 : ℕ) : ℝ) ≤ Real.sqrt h :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le h 1)
  have sp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have coeff : Real.sqrt 3 / 6 = 1 / (2 * Real.sqrt 3) := by
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have first := lastCost_error_of_arc_bound hh hg hc _ arc
  refine ⟨first, first.trans ?_⟩
  calc
    _ ≤ (2 * (h : ℝ) * ((n/h : ℕ) : ℝ)) * (g : ℝ) * (Real.sqrt 3 * Real.sqrt h *
        (Real.pi^2 * (g : ℝ)^2 / (6 * ((n/h : ℕ) : ℝ)))) / 2 := by
      gcongr
      exact min_le_right _ _
    _ = (Real.sqrt 3 / 6) * Real.pi^2 * (g : ℝ)^3 * (h : ℝ) * Real.sqrt h := by
      field_simp
    _ = _ := by rw [coeff]; ring

end JK
end Shellsort
end
