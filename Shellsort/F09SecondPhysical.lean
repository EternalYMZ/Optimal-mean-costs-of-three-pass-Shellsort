import Shellsort.ThreePassGapScales
import Shellsort.TaggedBernoulli

/-! Exact second-pass shift rewards of the original tagged keys. -/
noncomputable section
namespace Shellsort.F09Second
open Finset

/-- Count larger predecessors in the second-pass chain. After the first
pass a source contributes precisely the slots at or above its lower-key count. -/
def predecessorReward {n : ℕ} (h g : ℕ) (i : Fin n) (B : Finset (Fin n)) : ℕ :=
  let pos := i.val % h + h * chainLowerCount B h (i.val % h)
  ∑ j : Fin n, if j.val < pos ∧ j.val % g = pos % g ∧
    chainLowerCount B h (j.val % h) ≤ j.val / h then 1 else 0

private theorem reward_at_actual_tag {n : ℕ} (p : RankPlacement n) (h g : ℕ)
    (hh : 0 < h) (i : Fin n) :
    predecessorReward h g i (tagLowerState p i).val =
      let q := gapSort p h
      let x := p.symm i
      ∑ j : Fin n, if (j < q x ∧ j.val % g = (q x).val % g) ∧ x < q.symm j then 1 else 0 := by
  let q := gapSort p h
  let x := p.symm i
  have pos := gapSort_tag_position p h hh x
  change (q x).val = _ at pos
  have initial : p x = i := p.apply_symm_apply _
  rw [initial] at pos
  unfold predecessorReward
  apply Finset.sum_congr rfl
  intro j _
  have low : q.symm j < x ↔ j.val/h < chainLowerCount (tagLowerState p i).val h (j.val%h) := by
    change (q.symm j).val < x.val ↔ _
    rw [← threshold_mem, gapSort_threshold_commutes]
    simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and, chainOrdinal_eq_div h hh]
    rfl
  have rhs : (tagLowerState p i).val = thresholdSet p x.val := rfl
  rw [rhs, ← pos]
  change _ = (if (j < q x ∧ j.val%g = (q x).val%g) ∧ x < q.symm j then 1 else 0)
  by_cases early : j < q x
  · have ne : q.symm j ≠ x := fun he => early.ne (by simpa using congrArg q he)
    have compare : x < q.symm j ↔ chainLowerCount (thresholdSet p x.val) h (j.val%h) ≤ j.val/h := by
      rw [← not_lt, ← rhs, ← low]
      exact ⟨fun hlt => not_lt.mpr hlt.le, fun hle => lt_of_le_of_ne (le_of_not_gt hle) ne.symm⟩
    simp only [early, show j.val < (q x).val from early, true_and, compare]
  · simp [early, show ¬j.val < (q x).val from early]

/-- Identity on every permutation; each shift is owned by its smaller key. -/
theorem executed_shifts_eq_tag_sum {n : ℕ} (p : RankPlacement n) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) :
    gapInsertionCost (gapSort p h) g hg = ∑ i : Fin n, predecessorReward h g i (tagLowerState p i).val := by
  let q := gapSort p h
  simp_rw [reward_at_actual_tag p h g hh]
  rw [gapInsertionCost_eq_gapInversions, gapInversions_nat_pair_sum]
  let f (v : Fin n) := ∑ j : Fin n,
    if (j<v ∧ j.val%g=v.val%g) ∧ q.symm v < q.symm j then 1 else 0
  have eq := (p.symm.trans q).sum_comp f
  simpa [f, q, Equiv.trans_apply] using eq.symm

/-- Uniform permutation input, any positive gaps, including shared divisors.
The integral mixes only the independent bits at the original positions. -/
theorem uniform_executed_shifts_eq_tag_integrals (n h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort p h) g hg : ℝ)) =
      ∑ i : Fin n, ∫ t : ℝ in 0..1,
        mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
          (fun z => (predecessorReward h g i ((omittedBitsSubsetEquiv i) z).val : ℝ)) := by
  simp_rw [executed_shifts_eq_tag_sum _ h g hh hg, Nat.cast_sum]
  have swap : uniformAverage (fun p : RankPlacement n => ∑ i : Fin n,
      (predecessorReward h g i (tagLowerState p i).val : ℝ)) =
      ∑ i : Fin n, uniformAverage (fun p : RankPlacement n => (predecessorReward h g i (tagLowerState p i).val : ℝ)) := by
    unfold uniformAverage
    rw [Finset.sum_comm, Finset.sum_div]
  rw [swap]
  exact Finset.sum_congr rfl fun i _ =>
    uniform_tagged_bernoulli_mixture i (fun B => (predecessorReward h g i B.val : ℝ))

end Shellsort.F09Second
