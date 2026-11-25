import Shellsort.F09SecondSources

noncomputable section
namespace Shellsort.F09Second
open Finset

theorem mean_affine {α : Type*} [Fintype α] (w f : α → ℝ) (hw : ∑ x, w x = 1) (a b : ℝ) :
    mean w (fun x => a*f x+b) = a*mean w f + b := by
  unfold mean
  simp only [mul_add, sum_add_distrib, ← sum_mul, hw, one_mul, mul_left_comm _ a, ← mul_sum]

def positiveCount (m : ℕ) (t : ℝ) (y : ℕ) :=
  countAverage m t (fun z => ((y-z:ℕ):ℝ))

theorem positiveCount_succ (m : ℕ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (y : ℕ) :
    positiveCount m t y ≤ positiveCount m t (y+1) ∧
      positiveCount m t (y+1) ≤ positiveCount m t y + 1 := by
  constructor
  · exact countAverage_mono ht (fun z => by exact_mod_cast (show y-z ≤ y+1-z by omega))
  · have inc := countAverage_mono (n:=m) ht (f:=fun z => ((y+1-z:ℕ):ℝ))
        (g:=fun z => 1*((y-z:ℕ):ℝ)+1) (fun z => by
          rw [one_mul]; exact_mod_cast (show y+1-z ≤ y-z+1 by omega))
    unfold countAverage at inc
    rw [mean_affine _ _ (bernoulliVectorWeight_sum _ _), one_mul] at inc
    exact inc

theorem double_positiveCount (m : ℕ) (t : ℝ) :
    2 * countAverage m t (positiveCount m t) = countDifference m m t := by
  let avg := countAverage m t (positiveCount m t)
  have flip : avg = countAverage m t (fun y => countAverage m t (fun z => ((z-y:ℕ):ℝ))) := by
    unfold avg positiveCount countAverage mean
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  change 2*avg = _
  rw [two_mul]
  nth_rw 2 [flip]
  simp only [avg, positiveCount, countAverage, countDifference, mean, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [← mul_add, ← mul_add]
  congr 2
  rcases le_total (bitCount i) (bitCount j) with a|a
  · rw [Nat.sub_eq_zero_of_le a, Nat.cast_sub a, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast a))]
    simp
  · rw [Nat.sub_eq_zero_of_le a, Nat.cast_sub a, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast a))]
    simp

theorem owner_bit_bounds {L : ℕ} (o : Fin L) (v : Fin L → Bool) :
    ownerBitCount o v ≤ bitCount v ∧ bitCount v ≤ ownerBitCount o v + 1 ∧ ownerBitCount o v < L := by
  have A : ownerBitCount o v + (if v o then 1 else 0) = bitCount v := by
    have one : (∑ j : Fin L, if j=o then (if v j then 1 else 0) else 0) =
      (if v o then 1 else 0) := by simp
    rw [← one]
    unfold ownerBitCount bitCount
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    by_cases h : j=o <;> simp [h]
  have cap : ownerBitCount o v ≤ ∑ j : Fin L, if j=o then 0 else 1 := by
    apply sum_le_sum
    intro j _
    split_ifs <;> omega
  have cap' : (∑ j : Fin L, if j=o then 0 else 1) + 1 = L := by
    have one : (∑ j : Fin L, if j=o then 1 else 0) = 1 := by simp
    rw [← one, ← sum_add_distrib]
    simp [ite_add_ite]
  split_ifs at A <;> omega

/-- The omitted bit and the possible single long-chain trial each affect
the one-sided discrepancy by at most one. -/
theorem owner_positiveCount_bounds (h m ell : ℕ) (o : Fin h)
    (v : Fin (sourceTrialLength m ell o.val)) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    let P := countDifference m m t / 2
    let M := mean (sourceCoordinateWeight h m ell t o)
      (fun z => positiveCount m t (ownerBitCount v z))
    P - 1 ≤ M ∧ M ≤ P + 1 := by
  dsimp only
  let F := positiveCount m t
  let w := sourceCoordinateWeight h m ell t o
  have wsum : ∑ z, w z = 1 := sourceCoordinateWeight_sum h m ell t o
  have wn := sourceCoordinateWeight_nonneg h m ell t ht o
  have step := positiveCount_succ m t ht
  have cut (z) : F (ownerBitCount v z) ≤ F (bitCount z) ∧
      F (bitCount z) ≤ F (ownerBitCount v z)+1 := by
    have b := owner_bit_bounds v z
    rcases (show bitCount z = ownerBitCount v z ∨ bitCount z = ownerBitCount v z+1 by omega) with e|e
    · simp [e]
    · rw [e]; exact step _
  have cut₁ := mean_mono' wn (fun z => (cut z).1)
  have cut₂ := mean_mono' wn (fun z => (cut z).2)
  rw [mean_add, mean_const _ wsum] at cut₂
  have extra : countAverage m t F ≤ countAverage (sourceTrialLength m ell o.val) t F ∧
      countAverage (sourceTrialLength m ell o.val) t F ≤ countAverage m t F+1 := by
    unfold sourceTrialLength
    split_ifs
    · have l := countAverage_mono (n:=m) ht (fun z => (step z).1)
      have u := countAverage_mono (n:=m) ht (fun z => (step z).2)
      unfold countAverage at u ⊢
      rw [mean_add, mean_const _ (bernoulliVectorWeight_sum _ _)] at u
      rw [bernoulli_count_succ_mean]
      change countAverage m t F ≤ _ ∧ _ ≤ countAverage m t F+1
      change countAverage m t (fun z => F (z+1)) ≤ countAverage m t F+1 at u
      change countAverage m t F ≤ countAverage m t (fun z => F (z+1)) at l
      change countAverage m t F ≤ (1-t)*countAverage m t F+t*countAverage m t (fun z => F (z+1)) ∧
        (1-t)*countAverage m t F+t*countAverage m t (fun z => F (z+1)) ≤ _
      constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr l), mul_nonneg ht.1 (sub_nonneg.mpr u), ht.2]
    · constructor <;> linarith
  change _ ≤ countAverage (sourceTrialLength m ell o.val) t F at cut₁
  change countAverage (sourceTrialLength m ell o.val) t F ≤ _ at cut₂
  have exactPair := double_positiveCount m t
  change 2*countAverage m t F = _ at exactPair
  constructor <;> linarith only [cut₁,cut₂,extra.1,extra.2,exactPair]

end Shellsort.F09Second
