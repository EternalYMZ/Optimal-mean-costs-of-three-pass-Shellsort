import Shellsort.F09SecondPhysical
import Shellsort.F09SecondBinomial
import Shellsort.TaggedUpper

noncomputable section
namespace Shellsort.F09Second
open Finset

def slotReward (h g r j y z : ℕ) : ℝ :=
  if j < r+h*y ∧ j%g = (r+h*y)%g ∧ z ≤ j/h then 1 else 0

theorem mean_mono' {α : Type*} [Fintype α] {w f g : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (h : ∀ x, f x ≤ g x) : mean w f ≤ mean w g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x)

theorem countAverage_mono {n : ℕ} {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) {f g : ℕ → ℝ}
    (h : ∀ x, f x ≤ g x) : countAverage n t f ≤ countAverage n t g :=
  mean_mono' (bernoulliVectorWeight_nonneg t ht n) fun x => h (bitCount x)

theorem countAverage_sum {ι : Type*} [Fintype ι] (n : ℕ) (t : ℝ) (f : ι → ℕ → ℝ) :
    countAverage n t (fun z => ∑ i, f i z) = ∑ i, countAverage n t (f i) :=
  mean_sum _ _

def nonownerMean (n h g r y : ℕ) (t : ℝ) :=
  ∑ j : Fin n, if j.val%h = r then 0 else
    countAverage (sourceTrialLength (n/h) (n%h) (j.val%h)) t (slotReward h g r j.val y)

private theorem owner_slot_zero (h g r j y : ℕ) (hh : 0 < h) (hs : j%h = r) :
    slotReward h g r j y y = 0 := by
  unfold slotReward
  split_ifs with H
  · have id := Nat.mod_add_div j h
    rw [hs] at id
    have := Nat.mul_le_mul_left h H.2.2
    omega
  · rfl

private theorem two_coordinate_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (w : ∀ i, β i → ℝ) (hw : ∀ i, ∑ z, w i z = 1)
    (o s : ι) (hs : s ≠ o) (F : β o → β s → ℝ) :
    mean (productWeight w) (fun x => F (x o) (x s)) =
      mean (w o) (fun a => mean (w s) (F a)) := by
  rw [productWeight_owner_diagonal w o (hw o) (fun a x => F a (x s))
    (fun a x z same => congrArg (F a) (same s hs))]
  congr 1
  funext a
  let f (j : ι) (v : β j) : ℝ := if e : j=s then F a (e ▸ v) else 0
  simpa [f] using productWeight_mean_coordinate w f hw s

def tagSourceMean (n h g : ℕ) (hh : 0 < h) (i : Fin n) (t : ℝ) :=
  let coord := positionChainEquiv n h hh i
  mean (sourceCoordinateWeight h (n/h) (n%h) t coord.1) fun a =>
    nonownerMean n h g coord.1.val (ownerBitCount coord.2 a) t

/-- Exact marginalization on the true original owner. The actual second-chain
residue still depends on the owner's count. No two post-sort states are decoupled. -/
theorem tagIntegral_source_mean (n h g : ℕ) (hh : 0 < h) (i : Fin n) (t : ℝ) :
    mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
      (fun z => (predecessorReward h g i ((omittedBitsSubsetEquiv i) z).val : ℝ)) =
        tagSourceMean n h g hh i t := by
  rw [← bernoulli_mean_add_dummy i t (fun z =>
    (predecessorReward h g i ((omittedBitsSubsetEquiv i) z).val : ℝ))]
  let o := ((positionChainEquiv n h hh) i).1
  let v := ((positionChainEquiv n h hh) i).2
  let s (j : Fin n) : Fin h := ⟨j.val%h, Nat.mod_lt _ hh⟩
  let X := (j : Fin h) → Fin (sourceTrialLength (n/h) (n%h) j.val) → Bool
  let F (x : X) := ∑ j : Fin n, if s j = o then 0 else
      slotReward h g o.val j.val (ownerBitCount v (x o)) (bitCount (x (s j)))
  have point (z : Fin n → Bool) :
      (predecessorReward h g i (fullBitsSubset i z) : ℝ) = F (chainBits hh z) := by
    unfold predecessorReward
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro j _
    have ho : o.val = i.val%h := rfl
    have own := owner_fullBits_chain_count hh i z
    change chainLowerCount (fullBitsSubset i z) h o.val = ownerBitCount v (chainBits hh z o) at own
    push_cast
    change slotReward h g (i.val%h) j.val (chainLowerCount _ h (i.val%h))
      (chainLowerCount _ h (j.val%h)) = _
    rw [← ho, own]
    by_cases same : s j=o
    · have same' : j.val%h=o.val := congrArg Fin.val same
      simp only [same, ite_true]
      rw [same', own]
      exact owner_slot_zero h g _ _ _ hh same'
    · simp only [same, ite_false]
      have other : (s j).val ≠ i.val%h := fun e => same (Fin.ext (e.trans ho.symm))
      rw [show j.val%h = (s j).val from rfl, nonowner_fullBits_chain_count hh i z (s j) other]
  change mean _ (fun z => (predecessorReward h g i (fullBitsSubset i z):ℝ)) = _
  simp_rw [point]
  rw [fullBits_mean_chainBits n h hh t F]
  unfold F tagSourceMean nonownerMean
  rw [mean_sum, mean_sum]
  apply sum_congr rfl
  intro j _
  by_cases same : s j=o
  · have eqv : j.val%h=o.val := congrArg Fin.val same
    simp only [same, ite_true, show j.val%h=((positionChainEquiv n h hh) i).1.val from eqv]
    simp [mean]
  · have ne : j.val%h ≠ ((positionChainEquiv n h hh) i).1.val := fun e => same (Fin.ext e)
    simp only [same, ite_false, ne]
    exact two_coordinate_mean (sourceCoordinateWeight h (n/h) (n%h) t)
      (sourceCoordinateWeight_sum h (n/h) (n%h) t) o (s j) same
        (fun a b => slotReward h g o.val j.val (ownerBitCount v a) (bitCount b))

theorem uniform_second_source_integral (n h g : ℕ) (hh : 0 < h) (hg : 0 < g) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost (gapSort p h) g hg : ℝ)) =
      ∑ i : Fin n, ∫ t : ℝ in 0..1, tagSourceMean n h g hh i t := by
  rw [uniform_executed_shifts_eq_tag_integrals n h g hh hg]
  simp_rw [tagIntegral_source_mean n h g hh]

private theorem sourceLength_sandwich (m ell s : ℕ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (F : ℕ → ℝ) (mono : ∀ z, F (z+1) ≤ F z) :
    countAverage m t (fun z => F (z+1)) ≤ countAverage (sourceTrialLength m ell s) t F ∧
      countAverage (sourceTrialLength m ell s) t F ≤ countAverage m t F := by
  have bound := countAverage_mono (n:=m) ht mono
  unfold sourceTrialLength
  split_ifs
  · change _ ≤ mean _ _ ∧ mean _ _ ≤ _
    rw [bernoulli_count_succ_mean]
    change _ ≤ (1-t)*countAverage m t F + t*countAverage m t (fun z => F (z+1)) ∧
      (1-t)*countAverage m t F + t*countAverage m t (fun z => F (z+1)) ≤ _
    constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr bound),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr bound)]
  · exact ⟨bound, le_rfl⟩

/-- Replacing all nonowner lengths by a common test count only changes their
threshold by at most one. The common count is used after taking marginal means. -/
theorem common_count_window (n h g r y : ℕ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    countAverage (n/h) t (fun z => ∑ j : Fin n,
      if j.val%h = r then 0 else slotReward h g r j.val y (z+1)) ≤ nonownerMean n h g r y t ∧
    nonownerMean n h g r y t ≤ countAverage (n/h) t (fun z => ∑ j : Fin n,
      slotReward h g r j.val y z) := by
  unfold nonownerMean
  rw [countAverage_sum, countAverage_sum]
  constructor <;> apply sum_le_sum <;> intro j _
  all_goals
    have mono (z : ℕ) : slotReward h g r j.val y (z+1) ≤ slotReward h g r j.val y z := by
      unfold slotReward
      split_ifs <;> grind
    have bounds := sourceLength_sandwich (n/h) (n%h) (j.val%h) t ht _ mono
    by_cases same : j.val%h=r
    · simp only [same, ite_true]
      first
      | solve | simp [countAverage, mean]
      | exact sum_nonneg fun z _ => mul_nonneg
          (bernoulliVectorWeight_nonneg t ht _ _) (by dsimp only [slotReward]; split_ifs <;> norm_num)
    · simp only [same, ite_false]
      first | exact bounds.1 | exact bounds.2

end Shellsort.F09Second
