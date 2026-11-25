import Shellsort.F09PhaseCross
import Shellsort.PivotArcEndpoints
import Shellsort.PivotArcCostBridge

/-! Mean corrections for physical target fields and a conditioned owner.
They are bounded before taking any normal approximation. -/
noncomputable section
namespace Shellsort
open Real Set
open scoped BigOperators

/-- Conditional expected number of visits in a complete reference class
with its two true source lengths. -/
def referenceVisitMean (h g j m rem : ℕ) (t : ℝ) :=
  ∑ s ∈ Finset.range h, mean (bernoulliVectorWeight t (sourceTrialLength m rem s)) fun x =>
    (sourcePrefixCount h g j s (bitCount x):ℝ)

theorem phase_bitCount_mean (m : ℕ) (t : ℝ) :
    mean (bernoulliVectorWeight t m) (fun x => (bitCount x:ℝ)) = (m:ℝ)*t := by
  have eq (x : Fin m → Bool) : (bitCount x:ℝ) = ∑ i, if x i then (1:ℝ) else 0 := by simp [bitCount]
  simp only [eq]
  unfold bernoulliVectorWeight
  rw [productWeight_mean_sum (fun _ : Fin m => bernoulliWeight t)
    (fun _ (b : Bool) => if b then (1:ℝ) else 0) (fun _ => bernoulliWeight_sum t)]
  simp [bernoulli_scaled_mean]

/-- This cancellation uses only marginal expectations. The independent
reference samples keep their actual distribution when computing moments. -/
theorem reference_visit_mean_near (h g j m rem : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1)
    (hr : rem ≤ h) (hg : 0 < g) (hj : j < g) :
    |referenceVisitMean h g j m rem t - (((h:ℝ)*m+rem)*t/g)| ≤ 1 := by
  have H := referencePrefixMean_balance h g j rem (bernoulliVectorWeight t m) bitCount t
    (bernoulliVectorWeight_nonneg t ht m) (bernoulliVectorWeight_sum t m) ht.1 ht.2 hr hg hj
  have each (s : ℕ) : referencePrefixMean h g j rem (bernoulliVectorWeight t m) bitCount t s =
      (g:ℝ) * mean (bernoulliVectorWeight t (sourceTrialLength m rem s))
        (fun x => (sourcePrefixCount h g j s (bitCount x):ℝ)) - (sourceTrialLength m rem s:ℝ)*t := by
    rw [← bernoulli_source_mean_eq_reference]
    simp only [sourceResidualReal, mean_sub, phaseMean_scale, phase_bitCount_mean]
  have lengths : (∑ s ∈ Finset.range h, (sourceTrialLength m rem s:ℝ)) = (h:ℝ)*m+rem := by
    have eq (s : ℕ) : (sourceTrialLength m rem s:ℝ) = (m:ℝ) + (if s<rem then 1 else 0) := by
      unfold sourceTrialLength; split <;> simp_all
    have cut : (Finset.range h).filter (fun s => s < rem) = Finset.range rem := by ext s; simp; omega
    simp [eq, Finset.sum_add_distrib, Finset.sum_boole,cut]
  simp only [each, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, lengths] at H
  change 0 ≤ (j:ℝ)+(g*referenceVisitMean h g j m rem t - (((h:ℝ)*m+rem)*t)) ∧
    (j:ℝ)+(g*referenceVisitMean h g j m rem t - (((h:ℝ)*m+rem)*t)) ≤ (g:ℝ)-1 at H
  have jp : (j:ℝ) < g := by exact_mod_cast hj
  have gp : (g:ℝ) > 0 := by exact_mod_cast hg
  apply abs_le.mpr
  constructor
  · rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ gp]
    linarith [H.1]
  · rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ gp]
    linarith [H.2, Nat.cast_nonneg (α:=ℝ) j]

private theorem phase_arcHits_bit (h g o ell y z : ℕ) (hc : Nat.Coprime h g) (hl : ell < g) :
    arcHits h g ((o+h*y)%g) ell z = if z%g ∈ pivotArcSites h g o ell y then 1 else 0 := by
  let D := (Finset.range ell).filter (fun w => ((o+h*y)%g+h*(w+1))%g=z%g)
  have eq : arcHits h g ((o+h*y)%g) ell z = D.card := by
    unfold arcHits D
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_one]
    rfl
  have E : D.Nonempty ↔ z%g ∈ pivotArcSites h g o ell y := by
    simp [Finset.Nonempty,D,pivotArcSites,Nat.mod_add_mod]
  have bound := arcHits_le_one h g ((o+h*y)%g) ell z hc hl
  rw [eq] at bound ⊢
  split_ifs with mem
  · have := Finset.card_pos.mpr (E.mpr mem); omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp (fun n => mem (E.mp n))]

/-- Actual source hit, on the selected owner phase with the owner omitted. -/
def phaseArcReward (h g o ell y s b : ℕ) : ℝ :=
  if pivotArcHit h g o ell y s b then 1 else 0

theorem phaseArcReward_eq_removed_endpoint (h g o ell y s b : ℕ)
    (hc : Nat.Coprime h g) (hl : ell < g) :
    phaseArcReward h g o ell y s b =
      if s=o then 0 else (arcHits h g ((o+h*y)%g) ell (s+h*b):ℝ) := by
  rw [phase_arcHits_bit _ _ _ _ _ _ hc hl]
  by_cases e : s=o <;> simp [phaseArcReward, pivotArcHit, e]

/-- The drift of the independently sampled *nonowner* arc about its geometric
floor is bounded at every threshold, including when the selected owner count
has been fixed. This bound is sufficient on the square-root source scale. -/
theorem phaseArc_mean_drift (h g m rem ell : ℕ) (o : Fin h) (y : ℕ) (t : ℝ)
    (ht : t ∈ Icc 0 1) (hr : rem ≤ h) (hg : 0 < g) (hc : Nat.Coprime h g) (hl : ell < g) :
    |(∑ s : Fin h, mean (sourceCoordinateWeight h m rem t s)
      (fun z => phaseArcReward h g o.val ell y s.val (bitCount z))) - ((h*ell/g:ℕ):ℝ)| ≤ 4 := by
  let j := (o.val+h*y)%g
  let r := (j+h*ell)%g
  let K := ((h*ell/g:ℕ):ℝ)
  let carry : ℝ := if r<j then 1 else 0
  let E := fun (s : ℕ) (b : ℕ) => (arcHits h g j ell (s+h*b):ℝ)
  let w := fun s : ℕ => bernoulliVectorWeight t (sourceTrialLength m rem s)
  let q := fun s : ℕ => mean (w s) (fun z => E s (bitCount z))
  let V := fun a s : ℕ => mean (w s) (fun z => (sourcePrefixCount h g a s (bitCount z):ℝ))
  have hj : j < g := Nat.mod_lt _ hg
  have hx : r < g := Nat.mod_lt _ hg
  have each (s b : ℕ) : E s b = (sourcePrefixCount h g j s b:ℝ) -
      sourcePrefixCount h g r s b + (arcHits h g j ell s:ℝ) := by
    have diff := sourcePrefixCount_arc_difference h g j ell s b
    rw [Nat.mod_eq_of_lt hj] at diff
    have eq : (arcHits h g j ell (s+h*b):ℤ) =
        (sourcePrefixCount h g j s b:ℤ) - sourcePrefixCount h g r s b + arcHits h g j ell s := by
      dsimp [r]; omega
    dsimp only [E]
    exact_mod_cast eq
  have meanEq (s : ℕ) : q s = V j s - V r s + (arcHits h g j ell s:ℝ) := by
    simp only [q, each, mean_add, mean_sub, mean_const (w s) (bernoulliVectorWeight_sum t _), V]
  have init := sum_source_arc_endpoint_identity h g j ell hg hj (fun _ => 0)
  simp only [sourcePrefixCount, Finset.range_zero, Finset.sum_empty, Finset.sum_const_zero,
    Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.cast_zero, sub_zero] at init
  have initR : (∑ s ∈ Finset.range h, (arcHits h g j ell s:ℝ)) - K = carry := by
    dsimp only [K,carry,r]
    split_ifs with cmp <;> simp only [cmp,ite_true,ite_false] at init ⊢ <;>
      exact_mod_cast init.symm
  have total : (∑ s ∈ Finset.range h, q s) - K =
      referenceVisitMean h g j m rem t - referenceVisitMean h g r m rem t + carry := by
    simp only [meanEq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    change (referenceVisitMean h g j m rem t - referenceVisitMean h g r m rem t +
      (∑ s ∈ Finset.range h, (arcHits h g j ell s:ℝ))) - K = _
    linarith
  have erase : (∑ s : Fin h, mean (sourceCoordinateWeight h m rem t s)
      (fun z => phaseArcReward h g o.val ell y s.val (bitCount z))) + q o.val =
        ∑ s ∈ Finset.range h, q s := by
    rw [← Fin.sum_univ_eq_sum_range q h, ← Finset.sum_erase_add Finset.univ
      (fun s : Fin h => q s.val) (Finset.mem_univ o)]
    congr 1
    calc
      _ = ∑ s : Fin h, if s=o then 0 else q s.val := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases eq : s=o
        · subst s; simp [phaseArcReward,pivotArcHit,mean]
        · have ne : s.val ≠ o.val := fun a => eq (Fin.ext a)
          simp only [phaseArcReward_eq_removed_endpoint _ _ _ _ _ _ _ hc hl, ne, eq, ite_false]; rfl
      _ = _ := by rw [Finset.sum_ite]; simp [Finset.filter_ne']
  have qB : 0 ≤ q o.val ∧ q o.val ≤ 1 := by
    have upper (x : Fin (sourceTrialLength m rem o.val) → Bool) : E o.val (bitCount x) ≤ 1 := by
      dsimp only [E]
      exact_mod_cast arcHits_le_one h g j ell (o.val+h*bitCount x) hc hl
    exact ⟨Finset.sum_nonneg fun z _ => mul_nonneg (bernoulliVectorWeight_nonneg t ht _ z) (Nat.cast_nonneg _),
      (phaseMean_mono _ (bernoulliVectorWeight_nonneg t ht _) upper).trans_eq
        (mean_const _ (bernoulliVectorWeight_sum t _) _)⟩
  have cB : 0 ≤ carry ∧ carry ≤ 1 := by dsimp [carry]; split <;> norm_num
  have bj := abs_le.mp (reference_visit_mean_near h g j m rem t ht hr hg hj)
  have br := abs_le.mp (reference_visit_mean_near h g r m rem t ht hr hg hx)
  change |_ - K| ≤ 4
  exact abs_le.mpr ⟨by linarith [bj.1,br.2,qB.2,cB.1], by linarith [bj.2,br.1,qB.1,cB.2]⟩

end Shellsort
end
