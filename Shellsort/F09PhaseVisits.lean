import Shellsort.ResidueCount
import Shellsort.FirstPassMoments

/-! Exact variance of physical prefix visits averaged over a whole period.
The residue rounding term is retained even for prefixes longer than a period. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

private theorem sum_phase_interval (g lo hi : ℕ) (hb : hi ≤ g) :
    (∑ a : Fin g, if lo ≤ a.val ∧ a.val < hi then (1 : ℝ) else 0) = (hi-lo : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => if lo ≤ a ∧ a < hi then (1:ℝ) else 0),
    Finset.sum_boole]
  have hset : (Finset.range g).filter (fun a => lo ≤ a ∧ a < hi) = Finset.Ico lo hi := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]

private theorem phase_visit_sq_ordered (g x y : ℕ) (hg : 0 < g) (hxy : y%g ≤ x%g) :
    (g:ℝ) * (∑ a : Fin g, ((residuePrefixCount g a.val x : ℝ) - residuePrefixCount g a.val y)^2) =
      ((x:ℝ)-y)^2 + |((x%g : ℕ):ℝ) - (y%g : ℕ)| * (g - |((x%g : ℕ):ℝ) - (y%g : ℕ)|) := by
  let q := ((x/g : ℕ):ℝ) - ((y/g : ℕ):ℝ)
  let u := ((x%g : ℕ):ℝ) - ((y%g : ℕ):ℝ)
  let hit := fun a : Fin g => if y%g ≤ a.val ∧ a.val < x%g then (1:ℝ) else 0
  have sumhit : ∑ a : Fin g, hit a = u := by
    rw [sum_phase_interval g (y%g) (x%g) (Nat.le_of_lt (Nat.mod_lt x hg)), Nat.cast_sub hxy]
  have entry (a : Fin g) : ((residuePrefixCount g a.val x : ℝ) - residuePrefixCount g a.val y)^2 =
      q^2 + (2*q+1)*hit a := by
    rw [residuePrefixCount_formula g a.val x hg a.isLt, residuePrefixCount_formula g a.val y hg a.isLt]
    by_cases hx : a.val < x%g <;> by_cases hy : a.val < y%g
    all_goals simp [q, hit, hx, hy, show (y%g ≤ a.val) ↔ ¬a.val < y%g by omega]
    all_goals try (exfalso; omega)
    ring
  have eqx : ((x%g : ℕ):ℝ) + (g:ℝ) * ((x/g : ℕ):ℝ) = x := by exact_mod_cast Nat.mod_add_div x g
  have eqy : ((y%g : ℕ):ℝ) + (g:ℝ) * ((y/g : ℕ):ℝ) = y := by exact_mod_cast Nat.mod_add_div y g
  have decomp : (x:ℝ)-y = (g:ℝ)*q+u := by dsimp [q,u]; linarith
  have hu : 0 ≤ u := sub_nonneg.mpr (by exact_mod_cast hxy)
  change _ = ((x:ℝ)-y)^2 + |u| * (g - |u|)
  simp only [entry, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, sumhit, abs_of_nonneg hu, decomp]
  ring

/-- Exact squared difference of residue visits across phases. The final term
is the quadratic residue-rounding kernel with no restrictions on the lengths. -/
theorem phase_visit_sq_sum (g x y : ℕ) (hg : 0 < g) :
    (g:ℝ) * (∑ a : Fin g, ((residuePrefixCount g a.val x : ℝ) - residuePrefixCount g a.val y)^2) =
      ((x:ℝ)-y)^2 + |((x%g : ℕ):ℝ) - (y%g : ℕ)| * (g - |((x%g : ℕ):ℝ) - (y%g : ℕ)|) := by
  rcases le_total (y%g) (x%g) with h | h
  · exact phase_visit_sq_ordered g x y hg h
  · simpa only [abs_sub_comm ((y%g : ℕ):ℝ) ((x%g : ℕ):ℝ), sub_sq_comm (y:ℝ) (x:ℝ),
      sub_sq_comm (residuePrefixCount g _ y : ℝ) (residuePrefixCount g _ x : ℝ)] using
      phase_visit_sq_ordered g y x hg h

private theorem quotientMean_mul {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => a*f x) = a*mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

theorem phase_two_copy_square {α : Type*} [Fintype α] (w f : α → ℝ) (hw : ∑ i, w i = 1) :
    (mean w fun x => mean w fun y => (f x-f y)^2) = 2 * centeredSecond w f := by
  have pt (x y : α) : (f x - f y)^2 = f x^2 - (2*f x)*f y + f y^2 := by ring
  have outer (x : α) : f x^2 - (2*f x)*mean w f + mean w (fun z => f z^2) =
      f x^2 - (2*mean w f)*f x + mean w (fun z => f z^2) := by ring
  simp only [pt, mean_add, mean_sub, mean_const w hw, quotientMean_mul, outer,
    centeredSecond_identity w f hw]
  change _ = 2 * (mean w (fun z => f z^2) - (mean w f)^2)
  ring

theorem phase_bitCount_exact_variance (m : ℕ) (t : ℝ) :
    centeredSecond (bernoulliVectorWeight t m) (fun x => (bitCount x:ℝ)) = m*t*(1-t) := by
  have point (x : Fin m → Bool) : (bitCount x : ℝ) = ∑ i, if x i then (1:ℝ) else 0 := by
    simp [bitCount]
  simp only [point]
  unfold bernoulliVectorWeight
  rw [productWeight_variance_sum (fun _ : Fin m => bernoulliWeight t)
    (fun _ (b : Bool) => if b then (1:ℝ) else 0) (fun _ => bernoulliWeight_sum t)]
  simp [bernoulli_scaled_variance, mul_assoc]

/-- The finite numerator of the periodic rounding variance. -/
def visitRoundingNumerator (g x y : ℕ) : ℝ :=
  let u := |((x%g : ℕ):ℝ) - (y%g : ℕ)|
  u*((g:ℝ)-u)

/-- For actual binomial prefix lengths this is the exact complete-block
variance. Division by 2g² gives the binomial term m t(1-t)/g² plus the
mean of the periodic quadratic rounding kernel. -/
theorem binomial_phase_visit_variance (g m : ℕ) (t : ℝ) (hg : 0 < g) :
    2*(g:ℝ)*(∑ a : Fin g, centeredSecond (bernoulliVectorWeight t m)
      (fun x => (residuePrefixCount g a.val (bitCount x) : ℝ))) =
      2*m*t*(1-t) + mean (bernoulliVectorWeight t m) (fun x =>
        mean (bernoulliVectorWeight t m) (fun y => visitRoundingNumerator g (bitCount x) (bitCount y))) := by
  let w := bernoulliVectorWeight t m
  let F := fun (a : Fin g) (x : Fin m → Bool) => (residuePrefixCount g a.val (bitCount x):ℝ)
  have hw := bernoulliVectorWeight_sum t m
  have H (x y : Fin m → Bool) : (g:ℝ)*(∑ a : Fin g, (F a x - F a y)^2) =
      ((bitCount x:ℝ)-bitCount y)^2 + visitRoundingNumerator g (bitCount x) (bitCount y) :=
    phase_visit_sq_sum g (bitCount x) (bitCount y) hg
  have total := congrArg (fun f : (Fin m → Bool) → (Fin m → Bool) → ℝ =>
    mean w fun x => mean w fun y => f x y) (funext fun x => funext (H x))
  simp only [quotientMean_mul, mean_sum, mean_add, phase_two_copy_square w _ hw,
    ← Finset.mul_sum, w, phase_bitCount_exact_variance] at total
  change 2*(g:ℝ)*(∑ a, centeredSecond (bernoulliVectorWeight t m) (F a)) = _
  linarith

/-- Changing from consecutive source labels to the hit phases of a fixed
physical target permutes one complete block. Thus the rounding term
belongs to the original source-prefix geometry for every fixed target. -/
theorem source_block_visit_variance (h g j start m : ℕ) (t : ℝ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hj : j < g) :
    2*(g:ℝ)*(∑ s : Fin g, centeredSecond (bernoulliVectorWeight t m)
      (fun x => (sourcePrefixCount h g j (start+s.val) (bitCount x) : ℝ))) =
      2*m*t*(1-t) + mean (bernoulliVectorWeight t m) (fun x =>
        mean (bernoulliVectorWeight t m) (fun y => visitRoundingNumerator g (bitCount x) (bitCount y))) := by
  choose a ha hp using fun s : Fin g => exists_coprime_source_phase h g j (start+s.val) hg hc hj
  let phase := fun s : Fin g => (⟨a s, ha s⟩ : Fin g)
  have inj : Function.Injective phase := by
    intro s u he
    have ae : a s = a u := congrArg Fin.val he
    have pe := (hp s).trans (hp u).symm
    rw [ae] at pe
    have sub := Nat.ModEq.add_right_cancel' (h*a u) pe
    have key := Nat.ModEq.add_left_cancel' start sub
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt u.isLt] using key
  let e := Equiv.ofBijective phase ((Finite.injective_iff_bijective).mp inj)
  let V := fun p : Fin g => centeredSecond (bernoulliVectorWeight t m)
    (fun x => (residuePrefixCount g p.val (bitCount x) : ℝ))
  have sumEq : (∑ s : Fin g, centeredSecond (bernoulliVectorWeight t m)
      (fun x => (sourcePrefixCount h g j (start+s.val) (bitCount x) : ℝ))) = ∑ k : Fin g, V k := by
    rw [← Equiv.sum_comp e V]
    apply Finset.sum_congr rfl
    intro s _
    simp only [sourcePrefixCount_eq_of_phase h g j (start+s.val) (a s) _ hc (ha s) (hp s)]
    rfl
  rw [sumEq]
  exact binomial_phase_visit_variance g m t hg

end Shellsort
end
