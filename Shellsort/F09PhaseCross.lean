import Shellsort.F09PhaseMixed
import Shellsort.F09PhaseVisits

/-! The complete count field of one class for a cross-class pivot. Its
source lengths are those of the physical array and may have a remainder. -/
noncomputable section
namespace Shellsort
open Filter Set Real
open scoped BigOperators Topology

theorem phaseMean_mono {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    {f z : α → ℝ} (hf : ∀ a, f a ≤ z a) : mean w f ≤ mean w z :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf a) (hw a)

/-- No selected source phase can amplify a change in count by more than
one visit beyond the scaled count change. The owner phase may be random. -/
theorem source_prefix_pair_scaled (h g j s x y : ℕ) (hg : 0 < g) (hc : Nat.Coprime h g) (hj : j < g) :
    |(g:ℝ)*((sourcePrefixCount h g j s x:ℝ)-sourcePrefixCount h g j s y) -
      ((x:ℝ)-y)| ≤ g := by
  have realBound :
      |((g:ℝ)*sourcePrefixCount h g j s x - x) -
       ((g:ℝ)*sourcePrefixCount h g j s y - y)| ≤ (g:ℝ)-1 := by
    exact_mod_cast source_residual_diff_bound h g j s x y hg hc hj
  have same : (g:ℝ)*((sourcePrefixCount h g j s x:ℝ)-sourcePrefixCount h g j s y) -
      ((x:ℝ)-y) = ((g:ℝ)*sourcePrefixCount h g j s x - x) -
       ((g:ℝ)*sourcePrefixCount h g j s y - y) := by ring
  rw [same]; linarith

/-- Uniform second moment of the centered visits to a specified physical
target in the critical scaling. -/
theorem source_visit_variance_bound (h g j s m : ℕ) (t : ℝ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hj : j < g) (ht : t ∈ Icc 0 1) :
    centeredSecond (bernoulliVectorWeight t m)
      (fun z => (sourcePrefixCount h g j s (bitCount z):ℝ)) ≤ 1+2*m/(g:ℝ)^2 := by
  let w := bernoulliVectorWeight t m
  let F := fun z : Fin m → Bool => (sourcePrefixCount h g j s (bitCount z):ℝ)
  let B := fun z : Fin m → Bool => (bitCount z:ℝ)
  let A := (g:ℝ)^2
  have gp : (0:ℝ) < g := by exact_mod_cast hg
  have pBound (x y : Fin m → Bool) :
      A*(F x-F y)^2 ≤ 2*(B x-B y)^2+2*A := by
    have de := source_prefix_pair_scaled h g j s (bitCount x) (bitCount y) hg hc hj
    change |(g:ℝ)*(F x-F y)-(B x-B y)| ≤ g at de
    have sq := sq_le_sq' (abs_le.mp de).1 (abs_le.mp de).2
    dsimp only [A]
    nlinarith [sq_nonneg ((g:ℝ)*(F x-F y)-2*(B x-B y))]
  have nn := bernoulliVectorWeight_nonneg t ht m
  have est := phaseMean_mono w nn (fun x => phaseMean_mono w nn (pBound x))
  simp only [phaseMean_scale, mean_add, mean_const w (bernoulliVectorWeight_sum t m),
    phase_two_copy_square w _ (bernoulliVectorWeight_sum t m)] at est
  change A*(2*centeredSecond w F) ≤ 2*(2*centeredSecond w B)+2*A at est
  have bin : centeredSecond w B = (m:ℝ)*t*(1-t) := phase_bitCount_exact_variance m t
  rw [bin] at est
  have uv : t*(1-t) ≤ 1 := by nlinarith [sq_nonneg (t-1/2)]
  have cap := mul_le_mul_of_nonneg_left uv (Nat.cast_nonneg m)
  change centeredSecond w F ≤ 1+2*m/(g:ℝ)^2
  rw [← sub_le_iff_le_add', le_div_iff₀ (sq_pos_of_pos gp)]
  dsimp only [A] at est
  linarith

/-- Sum of the conditional source variances in the complete reference
class, for a target j which is independent of that reference field. -/
def referenceVisitVariance (h g j m rem : ℕ) (t : ℝ) :=
  ∑ s ∈ Finset.range h, centeredSecond (bernoulliVectorWeight t (sourceTrialLength m rem s))
    (fun x => (sourcePrefixCount h g j s (bitCount x):ℝ))

/-- The variance sum is the variance of the actual complete independent
reference field, with the physical long and short source lengths. -/
theorem referenceVisitVariance_eq_field (h g j m rem : ℕ) (t : ℝ) :
    centeredSecond (conditionalSourceWeight h m rem t)
      (fun x => ∑ s : Fin h, (sourcePrefixCount h g j s.val (bitCount (x s)):ℝ)) =
      referenceVisitVariance h g j m rem t := by
  unfold conditionalSourceWeight referenceVisitVariance
  rw [productWeight_variance_sum (fun s => sourceCoordinateWeight h m rem t s)
    (fun s x => (sourcePrefixCount h g j s.val (bitCount x):ℝ)) (sourceCoordinateWeight_sum h m rem t)]
  exact Fin.sum_univ_eq_sum_range (fun s : ℕ => centeredSecond (bernoulliVectorWeight t (sourceTrialLength m rem s))
    (fun x => (sourcePrefixCount h g j s (bitCount x):ℝ))) h

theorem mixed_reference_visit_critical_limit {G H m rem j : ℕ → ℕ}
    {t : ℕ → ℝ} {lam T : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop)
    (hGH : Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0))
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (ht01 : ∀ n, t n ∈ Icc 0 1)
    (hc : ∀ n, Nat.Coprime (H n) (G n)) (hj : ∀ n, j n < G n)
    (hh : ∀ n, 0 < H n) (hr : ∀ n, rem n ≤ H n) :
    Tendsto (fun n => referenceVisitVariance (H n) (G n) (j n) (m n) (rem n) (t n)/(H n:ℝ))
      atTop (𝓝 (lam*F09.v T + F09.W (lam*F09.v T))) := by
  let F := fun n M s => centeredSecond (bernoulliVectorWeight (t n) M)
    (fun x => (sourcePrefixCount (H n) (G n) (j n) s (bitCount x):ℝ))
  let C := fun n => 1+2*(((m n+1:ℕ):ℝ)/(G n:ℝ)^2)
  have one := critical_plus_one_source_length hG hm
  have hC : Tendsto C atTop (𝓝 (1+2*lam)) := tendsto_const_nhds.add (tendsto_const_nhds.mul one)
  have err : Tendsto (fun n => (3*(G n:ℝ)*C n)/(H n:ℝ)) atTop (𝓝 0) := by
    have H := ((tendsto_const_nhds (x:=(3:ℝ))).mul hGH).mul hC
    convert H using 1
    · funext n; ring
    · ring
  have per (n M s : ℕ) : F n M (s%G n) = F n M s := by simp [F,sourcePrefixCount,Nat.mod_add_mod]
  have bd (n M s : ℕ) (hM : M ≤ m n+1) : 0 ≤ F n M s ∧ F n M s ≤ C n := by
    refine ⟨centeredSecond_nonneg _ _ (bernoulliVectorWeight_nonneg _ (ht01 n) _), ?_⟩
    apply (source_visit_variance_bound (H n) (G n) (j n) s M (t n) (by have := hj n; omega)
      (hc n) (hj n) (ht01 n)).trans
    dsimp [C]
    have cmp := div_le_div_of_nonneg_right (by exact_mod_cast hM : (M:ℝ) ≤ (m n+1:ℕ)) (sq_nonneg (G n:ℝ))
    rw [mul_div_assoc]
    linarith
  apply mixed_phase_average_limit hh hr (source_block_visit_critical_limit (start:=fun _ => 0) hG hm ht ht01 hc hj)
    (source_block_visit_critical_limit (start:=fun _ => 0) hG one ht ht01 hc hj) err
  intro n
  have mix := mixed_phase_error (G n) (H n) (rem n) (by have := hj n; omega) (hr n) (F n (m n)) (F n (m n+1))
    (C n) (per _ _) (per _ _) (fun s => bd n (m n) s (by omega)) (fun s => bd n (m n+1) s le_rfl)
  have expand (s : ℕ) : F n (sourceTrialLength (m n) (rem n) s) s =
      if s<rem n then F n (m n+1) s else F n (m n) s := by dsimp only [sourceTrialLength]; split <;> rfl
  change |(∑ s ∈ Finset.range (H n), F n (sourceTrialLength (m n) (rem n) s) s) - _| ≤ _
  simp_rw [expand]
  dsimp only at mix
  rw [← Fin.sum_univ_eq_sum_range (F n (m n)) (G n), ← Fin.sum_univ_eq_sum_range (F n (m n+1)) (G n)] at mix
  simpa only [Nat.zero_add, F] using mix

end Shellsort
end
