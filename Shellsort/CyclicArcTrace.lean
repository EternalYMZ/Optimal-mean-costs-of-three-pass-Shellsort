import Shellsort.CyclicArcDefinitions
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Group.Fin.Basic

noncomputable section
namespace Shellsort
open scoped BigOperators

private theorem sum_rotate (g b : ℕ) (hg : 0 < g) (F : ℕ → ℝ) :
    (∑ s : Fin g, F ((s.val+b)%g)) = ∑ s : Fin g, F s.val := by
  let _ : NeZero g := ⟨hg.ne'⟩
  simpa only [Equiv.coe_addRight, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod] using
    (Equiv.sum_comp (Equiv.addRight (⟨b%g, Nat.mod_lt _ hg⟩ : Fin g)) (fun s : Fin g => F s.val))

private theorem sum_interval (g lo hi : ℕ) (_hle : lo ≤ hi) (hhi : hi ≤ g) :
    (∑ s : Fin g, if lo ≤ s.val ∧ s.val < hi then (1:ℝ) else 0) = (hi-lo : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => if lo ≤ s ∧ s < hi then (1:ℝ) else 0), Finset.sum_boole]
  have sets : (Finset.range g).filter (fun x => lo ≤ x ∧ x < hi) = Finset.Ico lo hi := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [sets, Nat.card_Ico]

/-- The shifted interval exits at exactly d sites when d is shorter than
both the interval and its complement. -/
private theorem exact_outgoing (g ell d : ℕ) (hd : d ≤ ell) (hd' : d ≤ g-ell) (hl : ell ≤ g) :
    (∑ s : Fin g, if s.val < ell ∧ ell ≤ (s.val+d)%g then (1:ℝ) else 0) = d := by
  calc
    _ = ∑ s : Fin g, if ell-d ≤ s.val ∧ s.val < ell then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      have eq : s.val < ell ∧ ell ≤ (s.val+d)%g ↔ ell-d ≤ s.val ∧ s.val < ell := by
        by_cases H : s.val < ell
        · rw [Nat.mod_eq_of_lt (show s.val+d < g by omega)]
          omega
        · omega
      simp only [eq]
    _ = _ := by rw [sum_interval _ _ _ (by omega) hl]; congr 1; omega

private theorem exact_incoming (g ell d : ℕ) (hd : d ≤ ell) (hd' : d ≤ g-ell) (hl : ell ≤ g) :
    (∑ s : Fin g, if (s.val+d)%g < ell ∧ ell ≤ s.val then (1:ℝ) else 0) = d := by
  calc
    _ = ∑ s : Fin g, if g-d ≤ s.val ∧ s.val < g then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      have sl := s.isLt
      have eq : (s.val+d)%g < ell ∧ ell ≤ s.val ↔ g-d ≤ s.val ∧ s.val < g := by
        by_cases H : s.val+d < g
        · rw [Nat.mod_eq_of_lt H]; omega
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show s.val+d-g<g by omega)]
          omega
      simp only [eq]
    _ = _ := by rw [sum_interval _ _ _ (by omega) (le_refl g)]; congr 1; omega

def arcDeparture (g ell x y s : ℕ) : ℝ :=
  if (s+x)%g < ell ∧ ell ≤ (s+y)%g then 1 else 0

theorem truncated_le_phase_departures (g ell x y : ℕ) (hg : 0 < g) (hl : ell ≤ g) :
    (if Nat.dist x y ≤ min ell (g-ell) then (Nat.dist x y : ℝ) else 0) ≤
      ∑ s : Fin g, arcDeparture g ell x y s.val := by
  split_ifs with small
  · have he := (le_min_iff.mp small).1
    have hc := (le_min_iff.mp small).2
    rcases le_total x y with hxy | hyx
    · let d := y-x
      have eq : y=x+d := by dsimp [d]; omega
      have dist : Nat.dist x y = d := by simp [Nat.dist,d, Nat.sub_eq_zero_of_le hxy]
      rw [dist] at he hc ⊢
      have H := sum_rotate g x hg (fun a => if a < ell ∧ ell ≤ (a+d)%g then (1:ℝ) else 0)
      rw [exact_outgoing _ _ _ he hc hl] at H
      rw [← H]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro s _
      simp [arcDeparture, Nat.mod_add_mod, Nat.add_assoc, ← eq]
    · let d := x-y
      have eq : x=y+d := by dsimp [d]; omega
      have dist : Nat.dist x y = d := by simp [Nat.dist,d, Nat.sub_eq_zero_of_le hyx]
      rw [dist] at he hc ⊢
      have H := sum_rotate g y hg (fun a => if (a+d)%g < ell ∧ ell ≤ a then (1:ℝ) else 0)
      rw [exact_incoming _ _ _ he hc hl] at H
      rw [← H]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro s _
      simp [arcDeparture, Nat.mod_add_mod, Nat.add_assoc, ← eq]
  · apply Finset.sum_nonneg
    intro s _
    unfold arcDeparture
    split <;> norm_num

private lemma arc_mean_lmul {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => a * f x) = a * mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

private lemma arc_mean_rmul {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => f x * a) = mean w f * a := by
  simp only [mean, Finset.sum_mul, mul_assoc]

private lemma arc_mean_mono {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    {f b : α → ℝ} (h : ∀ i, f i ≤ b i) : mean w f ≤ mean w b :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hw i)

private theorem departure_mean (g ell m s : ℕ) (t : ℝ) :
    (mean (bernoulliVectorWeight t m) fun x => mean (bernoulliVectorWeight t m) fun y =>
      arcDeparture g ell (bitCount x) (bitCount y) s) =
      canonicalArcProb g ell m t s * (1-canonicalArcProb g ell m t s) := by
  let w := bernoulliVectorWeight t m
  let f (x : Fin m → Bool) : ℝ := if (s+bitCount x)%g < ell then 1 else 0
  have point (x y : Fin m → Bool) : arcDeparture g ell (bitCount x) (bitCount y) s =
      f x * (1-f y) := by
    unfold arcDeparture f
    split_ifs <;> norm_num <;> omega
  have hw := bernoulliVectorWeight_sum t m
  change (mean w fun x => mean w fun y => _) = mean w f * (1-mean w f)
  simp only [point,arc_mean_lmul,mean_sub,mean_const w hw,arc_mean_rmul]

theorem truncated_binomial_le_own_trace (g ell m : ℕ) (t : ℝ) (hg : 0 < g) (hl : ell ≤ g)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    (mean (bernoulliVectorWeight t m) fun x => mean (bernoulliVectorWeight t m) fun y =>
      if Nat.dist (bitCount x) (bitCount y) ≤ min ell (g-ell) then
        (Nat.dist (bitCount x) (bitCount y) : ℝ) else 0) ≤ canonicalArcTrace g ell m t := by
  unfold canonicalArcTrace
  simp_rw [← departure_mean, ← mean_sum]
  have nn := bernoulliVectorWeight_nonneg t ht m
  exact arc_mean_mono _ nn fun x => arc_mean_mono _ nn fun y =>
    truncated_le_phase_departures _ _ _ _ hg hl

theorem canonicalArcProb_half (g ell m : ℕ) (t : ℝ) (s : Fin g)
    (hg : 0 < g) (_hl : ell ≤ g) (ht : 0 ≤ t ∧ t ≤ 1) :
    2*(canonicalArcProb g ell m t s.val*(1-canonicalArcProb g ell m t s.val)) ≤
      canonicalArcTrace g ell m t := by
  let mask := fun z : Fin m → Bool => Finset.univ.filter
    (fun i : Fin g => (i.val + bitCount z)%g < ell)
  have card (z : Fin m → Bool) :
      ((mask z).card : ℝ) = ∑ i : Fin g, if i.val < ell then 1 else 0 := by
    rw [← sum_rotate g (bitCount z) hg (fun i => if i < ell then 1 else 0)]
    simp [mask, Finset.sum_boole]
  have fixed (x y : Fin m → Bool) : (mask x).card = (mask y).card := by
    exact_mod_cast (card x).trans (card y).symm
  have ident (i : Fin g) : phaseMarginal (bernoulliVectorWeight t m) mask i =
      canonicalArcProb g ell m t i.val := by simp [phaseMarginal,mask,canonicalArcProb]
  simpa only [ident,canonicalArcTrace] using fixed_card_phase_variance
    (bernoulliVectorWeight t m) mask (bernoulliVectorWeight_nonneg t ht m)
    (bernoulliVectorWeight_sum t m) (fun x y _ _ => fixed x y) s

theorem canonicalArcTrace_succ (g ell m : ℕ) (t : ℝ) (hg : 0 < g) (ht : 0 ≤ t ∧ t ≤ 1) :
    canonicalArcTrace g ell m t ≤ canonicalArcTrace g ell (m+1) t := by
  let p := canonicalArcProb g ell m t
  let v (s : ℕ) := p s*(1-p s)
  have periodic (s : ℕ) : p (s%g) = p s := by simp [p,canonicalArcProb,Nat.mod_add_mod]
  have shift : (∑ s : Fin g, v (s.val+1)) = ∑ s : Fin g, v s.val := by
    simpa only [v,periodic] using sum_rotate g 1 hg v
  have add (s : ℕ) : canonicalArcProb g ell (m+1) t s = (1-t)*p s + t*p (s+1) := by
    have H := bernoulli_count_succ_mean t m (fun x => if (s+x)%g < ell then 1 else 0)
    simpa only [p,canonicalArcProb, Nat.add_assoc, Nat.add_comm 1] using H
  have concave (s : Fin g) : (1-t)*v s.val + t*v (s.val+1) ≤
      canonicalArcProb g ell (m+1) t s.val*(1-canonicalArcProb g ell (m+1) t s.val) := by
    rw [add]; dsimp only [v]
    nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (p s.val - p (s.val+1)))]
  have H := Finset.sum_le_sum (s := Finset.univ) (fun s _ => concave s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, shift] at H
  change (∑ s : Fin g, v s.val) ≤ _
  dsimp only [canonicalArcTrace] at *
  linarith

theorem truncated_binomial_le_trace (g ell k m : ℕ) (t : ℝ) (hg : 0 < g) (hl : ell ≤ g)
    (hkm : k ≤ m) (ht : 0 ≤ t ∧ t ≤ 1) :
    (mean (bernoulliVectorWeight t k) fun x => mean (bernoulliVectorWeight t k) fun y =>
      if Nat.dist (bitCount x) (bitCount y) ≤ min ell (g-ell) then
        (Nat.dist (bitCount x) (bitCount y) : ℝ) else 0) ≤ canonicalArcTrace g ell m t :=
  (truncated_binomial_le_own_trace g ell k t hg hl ht).trans
    ((monotone_nat_of_le_succ fun j => canonicalArcTrace_succ g ell j t hg ht) hkm)

end Shellsort
end
