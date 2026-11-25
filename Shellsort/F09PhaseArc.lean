import Shellsort.CyclicArcTrace
import Shellsort.SourceArcBlocks

/-! Exact one-dimensional kernel for the finite arc variance. All shifts
may wind around the residue circle arbitrarily many times. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Number of starting phases leaving a cyclic interval when its endpoint
is translated by the directed residue difference from x to y. -/
def cyclicArcLoss (g ell x y : ℕ) : ℕ :=
  let d := (y + (g - x % g)) % g
  min (min ell (g - ell)) (min d (g - d))

private theorem phase_rotation_sum (g b : ℕ) (hg : 0 < g) (F : ℕ → ℝ) :
    (∑ s : Fin g, F ((s.val + b) % g)) = ∑ s : Fin g, F s.val := by
  let _ : NeZero g := ⟨hg.ne'⟩
  simpa only [Equiv.coe_addRight, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod] using
    (Equiv.sum_comp (Equiv.addRight (⟨b%g, Nat.mod_lt _ hg⟩ : Fin g)) (fun s : Fin g => F s.val))

private theorem phase_exit_count (g ell d : ℕ) (hl : ell ≤ g) (hd : d < g) :
    (∑ s : Fin g, if s.val < ell ∧ ell ≤ (s.val + d) % g then (1:ℝ) else 0) =
      (min (min ell (g-ell)) (min d (g-d)) : ℕ) := by
  let lo := ell - d
  let hi := min ell (g - d)
  have seteq : (Finset.range g).filter
      (fun s => s < ell ∧ ell ≤ (s + d) % g) = Finset.Ico lo hi := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, lo, hi, lt_min_iff]
    by_cases hs : s < g
    · by_cases hw : s + d < g
      · rw [Nat.mod_eq_of_lt hw]; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show s+d-g < g by omega)]
        omega
    · omega
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ =>
    if s < ell ∧ ell ≤ (s+d)%g then (1:ℝ) else 0), Finset.sum_boole, seteq, Nat.card_Ico]
  congr 1
  dsimp only [lo, hi]
  omega

theorem phase_departures_eq_cyclicArcLoss (g ell x y : ℕ) (hg : 0 < g) (hl : ell ≤ g) :
    (∑ s : Fin g, arcDeparture g ell x y s.val) = (cyclicArcLoss g ell x y : ℝ) := by
  let d := (y + (g - x % g)) % g
  have hxd : (x + d) % g = y % g := by
    dsimp [d]
    rw [Nat.add_mod_mod, ← Nat.mod_add_mod]
    have key : x % g + (y + (g - x % g)) = y + g := by have := Nat.mod_lt x hg; omega
    rw [key, Nat.add_mod_right]
  have shift (s : ℕ) : ((s + x)%g + d)%g = (s+y)%g := by
    rw [Nat.mod_add_mod, Nat.add_assoc, ← Nat.add_mod_mod, hxd, Nat.add_mod_mod]
  let F := fun a : ℕ => if a < ell ∧ ell ≤ (a+d)%g then (1:ℝ) else 0
  calc
    _ = ∑ s : Fin g, F ((s.val+x)%g) := by
      apply Finset.sum_congr rfl
      intro s _
      dsimp [F, arcDeparture]
      rw [shift]
    _ = ∑ s : Fin g, F s.val := phase_rotation_sum g x hg F
    _ = _ := phase_exit_count g ell d hl (Nat.mod_lt _ hg)

private theorem phaseMean_left {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => a*f x) = a*mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

private theorem phaseMean_right {α : Type*} [Fintype α] (w f : α → ℝ) (a : ℝ) :
    mean w (fun x => f x*a) = mean w f*a := by
  simp only [mean, Finset.sum_mul, mul_assoc]

private theorem phaseDepartureMean (g ell m s : ℕ) (t : ℝ) :
    (mean (bernoulliVectorWeight t m) fun x => mean (bernoulliVectorWeight t m) fun y =>
      arcDeparture g ell (bitCount x) (bitCount y) s) =
      canonicalArcProb g ell m t s * (1-canonicalArcProb g ell m t s) := by
  let w := bernoulliVectorWeight t m
  let f (x : Fin m → Bool) : ℝ := if (s+bitCount x)%g < ell then 1 else 0
  have point (x y : Fin m → Bool) : arcDeparture g ell (bitCount x) (bitCount y) s =
      f x * (1-f y) := by
    unfold arcDeparture f
    split_ifs <;> norm_num <;> omega
  change (mean w fun x => mean w fun y => _) = mean w f * (1-mean w f)
  simp only [point, phaseMean_left, mean_sub, mean_const w (bernoulliVectorWeight_sum t m),
    phaseMean_right]

/-- The entire finite-block variance is the expectation of the exact
cyclic loss for two independent counts, including the wraparound region. -/
theorem canonicalArcTrace_eq_phaseKernel (g ell m : ℕ) (t : ℝ) (hg : 0 < g) (hl : ell ≤ g) :
    canonicalArcTrace g ell m t = mean (bernoulliVectorWeight t m) fun x =>
      mean (bernoulliVectorWeight t m) fun y => (cyclicArcLoss g ell (bitCount x) (bitCount y) : ℝ) := by
  unfold canonicalArcTrace
  simp_rw [← phaseDepartureMean, ← mean_sum, phase_departures_eq_cyclicArcLoss _ _ _ _ hg hl]

/-- The same kernel governs an entire physical source block with coprime
reduced increments, for every selected owner phase and every pivot count. -/
theorem fullArcTrace_eq_phaseKernel (h g o ell y m : ℕ) (t : ℝ) (hg : 0 < g)
    (hc : Nat.Coprime h g) (hl : ell ≤ g) :
    fullArcTrace h g o ell y m t = mean (bernoulliVectorWeight t m) fun x =>
      mean (bernoulliVectorWeight t m) fun z => (cyclicArcLoss g ell (bitCount x) (bitCount z) : ℝ) :=
  (fullArcTrace_eq_canonical h g o ell y m t hg hc hl).trans
    (canonicalArcTrace_eq_phaseKernel g ell m t hg hl)

end Shellsort
end
