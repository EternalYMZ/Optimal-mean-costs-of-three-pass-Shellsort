import Shellsort.AllGapThreePassLower
import Mathlib.Order.Interval.Finset.Nat

/-! Summing lower bounds on the middle half of the residue arcs. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

def centralArcLengths (g : ℕ) : Finset ℕ := Finset.Icc ((g+3)/4) (3*g/4)

theorem centralArcLengths_size (g : ℕ) (hg : 2 ≤ g) :
    g ≤ 4 * (centralArcLengths g).card := by
  rw [centralArcLengths,Nat.card_Icc]
  omega

theorem centralArcLengths_valid {g l : ℕ} (hg : 2 ≤ g) (hl : l ∈ centralArcLengths g) :
    0 < l ∧ l < g ∧ g ≤ 4*min l (g-l) := by
  obtain ⟨low,high⟩ := Finset.mem_Icc.mp hl
  change (g+3)/4 ≤ l at low
  change l ≤ 3*g/4 at high
  omega

/-- The paper's fluctuation scale on a central arc controls half of the
uniform scale per arc, also for the small moduli g=2,3. -/
theorem centralArc_scale_lower {g l : ℕ} (hg : 2 ≤ g) (hl : l ∈ centralArcLengths g)
    (b s : ℝ) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    Real.sqrt (b*min (g:ℝ) s)/2 ≤ Real.sqrt (b*min ((min l (g-l):ℕ):ℝ) s) := by
  have ge : (g:ℝ) ≤ 4*((min l (g-l) : ℕ):ℝ) := by
    exact_mod_cast (centralArcLengths_valid hg hl).2.2
  have bound : min (g:ℝ) s ≤ 4*min ((min l (g-l):ℕ):ℝ) s := by
    rcases le_total ((min l (g-l):ℕ):ℝ) s with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans ge
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith)
  have roots := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left bound hb)
  rwa [show b*(4*min ((min l (g-l):ℕ):ℝ) s)=
      2^2 * (b*min ((min l (g-l):ℕ):ℝ) s) by ring,
    Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ)^2),Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2),
    ← div_le_iff₀' (by norm_num : (0:ℝ) < 2)] at roots

/-- The arc count lower estimates at fixed original slots aggregate to a
single bound on any total counted exactly twice by those arcs. -/
theorem centralArc_double_sum_lower (n g : ℕ) (hg : 2 ≤ g) (b s total : ℝ)
    (hb : 0 ≤ b) (hs : 0 ≤ s) (reward : Fin n → ℕ → ℝ) (hnonneg : ∀ i l, 0 ≤ reward i l)
    (lower : ∀ i, ∀ l ∈ centralArcLengths g,
      Real.sqrt (b*min ((min l (g-l):ℕ):ℝ) s)/1600 ≤ reward i l)
    (double : 2*total = ∑ i, ∑ l ∈ Finset.range g, reward i l) :
    (n:ℝ)*g*Real.sqrt (b*min (g:ℝ) s)/25600 ≤ total := by
  let T := Real.sqrt (b*min (g:ℝ) s)
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have card : (g:ℝ) ≤ 4*((centralArcLengths g).card : ℝ) := by
    exact_mod_cast centralArcLengths_size g hg
  have allArcs (i : Fin n) : (g:ℝ)*T/12800 ≤ ∑ l ∈ Finset.range g, reward i l := by
    calc
      _ ≤ ((centralArcLengths g).card:ℝ)*(T/3200) := by
        nlinarith [mul_le_mul_of_nonneg_right card hT]
      _ = ∑ _l ∈ centralArcLengths g, T/3200 := by simp
      _ ≤ ∑ l ∈ centralArcLengths g, reward i l := by
        apply Finset.sum_le_sum
        intro l hl
        have cut := centralArc_scale_lower hg hl b s hb hs
        change T/2 ≤ _ at cut
        linarith [lower i l hl]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun l hl => Finset.mem_range.mpr (centralArcLengths_valid hg hl).2.1)
        (fun l _ _ => hnonneg i l)
  have a := Finset.sum_le_sum (s := Finset.univ) (fun i _ => allArcs i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← double] at a
  dsimp [T] at a
  linarith

/-- Converting the integer source length to the two-scale bound uses
only the uniform rounding factor when h ≤ n. -/
theorem arc_scale_rounding (n h g : ℕ) (hh : 0 < h) (hhn : h ≤ n) (hg : 0 < g) :
    min ((g:ℝ)*Real.sqrt h) (Real.sqrt g * Real.sqrt (Real.sqrt ((n:ℝ)*h))) ≤
    (5/4:ℝ)*((g:ℝ)*Real.sqrt ((h:ℝ)/g*min (g:ℝ) (Real.sqrt (n/h:ℕ)))) := by
  let m := n/h
  have gp : (0:ℝ) < g := by exact_mod_cast hg
  have hpos : (0:ℝ) < h := by exact_mod_cast hh
  have mpos : 1 ≤ m := (Nat.le_div_iff_mul_le hh).mpr (by simpa using hhn)
  have natbound : n ≤ 2*m*h := by
    have := Nat.mod_add_div n h
    have := Nat.mod_lt n hh
    have hm := Nat.mul_le_mul_right h mpos
    dsimp [m] at *
    rw [Nat.mul_comm h (n/h)] at *
    rw [Nat.mul_assoc]
    omega
  have rn : (n:ℝ) ≤ 2*(m:ℝ)*h := by exact_mod_cast natbound
  change _ ≤ (5/4:ℝ)*((g:ℝ)*Real.sqrt ((h:ℝ)/g*min (g:ℝ) (Real.sqrt m)))
  rcases le_total (g:ℝ) (Real.sqrt m) with small | large
  · rw [min_eq_left small, div_mul_cancel₀ _ gp.ne']
    apply (min_le_left _ _).trans
    nlinarith [show 0 ≤ (g:ℝ)*Real.sqrt h by positivity]
  · rw [min_eq_right large]
    apply (min_le_right _ _).trans
    have frac : 0 ≤ (h:ℝ)/g*Real.sqrt m := by positivity
    have base : ((g:ℝ)*Real.sqrt ((h:ℝ)/g*Real.sqrt m))^2 = (g:ℝ)*h*Real.sqrt m := by
      rw [mul_pow, Real.sq_sqrt frac]
      field_simp
    have inner : Real.sqrt ((n:ℝ)*h) ≤ 25/16*((h:ℝ)*Real.sqrt m) := by
      apply le_of_sq_le_sq _ (by positivity)
      rw [Real.sq_sqrt (by positivity), mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      nlinarith [mul_le_mul_of_nonneg_right rn hpos.le,
        mul_nonneg (Nat.cast_nonneg m) (sq_nonneg (h:ℝ))]
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _), mul_pow, base]
    nlinarith [mul_le_mul_of_nonneg_left inner gp.le]

theorem centralArc_remaining_scale_lower (n h g : ℕ) (hh : 0 < h) (hhn : h ≤ n)
    (hg : 0 < g) (hLarge : n ≤ h^2) (gLarge : h ≤ g^2) :
    Real.sqrt n/2 ≤ (g:ℝ)*Real.sqrt ((h:ℝ)/g*min (g:ℝ) (Real.sqrt (n/h:ℕ))) := by
  have s := lower_twoPass_scales_of_large_gaps (Nat.cast_nonneg n) (Nat.cast_nonneg h)
    (Nat.cast_nonneg g) (by exact_mod_cast hLarge) (by exact_mod_cast gLarge)
  linarith [s.trans (arc_scale_rounding n h g hh hhn hg), Real.sqrt_nonneg (n:ℝ)]

end Shellsort
end

