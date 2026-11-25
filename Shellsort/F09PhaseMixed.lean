import Shellsort.F09PhaseArcLimit
import Mathlib.Tactic

/-! Actual mixed source lengths and the missing pivot source. All errors
are uniform in pivot phase, height and threshold, including empty intervals. -/
noncomputable section
namespace Shellsort
open Filter Real Set
open scoped BigOperators Topology

private theorem whole_phase_blocks (g q : ℕ) (f : ℕ → ℝ) (hp : ∀ a, f (a%g) = f a) :
    ∑ s ∈ Finset.range (q*g), f s = q * ∑ r ∈ Finset.range g, f r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have eq (s : ℕ) : f (q*g+s) = f s := by
      calc
        _ = f ((q*g+s)%g) := (hp _).symm
        _ = f (s%g) := by rw [Nat.mul_comm q g, Nat.mul_add_mod_self_left]
        _ = _ := hp s
    simp only [eq, Nat.cast_succ]; ring

/-- A terminal incomplete period loses at most g times one summand's range. -/
theorem phase_prefix_error (g N : ℕ) (hg : 0 < g) (f : ℕ → ℝ) (C : ℝ)
    (hp : ∀ a, f (a%g) = f a) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ C) :
    |(∑ s ∈ Finset.range N, f s) - N*((∑ s ∈ Finset.range g, f s)/(g:ℝ))| ≤ g*C := by
  let avg := (∑ s ∈ Finset.range g, f s)/(g:ℝ)
  have sumBounds (K : ℕ) (a : ℕ) : 0 ≤ ∑ s ∈ Finset.range K, f (a+s) ∧
      (∑ s ∈ Finset.range K, f (a+s)) ≤ K*C := by
    exact ⟨Finset.sum_nonneg fun s _ => (hf _).1,
      (Finset.sum_le_sum fun s (_ : s ∈ Finset.range K) => (hf (a+s)).2).trans_eq (by simp)⟩
  have gp : (0:ℝ) < g := by exact_mod_cast hg
  have sa : 0 ≤ avg ∧ avg ≤ C := by
    have H := sumBounds g 0; simp only [Nat.zero_add] at H
    exact ⟨div_nonneg H.1 gp.le,(div_le_iff₀ gp).mpr (by linarith [H.2])⟩
  have avgId : ∑ s ∈ Finset.range g, f s = g*avg := by dsimp [avg]; field_simp
  have natEq : N/g*g + N%g = N := by rw [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]
  have eReal : ((N/g:ℕ):ℝ)*g+((N%g:ℕ):ℝ) = N := by exact_mod_cast natEq
  have sumId := Finset.sum_range_add f (N/g*g) (N%g)
  rw [natEq, whole_phase_blocks g (N/g) f hp, avgId] at sumId
  have tail := sumBounds (N%g) (N/g*g)
  have rg : ((N%g:ℕ):ℝ) ≤ g := by exact_mod_cast (Nat.mod_lt N hg).le
  have nn := (hf 0).1.trans (hf 0).2
  change |_ - (N:ℝ)*avg| ≤ _
  rw [sumId, ← eReal]
  have hb := mul_le_mul_of_nonneg_right rg nn
  have hu := mul_le_mul_of_nonneg_left sa.2 (Nat.cast_nonneg (N%g))
  have hz := mul_nonneg (Nat.cast_nonneg (N%g)) sa.1
  exact abs_le.mpr ⟨by linarith [tail.1],by linarith [tail.2]⟩

private theorem mixed_sum_eq (h rem : ℕ) (hr : rem ≤ h) (f z : ℕ → ℝ) :
    (∑ s ∈ Finset.range h, if s < rem then z s else f s) =
      (∑ s ∈ Finset.range h, f s) + (∑ s ∈ Finset.range rem, z s) - ∑ s ∈ Finset.range rem, f s := by
  have eq (s : ℕ) : (if s < rem then z s else f s) = f s + (if s<rem then z s-f s else 0) := by
    split_ifs <;> ring
  have cut : (Finset.range h).filter (fun s => s<rem) = Finset.range rem := by ext k; simp; omega
  simp only [eq, Finset.sum_add_distrib, ← Finset.sum_filter, cut, Finset.sum_sub_distrib]
  ring

/-- A pair of adjacent intervals with different source laws, using their own
complete-block averages. This estimate also applies to the visit variances. -/
theorem mixed_phase_error (g h rem : ℕ) (hg : 0 < g) (hr : rem ≤ h) (f z : ℕ → ℝ) (C : ℝ)
    (hp : ∀ s, f (s%g) = f s) (hz : ∀ s, z (s%g) = z s)
    (hf : ∀ s, 0 ≤ f s ∧ f s ≤ C) (hb : ∀ s, 0 ≤ z s ∧ z s ≤ C) :
    let A := (∑ s ∈ Finset.range g, f s)/(g:ℝ)
    let B := (∑ s ∈ Finset.range g, z s)/(g:ℝ)
    |(∑ s ∈ Finset.range h, if s<rem then z s else f s) -
      (((h:ℝ)-rem)*A+rem*B)| ≤ 3*g*C := by
  have e₁ := abs_le.mp (phase_prefix_error g h hg f C hp hf)
  have e₂ := abs_le.mp (phase_prefix_error g rem hg z C hz hb)
  have e₃ := abs_le.mp (phase_prefix_error g rem hg f C hp hf)
  rw [mixed_sum_eq h rem hr f z]
  exact abs_le.mpr ⟨by linarith [e₁.1,e₂.1,e₃.2],
    by linarith [e₁.2,e₂.2,e₃.1]⟩

private theorem physical_arc_var_bounds (h g o ell y m s : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    0 ≤ fullArcVar h g o ell y m s t ∧ fullArcVar h g o ell y m s t ≤ 1/4 := by
  let p := fullArcMarginal h g o ell y m s t
  have prob : 0 ≤ p ∧ p ≤ 1 := by
    unfold p fullArcMarginal mean
    constructor
    · exact Finset.sum_nonneg fun z _ => mul_nonneg
        (bernoulliVectorWeight_nonneg t ht _ _) (by dsimp only; split <;> norm_num)
    · apply le_trans _ (bernoulliVectorWeight_sum t m).le
      apply Finset.sum_le_sum
      intro z _
      dsimp only
      split <;> simp [bernoulliVectorWeight_nonneg t ht]
  change 0 ≤ p*(1-p) ∧ p*(1-p) ≤ 1/4
  exact ⟨mul_nonneg prob.1 (sub_nonneg.mpr prob.2), by nlinarith [sq_nonneg (p-1/2)]⟩

private theorem actual_arc_delete_owner (h g m rem ell : ℕ) (o : Fin h) (t : ℝ) (y : ℕ) :
    let f := fun s => fullArcVar h g o.val ell y (sourceTrialLength m rem s) s t
    sourceArcVariance h g m rem ell o t y + f o.val = ∑ s ∈ Finset.range h, f s := by
  let f := fun s => fullArcVar h g o.val ell y (sourceTrialLength m rem s) s t
  have sum : sourceArcVariance h g m rem ell o t y = ∑ s : Fin h, if s=o then 0 else f s.val := by
    apply Finset.sum_congr rfl
    intro s _
    let w := bernoulliVectorWeight t (sourceTrialLength m rem s.val)
    let e := fun z => pivotArcHit h g o.val ell y s.val (bitCount (m := sourceTrialLength m rem s.val) z)
    change eventMarginal w e * (1-eventMarginal w e) = _
    by_cases eq : s=o
    · subst s; simp [e,eventMarginal,pivotArcHit]
    · have ne : s.val ≠ o.val := fun he => eq (Fin.ext he)
      have raw : eventMarginal w e = fullArcMarginal h g o.val ell y (sourceTrialLength m rem s.val) s.val t := by
        unfold eventMarginal fullArcMarginal mean
        apply Finset.sum_congr rfl
        intro b _
        simp [e,w,pivotArcHit,ne,mul_ite]
      simp [eq,f,fullArcVar,raw]
  change _ + f o.val = ∑ s ∈ Finset.range h, f s
  rw [sum, ← Fin.sum_univ_eq_sum_range]
  have split := Finset.sum_erase_add Finset.univ (fun s : Fin h => f s.val) (Finset.mem_univ o)
  rw [← split]
  congr 1
  rw [Finset.sum_ite]
  simp [Finset.filter_ne']

/-- The centered variance of the true nonpivot endpoints, on the owner's
selected phase, differs from the two full-block averages by O(g). -/
theorem actual_arc_mixed_variance_error (h g m rem ell : ℕ) (o : Fin h) (t : ℝ) (y : ℕ)
    (hg : 0 < g) (hr : rem ≤ h) (ht : t ∈ Icc 0 1) :
    |sourceArcVariance h g m rem ell o t y -
      (((h:ℝ)-rem)*(fullArcTrace h g o.val ell y m t/g) +
          rem*(fullArcTrace h g o.val ell y (m+1) t/g))| ≤ (3*(g:ℝ)+1)/4 := by
  let F := fun m s => fullArcVar h g o.val ell y m s t
  have per (m s : ℕ) : F m (s%g) = F m s := by simp [F,fullArcVar,fullArcMarginal,Nat.mod_add_mod]
  have bd := fun m s => physical_arc_var_bounds h g o.val ell y m s t ht
  have mix := mixed_phase_error g h rem hg hr (F m) (F (m+1)) (1/4) (per _) (per _) (bd _) (bd _)
  have de := actual_arc_delete_owner h g m rem ell o t y
  have oe := bd (sourceTrialLength m rem o.val) o.val
  have ps (s : ℕ) : F (sourceTrialLength m rem s) s = if s<rem then F (m+1) s else F m s := by
    dsimp only [sourceTrialLength]; split <;> rfl
  change sourceArcVariance h g m rem ell o t y + F (sourceTrialLength m rem o.val) o.val =
      ∑ s ∈ Finset.range h, F (sourceTrialLength m rem s) s at de
  conv_rhs at de => simp only [ps]
  change |(∑ s ∈ Finset.range h, if s<rem then F (m+1) s else F m s) - _| ≤ _ at mix
  rw [← de] at mix
  dsimp only [F] at mix
  dsimp only [fullArcTrace]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp mix).1,oe.2], by linarith [(abs_le.mp mix).2,oe.1]⟩

/-- A bounded admixture of a second convergent block law has the same limit,
independently of the long-chain fraction. The error is in unnormalized units. -/
theorem mixed_phase_average_limit {h rem : ℕ → ℕ} {A B S err : ℕ → ℝ} {Z : ℝ}
    (hp : ∀ n, 0 < h n) (hr : ∀ n, rem n ≤ h n)
    (hA : Tendsto A atTop (𝓝 Z)) (hB : Tendsto B atTop (𝓝 Z))
    (he : Tendsto (fun n => err n/(h n:ℝ)) atTop (𝓝 0))
    (hS : ∀ n, |S n - (((h n:ℝ)-rem n)*A n + rem n*B n)| ≤ err n) :
    Tendsto (fun n => S n/(h n:ℝ)) atTop (𝓝 Z) := by
  let w := fun n => (rem n:ℝ)/(h n:ℝ)
  have wh (n : ℕ) : 0 ≤ w n ∧ w n ≤ 1 :=
    ⟨by dsimp [w]; positivity, (div_le_one (by exact_mod_cast hp n)).mpr (by exact_mod_cast hr n)⟩
  have d0 : Tendsto (fun n => B n - A n) atTop (𝓝 0) := by simpa using hB.sub hA
  have wd : Tendsto (fun n => w n*(B n-A n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => |B n-A n|)
    · intro n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (wh n).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (wh n).2
    · simpa [Function.comp_def] using continuous_abs.continuousAt.tendsto.comp d0
  let R := fun n => S n/(h n:ℝ) - (A n+w n*(B n-A n))
  have rem0 : Tendsto R atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => err n/(h n:ℝ)) _ he
    intro n
    have p : (0:ℝ) < h n := by exact_mod_cast hp n
    have ep : R n = (S n-(((h n:ℝ)-rem n)*A n+rem n*B n))/(h n:ℝ) := by
      dsimp [R,w]; field_simp; ring
    rw [Real.norm_eq_abs, ep, abs_div, abs_of_pos p]
    exact div_le_div_of_nonneg_right (hS n) p.le
  simpa only [R, sub_add_cancel, add_zero, zero_add] using rem0.add (hA.add wd)

theorem critical_plus_one_source_length {G m : ℕ → ℕ} {lam : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop)
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam)) :
    Tendsto (fun n => (((m n+1:ℕ):ℝ)/(G n:ℝ)^2)) atTop (𝓝 lam) := by
  have hinv := (tendsto_inv_atTop_zero.comp hG).pow 2
  simpa only [Function.comp_def, Nat.cast_succ, add_div, one_div, inv_pow, zero_pow (by decide : 2≠0), add_zero] using
    hm.add hinv

/-- The actual conditional variance with its pivot removed and both true
source lengths has the V limit, uniformly along every convergent critical
parameter sequence, regardless of the chosen pivot source and its count. -/
theorem actual_arc_conditional_variance_limit {G H m rem ell y : ℕ → ℕ} (o : ∀ n, Fin (H n))
    {t : ℕ → ℝ} {lam T X : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop) (hH : Tendsto (fun n => (H n:ℝ)) atTop atTop)
    (hGH : Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0))
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (ht01 : ∀ n, t n ∈ Icc 0 1)
    (hx : Tendsto (fun n => (ell n:ℝ)/(G n:ℝ)) atTop (𝓝 X))
    (hc : ∀ n, Nat.Coprime (H n) (G n)) (hg : ∀ n, 0 < G n)
    (hl : ∀ n, ell n ≤ G n) (hr : ∀ n, rem n ≤ H n) :
    Tendsto (fun n => sourceArcVariance (H n) (G n) (m n) (rem n) (ell n) (o n) (t n) (y n)/(H n:ℝ))
      atTop (𝓝 (F09.V (lam*F09.v T) X)) := by
  have he : Tendsto (fun n => ((3*(G n:ℝ)+1)/4)/(H n:ℝ)) atTop (𝓝 0) := by
    have h := (((tendsto_const_nhds (x:=(3:ℝ))).mul hGH).add (tendsto_inv_atTop_zero.comp hH)).div_const 4
    convert h using 1
    · funext n; simp only [Function.comp_apply, div_eq_mul_inv]; ring
    · norm_num
  exact mixed_phase_average_limit (fun n => by have := (o n).isLt; omega) hr
    (physical_arc_critical_limit (o:=fun n => (o n).val) (y:=y) hG hm ht ht01 hx hc hl)
    (physical_arc_critical_limit (o:=fun n => (o n).val) (y:=y) hG (critical_plus_one_source_length hG hm) ht ht01 hx hc hl)
    he (fun n => actual_arc_mixed_variance_error (H n) (G n) (m n) (rem n) (ell n) (o n) (t n) (y n)
      (hg n) (hr n) (ht01 n))

end Shellsort
end
