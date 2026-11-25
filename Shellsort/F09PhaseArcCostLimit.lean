import Shellsort.F09PhaseCenters
import Shellsort.F09ScaledAbsolute

/-! The actual omitted-owner arc under the specified independent source
bits has the Gaussian absolute first moment at every critical sequence. -/
noncomputable section
namespace Shellsort
open Filter Set Real
open scoped Topology BigOperators NNReal

theorem phase_mean_abs_shift {α : Type*} [Fintype α] (w f : α → ℝ)
    (h0 : ∀ x, 0 ≤ w x) (h1 : ∑ x, w x = 1) (c : ℝ) :
    |mean w (fun x => |f x + c|) - mean w (fun x => |f x|)| ≤ |c| := by
  have right := phaseMean_mono w h0 (fun x => abs_add_le (f x) c)
  have left := phaseMean_mono w h0 (fun x =>
    show |f x| ≤ |f x+c| + |c| by simpa [add_assoc] using abs_add_le (f x+c) (-c))
  simp only [mean_add, mean_const w h1] at right left
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Removing an O(1) mean correction on the growing source scale. -/
theorem phase_abs_shift_limit {α : ℕ → Type*} [∀ n, Fintype (α n)]
    (p f : ∀ n, α n → ℝ) (p0 : ∀ n x, 0 ≤ p n x) (p1 : ∀ n, ∑ x, p n x = 1)
    (H c : ℕ → ℝ) (hH : Tendsto H atTop atTop) (C Z : ℝ) (hc : ∀ n, |c n| ≤ C)
    (lim : Tendsto (fun n => mean (p n) (fun x => |f n x|)/sqrt (H n)) atTop (𝓝 Z)) :
    Tendsto (fun n => mean (p n) (fun x => |f n x+c n|)/sqrt (H n)) atTop (𝓝 Z) := by
  have bound : Tendsto (fun n => C/sqrt (H n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x:=C)).mul (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hH))
  have d : Tendsto (fun n =>
      mean (p n) (fun x => |f n x+c n|)/sqrt (H n) -
      mean (p n) (fun x => |f n x|)/sqrt (H n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ bound
    intro n
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_nonneg (sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right ((phase_mean_abs_shift _ _ (p0 n) (p1 n) _).trans (hc n)) (sqrt_nonneg _)
  simpa only [sub_add_cancel, zero_add] using d.add lim

private theorem phase_reward_moments {α : Type*} [Fintype α] (w : α → ℝ) (e : α → Bool)
    (h0 : ∀ x, 0 ≤ w x) (h1 : ∑ x, w x = 1) :
    let z := fun x => if e x then (1:ℝ) else 0
    let mu := mean w z
    mean w (fun x => (z x-mu)^2) = eventMarginal w e*(1-eventMarginal w e) ∧
    mean w (fun x => (z x-mu)^2) ≤ 1 ∧ mean w (fun x => |z x-mu|^3) ≤ 1 := by
  let z := fun x => if e x then (1:ℝ) else 0
  let mu := mean w z
  have z01 (x : α) : 0 ≤ z x ∧ z x ≤ 1 := by simp [z]; split <;> norm_num
  have mu0 : 0 ≤ mu := Finset.sum_nonneg fun x _ => mul_nonneg (h0 x) (z01 x).1
  have mu1 : mu ≤ 1 := (phaseMean_mono w h0 (fun x => (z01 x).2)).trans_eq (mean_const w h1 1)
  have eq : mu = eventMarginal w e := by simp [mu,z,mean,eventMarginal,mul_ite]
  have second : secondMoment w z = mu := by
    apply Finset.sum_congr rfl
    intro x _; simp [z]
  have sq := centeredSecond_identity w z h1
  rw [second] at sq
  have abs1 (x : α) : |z x-mu| ≤ 1 := abs_le.mpr ⟨by linarith [(z01 x).1],by linarith [(z01 x).2]⟩
  change (mean w (fun x => (z x-mu)^2) = _) ∧ _ ∧ _
  constructor
  · change centeredSecond w z = _
    rw [sq, ← eq]; change mu - mu^2 = _; ring
  constructor
  · change centeredSecond w z ≤ 1; rw [sq]
    change mu - mu^2 ≤ 1; nlinarith [sq_nonneg mu]
  · apply (phaseMean_mono w h0 (fun x => pow_le_one₀ (abs_nonneg (z x-mu)) (abs1 x) (n:=3))).trans_eq
    exact mean_const w h1 1

/-- The conditional, physically charged same-class |Q-floor| term. The
geometric centering, source variance, normalization and eventual absolute
moment all refer to the same selected owner, arc and pivot count. -/
theorem actual_arc_conditional_abs_limit {G H m rem ell y : ℕ → ℕ} (o : ∀ n, Fin (H n))
    {t : ℕ → ℝ} {lam T X : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop) (hH : Tendsto (fun n => (H n:ℝ)) atTop atTop)
    (hGH : Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0))
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (ht01 : ∀ n, t n ∈ Icc 0 1)
    (hx : Tendsto (fun n => (ell n:ℝ)/(G n:ℝ)) atTop (𝓝 X))
    (hc : ∀ n, Nat.Coprime (H n) (G n)) (hl : ∀ n, ell n < G n) (hr : ∀ n, rem n ≤ H n) :
    Tendsto (fun n => mean (conditionalSourceWeight (H n) (m n) (rem n) (t n))
      (fun z => |(∑ s : Fin (H n), phaseArcReward (H n) (G n) (o n).val (ell n) (y n)
        s.val (bitCount (z s))) - (((H n*ell n/G n):ℕ):ℝ)|) / sqrt (H n))
      atTop (𝓝 (sqrt (2/π)*sqrt (F09.V (lam*F09.v T) X))) := by
  let w := fun n => sourceCoordinateWeight (H n) (m n) (rem n) (t n)
  let e := fun n (s : Fin (H n)) (z : Fin (sourceTrialLength (m n) (rem n) s.val) → Bool) =>
    pivotArcHit (H n) (G n) (o n).val (ell n) (y n) s.val (bitCount z)
  let Z := fun n s z => if e n s z then (1:ℝ) else 0
  let mu := fun n s => mean (w n s) (Z n s)
  let U := fun n s z => Z n s z-mu n s
  let P := fun n => productWeight (w n)
  let V := F09.V (lam*F09.v T) X
  have w0 := fun n => sourceCoordinateWeight_nonneg (H n) (m n) (rem n) (t n) (ht01 n)
  have w1 := fun n => sourceCoordinateWeight_sum (H n) (m n) (rem n) (t n)
  have p0 := fun n => productWeight_nonneg (w n) (w0 n)
  have p1 := fun n => productWeight_sum (w n) (w1 n)
  have cent (n) (s : Fin (H n)) : mean (w n s) (U n s) = 0 := by
    change mean (w n s) (fun z => Z n s z - mu n s) = 0
    rw [mean_sub, mean_const (w n s) (w1 n s)]; exact sub_self _
  have moments (n) (s : Fin (H n)) := phase_reward_moments (w n s) (e n s) (w0 n s) (w1 n s)
  have varEq (n) : (∑ s : Fin (H n), mean (w n s) (fun z => U n s z^2)) =
      sourceArcVariance (H n) (G n) (m n) (rem n) (ell n) (o n) (t n) (y n) :=
    Finset.sum_congr rfl fun s _ => (moments n s).1
  have hg := fun n => lt_of_le_of_lt (Nat.zero_le _) (hl n)
  have hvar := actual_arc_conditional_variance_limit (y:=y) o hG hH hGH hm ht ht01 hx hc hg (fun n => (hl n).le) hr
  have lim : Tendsto (fun n => (∑ s : Fin (H n), mean (w n s) (fun z => U n s z^2))/(H n:ℝ)) atTop (𝓝 V) := by
    simpa only [varEq] using hvar
  have v0 : 0 ≤ V := le_of_tendsto_of_tendsto' tendsto_const_nhds lim fun n =>
    div_nonneg (Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun z _ => mul_nonneg (w0 n s z) (sq_nonneg _)) (Nat.cast_nonneg _)
  let k := fun n => (((H n*ell n/G n):ℕ):ℝ)
  let F := fun n (z : ∀ s : Fin (H n), Fin (sourceTrialLength (m n) (rem n) s.val) → Bool) => ∑ s, U n s (z s)
  let c := fun n => (∑ s, mu n s)-k n
  have centered := F09.independent_abs_limit_scaled w U w0 w1 cent (fun n => (H n:ℝ))
    (fun n => by exact_mod_cast Nat.zero_lt_of_lt (o n).isLt) hH 1 1 (by norm_num)
    (.of_forall fun n => by simp) (.of_forall fun n s => (moments n s).2) ⟨V,v0⟩ lim
  have unc := phase_abs_shift_limit P F p0 p1 (fun n => (H n:ℝ)) c hH 4 _ (fun n =>
    phaseArc_mean_drift (H n) (G n) (m n) (rem n) (ell n) (o n) (y n) (t n) (ht01 n) (hr n) (hg n) (hc n) (hl n)) centered
  have eq (n) (z) : F n z + c n = (∑ s, Z n s (z s))-k n := by
    simp only [F,U,c,Finset.sum_sub_distrib]; ring
  simp only [eq] at unc
  exact unc

end Shellsort
end
