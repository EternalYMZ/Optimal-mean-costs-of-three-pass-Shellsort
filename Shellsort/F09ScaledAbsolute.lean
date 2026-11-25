import Shellsort.F09AbsoluteLimit

/-! Absolute first moments of a sum of sources on its physical square-root scale. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology
open scoped BigOperators NNReal

private theorem mean_divide {α : Type*} [Fintype α] (p X : α → ℝ) (u : ℝ) :
    mean p (fun x => X x/u) = mean p X/u := by
  simp only [mean,← mul_div_assoc,← Finset.sum_div]

/-- A critical row has O(H) independent sources, bounded individual centered
third and second moments, and a prescribed limit for its variance divided by H.
The conclusion is the absolute moment of their actual sum divided by √H. -/
theorem independent_abs_limit_scaled {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {α : (n : ℕ) → ι n → Type*} [∀ n i, Fintype (α n i)]
    (p X : (n : ℕ) → (i : ι n) → α n i → ℝ)
    (hp : ∀ n i x, 0 ≤ p n i x) (total : ∀ n i, ∑ x, p n i x = 1)
    (cent : ∀ n i, mean (p n i) (X n i) = 0)
    (H : ℕ → ℝ) (hH : ∀ n, 0 < H n) (grow : Tendsto H atTop atTop)
    (A D : ℝ) (d0 : 0 ≤ D) (count : ∀ᶠ n in atTop, (Fintype.card (ι n):ℝ) ≤ A*H n)
    (per : ∀ᶠ n in atTop, ∀ i, mean (p n i) (fun x => X n i x^2) ≤ D ∧
      mean (p n i) (fun x => |X n i x|^3) ≤ D)
    (s : ℝ≥0) (varLim : Tendsto (fun n => (∑ i, mean (p n i) (fun x => X n i x^2))/H n)
      atTop (𝓝 (s:ℝ))) :
    Tendsto (fun n => mean (productWeight (p n)) (fun z => |∑ i, X n i (z i)|)/Real.sqrt (H n))
      atTop (𝓝 (Real.sqrt (2/Real.pi)*Real.sqrt s)) := by
  let r n := Real.sqrt (H n)
  have rp n : 0 < r n := Real.sqrt_pos.mpr (hH _)
  have rs n : r n ^2 = H n := Real.sq_sqrt (hH _).le
  let Y n i x := X n i x/r n
  have center n i : mean (p n i) (Y n i) = 0 := by simp [Y,mean_divide,cent]
  let V n i := mean (p n i) (fun x => X n i x^2)
  let T n i := mean (p n i) (fun x => |X n i x|^3)
  have vn n i : 0 ≤ V n i := Finset.sum_nonneg (fun x _ => mul_nonneg (hp _ _ _) (sq_nonneg _))
  have tn n i : 0 ≤ T n i := Finset.sum_nonneg (fun x _ => mul_nonneg (hp _ _ _) (by positivity))
  have v n i : mean (p n i) (fun x => Y n i x^2) = V n i/H n := by simp [Y,V,div_pow,rs,mean_divide]
  have t n i : mean (p n i) (fun x => |Y n i x|^3) = T n i/(r n)^3 := by
    simp [Y,T,abs_div,abs_of_pos (rp n),div_pow,mean_divide]
  have vl : Tendsto (fun n => ∑ i, mean (p n i) (fun x => Y n i x^2)) atTop (𝓝 (s:ℝ)) := by
    simpa only [v,← Finset.sum_div,V] using varLim
  have tl : Tendsto (fun n => ∑ i, mean (p n i) (fun x => |Y n i x|^3)) atTop (𝓝 0) := by
    simp only [t,← Finset.sum_div]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _ : ℕ => (0:ℝ))
      tendsto_const_nhds (show Tendsto (fun n => A*D/r n) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp grow))
    · exact Eventually.of_forall (fun n => div_nonneg (Finset.sum_nonneg (fun i _ => tn n i)) (by positivity))
    · filter_upwards [count,per] with n cn bn
      have cap : ∑ i, T n i ≤ A*H n*D :=
        (Finset.sum_le_sum (fun i _ => (bn i).2)).trans (by simpa using mul_le_mul_of_nonneg_right cn d0)
      calc (∑ i, T n i)/r n^3 ≤ A*H n*D/r n^3 := div_le_div_of_nonneg_right cap (by positivity)
           _ = _ := by rw [← rs]; field_simp
  have sl : Tendsto (fun n => ∑ i, (mean (p n i) (fun x => Y n i x^2))^2) atTop (𝓝 0) := by
    simp only [v,div_pow,← Finset.sum_div]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _ : ℕ => (0:ℝ))
      tendsto_const_nhds (show Tendsto (fun n => A*D^2/H n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop grow)
    · exact Eventually.of_forall (fun n => div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _))
    · filter_upwards [count,per] with n cn bn
      have cap : ∑ i, V n i^2 ≤ A*H n*D^2 :=
        (Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (vn n i) (bn i).1 2)).trans
          (by simpa using mul_le_mul_of_nonneg_right cn (sq_nonneg D))
      calc (∑ i, V n i^2)/H n^2 ≤ A*H n*D^2/H n^2 := div_le_div_of_nonneg_right cap (sq_nonneg _)
           _ = _ := by field_simp
  apply (independent_abs_limit p Y hp total center s vl tl sl).congr
  intro n
  simp only [Y,← Finset.sum_div,abs_div,abs_of_pos (rp n),mean_divide,r]

end Shellsort.F09
end
