import Shellsort.F09SecondSources
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Floor

/-! Averaging on the changing grid of target phases. The pivot laws may
change with the size and with the threshold. Only the original finite mean
is taken; there is no replacement by an independent post-sort input. -/
noncomputable section
namespace Shellsort.F09
open MeasureTheory Filter Set Finset
open scoped Topology

/-- A moving-index limit uniform in the choice of a finite pivot state also
holds under arbitrary size-dependent probability weights on those states. -/
theorem phase_pivot_average_limit {α : ℕ → Type*} [∀ n, Fintype (α n)] [∀ n, Nonempty (α n)]
    (w f : ∀ n, α n → ℝ) (z : ℝ) (wn : ∀ n j, 0 ≤ w n j) (ws : ∀ n, ∑ j,w n j=1)
    (seq : ∀ choice : ∀ n, α n, Tendsto (fun n => f n (choice n)) atTop (𝓝 z)) :
    Tendsto (fun n => mean (w n) (f n)) atTop (𝓝 z) := by
  classical
  choose lo _ lower using fun n => univ.exists_min_image (f n) univ_nonempty
  choose hi _ upper using fun n => univ.exists_max_image (f n) univ_nonempty
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (seq lo) (seq hi)
  · intro n; change f n (lo n) ≤ _; rw [← mean_const (w n) (ws n) (f n (lo n))]
    exact F09Second.mean_mono' (wn n) (fun j => lower n j (mem_univ j))
  · intro n; change _ ≤ f n (hi n); rw [← mean_const (w n) (ws n) (f n (hi n))]
    exact F09Second.mean_mono' (wn n) (fun j => upper n j (mem_univ j))

private def gridStep (G : ℕ) (F : ℕ → ℝ) (x : ℝ) := F ⌊(G:ℝ)*x⌋₊

/-- The piecewise-constant phase observable has exactly the discrete
uniform grid mean as its unit integral, including both boundary cells. -/
theorem phase_grid_integral (G : ℕ) (hg : 0<G) (F : ℕ → ℝ) :
    (∫ x : ℝ in 0..1, gridStep G F x) = (∑ j ∈ range G, F j)/G := by
  let a (k : ℕ) := (k:ℝ)/G
  have gp : (0:ℝ)<G := by exact_mod_cast hg
  have order k : a k ≤ a (k+1) := by dsimp [a]; gcongr; omega
  have cell (k : ℕ) (x : ℝ) (hx : x ∈ Ioo (a k) (a (k+1))) :
      gridStep G F x = F k := by
    unfold gridStep
    have l := (div_lt_iff₀ gp).mp hx.1
    have u := (lt_div_iff₀ gp).mp hx.2
    apply congrArg F; apply (Nat.floor_eq_iff (by nlinarith only [l,Nat.cast_nonneg (α:=ℝ) k])).mpr
    push_cast at u
    constructor <;> linarith only [l,u,mul_comm x (G:ℝ)]
  have good (k : ℕ) : IntervalIntegrable (gridStep G F) volume (a k) (a (k+1)) := by
    apply (intervalIntegrable_const (c:=F k)).congr_uIoo
    rw [uIoo_of_le (order k)]
    exact fun x hx => (cell k x hx).symm
  have part (k : ℕ) : (∫ x : ℝ in (a k)..(a (k+1)), gridStep G F x) = F k/G := by
    rw [intervalIntegral.integral_congr_Ioo_of_le (order k) (cell k),
      intervalIntegral.integral_const,smul_eq_mul]
    dsimp only [a]; push_cast; ring
  have sum := intervalIntegral.sum_integral_adjacent_intervals (n:=G) (fun k _ => good k)
  simp_rw [part] at sum
  simpa [a,gp.ne',← Finset.sum_div] using sum.symm

private theorem inside_ae : ∀ᵐ x : ℝ ∂volume, x ∈ uIoc (0:ℝ) 1 → x ∈ Ioo (0:ℝ) 1 := by
  filter_upwards [volume.ae_ne (1:ℝ)] with x hx
  rw [uIoc_of_le zero_le_one]
  intro p
  exact ⟨p.1,lt_of_le_of_ne p.2 hx⟩

/-- Uniformly bounded moving rows, converging along each convergent interior
mesh coordinate, converge in uniform-grid mean to the interval integral. -/
theorem phase_grid_mean_limit {G : ℕ → ℕ} (gp : ∀ n, 0<G n)
    (grow : Tendsto (fun n => (G n:ℝ)) atTop atTop)
    (F : ℕ → ℕ → ℝ) (f : ℝ → ℝ) (C : ℝ) (bound : ∀ n k, k<G n → |F n k|≤C)
    (rows : ∀ x ∈ Ioo (0:ℝ) 1, ∀ k : ℕ → ℕ, (∀ n, k n<G n) →
      Tendsto (fun n => (k n:ℝ)/(G n:ℝ)) atTop (𝓝 x) → Tendsto (fun n => F n (k n)) atTop (𝓝 (f x))) :
    Tendsto (fun n => (∑ k ∈ range (G n), F n k)/(G n:ℝ)) atTop (𝓝 (∫ x : ℝ in 0..1, f x)) := by
  simp_rw [← phase_grid_integral _ (gp _) (F _)]
  have floor_lt (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : ⌊(G n:ℝ)*x⌋₊ < G n := by
    apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) hx.1.le)).mpr
    exact mul_lt_of_lt_one_right (by exact_mod_cast gp n) hx.2
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · apply Eventually.of_forall; intro n
    apply Measurable.aestronglyMeasurable
    exact measurable_from_nat.comp (by fun_prop : Measurable (fun x : ℝ => ⌊(G n:ℝ)*x⌋₊))
  · apply Eventually.of_forall; intro n
    filter_upwards [inside_ae] with x hx
    intro ha
    exact bound n _ (floor_lt n x (hx ha))
  · exact intervalIntegrable_const
  · filter_upwards [inside_ae] with x hx
    intro ha
    have p := hx ha
    apply rows x p _ (fun n => floor_lt n x p)
    simpa only [Function.comp_def,mul_comm x] using (tendsto_nat_floor_mul_div_atTop p.1.le).comp grow

/-- The discrete uniform phase average and the original beta threshold
integral can be taken together. A common integrable threshold envelope is
enough even when the endpoints have no local limiting law. -/
theorem phase_threshold_grid_limit {G : ℕ → ℕ} (gp : ∀ n, 0<G n)
    (grow : Tendsto (fun n => (G n:ℝ)) atTop atTop)
    (F : ℕ → ℝ → ℕ → ℝ) (f : ℝ → ℝ → ℝ) (B : ℝ → ℝ)
    (meas : ∀ n k, k<G n → Continuous (fun t => F n t k))
    (envelope : IntervalIntegrable B volume 0 1)
    (bound : ∀ n t, t∈Ioo (0:ℝ) 1 → ∀ k, k<G n → |F n t k| ≤ B t)
    (rows : ∀ t ∈ Ioo (0:ℝ) 1, ∀ x ∈ Ioo (0:ℝ) 1, ∀ k : ℕ → ℕ, (∀ n, k n<G n) →
      Tendsto (fun n => (k n:ℝ)/(G n:ℝ)) atTop (𝓝 x) → Tendsto (fun n => F n t (k n)) atTop (𝓝 (f t x))) :
    Tendsto (fun n => ∫ t : ℝ in 0..1, (∑ k ∈ range (G n), F n t k)/(G n:ℝ))
      atTop (𝓝 (∫ t : ℝ in 0..1, ∫ x : ℝ in 0..1, f t x)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence B
  · apply Eventually.of_forall; intro n
    apply Continuous.aestronglyMeasurable
    exact (continuous_finsetSum _ (fun k hk => meas n k (mem_range.mp hk))).div_const _
  · apply Eventually.of_forall; intro n
    filter_upwards [inside_ae] with t ht
    intro hi
    have gpos : (0:ℝ)<G n := by exact_mod_cast gp n
    rw [Real.norm_eq_abs,abs_div,abs_of_pos gpos]
    apply (div_le_iff₀ gpos).mpr
    calc
      |∑ k ∈ range (G n), F n t k| ≤ ∑ k ∈ range (G n), |F n t k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ range (G n), B t := sum_le_sum (fun k hk => bound n t (ht hi) k (mem_range.mp hk))
      _ = _ := by simp [mul_comm]
  · exact envelope
  · filter_upwards [inside_ae] with t ht
    intro hi
    exact phase_grid_mean_limit gp grow (fun n => F n t) (f t) (B t)
      (fun n => bound n t (ht hi)) (rows t (ht hi))

end Shellsort.F09
