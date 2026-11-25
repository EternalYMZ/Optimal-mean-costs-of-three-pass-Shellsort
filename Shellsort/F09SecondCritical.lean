import Shellsort.F09SecondLimit
import Mathlib.Algebra.Order.Floor.Semifield

noncomputable section
open Filter
open scoped Topology
namespace Shellsort.F09Second

/-- The executed second insertion pass at a critical gap pair. The original
permutation is uniform, the preceding h-sort is executed on that same input,
and the two gaps need satisfy no divisibility or coprimality restriction. -/
theorem critical_secondPass_limit (N h g : ℕ → ℕ) (grow : Tendsto N atTop atTop)
    (hh : ∀ i, 0<h i) (hg : ∀ i, 0<g i) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (first : Tendsto (fun i => (h i:ℝ)/Real.sqrt (N i)) atTop (𝓝 a))
    (second : Tendsto (fun i => (g i:ℝ)/Real.sqrt (Real.sqrt (N i))) atTop (𝓝 b)) :
    Tendsto (fun i => uniformAverage (fun p : RankPlacement (N i) =>
      (gapInsertionCost (gapSort p (h i)) (g i) (hg i) : ℝ)) / ((N i:ℝ)*Real.sqrt (N i)))
      atTop (𝓝 (Real.sqrt Real.pi * Real.sqrt a / (8*b))) := by
  let s i := Real.sqrt (N i:ℝ)
  let t i := Real.sqrt (s i)
  let A i := (h i:ℝ)/s i
  let B i := (g i:ℝ)/t i
  let q i := (N i:ℝ)/h i
  let m i := N i/h i
  have stop : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)
  have ttop : Tendsto t atTop atTop := Real.tendsto_sqrt_atTop.comp stop
  have ss i : s i ^ 2 = N i := Real.sq_sqrt (Nat.cast_nonneg _)
  have tt i : t i ^ 2 = s i := Real.sq_sqrt (Real.sqrt_nonneg _)
  have qeq i : q i = s i*(A i)⁻¹ := by
    dsimp [q,A]; rw [← ss i,inv_div]; ring
  have qtop : Tendsto q atTop atTop :=
    (stop.atTop_mul_pos (inv_pos.mpr ha) (first.inv₀ ha.ne')).congr (fun i => (qeq i).symm)
  have mt : Tendsto m atTop atTop := by
    simpa only [m,q,Function.comp_def,Nat.floor_div_eq_div] using tendsto_nat_floor_atTop.comp qtop
  have mf : Tendsto (fun i => (m i:ℝ)/q i) atTop (𝓝 1) := by
    simpa only [m,q,Function.comp_def,Nat.floor_div_eq_div] using tendsto_nat_floor_div_atTop.comp qtop
  have BA : Tendsto (fun i => A i/B i) atTop (𝓝 (a/b)) := first.div second hb.ne'
  have ratio : Tendsto (fun i => (h i:ℝ)/g i) atTop atTop := by
    apply (BA.pos_mul_atTop (div_pos ha hb) ttop).congr'
    filter_upwards [grow.eventually_ge_atTop 1] with i ni
    have sp : 0 < s i := Real.sqrt_pos.2 (by exact_mod_cast ni)
    have tp : 0 < t i := Real.sqrt_pos.2 sp
    have gp : (0:ℝ) < g i := by exact_mod_cast hg i
    change (A i/B i)*t i = _
    dsimp only [A,B]
    field_simp; nlinarith only [tt i]
  have ms : Tendsto (fun i => (m i:ℝ)/s i) atTop (𝓝 (1/a)) := by
    apply (mf.div first ha.ne').congr'
    filter_upwards [grow.eventually_ge_atTop 1] with i ni
    have np : (0:ℝ) < N i := by exact_mod_cast ni
    have hp : (0:ℝ) < h i := by exact_mod_cast hh i
    have sp : 0 < s i := Real.sqrt_pos.2 np
    change ((m i:ℝ)/q i)/A i = _
    dsimp only [q,A]; field_simp; nlinarith only [ss i]
  have factor : Tendsto (fun i => ((h i:ℝ)/g i)*Real.sqrt (m i)/s i) atTop (𝓝 (Real.sqrt a/b)) := by
    have lim := BA.mul (Real.continuous_sqrt.continuousAt.tendsto.comp ms)
    have aa : a/b*Real.sqrt (1/a) = Real.sqrt a/b := by
      rw [Real.sqrt_div zero_le_one,Real.sqrt_one]
      have ar := Real.sq_sqrt ha.le
      have ap := Real.sqrt_pos.2 ha
      field_simp; nlinarith
    rw [aa] at lim
    apply lim.congr'
    filter_upwards [grow.eventually_ge_atTop 1] with i ni
    have sp : 0 < s i := Real.sqrt_pos.2 (by exact_mod_cast ni)
    have tp : 0 < t i := Real.sqrt_pos.2 sp
    have gp : (0:ℝ) < g i := by exact_mod_cast hg i
    change (A i/B i)*Real.sqrt ((m i:ℝ)/s i) = _
    rw [Real.sqrt_div (Nat.cast_nonneg _)]
    change (((h i:ℝ)/s i)/((g i:ℝ)/t i))*(Real.sqrt (m i)/t i) = _
    field_simp
  have limit := (uniform_second_limit N h g hh hg mt ratio).mul factor
  rw [show Real.sqrt Real.pi/8*(Real.sqrt a/b) = Real.sqrt Real.pi*Real.sqrt a/(8*b) by ring] at limit
  apply limit.congr'
  filter_upwards [grow.eventually_ge_atTop 1, mt.eventually_ge_atTop 1] with i ni mi
  have np : (0:ℝ) < N i := by exact_mod_cast ni
  have sp : 0 < s i := Real.sqrt_pos.2 np
  have mp : 0 < Real.sqrt (m i) := Real.sqrt_pos.2 (by exact_mod_cast mi)
  have hp : (0:ℝ) < h i := by exact_mod_cast hh i
  have gp : (0:ℝ) < g i := by exact_mod_cast hg i
  change _ / ((N i:ℝ)*((h i:ℝ)/g i)*Real.sqrt (m i)) *
    (((h i:ℝ)/g i)*Real.sqrt (m i)/s i) = _ / ((N i:ℝ)*s i)
  field_simp

end Shellsort.F09Second
