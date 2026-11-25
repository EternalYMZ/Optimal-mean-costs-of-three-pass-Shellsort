import Shellsort.F09OptimalLimit

/-! Uniformity on compact positive parameter sets and the comparison
coefficient for ordinary three-pass linear insertion. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology Set

def normComparisons {n : ℕ} (w : LegalThreePassPair n) := threePassPairMeanComparisons w/(n*Real.sqrt n)

theorem comparisons_minus_shifts {N : ℕ → ℕ} (w : ∀ i, LegalThreePassPair (N i)) (grow : Tendsto N atTop atTop) :
    Tendsto (fun i => normComparisons (w i)-normCost (w i)) atTop (𝓝 0) := by
  have s := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)
  apply squeeze_zero _ _ (show Tendsto (fun i => (3:ℝ)/Real.sqrt (N i)) atTop (𝓝 0) from
    tendsto_const_nhds.div_atTop s)
  all_goals intro i
            have hg := (w i).property
            have hn := (w i).val.1.isLt
            have np : (0:ℝ) < N i := by exact_mod_cast (show 0 < N i by omega)
            have sp := Real.sqrt_pos.mpr np
            have e := uniform_threePassComparisonCost_bounds (N i) (w i).val.1.val (w i).val.2.val
              (by omega) (by omega)
            change threePassPairMeanShifts (w i) ≤ threePassPairMeanComparisons (w i) ∧
              threePassPairMeanComparisons (w i) ≤ threePassPairMeanShifts (w i) + 3*N i at e
            unfold normCost normComparisons
            rw [← sub_div]
  · exact div_nonneg (sub_nonneg.2 e.1) (by positivity)
  · calc _ ≤ (3*(N i:ℝ))/((N i:ℝ)*Real.sqrt (N i)) :=
              div_le_div_of_nonneg_right (by linarith [e.2]) (by positivity)
         _ = _ := by field_simp

theorem fixed_divisor_comparison_limit (law : CriticalCostLaw) (N : ℕ → ℕ)
    (w : ∀ i, LegalThreePassPair (N i)) (d : ℕ) (a b : ℝ) (grow : Tendsto N atTop atTop)
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) (gd : ∀ᶠ i in atTop, divisor (w i) = d)
    (al : Tendsto (fun i => scaleA (w i)) atTop (𝓝 a)) (bl : Tendsto (fun i => scaleB (w i)) atTop (𝓝 b)) :
    Tendsto (fun i => normComparisons (w i)) atTop (𝓝 (K d a b)) := by
  simpa using (comparisons_minus_shifts w grow).add (law N w d a b grow hd ha hb gd al bl)

private theorem approximate (law : CriticalCostLaw) (d : ℕ) (hd : 0<d) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (i : ℕ) (ε : ℝ) (he : 0<ε) : ∃ n, ∃ w : LegalThreePassPair n, i ≤ n ∧ divisor w=d ∧
      dist (scaleA w) a < ε ∧ dist (scaleB w) b < ε ∧ dist (normCost w) (K d a b) < ε := by
  let N (j : ℕ) := j+16
  have grow : Tendsto N atTop atTop := tendsto_atTop_mono (fun j => by dsimp [N]; omega) tendsto_id
  obtain ⟨w,gd,al,bl⟩ := recovery_family N (fun j => by dsimp [N]; omega) grow d hd a b ha hb
  have lim := law N w d a b grow hd ha hb gd al bl
  obtain ⟨j,hi,hg,h1,h2,h3⟩ := ((grow.eventually_ge_atTop i).and (gd.and
    ((Metric.tendsto_nhds.mp al _ he).and ((Metric.tendsto_nhds.mp bl _ he).and
      (Metric.tendsto_nhds.mp lim _ he))))).exists
  exact ⟨_,_,hi,hg,h1,h2,h3⟩

/-- Recovery at every size and the local law imply continuity along every
positive parameter sequence, even when its coordinates are not table scales. -/
theorem critical_values_tendsto (law : CriticalCostLaw) (d : ℕ) (hd : 0<d) (a b : ℕ → ℝ)
    {A B : ℝ} (ha : ∀ i, 0<a i) (hb : ∀ i, 0<b i) (hA : 0<A) (hB : 0<B)
    (al : Tendsto a atTop (𝓝 A)) (bl : Tendsto b atTop (𝓝 B)) :
    Tendsto (fun i => K d (a i) (b i)) atTop (𝓝 (K d A B)) := by
  let e (i : ℕ) := 1/((i:ℝ)+1)
  have e0 i : 0<e i := by dsimp [e]; positivity
  have el : Tendsto e atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  choose N w ge gd ca cb cost using fun i => approximate law d hd _ _ (ha i) (hb i) i (e i) (e0 i)
  have grow := tendsto_atTop_mono ge tendsto_id
  have app {f g : ℕ → ℝ} (cl : ∀ i, dist (f i) (g i) < e i) :
      Tendsto (fun i => dist (f i) (g i)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun i => (cl i).le) el
  have v := law N w d A B grow hd hA hB (Eventually.of_forall gd)
    (al.congr_dist (app (f:=a) (g:=fun i => scaleA (w i)) (fun i => by rw [dist_comm]; exact ca i)))
    (bl.congr_dist (app (f:=b) (g:=fun i => scaleB (w i)) (fun i => by rw [dist_comm]; exact cb i)))
  exact v.congr_dist (app cost)

/-- A single size threshold controls every fixed-divisor table in a given
compact positive set, for both counters, evaluated at its own coordinates. -/
theorem critical_compact_uniform (law : CriticalCostLaw) (d : ℕ) (hd : 0<d)
    (D : Set (ℝ × ℝ)) (compact : IsCompact D) (positive : ∀ p ∈ D, 0<p.1 ∧ 0<p.2)
    (ε : ℝ) (he : 0<ε) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ w : LegalThreePassPair n,
      divisor w=d → (scaleA w,scaleB w) ∈ D →
      |normCost w - K d (scaleA w) (scaleB w)| < ε ∧
      |normComparisons w - K d (scaleA w) (scaleB w)| < ε := by
  by_contra! h
  choose N ge w gd mem fail using h
  let X i := (scaleA (w i),scaleB (w i))
  obtain ⟨⟨a,b⟩,hm,φ,mono,v⟩ := compact.tendsto_subseq (x:=X) mem
  have grow := (tendsto_atTop_mono ge tendsto_id).comp mono.tendsto_atTop
  have da : Tendsto (fun i => scaleA (w (φ i))) atTop (𝓝 a) := v.fst_nhds
  have db : Tendsto (fun i => scaleB (w (φ i))) atTop (𝓝 b) := v.snd_nhds
  have ps := positive _ hm
  have par := critical_values_tendsto law d hd _ _ (fun i => (positive _ (mem (φ i))).1)
    (fun i => (positive _ (mem (φ i))).2) ps.1 ps.2 da db
  have mv := law (N ∘ φ) (fun i => w (φ i)) d a b grow hd ps.1 ps.2
    (Eventually.of_forall fun i => gd (φ i)) da db
  have cv := fixed_divisor_comparison_limit law (N ∘ φ) (fun i => w (φ i)) d a b grow hd ps.1 ps.2
    (Eventually.of_forall fun i => gd (φ i)) da db
  have m := (mv.sub par).abs
  have c := (cv.sub par).abs
  simp only [sub_self,abs_zero] at m c
  obtain ⟨i,ok,ok'⟩ := ((m.eventually_lt_const he).and (c.eventually_lt_const he)).exists
  exact (not_lt_of_ge (fail (φ i) ok)) ok'

end Shellsort.F09
end
