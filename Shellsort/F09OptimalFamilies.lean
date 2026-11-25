import Shellsort.F09GlobalOptimum
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! All limiting optimal shapes, including the case of multiple minimizers.
Compactness follows by approximating each shape with an actual finite table. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology Set
open scoped Metric

def coordinates {n : ℕ} (w : LegalThreePassPair n) : ℝ × ℝ := (scaleA w, scaleB w)
def optimalShapes : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ K 1 p.1 p.2 = kappa}

private theorem finite_approximation (law : CriticalCostLaw) {p : ℝ × ℝ} (hp : p ∈ optimalShapes)
    (i : ℕ) (ε : ℝ) (he : 0 < ε) : ∃ n : ℕ, ∃ w : LegalThreePassPair n,
    i ≤ n ∧ divisor w = 1 ∧ dist (coordinates w) p < ε ∧ dist (normCost w) kappa < ε := by
  let N (j : ℕ) := j+16
  have grow : Tendsto N atTop atTop := tendsto_atTop_mono (fun j => by dsimp [N]; omega) tendsto_id
  obtain ⟨w,gd,al,bl⟩ := recovery_family N (fun j => by dsimp [N]; omega) grow 1 (by decide)
    p.1 p.2 hp.1 hp.2.1
  have lim := law N w 1 p.1 p.2 grow (by decide) hp.1 hp.2.1 gd al bl
  rw [hp.2.2] at lim
  have pair : Tendsto (fun j => coordinates (w j)) atTop (𝓝 p) := al.prodMk_nhds bl
  obtain ⟨j,hi,hg,hd,hl⟩ := ((grow.eventually_ge_atTop i).and
    (gd.and ((Metric.tendsto_nhds.mp pair ε he).and (Metric.tendsto_nhds.mp lim ε he)))).exists
  exact ⟨_,_,hi,hg,hd,hl⟩

theorem optimalShapes_compact (law : CriticalCostLaw) : IsCompact optimalShapes := by
  apply IsSeqCompact.isCompact
  intro y hy
  let e (i : ℕ) := 1/((i:ℝ)+1)
  have e0 i : 0 < e i := by dsimp [e]; positivity
  have el : Tendsto e atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  choose N w lower gd coord cost using fun i => finite_approximation law (hy i) i (e i) (e0 i)
  have grow := tendsto_atTop_mono lower tendsto_id
  have clo : Tendsto (fun i => dist (coordinates (w i)) (y i)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun i => (coord i).le) el
  have opt : Tendsto (fun i => normCost (w i)) atTop (𝓝 kappa) := tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun _ => dist_nonneg) (fun i => (cost i).le) el)
  obtain ⟨C,upper⟩ := opt.bddAbove_range
  obtain ⟨d,a,b,φ,hd,ha,hb,mono,g,al,bl⟩ := budget_convergent_subsequence N w (max 1 C)
    (zero_lt_one.trans_le (le_max_left ..)) (fun i => (upper (mem_range_self _)).trans (le_max_right ..))
  have one : d = 1 := by obtain ⟨i,hi⟩ := g.exists; exact hi.symm.trans (gd _)
  subst d
  have val := law (N ∘ φ) (fun i => w (φ i)) 1 a b (grow.comp mono.tendsto_atTop)
    hd ha hb g al bl
  have pair : Tendsto (fun i => coordinates (w (φ i))) atTop (𝓝 (a,b)) := al.prodMk_nhds bl
  exact ⟨(a,b),⟨ha,hb,tendsto_nhds_unique val (opt.comp mono.tendsto_atTop)⟩,
    φ,mono,pair.congr_dist (clo.comp mono.tendsto_atTop)⟩

theorem optimalShapes_nonempty (law : CriticalCostLaw) (sep : DivisorSeparation) : optimalShapes.Nonempty := by
  let N (j : ℕ) := j+16
  have grow : Tendsto N atTop atTop := tendsto_atTop_mono (fun j => by dsimp [N]; omega) tendsto_id
  obtain ⟨_,_,mem⟩ := optimal_cost_limits_of_critical_law law N (fun j => by dsimp [N]; omega) grow
  rw [inf_critical_eq_kappa sep] at mem
  obtain ⟨d,hd,a,b,ha,hb,e⟩ := mem
  by_cases h : d=1
  · subst d; exact ⟨(a,b),ha,hb,e.symm⟩
  · exact ((sep d a b (by omega) ha hb).ne e).elim

/-- An equivalence for the full sequence of actual execution costs. -/
theorem asymptotically_optimal_iff (law : CriticalCostLaw) (sep : DivisorSeparation)
    (N : ℕ → ℕ) (w : ∀ i, LegalThreePassPair (N i)) (grow : Tendsto N atTop atTop) :
    Tendsto (fun i => normCost (w i)) atTop (𝓝 kappa) ↔
      (∀ᶠ i in atTop, divisor (w i) = 1) ∧
      Tendsto (fun i => Metric.infDist (coordinates (w i)) optimalShapes) atTop (𝓝 0) := by
  constructor
  · intro opt
    have one := eventually_coprime_of_optimal law sep N w grow opt
    refine ⟨one,tendsto_of_subseq_tendsto ?_⟩
    intro ns inc
    obtain ⟨C,upper⟩ := opt.bddAbove_range
    obtain ⟨d,a,b,φ,hd,ha,hb,mono,g,al,bl⟩ := budget_convergent_subsequence (N ∘ ns)
      (fun i => w (ns i)) (max 1 C) (zero_lt_one.trans_le (le_max_left ..))
      (fun i => (upper (mem_range_self _)).trans (le_max_right ..))
    have inc' := inc.comp mono.tendsto_atTop
    have eq : d = 1 := by obtain ⟨i,hi,hj⟩ := (g.and (inc'.eventually one)).exists; exact hi.symm.trans hj
    subst d
    have val := law (fun i => N (ns (φ i))) (fun i => w (ns (φ i))) 1 a b (grow.comp inc')
      hd ha hb g al bl
    have hmem : (a,b) ∈ optimalShapes := ⟨ha,hb,tendsto_nhds_unique val (opt.comp inc')⟩
    have pair : Tendsto (fun i => coordinates (w (ns (φ i)))) atTop (𝓝 (a,b)) := al.prodMk_nhds bl
    exact ⟨φ,squeeze_zero (fun _ => Metric.infDist_nonneg) (fun _ => Metric.infDist_le_dist_of_mem hmem)
      (tendsto_iff_dist_tendsto_zero.1 pair)⟩
  · rintro ⟨one,near⟩
    have comp := optimalShapes_compact law
    choose y mem eq using fun i => comp.exists_infDist_eq_dist (optimalShapes_nonempty law sep) (coordinates (w i))
    apply tendsto_of_subseq_tendsto
    intro ns inc
    obtain ⟨⟨a,b⟩,hm,φ,mono,lim⟩ := comp.tendsto_subseq (fun i => mem (ns i))
    have inc' := inc.comp mono.tendsto_atTop
    have close : Tendsto (fun i => dist (y (ns (φ i))) (coordinates (w (ns (φ i))))) atTop (𝓝 0) :=
      (near.comp inc').congr (fun i => (eq _).trans (dist_comm ..))
    have pair := lim.congr_dist close
    have v := law (fun i => N (ns (φ i))) (fun i => w (ns (φ i))) 1 a b (grow.comp inc') (by decide)
      hm.1 hm.2.1 (inc'.eventually one) pair.fst_nhds pair.snd_nhds
    exact ⟨φ,hm.2.2 ▸ v⟩

end Shellsort.F09
end
