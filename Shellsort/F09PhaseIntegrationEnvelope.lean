import Shellsort.F09PhaseIntegration
import Mathlib.Topology.Sequences

noncomputable section
namespace Shellsort.F09
open Set Finset Filter
open scoped Topology

/-- Convergence along every moving threshold and mesh index, including
limits on the boundary, already supplies a single constant majorant.
The majorant covers every finite grid and every original threshold. -/
theorem phase_envelope_of_moving_limits {G : ℕ → ℕ} (gp : ∀ n, 0<G n)
    (F : ℕ → ℝ → ℕ → ℝ) (cont : ∀ n k, k<G n → Continuous (fun t => F n t k))
    (limits : ∀ (j : ℕ → ℕ), Tendsto j atTop atTop → ∀ (t : ℕ → ℝ) (k : ℕ → ℕ),
      (∀ i, t i ∈ Icc (0:ℝ) 1) → (∀ i, k i<G (j i)) →
      ∀ T X : ℝ, Tendsto t atTop (𝓝 T) → Tendsto (fun i => (k i:ℝ)/(G (j i):ℝ)) atTop (𝓝 X) →
        ∃ z : ℝ, Tendsto (fun i => F (j i) (t i) (k i)) atTop (𝓝 z)) :
    ∃ C : ℝ, ∀ n t, t∈Icc (0:ℝ) 1 → ∀ k, k<G n → |F n t k|≤C := by
  classical
  have maxima (n : ℕ) (k : Fin (G n)) := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (zero_le_one : (0:ℝ)≤1)) ((cont n k.val k.isLt).abs.continuousOn)
  choose p _ maxp using maxima
  let B (n : ℕ) := ∑ k : Fin (G n), |F n (p n k) k.val|
  have bn (n : ℕ) : 0 ≤ B n := sum_nonneg (fun _ _ => abs_nonneg _)
  have bound (n : ℕ) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (k : ℕ) (hk : k<G n) : |F n t k| ≤ B n := by
    let u : Fin (G n) := ⟨k,hk⟩
    exact (maxp n u ht).trans (single_le_sum (f:=fun w : Fin (G n) => |F n (p n w) w.val|)
      (fun _ _ => abs_nonneg _) (mem_univ u))
  by_contra! no
  choose j t ht k hk high using fun i : ℕ => no ((i:ℝ)+∑ s ∈ range i,B s)
  have idx (i : ℕ) : i ≤ j i := by
    by_contra! bad
    have bin := single_le_sum (fun s (_ : s∈range i) => bn s) (mem_range.mpr bad)
    linarith only [bound _ _ (ht i) _ (hk i),high i, bin,Nat.cast_nonneg (α:=ℝ) i]
  have grow : Tendsto j atTop atTop := tendsto_atTop_mono idx tendsto_id
  let x i := (k i:ℝ)/(G (j i):ℝ)
  have qmem i : (t i,x i) ∈ (Icc (0:ℝ) 1) ×ˢ (Icc (0:ℝ) 1) :=
    ⟨ht i,div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (by exact_mod_cast gp (j i))).mpr (by exact_mod_cast (hk i).le)⟩
  obtain ⟨⟨T,X⟩,_,φ,mono,hφ⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq qmem
  obtain ⟨z,hz⟩ := limits (j ∘ φ) (grow.comp mono.tendsto_atTop) (t ∘ φ) (k ∘ φ)
    (fun i => ht _) (fun i => hk _) T X hφ.fst_nhds hφ.snd_nhds
  have az := (continuous_abs.continuousAt.tendsto.comp hz).eventually_lt_const (lt_add_one |z|)
  have inf := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp mono.tendsto_atTop
  obtain ⟨i,hu,hl⟩ := (az.and (inf.eventually_gt_atTop (|z|+1))).exists
  change |F (j (φ i)) (t (φ i)) (k (φ i))| < |z|+1 at hu
  change |z|+1 < (φ i:ℝ) at hl
  linarith only [high (φ i),hu,hl,sum_nonneg (s:=range (φ i)) (fun s _ => bn s)]

end Shellsort.F09
