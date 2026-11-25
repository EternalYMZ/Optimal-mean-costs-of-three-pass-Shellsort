import Shellsort.F09PhaseIntegrationSame
import Shellsort.F09PhaseProjection

noncomputable section
namespace Shellsort.F09
open Filter Real Set Finset
open scoped Topology

def sameArcMean (H G m rem ell : ℕ) (o : Fin H) (y : ℕ) (t : ℝ) :=
  mean (conditionalSourceWeight H m rem t) (fun z =>
    |(∑ s : Fin H,phaseArcReward H G o.val ell y s.val (bitCount (z s)))-((H*ell/G:ℕ):ℝ)|)/Real.sqrt H

set_option maxHeartbeats 300000 in
theorem targetClassPhaseMean_same {n : ℕ} (d H G ell : ℕ)
    (dp : 0<d) (hp : 0<H) (gp : 0<G) (cop : H.Coprime G) (el : ell<G) (i : Fin n) (t : ℝ) :
    let h := d*H
    let coord := positionChainEquiv n h (Nat.mul_pos dp hp) i
    let m := n/h
    let rem := classRem (n%h) d (i.val%d)
    targetClassPhaseMean n d H G ell 0 i t =
      mean (sourceCoordinateWeight h m (n%h) t coord.1) (fun a =>
        sameArcMean H G m rem ell (tagReducedOwner d H dp hp i) (ownerBitCount coord.2 a) t) := by
  let h := d*H
  let coord := positionChainEquiv n h (Nat.mul_pos dp hp) i
  let c : Fin d := ⟨i.val%d,Nat.mod_lt _ dp⟩
  let o := tagReducedOwner d H dp hp i
  let m := n/h
  let rem := classRem (n%h) d c.val
  let L (s : Fin H) := sourceTrialLength m rem s.val
  let F (y : ℕ) (z : Fin H → ℕ) := |(∑ s : Fin H,phaseArcReward H G o.val ell y s.val (z s))-((H*ell/G:ℕ):ℝ)|
  have own : classEmb H c o = coord.1 := by
    apply Fin.ext
    change d*((i.val%h)/d)+(i.val%d)=i.val%h
    rw [← Nat.mod_mod_of_dvd i.val (dvd_mul_right d H)]
    rw [Nat.add_comm]
    exact Nat.mod_add_div _ _
  have same (y : ℕ) (z : ∀ s : Fin H, Fin (L s) → Bool) :
      F y (fun s => if classEmb H c s = coord.1 then y else bitCount (z s)) = F y (fun s => bitCount (z s)) := by
    dsimp only [F]
    apply congrArg (fun u : ℝ => |u-((H*ell/G:ℕ):ℝ)|)
    apply sum_congr rfl; intro s _
    by_cases e : classEmb H c s = coord.1
    · have es : s=o := (classEmb H c).injective (e.trans own.symm)
      subst s; simp [phaseArcReward,pivotArcHit]
    · simp [e]
  have project := tagged_projected_mean i (Nat.mul_pos dp hp) t (classEmb H c) L (classEmb_length n H c) F
  have path (B : TaggedSubset i) : targetClassPhaseCost d H G ell 0 i B =
      F (chainLowerCount B.val h coord.1.val) (fun s => chainLowerCount B.val h (classEmb H c s).val) :=
    targetClassPhaseCost_same d H G ell dp hp gp cop el i B
  dsimp only
  unfold targetClassPhaseMean
  simp_rw [path]
  rw [project]
  dsimp only
  rw [← phaseMean_div]
  apply sum_congr rfl; intro z _
  apply congrArg (fun v : ℝ => sourceCoordinateWeight h m (n%h) t coord.1 z * v)
  apply congrArg (fun v : ℝ => v/Real.sqrt H)
  apply congrArg (mean (productWeight (fun s : Fin H => bernoulliVectorWeight t (L s))))
  exact funext (same (ownerBitCount coord.2 z))

/-- Unconditional same-class incidence on the actual array, for arbitrary
moving original tags, thresholds, and arc widths, including boundary limits. -/
theorem actual_tag_same_class_limit {N H G ell : ℕ → ℕ} (d : ℕ) (dp : 0<d)
    (hp : ∀ n, 0<H n) (gp : ∀ n, 0<G n) (cop : ∀ n, (H n).Coprime (G n))
    (Gn : Tendsto (fun n => (G n:ℝ)) atTop atTop) (Hn : Tendsto (fun n => (H n:ℝ)) atTop atTop)
    (GH : Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0))
    {lam T X : ℝ} (heat : Tendsto (fun n => ((N n/(d*H n):ℕ):ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (t : ℕ → ℝ) (ht : ∀ n, t n∈Icc (0:ℝ) 1) (tl : Tendsto t atTop (𝓝 T))
    (hl : ∀ n, ell n<G n) (width : Tendsto (fun n => (ell n:ℝ)/(G n:ℝ)) atTop (𝓝 X))
    (i : ∀ n, Fin (N n)) :
    Tendsto (fun n => targetClassPhaseMean (N n) d (H n) (G n) (ell n) 0 (i n) (t n)) atTop
      (𝓝 (targetClassKernel 0 lam T X)) := by
  let o n := tagReducedOwner d (H n) dp (hp n) (i n)
  let rem n := classRem (N n%(d*H n)) d ((i n).val%d)
  let m n := N n/(d*H n)
  let coord n := positionChainEquiv (N n) (d*H n) (Nat.mul_pos dp (hp n)) (i n)
  have hr n : rem n ≤ H n := classRem_le (Nat.mod_lt _ (Nat.mul_pos dp (hp n)))
  have K : targetClassKernel 0 lam T X = sqrt (2/π)*sqrt (V (lam*v T) X) := by
    simp only [targetClassKernel,ite_true]
    rw [Real.sqrt_div (by norm_num),Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    have a := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have p := Real.sqrt_pos.2 Real.pi_pos
    have q : 0 < √(2:ℝ) := by positivity
    congr 1; field_simp; nlinarith
  rw [K]
  simp_rw [targetClassPhaseMean_same _ _ _ _ dp (hp _) (gp _) (cop _) (hl _)]
  apply phase_pivot_average_limit
  · intro n z; exact sourceCoordinateWeight_nonneg _ _ _ _ (ht n) _ _
  · intro n; exact sourceCoordinateWeight_sum _ _ _ _ _
  · intro a
    exact actual_arc_conditional_abs_limit (m:=m) (rem:=rem) (ell:=ell)
      (y:=fun n => ownerBitCount (coord n).2 (a n)) o Gn Hn GH heat tl ht width cop hl hr

end Shellsort.F09
