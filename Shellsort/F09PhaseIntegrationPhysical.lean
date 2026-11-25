import Shellsort.F09PhaseIntegration
import Shellsort.F09PhaseClasses
import Shellsort.F09CertificateFunctions
import Shellsort.PivotArcCostBridge

noncomputable section
namespace Shellsort.F09
open Finset Filter MeasureTheory Set
open scoped Topology

def targetPhaseCost {n : ℕ} (d H G ell : ℕ) (i : Fin n) (B : TaggedSubset i) :=
  let h := d*H
  let o := i.val%h
  let j := (o+h*(chainLowerCount B.val h o))%(d*G)
  ∑ c ∈ range d, finalPivotPrefixCost h (d*G) (d*((j/d+H*ell)%G)+c) i B

private theorem phase_target_sum (d H G u : ℕ) (gp : 0<G) (cop : H.Coprime G) (f : ℕ → ℝ) :
    (∑ r ∈ range (d*G), f r) =
      ∑ ell ∈ range G, ∑ c ∈ range d, f (d*((u+H*ell)%G)+c) := by
  let row (j : ℕ) := ∑ c ∈ range d, f (d*j+c)
  have stripes (K : ℕ) : (∑ r ∈ range (d*K), f r) = ∑ j ∈ range K, row j := by
    induction K with
    | zero => simp
    | succ K ih => rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]
  rw [stripes]
  symm
  apply sum_bij (fun ell _ => (u+H*ell)%G)
  · intro ell _; exact mem_range.mpr (Nat.mod_lt _ gp)
  · intro i hi j hj eq
    simpa only [Nat.mod_eq_of_lt (mem_range.mp hi),Nat.mod_eq_of_lt (mem_range.mp hj)] using
      (coprime_affine_mod_eq_iff H G u i j cop).mp eq
  · intro r hr
    obtain ⟨k,hk,e⟩ := exists_coprime_source_phase H G r u gp cop (mem_range.mp hr)
    exact ⟨k,mem_range.mpr hk,e⟩
  · intro _ _; rfl

def actualPhaseRow (n d H G ell : ℕ) (t : ℝ) :=
  (∑ i : Fin n, mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
    (fun x => targetPhaseCost d H G ell i ((omittedBitsSubsetEquiv i) x)))/((n:ℝ)*Real.sqrt H)

theorem actualPhaseRow_continuous (n d H G ell : ℕ) : Continuous (actualPhaseRow n d H G ell) :=
  (continuous_finsetSum _ (fun i _ => bernoulli_product_mean_continuous _)).div_const _

/-- A finite equality for the actual uniform third-pass mean. Each arc width
indexes one target in each of the d classes. The rotation starting phase is
computed from the pivot on this very same input before reindexing its sum. -/
theorem actual_last_as_phase_grid (n d H G : ℕ) (np : 0<n) (dp : 0<d)
    (hp : 0<H) (gp : 0<G) (cop : H.Coprime G) :
    uniformAverage (fun p : RankPlacement n => (gapInsertionCost
      (gapSort (gapSort p (d*H)) (d*G)) 1 (by decide):ℝ)) /
      ((n:ℝ)*G*Real.sqrt H) =
      (∫ t : ℝ in 0..1, (∑ ell ∈ range G, actualPhaseRow n d H G ell t)/(G:ℝ))/2 := by
  let W (i : Fin n) (t : ℝ) := productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t)
  let V (i : Fin n) (ell : ℕ) (t : ℝ) :=
    mean (W i t) (fun x => targetPhaseCost d H G ell i ((omittedBitsSubsetEquiv i) x))
  have cont (i : Fin n) (ell : ℕ) : Continuous (V i ell) := bernoulli_product_mean_continuous _
  have path (i : Fin n) (B : TaggedSubset i) :
      (∑ r ∈ range (d*G), finalPivotPrefixCost (d*H) (d*G) r i B) =
        ∑ e ∈ range G, targetPhaseCost d H G e i B := by
    exact phase_target_sum d H G _ gp cop _
  have localmean (i : Fin n) (t : ℝ) :
      mean (W i t) (fun x => ∑ r ∈ range (d*G),
        finalPivotPrefixCost (d*H) (d*G) r i ((omittedBitsSubsetEquiv i) x)) =
        ∑ e ∈ range G,V i e t := by
    simp_rw [path]
    simp only [V,mean,mul_sum]; rw [sum_comm]
  have raw := uniform_lastCost_original_prefix_mixture n (d*H) (d*G)
    (Nat.mul_pos dp hp) (Nat.mul_pos dp gp)
  change 2*_ = ∑ i : Fin n, ∫ t : ℝ in 0..1, mean (W i t) _ at raw
  simp_rw [localmean] at raw
  have sw (e : ℕ) : (∫ t : ℝ in 0..1, actualPhaseRow n d H G e t) =
      (∑ i : Fin n, ∫ t : ℝ in 0..1, V i e t)/((n:ℝ)*Real.sqrt H) := by
    unfold actualPhaseRow
    rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum]
    exact fun i _ => (cont i e).intervalIntegrable _ _
  have irow (i : Fin n) :
      (∫ t : ℝ in 0..1, ∑ e ∈ range G,V i e t) = ∑ e ∈ range G, ∫ t : ℝ in 0..1, V i e t :=
    intervalIntegral.integral_finsetSum (fun e _ => (cont i e).intervalIntegrable _ _)
  simp_rw [irow] at raw
  rw [sum_comm] at raw
  rw [intervalIntegral.integral_div,intervalIntegral.integral_finsetSum
    (fun e _ => (actualPhaseRow_continuous n d H G e).intervalIntegrable _ _)]
  simp_rw [sw]
  rw [← sum_div, ← raw]
  have nn : (0:ℝ)<n := by exact_mod_cast np
  have gg : (0:ℝ)<G := by exact_mod_cast gp
  have hs : 0<Real.sqrt H := Real.sqrt_pos.2 (by exact_mod_cast hp)
  field_simp

end Shellsort.F09
