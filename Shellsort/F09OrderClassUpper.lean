import Shellsort.F09PhaseProjection
import Shellsort.F09PhaseClasses
import Shellsort.FirstPassUpper
import Shellsort.NaturalComparisonBounds

/-! A finite all-divisor transport bound via the true tagged source law.
Only first and second moment estimates are used here. -/
noncomputable section
namespace Shellsort.F09
open Finset Set

private theorem sum_subclass_counts {n : ℕ} (B : Finset (Fin n)) (d H c : ℕ)
    (dp : 0<d) (hp : 0<H) (cp : c<d) :
    (∑ s ∈ range H,chainLowerCount B (d*H) (d*s+c)) = chainLowerCount B d c := by
  let bucket (i : Fin n) := i.val%(d*H)/d
  let S := B.filter (fun i => i.val%d=c)
  have cap (i : Fin n) : bucket i < H := (Nat.div_lt_iff_lt_mul dp).mpr
    (by simpa [Nat.mul_comm] using Nat.mod_lt i.val (Nat.mul_pos dp hp))
  have each (s : ℕ) : chainLowerCount B (d*H) (d*s+c) = (S.filter (fun i => bucket i=s)).card := by
    unfold chainLowerCount
    apply congrArg Finset.card
    ext i
    simp only [S,bucket,mem_filter]
    have rem := Nat.mod_mod_of_dvd i.val (dvd_mul_right d H)
    have recov := Nat.mod_add_div (i.val%(d*H)) d
    constructor
    · rintro ⟨hi,e⟩
      rw [e] at rem ⊢
      have mod : (d*s+c)%d=c := by simp [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt cp]
      have quot : (d*s+c)/d=s := by
        rw [Nat.add_comm,Nat.mul_comm d s,Nat.add_mul_div_right _ _ dp,Nat.div_eq_of_lt cp,Nat.zero_add]
      exact ⟨⟨hi,rem.symm.trans mod⟩,quot⟩
    · rintro ⟨⟨hi,e⟩,q⟩
      rw [rem,e,q] at recov
      exact ⟨hi,by omega⟩
  simp_rw [each]
  exact (card_eq_sum_card_fiberwise (s:=S) (t:=range H) (f:=bucket)
    (fun i _ => mem_range.mpr (cap i))).symm

def reducedTaggedDisp (H G o y : ℕ) (b : Fin H → ℕ) :=
  let j := (o+H*y)%G
  (j:ℝ) + ∑ s : Fin H,sourceResidualReal H G j s.val (b s)

/-- On each tagged input, displacement from its final rank is the displacement
of the fully d-sorted tagged key plus d times its displacement from its rank
within its own divisor class. -/
theorem tagged_displacement_by_class {n : ℕ} (d H G : ℕ) (dp : 0<d) (hp : 0<H)
    (gp : 0<G) (i : Fin n) (B : Finset (Fin n)) :
    let b := chainLowerCount B (d*H)
    let u := i.val%(d*H)
    taggedSubsetDisplacement (d*H) (d*G) i B = firstPassSubsetDisplacement d i B +
      d*reducedTaggedDisp H G (u/d) (b u) (fun s => b (d*s.val+i.val%d)) := by
  let u := i.val%(d*H)
  let c := i.val%d
  let b := chainLowerCount B (d*H)
  let j := (u/d+H*b u)%G
  let P := ∑ s ∈ range H,sourcePrefixCount H G j s (b (d*s+c))
  have cp : c<d := Nat.mod_lt _ dp
  have recov : d*(u/d)+c=u := by
    change _+i.val%d=_
    rw [← Nat.mod_mod_of_dvd i.val (dvd_mul_right d H)]
    rw [Nat.add_comm]; exact Nat.mod_add_div u d
  have phase : taggedSubsetTarget (d*H) (d*G) i B = d*j+c := by
    change (u+d*H*b u)%(d*G)=_
    have e : u+d*H*b u = d*(u/d+H*b u)+c := by linear_combination recov.symm
    rw [e]; exact phase_scaled_target d G _ c gp cp
  have visits : (∑ s ∈ range (d*H),sourcePrefixCount (d*H) (d*G) (d*j+c) s (b s))=P :=
    targetPrefixCount_scale_class d H G c j b dp gp cp
  have red : reducedTaggedDisp H G (u/d) (b u) (fun s => b (d*s.val+c)) =
      (j:ℝ)+(G:ℝ)*P-chainLowerCount B d c := by
    change (j:ℝ)+(∑ s : Fin H,sourceResidualReal H G j s.val (b (d*s.val+c)))=_
    rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => sourceResidualReal H G j s (b (d*s+c)))]
    simp only [sourceResidualReal,sum_sub_distrib,← mul_sum,← Nat.cast_sum]
    rw [show (∑ s ∈ range H,b (d*s+c))=chainLowerCount B d c from sum_subclass_counts B d H c dp hp cp]
    dsimp only [P]; ring
  dsimp only
  change taggedSubsetDisplacement (d*H) (d*G) i B = firstPassSubsetDisplacement d i B + d*reducedTaggedDisp H G (u/d) (b u) (fun s => b (d*s.val+c))
  rw [red]; unfold taggedSubsetDisplacement
  rw [phase]
  simp only [sourceResidualReal,sum_sub_distrib,← mul_sum,← Nat.cast_sum]
  rw [visits,sum_chainLowerCount B (d*H) (Nat.mul_pos dp hp)]
  unfold firstPassSubsetDisplacement; push_cast
  change _ = (c:ℝ)+_*(chainLowerCount B d c:ℝ)-_+_
  ring

private theorem uniform_reduced_tag_bound {n : ℕ} (d H G : ℕ) (dp : 0<d) (hp : 0<H)
    (gp : 0<G) (cop : H.Coprime G) (i : Fin n) :
    let h := d*H
    let u := i.val%h
    let c := i.val%d
    uniformAverage (fun p : RankPlacement n =>
      let b := chainLowerCount (tagLowerState p i).val h
      |reducedTaggedDisp H G (u/d) (b u) (fun s => b (d*s.val+c))|) ≤
        ((G:ℝ)-1)*Real.sqrt ((H:ℝ)+3)/2 := by
  let h := d*H
  let u := i.val%h
  let c : Fin d := ⟨i.val%d,Nat.mod_lt _ dp⟩
  let o := tagReducedOwner d H dp hp i
  let coord := positionChainEquiv n h (Nat.mul_pos dp hp) i
  let R := n%h
  let m := n/h
  let rem := classRem R d c.val
  let L (s : Fin H) := sourceTrialLength m rem s.val
  let F (y : ℕ) (z : Fin H → ℕ) := |reducedTaggedDisp H G o.val y z|
  have own : classEmb H c o = coord.1 := by
    apply Fin.ext
    change d*(u/d)+(i.val%d)=u
    rw [← Nat.mod_mod_of_dvd i.val (dvd_mul_right d H),Nat.add_comm]
    exact Nat.mod_add_div _ _
  let f (B : TaggedSubset i) := F (chainLowerCount B.val h u)
    (fun s => chainLowerCount B.val h (classEmb H c s).val)
  apply uniform_tagged_mean_le_of_bernoulli_bound i f
  intro t ht0 ht1
  have project := tagged_projected_mean i (Nat.mul_pos dp hp) t (classEmb H c) L (classEmb_length n H c) F
  change mean _ (fun z => F (chainLowerCount ((omittedBitsSubsetEquiv i) z).val h coord.1.val)
    (fun s => chainLowerCount ((omittedBitsSubsetEquiv i) z).val h (classEmb H c s).val)) ≤ _
  rw [project]
  let w := sourceCoordinateWeight h m R t coord.1
  let K := ((G:ℝ)-1)*Real.sqrt ((H:ℝ)+3)/2
  have point (y : ℕ) (z : ∀ s : Fin H,Fin (L s) → Bool) :
      F y (fun s => if classEmb H c s=coord.1 then y else bitCount (z s)) =
      |conditionalSourceDisplacement H G m rem o y z| := by
    unfold F reducedTaggedDisp conditionalSourceDisplacement
    apply congrArg abs
    apply congrArg (fun a : ℝ => (((o.val+H*y)%G:ℕ):ℝ)+a)
    apply sum_congr rfl; intro s _
    unfold conditionalSourceResidual
    by_cases e : s=o
    · subst s; simp [own]
    · have ne : classEmb H c s ≠ coord.1 := fun q => e ((classEmb H c).injective (q.trans own.symm))
      simp [e,ne]
  change mean w (fun a => mean (productWeight (fun s : Fin H => bernoulliVectorWeight t (L s)))
    (fun z => F (ownerBitCount coord.2 a) (fun s =>
      if classEmb H c s=coord.1 then ownerBitCount coord.2 a else bitCount (z s)))) ≤ K
  simp_rw [point]
  calc
    _ ≤ mean w (fun _ => K) := by
      apply sum_le_sum; intro z _
      exact mul_le_mul_of_nonneg_left
        (conditionalSourceDisplacement_absMean_bound H G m rem t o (ownerBitCount coord.2 z)
          ⟨ht0,ht1⟩ (classRem_le (Nat.mod_lt _ (Nat.mul_pos dp hp))) gp cop)
        (sourceCoordinateWeight_nonneg _ _ _ _ ⟨ht0,ht1⟩ _ _)
    _ = _ := mean_const w (sourceCoordinateWeight_sum ..) K

/-- Finite two-pass footrule bound valid for every greatest common divisor.
The single-pass term is the physical interleaving of the classes. The local
term is the reduced true second-pass placement inside the pivot's class. -/
theorem uniform_twoPass_footrule_all_divisors (n d H G : ℕ) (dp : 0<d) (hp : 0<H)
    (gp : 0<G) (cop : H.Coprime G) :
    uniformAverage (fun p : RankPlacement n => footrule (gapSort (gapSort p (d*H)) (d*G))) ≤
      n*((d:ℝ)-1+Real.sqrt ((n:ℝ)*d)/2+d*(((G:ℝ)-1)*Real.sqrt ((H:ℝ)+3)/2)) := by
  rw [uniform_twoPass_footrule_by_original_positions]
  let K := (d:ℝ)-1+Real.sqrt ((n:ℝ)*d)/2+d*(((G:ℝ)-1)*Real.sqrt ((H:ℝ)+3)/2)
  have each (i : Fin n) :
      uniformAverage (fun p : RankPlacement n => |((gapSort (gapSort p (d*H)) (d*G) (p.symm i)).val:ℝ)-
        ((p.symm i).val:ℝ)|) ≤ K := by
    let one (p : RankPlacement n) := firstPassSubsetDisplacement d i (tagLowerState p i).val
    let localD (p : RankPlacement n) := let b := chainLowerCount (tagLowerState p i).val (d*H)
      let u := i.val%(d*H)
      reducedTaggedDisp H G (u/d) (b u) (fun s => b (d*s.val+i.val%d))
    have stage := uniform_onePass_tag_abs_bound d dp i
    simp_rw [actual_onePass_tag_displacement _ d dp i] at stage
    have localbd := uniform_reduced_tag_bound d H G dp hp gp cop i
    change uniformAverage (fun p => |localD p|) ≤ _ at localbd
    change uniformAverage (fun p => |one p|) ≤ _ at stage
    simp_rw [actual_tagged_displacement_eq _ _ _ (Nat.mul_pos dp hp) (Nat.mul_pos dp gp) i,
      tagged_displacement_by_class d H G dp hp gp i]
    change uniformAverage (fun p => |one p+d*localD p|) ≤ _
    have triangle := uniformAverage_mono (fun p => |one p+d*localD p|) (fun p => |one p|+d*|localD p|)
      (fun p => by simpa only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) d)] using abs_add_le (one p) ((d:ℝ)*localD p))
    rw [uniformAverage_add,uniformAverage_const_mul] at triangle
    exact triangle.trans (add_le_add stage (mul_le_mul_of_nonneg_left localbd (Nat.cast_nonneg d)))
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,K] using sum_le_sum (s:=univ) (fun i _ => each i)

end Shellsort.F09
