import Shellsort.F09PhaseIntegrationTags
import Shellsort.F09PhaseArcCostLimit
import Shellsort.F09PhaseProjection

noncomputable section
namespace Shellsort.F09
open Finset Set Filter Real
open scoped Topology


/-- The same-class physical observable is exactly the discrepancy of the
nonowner source endpoints in the true reduced cyclic arc, on every original
tag and lower-key subset. The integer carry cancels pathwise. -/
theorem targetClassPhaseCost_same {n : ℕ} (d H G ell : ℕ)
    (dp : 0<d) (hp : 0<H) (gp : 0<G) (cop : H.Coprime G) (el : ell<G)
    (i : Fin n) (B : TaggedSubset i) :
    let b := chainLowerCount B.val (d*H)
    let u := i.val%(d*H)
    let o := u/d
    let y := b u
    targetClassPhaseCost d H G ell 0 i B =
      |(∑ s : Fin H,phaseArcReward H G o ell y s.val (b (d*s.val+i.val%d))) -
        ((H*ell/G:ℕ):ℝ)| := by
  let b := chainLowerCount B.val (d*H)
  let u := i.val%(d*H)
  let c := i.val%d
  let o := u/d
  let y := b u
  let j := (o+H*y)%G
  let r := (j+H*ell)%G
  let A (s : ℕ) := b (d*s+c)
  have uc : u%d=c := Nat.mod_mod_of_dvd _ (dvd_mul_right d H)
  have cp : c<d := Nat.mod_lt _ dp
  have reconstruct : d*o+c=u := by rw [← uc, Nat.add_comm]; exact Nat.mod_add_div u d
  have Ao : A o=y := by dsimp only [A,y]; rw [reconstruct]
  have physj : (u+d*H*y)%(d*G)=d*j+c := by
    have eq : u+d*H*y=d*(o+H*y)+c := by rw [←reconstruct]; ring
    rw [eq]; exact phase_scaled_target _ _ _ _ gp cp
  have quot (s : ℕ) : (d*s+c)/d=s := by
    rw [Nat.add_comm,Nat.mul_comm d s,Nat.add_mul_div_right _ _ dp,Nat.div_eq_of_lt cp,Nat.zero_add]
  have rem (s : ℕ) : (d*s+c)%d=c := by simp [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt cp]
  have carry : d*r+c<d*j+c ↔ r<j := by
    rw [Nat.add_lt_add_iff_right,Nat.mul_lt_mul_left dp]
  have endpoints := sum_source_arc_endpoint_identity H G j ell gp (Nat.mod_lt _ gp) A
  have sums : (∑ s ∈ range H, (arcHits H G j ell (s+H*A s):ℝ)) =
      ∑ s : Fin H, phaseArcReward H G o ell y s.val (A s.val) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl; intro s _
    rw [phaseArcReward_eq_removed_endpoint H G o ell y s.val (A s.val) cop el]
    by_cases e : s.val=o
    · rw [e,Ao]
      have z := arcHits_start H G j ell (o+H*y) cop el (by dsimp [j]; simp)
      simp [z]
    · simp [e,j]
  have realEnd : (((∑ s ∈ range H,sourcePrefixCount H G j s (A s))+
      (if r<j then 1 else 0):ℕ):ℝ) - (∑ s ∈ range H, sourcePrefixCount H G r s (A s):ℕ) =
      (∑ s ∈ range H,(arcHits H G j ell (s+H*A s):ℝ)) - ((H*ell/G:ℕ):ℝ) := by
    exact_mod_cast endpoints
  change finalPivotPrefixCost (d*H) (d*G) (d*((((u+d*H*y)%(d*G))/d+H*ell)%G)+(i.val+0)%d) i B = _
  rw [Nat.add_zero,physj,quot]
  change finalPivotPrefixCost (d*H) (d*G) (d*r+c) i B = _
  rw [finalPivotPrefixCost_eq_reduced_classes d H G (d*r+c) dp gp]
  let V (a : ℕ) := ∑ s ∈ range H,sourcePrefixCount H G (a/d) s (b (d*s+a%d))
  change |((V ((u+d*H*y)%(d*G)) + (if d*r+c<(u+d*H*y)%(d*G) then 1 else 0):ℕ):ℝ) - (V (d*r+c):ℝ)| = _
  rw [physj]
  dsimp only [V]
  rw [quot,quot,rem,rem,if_congr carry rfl rfl,realEnd,sums]

end Shellsort.F09
