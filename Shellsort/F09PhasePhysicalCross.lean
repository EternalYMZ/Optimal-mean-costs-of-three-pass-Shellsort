import Shellsort.F09PhaseIntegrationSame
import Shellsort.F09PhaseOwnerReplacement
import Shellsort.F09PhaseProjection

/-! The cross-class quantity is composed from the original Bernoulli law,
including its actual owner, both physical class remainders and the order
correction in the final insertion pass. -/
noncomputable section
namespace Shellsort.F09
open Filter Real Set Finset
open scoped Topology

private def tagClass {n : ℕ} (d : ℕ) (dp : 0<d) (i : Fin n) : Fin d := ⟨i.val%d,Nat.mod_lt _ dp⟩
private def tagOther {n : ℕ} (d : ℕ) (dp : 0<d) (i : Fin n) (off : Fin d) : Fin d :=
  ⟨(i.val+off.val)%d,Nat.mod_lt _ dp⟩

private theorem tag_other_ne {n d : ℕ} (dp : 0<d) (i : Fin n) (off : Fin d) (pos : off.val≠0) :
    tagClass d dp i ≠ tagOther d dp i off := by
  let : NeZero d := ⟨dp.ne'⟩
  let c := tagClass d dp i
  have e : tagOther d dp i off = c+off := by
    apply Fin.ext; change (i.val+off.val)%d = (i.val%d+off.val)%d
    exact (Nat.mod_add_mod _ _ _).symm
  rw [e]; intro he
  have o : (0:Fin d)=off := add_left_cancel (show c+0=c+off from (add_zero c).trans he)
  exact pos (by simpa using (congrArg Fin.val o.symm))

private def crossJ (H G o y : ℕ) := (o+H*y)%G
private def crossR (H G ell j : ℕ) := (j+H*ell)%G
private def crossOrder (d c k j r : ℕ) : ℝ := if d*r+k<d*j+c then 1 else 0

private def crossField {H : ℕ} (G j r : ℕ) (carry : ℝ) (z : PhasePairSource H → ℕ) : ℝ :=
  |(∑ s : PhasePairSource H, s.elim (fun u => (sourcePrefixCount H G j u.val (z (.inl u)):ℝ))
      (fun u => -(sourcePrefixCount H G r u.val (z (.inr u)):ℝ))) + carry|

private theorem crossField_split {H : ℕ} (G j r : ℕ) (carry : ℝ) (z : PhasePairSource H → ℕ) :
    crossField G j r carry z =
      |((∑ s : Fin H, (sourcePrefixCount H G j s.val (z (.inl s)):ℝ)) -
        (∑ s : Fin H, (sourcePrefixCount H G r s.val (z (.inr s)):ℝ))) + carry| := by
  unfold crossField
  rw [Fintype.sum_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr,Finset.sum_neg_distrib,sub_eq_add_neg]

set_option maxHeartbeats 1200000 in
private theorem crossCost_path {n : ℕ} (d H G ell : ℕ) (dp : 0<d) (hp : 0<H) (gp : 0<G)
    (i : Fin n) (B : TaggedSubset i) (off : Fin d) (pos : off.val≠0) :
    let h := d*H
    let co := positionChainEquiv n h (Nat.mul_pos dp hp) i
    let c := tagClass d dp i
    let k := tagOther d dp i off
    let o := tagReducedOwner d H dp hp i
    let b := chainLowerCount B.val h
    let j := crossJ H G o.val (b co.1.val)
    let r := crossR H G ell j
    targetClassPhaseCost d H G ell off.val i B =
      crossField G j r (crossOrder d c.val k.val j r)
        (fun s => b (pairEmb H c k (tag_other_ne dp i off pos) s).val) := by
  let h := d*H
  let c := tagClass d dp i
  let k := tagOther d dp i off
  let b := chainLowerCount B.val h
  let u := i.val%h
  let o := u/d
  let j := crossJ H G o (b u)
  let r := crossR H G ell j
  have reconstruct : d*o+c.val=u := by
    change d*(u/d)+(i.val%d)=u
    rw [←Nat.mod_mod_of_dvd i.val (dvd_mul_right d H),Nat.add_comm]
    exact Nat.mod_add_div _ _
  have phys : (u+d*H*b u)%(d*G) = d*j+c.val := by
    have eq : u+d*H*b u = d*(o+H*b u)+c.val := by
      conv_lhs => lhs; rw [←reconstruct]
      ring
    rw [eq]; exact phase_scaled_target _ _ _ _ gp c.isLt
  have quot (s : ℕ) (a : Fin d) : (d*s+a.val)/d=s := by
    rw [Nat.add_comm,Nat.mul_comm d s,Nat.add_mul_div_right _ _ dp,Nat.div_eq_of_lt a.isLt,Nat.zero_add]
  have md (s : ℕ) (a : Fin d) : (d*s+a.val)%d=a.val := by simp [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt a.isLt]
  let A (q : ℕ) := ∑ s ∈ range H,sourcePrefixCount H G (q/d) s (b (d*s+q%d))
  change finalPivotPrefixCost h (d*G) (d*((((u+d*H*b u)%(d*G))/d+H*ell)%G)+k.val) i B = _
  rw [phys,quot]
  change finalPivotPrefixCost h (d*G) (d*r+k.val) i B = _
  rw [finalPivotPrefixCost_eq_reduced_classes d H G (d*r+k.val) dp gp]
  change |((A ((u+d*H*b u)%(d*G)) + (if d*r+k.val<(u+d*H*b u)%(d*G) then 1 else 0):ℕ):ℝ) - (A (d*r+k.val):ℝ)| =
    crossField G j r _ _
  rw [phys,crossField_split]
  dsimp only [A]
  rw [quot,quot,md,md]
  rw [←Fin.sum_univ_eq_sum_range,←Fin.sum_univ_eq_sum_range]
  push_cast
  let J := ∑ s : Fin H,(sourcePrefixCount H G j s.val (b (d*s.val+c.val)):ℝ)
  let R := ∑ s : Fin H,(sourcePrefixCount H G r s.val (b (d*s.val+k.val)):ℝ)
  change |J+(if d*r+k.val<d*j+c.val then 1 else 0 : ℝ)-R| = |(J-R)+(if d*r+k.val<d*j+c.val then 1 else 0)|
  congr 1; ring

private theorem cross_owned {n : ℕ} (d H : ℕ) (dp : 0<d) (hp : 0<H) (i : Fin n) :
    classEmb H (tagClass d dp i) (tagReducedOwner d H dp hp i) =
      (positionChainEquiv n (d*H) (Nat.mul_pos dp hp) i).1 := by
  apply Fin.ext
  change d*((i.val%(d*H))/d)+(i.val%d)=i.val%(d*H)
  rw [← Nat.mod_mod_of_dvd i.val (dvd_mul_right d H),Nat.add_comm]
  exact Nat.mod_add_div _ _

set_option maxHeartbeats 1200000 in
theorem targetClassPhaseMean_cross {n : ℕ} (d H G ell : ℕ) (dp : 0<d) (hp : 0<H) (gp : 0<G)
    (i : Fin n) (off : Fin d) (pos : off.val≠0) (t : ℝ) :
    let h := d*H
    let co := positionChainEquiv n h (Nat.mul_pos dp hp) i
    let c := tagClass d dp i
    let k := tagOther d dp i off
    let o := tagReducedOwner d H dp hp i
    let m := n/h
    let a := classRem (n%h) d c.val
    let b := classRem (n%h) d k.val
    targetClassPhaseMean n d H G ell off.val i t =
      mean (sourceCoordinateWeight h m (n%h) t co.1) (fun u =>
        let y := ownerBitCount co.2 u
        let j := crossJ H G o.val y
        let r := crossR H G ell j
        phasePairPinnedAbs H G j r m a b o y t (crossOrder d c.val k.val j r)) /sqrt H := by
  classical
  let h := d*H
  let co := positionChainEquiv n h (Nat.mul_pos dp hp) i
  let c := tagClass d dp i
  let k := tagOther d dp i off
  let o := tagReducedOwner d H dp hp i
  let m := n/h
  let a := classRem (n%h) d c.val
  let b := classRem (n%h) d k.val
  let e := pairEmb H c k (tag_other_ne dp i off pos)
  let J (y : ℕ) := crossJ H G o.val y
  let R (y : ℕ) := crossR H G ell (J y)
  let order (y : ℕ) := crossOrder d c.val k.val (J y) (R y)
  let F (y : ℕ) (z : PhasePairSource H → ℕ) := crossField G (J y) (R y) (order y) z
  have lengths : ∀ s : PhasePairSource H, sourceTrialLength m (n%h) (e s).val = phasePairLength m a b s := by
    rintro (s|s); exact classEmb_length n H c s; exact classEmb_length n H k s
  have projected := tagged_projected_mean i (Nat.mul_pos dp hp) t e (phasePairLength m a b) lengths F
  have path (B : TaggedSubset i) : targetClassPhaseCost d H G ell off.val i B =
      F (chainLowerCount B.val h co.1.val) (fun s => chainLowerCount B.val h (e s).val) :=
    crossCost_path d H G ell dp hp gp i B off pos
  have own : e (.inl o) = co.1 := cross_owned d H dp hp i
  have eq (s : PhasePairSource H) : e s = co.1 ↔ s = .inl o := by rw [←own,e.injective.eq_iff]
  have pt (y : ℕ) (z : ∀ s : PhasePairSource H, Fin (phasePairLength m a b s) → Bool) :
      F y (fun s => if e s=co.1 then y else bitCount (z s)) =
        |(∑ s : PhasePairSource H, if s = Sum.inl o then (sourcePrefixCount H G (J y) o.val y:ℝ)
          else phasePairVisit G (J y) (R y) m a b s (z s)) + order y| := by
    unfold F crossField
    apply congrArg (fun A : ℝ => |A+order y|)
    apply Finset.sum_congr rfl
    rintro (s|s) _
    · dsimp only [Sum.elim_inl]
      by_cases E : s=o
      · subst s; simp only [own,ite_true]
      · have ne : (Sum.inl s : PhasePairSource H) ≠ Sum.inl o := by simpa using E
        have ne' := ne ∘ (eq (.inl s)).mp
        simp only [ite_eq_right ne',ite_eq_right ne,phasePairVisit]; rfl
    · have ne : (Sum.inr s : PhasePairSource H) ≠ Sum.inl o := by simp
      have ne' := ne ∘ (eq (.inr s)).mp
      dsimp only [Sum.elim_inr]
      simp only [ite_eq_right ne',ite_eq_right ne,phasePairVisit]; rfl
  dsimp only
  unfold targetClassPhaseMean
  simp_rw [path]
  rw [projected]
  dsimp only
  congr 1
  apply Finset.sum_congr rfl; intro z _
  apply congrArg (fun q : ℝ => sourceCoordinateWeight h m (n%h) t co.1 z * q)
  let y := ownerBitCount co.2 z
  change mean (productWeight _) (fun a' => F y (fun s => if e s=co.1 then y else bitCount (a' s))) =
    phasePairPinnedAbs H G (J y) (R y) m a b o y t (order y)
  unfold phasePairPinnedAbs
  apply Finset.sum_congr rfl; intro a' _
  exact congrArg (fun q : ℝ => productWeight (phasePairWeight (h:=H) m a b t) a' * q) (pt y a')

set_option maxHeartbeats 1200000 in
/-- At every actual pivot slot, every other physical residue class has the
same critical limit. Thresholds and offsets are allowed to reach the
endpoints in the limit. -/
theorem actual_tag_cross_class_limit {N H G ell : ℕ → ℕ} (d : ℕ) (dp : 0<d)
    (hp : ∀ n, 0<H n) (gp : ∀ n, 0<G n) (cop : ∀ n, (H n).Coprime (G n))
    (Gn : Tendsto (fun n => (G n:ℝ)) atTop atTop) (Hn : Tendsto (fun n => (H n:ℝ)) atTop atTop)
    (GH : Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0))
    {lam T X : ℝ} (heat : Tendsto (fun n => ((N n/(d*H n):ℕ):ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (t : ℕ → ℝ) (ht : ∀ n, t n∈Icc (0:ℝ) 1) (tl : Tendsto t atTop (𝓝 T))
    (_hl : ∀ n, ell n<G n) (_width : Tendsto (fun n => (ell n:ℝ)/(G n:ℝ)) atTop (𝓝 X))
    (i : ∀ n, Fin (N n)) (off : Fin d) (pos : off.val≠0) :
    Tendsto (fun n => targetClassPhaseMean (N n) d (H n) (G n) (ell n) off.val (i n) (t n)) atTop
      (𝓝 (targetClassKernel off.val lam T X)) := by
  let h n := d*H n
  let R n := N n % h n
  let m n := N n / h n
  let co n := positionChainEquiv (N n) (h n) (Nat.mul_pos dp (hp n)) (i n)
  let c n := tagClass d dp (i n)
  let k n := tagOther d dp (i n) off
  let o n := tagReducedOwner d (H n) dp (hp n) (i n)
  let a n := classRem (R n) d (c n).val
  let b n := classRem (R n) d (k n).val
  let L n := sourceTrialLength (m n) (R n) (co n).1.val
  let y n (u : Fin (L n) → Bool) := ownerBitCount (co n).2 u
  let j n u := crossJ (H n) (G n) (o n).val (y n u)
  let r n u := crossR (H n) (G n) (ell n) (j n u)
  let order n u := crossOrder d (c n).val (k n).val (j n u) (r n u)
  have len n : L n = sourceTrialLength (m n) (a n) (o n).val := by
    have own : classEmb (H n) (c n) (o n) = (co n).1 := cross_owned d (H n) dp (hp n) (i n)
    dsimp only [L]; rw [←own]
    exact classEmb_length (N n) (H n) (c n) (o n)
  have Rb n : R n < d*H n := Nat.mod_lt _ (Nat.mul_pos dp (hp n))
  have near n : |(a n:ℝ)-(b n:ℝ)|≤1 := by
    dsimp only [a,b,classRem,sourceTrialLength]
    split <;> split <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith
  have ord n u : |order n u|≤1 := by dsimp only [order,crossOrder]; split <;> norm_num
  have lim := actual_cross_owner_abs_limit (m:=m) (a:=a) (b:=b) o (fun n => (co n).2) len j r order
    Gn Hn GH heat tl ht cop (fun n _ => Nat.mod_lt _ (gp n)) (fun n _ => Nat.mod_lt _ (gp n)) hp
    (fun n => classRem_le (Rb n)) (fun n => classRem_le (Rb n)) near ord
  have kernel : targetClassKernel off.val lam T X =
      sqrt (2/π)*sqrt (2*(lam*v T+W (lam*v T))) := by
    unfold targetClassKernel; rw [ite_eq_right pos,Real.sqrt_div (by norm_num),Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    have two := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have p := Real.sqrt_pos.2 Real.pi_pos
    field_simp; linear_combination - sqrt (lam*v T+W (lam*v T)) * two
  rw [kernel]
  apply lim.congr'
  filter_upwards [] with n
  exact (targetClassPhaseMean_cross d (H n) (G n) (ell n) dp (hp n) (gp n) (i n) off pos (t n)).symm

end Shellsort.F09
