import Shellsort.F09PhaseIntegrationAssembly

noncomputable section
namespace Shellsort.F09
open Filter Finset Real Set
open scoped Topology

/-- One actual target relative to the original pivot's class. Offset zero
is always its own class. The phase in that target class is selected by the
owner's true original smaller-key count. -/
def targetClassPhaseCost {n : ℕ} (d H G ell offset : ℕ) (i : Fin n) (B : TaggedSubset i) :=
  let h := d*H
  let o := i.val%h
  let j := (o+h*(chainLowerCount B.val h o))%(d*G)
  finalPivotPrefixCost h (d*G) (d*((j/d+H*ell)%G)+(i.val+offset)%d) i B

def targetClassPhaseMean (n d H G ell offset : ℕ) (i : Fin n) (t : ℝ) :=
  mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
    (fun x => targetClassPhaseCost d H G ell offset i ((omittedBitsSubsetEquiv i) x)) /Real.sqrt H

private theorem target_sum_offset {n : ℕ} (d H G ell : ℕ) (dp : 0<d) (i : Fin n) (B : TaggedSubset i) :
    targetPhaseCost d H G ell i B = ∑ c : Fin d, targetClassPhaseCost d H G ell c.val i B := by
  let _ : NeZero d := ⟨dp.ne'⟩
  let h := d*H
  let o := i.val%h
  let j := (o+h*(chainLowerCount B.val h o))%(d*G)
  let f (c : ℕ) := finalPivotPrefixCost h (d*G) (d*((j/d+H*ell)%G)+c) i B
  change (∑ c ∈ range d,f c) = ∑ c : Fin d,f ((i.val+c.val)%d)
  rw [← Fin.sum_univ_eq_sum_range]
  have eq := Equiv.sum_comp (Equiv.addRight (⟨i.val%d,Nat.mod_lt _ dp⟩ : Fin d)) (fun c => f c.val)
  simpa only [Equiv.coe_addRight,Fin.val_add,Nat.add_mod_mod, Nat.add_comm i.val] using eq.symm

theorem actualPhaseRow_eq_tag_classes (n d H G ell : ℕ) (dp : 0<d) (t : ℝ) :
    actualPhaseRow n d H G ell t = mean (fun _ : Fin n => (1:ℝ)/n)
      (fun i => ∑ c : Fin d, targetClassPhaseMean n d H G ell c.val i t) := by
  let W (i : Fin n) := productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t)
  let A (i : Fin n) (c : Fin d) := mean (W i)
    (fun x => targetClassPhaseCost d H G ell c.val i ((omittedBitsSubsetEquiv i) x))
  have e (i : Fin n) : mean (W i) (fun x => targetPhaseCost d H G ell i ((omittedBitsSubsetEquiv i) x)) = ∑ c,A i c := by
    simp_rw [target_sum_offset d H G ell dp]
    exact mean_sum _ _
  change (∑ i : Fin n,mean (W i) _)/_ = ∑ i : Fin n, (1:ℝ)/n*(∑ c : Fin d,A i c/Real.sqrt H)
  simp_rw [e]
  simp only [sum_div, mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl; intro c _
  ring

def targetClassKernel (off : ℕ) (lam t x : ℝ) :=
  if off=0 then 2/Real.sqrt (2*π)*Real.sqrt (V (lam*v t) x)
    else 2/Real.sqrt π*Real.sqrt (lam*v t+W (lam*v t))

theorem phase_class_kernel_sum (d : ℕ) (dp : 0<d) (lam t x : ℝ) :
    (∑ c : Fin d, targetClassKernel c.val lam t x) = phase_incident_kernel d lam t x := by
  cases d with
  | zero => omega
  | succ d =>
    simp only [Fin.sum_univ_succ,targetClassKernel,Fin.val_zero,ite_true,Fin.val_succ,
      Nat.succ_ne_zero,ite_false,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
      phase_incident_kernel,Nat.cast_succ]
    ring

/-- Average the actual moving pivot slots and the d fixed class offsets.
The convergence input is at one tagged physical incidence at a time. -/
theorem phase_row_limit_of_tagged_classes {N H G ell : ℕ → ℕ} (d : ℕ) (dp : 0<d)
    (np : ∀ n, 0<N n) (t : ℕ → ℝ) (lam T X : ℝ)
    (localLaw : ∀ (i : ∀ n, Fin (N n)) (c : Fin d), Tendsto
      (fun n => targetClassPhaseMean (N n) d (H n) (G n) (ell n) c.val (i n) (t n)) atTop
        (𝓝 (targetClassKernel c.val lam T X))) :
    Tendsto (fun n => actualPhaseRow (N n) d (H n) (G n) (ell n) (t n)) atTop
      (𝓝 (phase_incident_kernel d lam T X)) := by
  letI : ∀ n, Nonempty (Fin (N n)) := fun n => ⟨⟨0,np n⟩⟩
  simp_rw [actualPhaseRow_eq_tag_classes _ d _ _ _ dp]
  apply phase_pivot_average_limit
  · intro n i; positivity
  · intro n; simp [nsmul_eq_mul,(by exact_mod_cast (np n).ne' : (N n:ℝ) ≠ 0)]
  · intro i
    rw [← phase_class_kernel_sum d dp]
    exact tendsto_finsetSum _ fun c _ => localLaw i c

end Shellsort.F09
