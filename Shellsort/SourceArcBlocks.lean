import Shellsort.ArcVarianceCostAssembly
import Shellsort.CyclicArcDefinitions

/-! Long/short binomial sources compared to a repeated equal-length phase block. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

def fullArcMarginal (h g owner ell y m s : ℕ) (t : ℝ) : ℝ :=
  mean (bernoulliVectorWeight t m) (fun z =>
    if (s+h*bitCount z)%g ∈ pivotArcSites h g owner ell y then 1 else 0)

def fullArcVar (h g owner ell y m s : ℕ) (t : ℝ) : ℝ :=
  let p := fullArcMarginal h g owner ell y m s t
  p*(1-p)

def fullArcTrace (h g owner ell y m : ℕ) (t : ℝ) : ℝ :=
  ∑ s ∈ Finset.range g, fullArcVar h g owner ell y m s t

private theorem marginal_bounds (h g o ell y m s : ℕ) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    0 ≤ fullArcMarginal h g o ell y m s t ∧ fullArcMarginal h g o ell y m s t ≤ 1 := by
  unfold fullArcMarginal mean
  constructor
  · exact Finset.sum_nonneg fun z _ => mul_nonneg
      (bernoulliVectorWeight_nonneg t ht _ _) (by dsimp only; split <;> norm_num)
  · apply le_trans _ (bernoulliVectorWeight_sum t m).le
    apply Finset.sum_le_sum
    intro z _
    dsimp only
    split <;> simp [bernoulliVectorWeight_nonneg t ht]

private theorem var_nonneg (h g o ell y m s : ℕ) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    0 ≤ fullArcVar h g o ell y m s t :=
  mul_nonneg (marginal_bounds _ _ _ _ _ _ _ _ ht).1
    (sub_nonneg.mpr (marginal_bounds _ _ _ _ _ _ _ _ ht).2)

private theorem var_succ_lower (h g o ell y m s : ℕ) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    (1-t)*fullArcVar h g o ell y m s t ≤ fullArcVar h g o ell y (m+1) s t := by
  let p := fullArcMarginal h g o ell y m s t
  let q := fullArcMarginal h g o ell y m (s+h) t
  have hp := marginal_bounds h g o ell y m s t ht
  have hq := marginal_bounds h g o ell y m (s+h) t ht
  change 0 ≤ q ∧ q ≤ 1 at hq
  have eq : fullArcMarginal h g o ell y (m+1) s t = (1-t)*p+t*q := by
    unfold fullArcMarginal
    let F (u : ℕ) : ℝ := if (s+h*u)%g ∈ pivotArcSites h g o ell y then 1 else 0
    apply (bernoulli_count_succ_mean t m F).trans
    simp [F,p,q,fullArcMarginal,Nat.mul_add,add_assoc,add_left_comm,add_comm]
  unfold fullArcVar
  rw [eq]
  change (1-t)*(p*(1-p)) ≤ ((1-t)*p+t*q)*(1-((1-t)*p+t*q))
  nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (p-q)),
    mul_nonneg ht.1 (mul_nonneg hq.1 (sub_nonneg.mpr hq.2))]

private theorem sourceArcVariance_eq (h g m rem ell : ℕ) (o : Fin h) (t : ℝ) (y : ℕ) :
    sourceArcVariance h g m rem ell o t y =
      ∑ s : Fin h, if s=o then 0 else fullArcVar h g o.val ell y (sourceTrialLength m rem s.val) s.val t := by
  apply Finset.sum_congr rfl
  intro s _
  let w := bernoulliVectorWeight t (sourceTrialLength m rem s.val)
  let e := fun z => pivotArcHit h g o.val ell y s.val (bitCount (m := sourceTrialLength m rem s.val) z)
  change eventMarginal w e * (1-eventMarginal w e) = _
  by_cases eq : s=o
  · subst s
    simp [e,eventMarginal,pivotArcHit]
  · have ne : s.val ≠ o.val := fun he => eq (Fin.ext he)
    have raw : eventMarginal w e = fullArcMarginal h g o.val ell y (sourceTrialLength m rem s.val) s.val t := by
      unfold eventMarginal fullArcMarginal mean
      apply Finset.sum_congr rfl
      intro b _
      simp [e,w,pivotArcHit,ne,mul_ite]
    simp [eq,fullArcVar,raw]

private theorem var_mod (h g o ell y m s : ℕ) (t : ℝ) :
    fullArcVar h g o ell y m (s%g) t = fullArcVar h g o ell y m s t := by
  simp [fullArcVar,fullArcMarginal,Nat.mod_add_mod]

private theorem wholeBlocks_sum (g d : ℕ) (f : ℕ → ℝ) (periodic : ∀ s, f (s%g) = f s) :
    ∑ s ∈ Finset.range (d*g), f s = d * ∑ s ∈ Finset.range g, f s := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have per (i : ℕ) : f (d*g+i) = f i := by
      calc
        _ = f ((d*g+i)%g) := (periodic _).symm
        _ = f (i%g) := by rw [Nat.mul_comm d g, Nat.mul_add_mod_self_left]
        _ = f i := periodic i
    simp only [per,Nat.cast_succ]
    ring

theorem sourceArcVariance_lower_of_max (h g m rem ell : ℕ) (o : Fin h) (t : ℝ) (y : ℕ)
    (ht : 0≤t ∧ t≤1)
    (half : 2 * fullArcVar h g o.val ell y m o.val t ≤ fullArcTrace h g o.val ell y m t) :
    (1-t)*(((h/g:ℕ):ℝ)-1/2)*fullArcTrace h g o.val ell y m t ≤
      sourceArcVariance h g m rem ell o t y := by
  let v (s : ℕ) := fullArcVar h g o.val ell y m s t
  let T := fullArcTrace h g o.val ell y m t
  have vp (s : ℕ) : 0 ≤ v s := var_nonneg _ _ _ _ _ _ _ _ ht
  have block : ((h/g:ℕ):ℝ)*T ≤ ∑ s : Fin h, v s.val := by
    change ((h/g:ℕ):ℝ)*(∑ s ∈ Finset.range g, v s) ≤ _
    rw [Fin.sum_univ_eq_sum_range, ← wholeBlocks_sum g (h/g) v (fun s => var_mod _ _ _ _ _ _ _ _)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.div_mul_le_self h g))
      (fun s _ _ => vp s)
  have split := Finset.sum_erase_add Finset.univ (fun s : Fin h => v s.val) (Finset.mem_univ o)
  have total : (1-t) * ∑ s ∈ Finset.univ.erase o, v s.val ≤ sourceArcVariance h g m rem ell o t y := by
    rw [Finset.mul_sum,sourceArcVariance_eq]
    apply le_trans (Finset.sum_le_sum (g := fun s : Fin h => if s=o then 0 else
      fullArcVar h g o.val ell y (sourceTrialLength m rem s.val) s.val t) ?_)
    · apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset o _) (fun s _ _ => ?_)
      split <;> first | rfl | exact var_nonneg _ _ _ _ _ _ _ _ ht
    · intro s hs
      simp [(Finset.mem_erase.mp hs).1]
      unfold sourceTrialLength
      split
      · exact var_succ_lower _ _ _ _ _ _ _ _ ht
      · change (1-t)*v s.val ≤ v s.val
        nlinarith [mul_nonneg ht.1 (vp s.val)]
  apply le_trans _ total
  change 2*v o.val ≤ T at half
  change (1-t)*(_-1/2)*T ≤ _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht.2)
  nlinarith [block, split, half]

private theorem phased_mem_iff (h g o ell y a b : ℕ) (hc : Nat.Coprime h g) (hl : ell ≤ g) :
    (((o+h*y+h+h*a)%g+h*b)%g ∈ pivotArcSites h g o ell y) ↔ (a+b)%g < ell := by
  let base := o+h*y+h
  have left : ((o+h*y+h+h*a)%g+h*b)%g = (base+h*(a+b))%g := by
    rw [Nat.mod_add_mod]
    dsimp [base]
    congr 1
    ring
  rw [left]
  constructor
  · intro hm
    obtain ⟨w,hw,hw'⟩ := Finset.mem_image.mp hm
    have hwlt := Finset.mem_range.mp hw
    have shifted : o+h*y+h*(w+1) = base+h*w := by dsimp [base]; ring
    rw [shifted] at hw'
    have eq := (coprime_affine_mod_eq_iff h g base w (a+b) hc).mp hw'
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hwlt hl)] at eq
    omega
  · intro small
    apply Finset.mem_image.mpr
    refine ⟨(a+b)%g,Finset.mem_range.mpr small,?_⟩
    have shifted : o+h*y+h*((a+b)%g+1) = base+h*((a+b)%g) := by dsimp [base]; ring
    rw [shifted]
    exact (coprime_affine_mod_eq_iff h g base ((a+b)%g) (a+b) hc).mpr (Nat.mod_mod _ _)

theorem fullArcMarginal_affine (h g o ell y m a : ℕ) (t : ℝ)
    (hc : Nat.Coprime h g) (hl : ell ≤ g) :
    fullArcMarginal h g o ell y m ((o+h*y+h+h*a)%g) t = canonicalArcProb g ell m t a := by
  unfold fullArcMarginal canonicalArcProb mean
  simp only [phased_mem_iff h g o ell y a _ hc hl]

theorem fullArcTrace_eq_canonical (h g o ell y m : ℕ) (t : ℝ)
    (hg : 0 < g) (hc : Nat.Coprime h g) (hl : ell ≤ g) :
    fullArcTrace h g o ell y m t = canonicalArcTrace g ell m t := by
  let f (a : Fin g) : Fin g := ⟨(o+h*y+h+h*a.val)%g,Nat.mod_lt _ hg⟩
  have inj : Function.Injective f := by
    intro a b eq
    apply Fin.ext
    have e := (coprime_affine_mod_eq_iff h g (o+h*y+h) a.val b.val hc).mp (congrArg Fin.val eq)
    simpa [Nat.mod_eq_of_lt a.isLt,Nat.mod_eq_of_lt b.isLt] using e
  let perm := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp inj)
  let F (s : Fin g) := fullArcVar h g o ell y m s.val t
  calc
    fullArcTrace h g o ell y m t = ∑ s : Fin g, F s := (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ a : Fin g, F (perm a) := (Equiv.sum_comp perm F).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      change fullArcMarginal h g o ell y m ((o+h*y+h+h*a.val)%g) t *
        (1-fullArcMarginal h g o ell y m ((o+h*y+h+h*a.val)%g) t) = _
      simp only [fullArcMarginal_affine h g o ell y m a.val t hc hl]

/-- Assemble the all-gap central variance input from uniform canonical blocks.
The half-deletion premise is valid for a random translate of any fixed arc. -/
theorem centralSourceVarianceBound_of_trace (n h g : ℕ) (hh : 0 < h) (hgh : g ≤ h)
    (hg : 2 ≤ g) (hc : Nat.Coprime h g)
    (half : ∀ ell ∈ centralArcLengths g, ∀ t : ℝ, 1/4 ≤ t → t ≤ 3/4 →
      ∀ u : Fin g, 2*(canonicalArcProb g ell (n/h) t u.val *
       (1-canonicalArcProb g ell (n/h) t u.val)) ≤ canonicalArcTrace g ell (n/h) t)
    (traceLower : ∀ ell ∈ centralArcLengths g, ∀ t : ℝ, 1/4 ≤ t → t ≤ 3/4 →
      min ((min ell (g-ell):ℕ):ℝ) (Real.sqrt (n/h:ℕ))/48 ≤ canonicalArcTrace g ell (n/h) t) :
    centralSourceVarianceBound n h g hh := by
  intro i ell hel t tl tu coord a
  let o := coord.1
  let y := ownerBitCount coord.2 a
  have gp : 0<g := by omega
  have el := (centralArcLengths_valid hg hel).2.1.le
  have eqT := fullArcTrace_eq_canonical h g o.val ell y (n/h) t gp hc el
  obtain ⟨u,hu,hu'⟩ := exists_coprime_source_phase h g (o.val%g) (o.val+h*y+h) gp hc (Nat.mod_lt _ gp)
  have emp := fullArcMarginal_affine h g o.val ell y (n/h) u t hc el
  have vars : fullArcVar h g o.val ell y (n/h) o.val t = canonicalArcProb g ell (n/h) t u *
      (1-canonicalArcProb g ell (n/h) t u) := by
    rw [← var_mod h g o.val ell y (n/h) o.val t, ← hu']
    simp only [fullArcVar,emp]
  have halfRaw : 2 * fullArcVar h g o.val ell y (n/h) o.val t ≤ fullArcTrace h g o.val ell y (n/h) t := by
    rw [vars,eqT]
    exact half ell hel t tl tu ⟨u,hu⟩
  have lower := sourceArcVariance_lower_of_max h g (n/h) (n%h) ell o t y ⟨by linarith,by linarith⟩ halfRaw
  rw [eqT] at lower
  apply le_trans _ lower
  let x : ℝ := min ((min ell (g-ell):ℕ):ℝ) (Real.sqrt (n/h:ℕ))
  let d : ℝ := (h/g:ℕ)
  let ratio : ℝ := (h:ℝ)/g
  have gR : (0:ℝ)<g := by exact_mod_cast gp
  have dpos : 1 ≤ h/g := (Nat.le_div_iff_mul_le gp).mpr (by simpa using hgh)
  have d1 : 1 ≤ d := by dsimp [d]; exact_mod_cast dpos
  have upper : ratio ≤ d+1 := by
    apply (div_le_iff₀ gR).mpr
    have ht : h ≤ (h/g+1)*g := by
      rw [Nat.add_mul,Nat.one_mul]
      have := Nat.mod_add_div h g
      have := Nat.mod_lt h gp
      rw [Nat.mul_comm g (h/g)] at *
      omega
    dsimp [d]
    exact_mod_cast ht
  have quarter : ratio/4 ≤ d-1/2 := by linarith
  have fac : ratio/16 ≤ (1-t)*(d-1/2) := by
    nlinarith [mul_nonneg (show 0 ≤ 3/4-t by linarith) (show 0 ≤ d-1/2 by linarith)]
  have tr := traceLower ell hel t tl tu
  change x/48 ≤ _ at tr
  have xpos : 0 ≤ x := le_min (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ = ratio/16*(x/48) := by dsimp [ratio,x]; ring
    _ ≤ ((1-t)*(d-1/2)) * (x/48) := mul_le_mul_of_nonneg_right fac (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left tr (mul_nonneg (by linarith) (by linarith))

end Shellsort
end