import Shellsort.F09OptimalLimit
import Shellsort.F09CertificateCover

/-! Identification of the global infimum, eventual coprimality and the
subsequence characterization for actual asymptotically optimal tables. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology Set

theorem kappa_le_shape {z : ℝ} (hz : 0 < z) : kappa ≤ H z :=
  csInf_le (show BddBelow (H '' Ioi 0) from ⟨0,by rintro _ ⟨t,ht,rfl⟩; exact H_nonneg ht⟩)
    ⟨z,hz,rfl⟩

theorem kappa_le_coprime {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : kappa ≤ K 1 a b :=
  (K_lowerBounds (by decide : 0 < 1) kappa).2
    (fun z hz => by rw [reduced_one]; exact kappa_le_shape hz) a b ha hb

theorem coprime_minimizer_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    K 1 a b = kappa ↔ H (shape 1 a b) = kappa ∧ 1/(4*a) = c*Real.sqrt a/b := by
  let z := shape 1 a b
  let u := 1/(4*a)
  let w := c*Real.sqrt a/b
  have zp : 0 < z := shape_pos (by decide) ha hb
  have up : 0 < u := by dsimp [u]; positivity
  have wp : 0 < w := by dsimp [w]; exact div_pos (mul_pos c_pos (Real.sqrt_pos.mpr ha)) hb
  have arg : (1:ℝ)/(a*b^2) = 1/z^2 := by
    dsimp [z,shape]
    rw [Nat.cast_one,div_one,mul_pow,Real.sq_sqrt ha.le]
    ring
  have kval : K 1 a b = u+w+z*J (1/z^2) := by
    simp [K,z,shape,u,w,arg,show (b*Real.sqrt a)^2 = a*b^2 by rw [mul_pow,Real.sq_sqrt ha.le]; ring]
  have square : 4*u*w = c/z := by
    have hp := Real.sqrt_pos.mpr ha
    dsimp [u,w,z,shape]; push_cast; field_simp; rw [Real.sq_sqrt ha.le]; ring
  have root : (Real.sqrt (c/z))^2 = 4*u*w := (Real.sq_sqrt (div_nonneg c_pos.le zp.le)).trans square.symm
  have bounded : H z ≤ K 1 a b :=
    (reduced_one z) ▸ (K_slice (by decide : 0 < 1) zp).2 ⟨a,b,ha,hb,rfl,rfl⟩
  constructor
  · intro eq
    have he := le_antisymm (eq ▸ bounded) (kappa_le_shape zp)
    have sum : u+w = Real.sqrt (c/z) := by
      have e' : u+w+z*J (1/z^2) = Real.sqrt (c/z)+z*J (1/z^2) := kval.symm.trans (eq.trans he.symm)
      exact add_right_cancel e'
    rw [← sum] at root
    exact ⟨he,by nlinarith [sq_nonneg (u-w)]⟩
  · rintro ⟨he,e⟩
    change u = w at e
    have sum : Real.sqrt (c/z) = u+w := by
      rw [← e] at root ⊢
      nlinarith [Real.sqrt_nonneg (c/z),sq_nonneg (Real.sqrt (c/z) - 2*u)]
    rw [← he,kval]
    change _ = Real.sqrt (c/z)+z*J (1/z^2)
    rw [sum]

def DivisorSeparation : Prop :=
  ∀ (d : ℕ) (a b : ℝ), 2 ≤ d → 0 < a → 0 < b → kappa < K d a b

theorem divisorSeparation_of_quadrature (q : QuadratureBounds) : DivisorSeparation := by
  intro d a b hd ha hb
  linarith [(kappa_enclosure q).2,K_noncoprime q hd ha hb]

theorem inf_critical_eq_kappa (sep : DivisorSeparation) : sInf criticalValues = kappa := by
  have lower : kappa ∈ lowerBounds criticalValues := by
    rintro _ ⟨d,hd,a,b,ha,hb,rfl⟩
    by_cases h : d = 1
    · simpa [h] using kappa_le_coprime ha hb
    · exact (sep d a b (by omega) ha hb).le
  have nonempty : criticalValues.Nonempty := ⟨K 1 1 1,1,by decide,1,1,by norm_num,by norm_num,rfl⟩
  refine le_antisymm (le_csInf ⟨H 1, 1, by norm_num, rfl⟩ ?_) (le_csInf nonempty lower)
  rintro x ⟨z,hz,rfl⟩
  obtain ⟨a,b,ha,hb,_,he⟩ := (K_slice (by decide : 0 < 1) hz).1
  rw [reduced_one] at he
  exact csInf_le ⟨_,lower⟩ ⟨1,by decide,a,b,ha,hb,he⟩

/-- All optimal families ultimately have relatively prime gaps. -/
theorem eventually_coprime_of_optimal (law : CriticalCostLaw) (sep : DivisorSeparation)
    (N : ℕ → ℕ) (w : ∀ i, LegalThreePassPair (N i)) (grow : Tendsto N atTop atTop)
    (opt : Tendsto (fun i => normCost (w i)) atTop (𝓝 kappa)) :
    ∀ᶠ i in atTop, divisor (w i) = 1 := by
  by_contra bad
  obtain ⟨ns,inc,viol⟩ := exists_seq_forall_of_frequently
    (show ∃ᶠ i in atTop, divisor (w i) ≠ 1 from by simpa only [Filter.Frequently,not_not] using bad)
  obtain ⟨T,ht⟩ := opt.bddAbove_range
  obtain ⟨d,a,b,φ,hd,ha,hb,up,gd,al,bl⟩ :=
    budget_convergent_subsequence (N ∘ ns) (fun i => w (ns i)) (max 1 T)
      (lt_of_lt_of_le zero_lt_one (le_max_left ..)) (fun i => (ht (mem_range_self _)).trans (le_max_right ..))
  have h2 : 2 ≤ d := by
    obtain ⟨i,hi⟩ := gd.exists
    have := viol (φ i)
    omega
  have v := law (fun i => N (ns (φ i))) (fun i => w (ns (φ i))) d a b
    ((grow.comp inc).comp up.tendsto_atTop) hd ha hb gd al bl
  exact (sep d a b h2 ha hb).ne (tendsto_nhds_unique ((opt.comp inc).comp up.tendsto_atTop) v)

end Shellsort.F09
end
