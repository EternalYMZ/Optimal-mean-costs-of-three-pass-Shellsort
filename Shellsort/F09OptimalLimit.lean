import Shellsort.F09ResidueRestriction
import Shellsort.F09CertificateFunctions
import Mathlib.Topology.Sequences

/-! Compactness, recovery at every size and minimization for the actual finite
three-pass cost. The fixed-divisor critical law is an explicit input to the
limit-transfer theorem. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology Set

def scaleA {n : ℕ} (w : LegalThreePassPair n) := (w.val.1.val:ℝ)/Real.sqrt n
def scaleB {n : ℕ} (w : LegalThreePassPair n) := (w.val.2.val:ℝ)/Real.sqrt (Real.sqrt n)
def divisor {n : ℕ} (w : LegalThreePassPair n) := Nat.gcd w.val.1.val w.val.2.val
def normCost {n : ℕ} (w : LegalThreePassPair n) := threePassPairMeanShifts w/(n*Real.sqrt n)

def CriticalCostLaw : Prop :=
  ∀ (N : ℕ → ℕ) (w : ∀ i, LegalThreePassPair (N i)) (d : ℕ) (a b : ℝ),
    Tendsto N atTop atTop → 0 < d → 0 < a → 0 < b →
    (∀ᶠ i in atTop, divisor (w i) = d) →
    Tendsto (fun i => scaleA (w i)) atTop (𝓝 a) →
    Tendsto (fun i => scaleB (w i)) atTop (𝓝 b) →
    Tendsto (fun i => normCost (w i)) atTop (𝓝 (K d a b))

/-- Every uniformly budgeted sequence admits a subsequence with fixed gcd
and two positive limiting coordinates. No asymptotic distributional premise. -/
theorem budget_convergent_subsequence (N : ℕ → ℕ) (w : ∀ i, LegalThreePassPair (N i))
    (C : ℝ) (hp : 0 < C) (budget : ∀ i, normCost (w i) ≤ C) :
    ∃ (d : ℕ) (a b : ℝ) (φ : ℕ → ℕ), 0 < d ∧ 0 < a ∧ 0 < b ∧ StrictMono φ ∧
      (∀ᶠ i in atTop, divisor (w (φ i)) = d) ∧
      Tendsto (fun i => scaleA (w (φ i))) atTop (𝓝 a) ∧
      Tendsto (fun i => scaleB (w (φ i))) atTop (𝓝 b) := by
  obtain ⟨L,L1,rect⟩ := threePass_budget_rectangle C hp
  have lp : 0 < L := by linarith
  let D : ℕ := ⌈1+(2048*C)^2⌉₊
  let S : Set (ℕ × (ℝ × ℝ)) := Icc 1 D ×ˢ (Icc (1/L) L ×ˢ Icc (1/L) L)
  let X (i : ℕ) : ℕ × (ℝ × ℝ) := (divisor (w i), scaleA (w i), scaleB (w i))
  have compact : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have mem (i) : X i ∈ S := by
    let n := N i
    let h := (w i).val.1.val
    let g := (w i).val.2.val
    have hn : h < n := (w i).val.1.isLt
    have hg : g < h := (w i).property.2
    have g₂ : 2 ≤ g := (w i).property.1
    have np : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have sp := Real.sqrt_pos.2 np
    have tp := Real.sqrt_pos.2 sp
    have cost := (div_le_iff₀ (mul_pos np sp)).1 (budget i)
    rw [← mul_assoc] at cost
    obtain ⟨h₁,h₂,g₁,g₂'⟩ := rect n h g hn hg g₂ cost
    have dpos : 0 < Nat.gcd h g := Nat.gcd_pos_of_pos_left g (by omega)
    have dcap : (Nat.gcd h g:ℝ) ≤ 1+(2048*C)^2 := by
      by_cases two : 2 ≤ Nat.gcd h g
      · have root := threePass_common_divisor_budget n h g (Nat.gcd h g) hn hg g₂ two
          (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..) C cost
        have sq := mul_self_le_mul_self (Real.sqrt_nonneg _) root
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg (Nat.gcd h g))]
      · have eq : Nat.gcd h g = 1 := by omega
        rw [eq]; push_cast; nlinarith [sq_nonneg (2048*C)]
    have dc : Nat.gcd h g ≤ D := by exact_mod_cast dcap.trans (Nat.le_ceil _)
    change (1 ≤ Nat.gcd h g ∧ Nat.gcd h g ≤ D) ∧
      ((1/L ≤ (h:ℝ)/Real.sqrt n ∧ (h:ℝ)/Real.sqrt n ≤ L) ∧
       (1/L ≤ (g:ℝ)/Real.sqrt (Real.sqrt n) ∧ (g:ℝ)/Real.sqrt (Real.sqrt n) ≤ L))
    exact ⟨⟨dpos,dc⟩,⟨(div_le_div_iff₀ lp sp).2 (by linarith),
           (div_le_iff₀ sp).2 h₂⟩,⟨(div_le_div_iff₀ lp tp).2 (by linarith),(div_le_iff₀ tp).2 g₂'⟩⟩
  obtain ⟨⟨d,a,b⟩,hS,φ,mono,lim⟩ := compact.tendsto_subseq mem
  have hdlim : Tendsto (fun i => divisor (w (φ i))) atTop (𝓝 d) := lim.fst_nhds
  have hd : ∀ᶠ i in atTop, divisor (w (φ i)) = d := by
    exact hdlim ((isOpen_discrete ({d} : Set ℕ)).mem_nhds (by simp))
  exact ⟨d,a,b,φ,hS.1.1,lt_of_lt_of_le (by positivity : 0 < 1/L) hS.2.1.1,
    lt_of_lt_of_le (by positivity : 0 < 1/L) hS.2.2.1,mono,hd,lim.snd_nhds.fst_nhds,lim.snd_nhds.snd_nhds⟩

private def fallback (n : ℕ) (hn : 16 ≤ n) : LegalThreePassPair n :=
  ⟨(⟨3,by omega⟩,⟨2,by omega⟩),by change 2 ≤ 2; decide,by change 2 < 3; decide⟩

/-- An actual legal table at each array size, including all pre-asymptotic
sizes in any sequence above the finite minimum's domain. -/
theorem recovery_family (N : ℕ → ℕ) (lo : ∀ i, 16 ≤ N i) (grow : Tendsto N atTop atTop)
    (d : ℕ) (hd : 0 < d) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ w : ∀ i, LegalThreePassPair (N i), (∀ᶠ i in atTop, divisor (w i) = d) ∧
      Tendsto (fun i => scaleA (w i)) atTop (𝓝 a) ∧
      Tendsto (fun i => scaleB (w i)) atTop (𝓝 b) := by
  obtain ⟨h,g,gcd,legal,alim,blim⟩ := critical_gap_realization d hd a b ha hb
  let w (i) : LegalThreePassPair (N i) :=
    if ok : 2 ≤ g (N i) ∧ g (N i) < h (N i) ∧ h (N i) < N i then
      ⟨(⟨h (N i),ok.2.2⟩,⟨g (N i),ok.2.1.trans ok.2.2⟩),ok.1,ok.2.1⟩
    else fallback (N i) (lo i)
  have ev := grow.eventually legal
  refine ⟨w,?_,(alim.comp grow).congr' ?_,(blim.comp grow).congr' ?_⟩
  · filter_upwards [ev] with i hi
    simpa [w,hi,divisor] using gcd (N i)
  · filter_upwards [ev] with i hi; simp [w,hi,scaleA]
  · filter_upwards [ev] with i hi; simp [w,hi,scaleB]

def criticalValues : Set ℝ := {x | ∃ d : ℕ, 0 < d ∧ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ x = K d a b}


private theorem has_minimizer (n : ℕ) (hn : 16 ≤ n) :
    ∃ w : LegalThreePassPair n, threePassPairMeanShifts w = optimalThreePassMeanShifts n hn ∧
      ∀ v : LegalThreePassPair n, normCost w ≤ normCost v := by
  classical
  obtain ⟨w,_,heq⟩ := Finset.exists_mem_eq_inf'
    (show (Finset.univ : Finset (LegalThreePassPair n)).Nonempty from
      ⟨fallback n hn,Finset.mem_univ _⟩) threePassPairMeanShifts
  refine ⟨w,heq.symm,?_⟩
  intro v
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact heq.ge.trans (Finset.inf'_le threePassPairMeanShifts (Finset.mem_univ v))

/-- Minimization over *all* legal words, independently for the two executed
costs. The only analytic input is the fixed-divisor critical law, including
its second- and final-pass contributions. Even attainment of the limiting
infimum follows from actual finite minimizers. -/
theorem optimal_cost_limits_of_critical_law (law : CriticalCostLaw)
    (N : ℕ → ℕ) (lo : ∀ i, 16 ≤ N i) (grow : Tendsto N atTop atTop) :
    Tendsto (fun i => optimalThreePassMeanShifts (N i) (lo i) / (N i * Real.sqrt (N i)))
      atTop (𝓝 (sInf criticalValues)) ∧
    Tendsto (fun i => optimalThreePassMeanComparisons (N i) (lo i) / (N i * Real.sqrt (N i)))
      atTop (𝓝 (sInf criticalValues)) ∧ sInf criticalValues ∈ criticalValues := by
  choose w eq best using fun i => has_minimizer (N i) (lo i)
  have np (i) : (0:ℝ) < N i := by exact_mod_cast (show 0 < N i by have := lo i; omega)
  have den (i) : (0:ℝ) < N i * Real.sqrt (N i) := mul_pos (np _) (Real.sqrt_pos.2 (np _))
  have budget (i) : normCost (w i) ≤ 2 := by
    apply (div_le_iff₀ (den i)).2
    rw [eq i, ← mul_assoc]
    exact (optimal_threePass_mean_refined_upper _ _).1
  have extract (ns : ℕ → ℕ) (nsGrow : Tendsto ns atTop atTop) :
      ∃ φ : ℕ → ℕ, Tendsto (fun i => normCost (w (ns (φ i)))) atTop (𝓝 (sInf criticalValues))
        ∧ sInf criticalValues ∈ criticalValues := by
    obtain ⟨d,a,b,φ,hd,ha,hb,hφ,gd,al,bl⟩ := budget_convergent_subsequence
      (N ∘ ns) (fun i => w (ns i)) 2 (by norm_num) (fun i => budget (ns i))
    let sizes (i) := N (ns (φ i))
    have incl : Tendsto sizes atTop atTop := (grow.comp nsGrow).comp hφ.tendsto_atTop
    have limit := law sizes (fun i => w (ns (φ i))) d a b incl hd ha hb gd al bl
    have least : IsLeast criticalValues (K d a b) := by
      refine ⟨⟨d,hd,a,b,ha,hb,rfl⟩,?_⟩
      rintro y ⟨e,he,s,t,hs,ht,rfl⟩
      obtain ⟨v,vd,va,vb⟩ := recovery_family sizes (fun i => lo _) incl e he s t hs ht
      exact le_of_tendsto_of_tendsto' limit (law sizes v e s t incl he hs ht vd va vb)
        (fun i => best _ (v i))
    exact ⟨φ,least.csInf_eq.symm ▸ limit,least.csInf_eq.symm ▸ least.1⟩
  have shifts : Tendsto (fun i => normCost (w i)) atTop (𝓝 (sInf criticalValues)) :=
    tendsto_of_subseq_tendsto (fun ns hg => by
      obtain ⟨φ,ok,_⟩ := extract ns hg
      exact ⟨φ,ok⟩)
  have sm : Tendsto (fun i => optimalThreePassMeanShifts (N i) (lo i) / (N i * Real.sqrt (N i)))
      atTop (𝓝 (sInf criticalValues)) := shifts.congr (fun i => by unfold normCost; rw [eq])
  obtain ⟨_,_,attained⟩ := extract id tendsto_id
  refine ⟨sm,?_,attained⟩
  have root := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp grow)
  have van : Tendsto (fun i => (3:ℝ) / Real.sqrt (N i)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop root
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le sm (by simpa using sm.add van)
  · intro i
    exact div_le_div_of_nonneg_right (sub_nonneg.mp (optimal_threePass_mean_difference _ _).1) (den i).le
  · intro i
    apply (div_le_iff₀ (den i)).2
    have h := (optimal_threePass_mean_difference (N i) (lo i)).2
    have rootp := Real.sqrt_pos.2 (np i)
    rw [add_mul, div_mul_cancel₀ _ (den i).ne']
    have err : 3/Real.sqrt (N i)*((N i:ℝ)*Real.sqrt (N i)) = 3*(N i:ℝ) := by field_simp
    rw [err]; linarith
end Shellsort.F09
end
