import Shellsort.F09PhaseIntegrationLaw
import Shellsort.F09OptimalLimit
import Shellsort.F09PhaseIntegrationEnvelope

noncomputable section
namespace Shellsort.F09
open Filter Real Set MeasureTheory
open scoped Topology

/-- The remaining local probability statement, using the actual, unreset
source ensemble, and the natural scaling assumptions on reduced classes. -/
def PhysicalPhaseRows : Prop :=
  ∀ (N H G : ℕ → ℕ) (d : ℕ) (lam : ℝ), 0<d → 0<lam →
    (∀ n, 0<N n) → (∀ n, 0<H n) → (∀ n, 0<G n) → (∀ n, (H n).Coprime (G n)) →
    Tendsto (fun n => (G n:ℝ)) atTop atTop → Tendsto (fun n => (H n:ℝ)) atTop atTop →
    Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0) →
    Tendsto (fun n => ((N n/(d*H n):ℕ):ℝ)/(G n:ℝ)^2) atTop (𝓝 lam) →
    ∃ envelope : ℝ → ℝ, IntervalIntegrable envelope volume 0 1 ∧
      (∀ n t, t∈Ioo (0:ℝ) 1 → ∀ k, k<G n → |actualPhaseRow (N n) d (H n) (G n) k t| ≤ envelope t) ∧
      (∀ t ∈ Ioo (0:ℝ) 1, ∀ x ∈ Ioo (0:ℝ) 1, ∀ k : ℕ → ℕ, (∀ n, k n<G n) →
        Tendsto (fun n => (k n:ℝ)/(G n:ℝ)) atTop (𝓝 x) →
        Tendsto (fun n => actualPhaseRow (N n) d (H n) (G n) (k n) t) atTop (𝓝 (phase_incident_kernel d lam t x)))

/-- A single moving-parameter local limit. A separate domination hypothesis
is unnecessary when the local theorem also handles thresholds and widths
approaching their endpoints. -/
def MovingPhysicalPhaseRows : Prop :=
  ∀ (N H G : ℕ → ℕ) (d : ℕ) (lam : ℝ), 0<d → 0<lam →
    (∀ n, 0<N n) → (∀ n, 0<H n) → (∀ n, 0<G n) → (∀ n, (H n).Coprime (G n)) →
    Tendsto (fun n => (G n:ℝ)) atTop atTop → Tendsto (fun n => (H n:ℝ)) atTop atTop →
    Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0) →
    Tendsto (fun n => ((N n/(d*H n):ℕ):ℝ)/(G n:ℝ)^2) atTop (𝓝 lam) →
    ∀ (t : ℕ → ℝ) (k : ℕ → ℕ) (T X : ℝ), (∀ n, t n∈Icc (0:ℝ) 1) → (∀ n, k n<G n) →
      Tendsto t atTop (𝓝 T) → Tendsto (fun n => (k n:ℝ)/(G n:ℝ)) atTop (𝓝 X) →
      Tendsto (fun n => actualPhaseRow (N n) d (H n) (G n) (k n) (t n)) atTop
        (𝓝 (phase_incident_kernel d lam T X))

theorem physicalPhaseRows_of_moving (law : MovingPhysicalPhaseRows) : PhysicalPhaseRows := by
  intro N H G d lam dp lp np hp gp cop Gn Hn GH heat
  have cont n k (_ : k<G n) := actualPhaseRow_continuous (N n) d (H n) (G n) k
  obtain ⟨C,hC⟩ := phase_envelope_of_moving_limits gp
    (fun n t k => actualPhaseRow (N n) d (H n) (G n) k t) cont (by
      intro j hj t k ht hk T X tl xl
      exact ⟨_, law (N ∘ j) (H ∘ j) (G ∘ j) d lam dp lp (fun n => np _) (fun n => hp _)
        (fun n => gp _) (fun n => cop _) (Gn.comp hj) (Hn.comp hj) (GH.comp hj) (heat.comp hj)
        t k T X ht hk tl xl⟩)
  refine ⟨fun _ => C,intervalIntegrable_const,fun n t ht k hk => hC n t ⟨ht.1.le,ht.2.le⟩ k hk,?_⟩
  intro t ht x hx k hk width
  exact law N H G d lam dp lp np hp gp cop Gn Hn GH heat (fun _ => t) k t x
    (fun _ => ⟨ht.1.le,ht.2.le⟩) hk tendsto_const_nhds width

/-- With the local physical phase rows established, all remaining
normalizations, original threshold and phase averages and the sum of the
three executed passes give the fixed-divisor uniform critical law. -/
theorem criticalCostLaw_of_physicalPhaseRows (law : PhysicalPhaseRows) : CriticalCostLaw := by
  intro N w d a b grow dp ap bp divisorEq alim blim
  let h i := (w i).val.1.val
  let g i := (w i).val.2.val
  let u i := Nat.gcd (h i) (g i)
  let H i := h i/u i
  let G i := g i/u i
  have hpos i : 0<h i := by dsimp [h]; have := (w i).property; omega
  have gpos i : 0<g i := by dsimp [g]; have := (w i).property; omega
  have np i : 0<N i := ((gpos i).trans (w i).val.2.isLt)
  have up i : 0<u i := Nat.gcd_pos_of_pos_left _ (hpos i)
  have hp i : 0<H i := Nat.div_pos (Nat.le_of_dvd (hpos i) (Nat.gcd_dvd_left _ _)) (up i)
  have gp i : 0<G i := Nat.div_pos (Nat.le_of_dvd (gpos i) (Nat.gcd_dvd_right _ _)) (up i)
  have cop i : (H i).Coprime (G i) := Nat.coprime_div_gcd_div_gcd (up i)
  have eqs : ∀ᶠ i in atTop, d*H i=h i ∧ d*G i=g i := by
    filter_upwards [divisorEq] with i e
    change u i=d at e
    rw [←e]
    exact ⟨Nat.mul_div_cancel' (Nat.gcd_dvd_left ..),Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)⟩
  have ah : Tendsto (fun i => ((d*H i:ℕ):ℝ)/Real.sqrt (N i)) atTop (𝓝 a) := by
    apply alim.congr'; filter_upwards [eqs] with i e
    dsimp only [scaleA]; rw [e.1]
  have bg : Tendsto (fun i => ((d*G i:ℕ):ℝ)/Real.sqrt (Real.sqrt (N i))) atTop (𝓝 b) := by
    apply blim.congr'; filter_upwards [eqs] with i e
    dsimp only [scaleB]; rw [e.2]
  obtain ⟨Gn,Hn,GH,heat,conv⟩ := phase_reduced_critical_scales N H G d dp grow a b ap bp ah bg
  let lam := (d:ℝ)^2/(a*b^2)
  have lp : 0<lam := by dsimp [lam]; positivity
  obtain ⟨env,integ,bound,rows⟩ := law N H G d lam dp lp np hp gp cop Gn Hn GH heat
  have localLimit := actual_last_phase_limit N H G d dp np hp gp cop Gn lam lp.le env integ bound rows
  have last := localLimit.mul conv
  let M₃ i := uniformAverage (fun p : RankPlacement (N i) => (gapInsertionCost
    (gapSort (gapSort p (h i)) (g i)) 1 (by decide):ℝ))
  have finalPass : Tendsto (fun i => M₃ i/((N i:ℝ)*Real.sqrt (N i))) atTop
      (𝓝 ((J lam+((d:ℝ)-1)*L lam)*(b*Real.sqrt a/(d*Real.sqrt d)))) := by
    apply last.congr'
    filter_upwards [eqs] with i e
    have nPos : (0:ℝ)<N i := by exact_mod_cast np i
    have gPos : (0:ℝ)<G i := by exact_mod_cast gp i
    have hRoot : 0<Real.sqrt (H i) := Real.sqrt_pos.2 (by exact_mod_cast hp i)
    have nRoot := Real.sqrt_pos.2 nPos
    change _ / ((N i:ℝ)*G i*Real.sqrt (H i)) * ((G i:ℝ)*Real.sqrt (H i)/Real.sqrt (N i)) = _
    rw [e.1,e.2]; unfold M₃; field_simp
  have first := threePass_critical_firstPass_limit N h grow hpos a ap alim
  have second := F09Second.critical_secondPass_limit N h g grow hpos gpos a b ap bp alim blim
  have lim := (first.add second).add finalPass
  have eqK : 1/(4*a)+Real.sqrt π*Real.sqrt a/(8*b)+
      (J lam+((d:ℝ)-1)*L lam)*(b*Real.sqrt a/(d*Real.sqrt d)) = K d a b := by
    dsimp [K,c,lam]; ring
  rw [eqK] at lim
  refine lim.congr fun i => ?_
  change _ / _ + _ / _ + M₃ i/_ = threePassPairMeanShifts (w i)/_
  unfold threePassPairMeanShifts
  rw [uniform_threePassInsertionCost_decomposition,add_div,add_div]

end Shellsort.F09
