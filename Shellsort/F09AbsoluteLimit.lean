import Shellsort.F09GaussianAbsolute
import Shellsort.F09CharacteristicProduct
import Shellsort.ProductVariance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Absolute-cost limit for a triangular array of genuine independent finite
sources. The result permits zero limiting variance and unequal local laws. -/
noncomputable section
namespace Shellsort.F09
open Filter Topology MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

private def pmf {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (total : ∑ x, p x = 1) : PMF α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x))
    (by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), total]; simp)

private def lawOf {α : Type*} [Fintype α] (p X : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (total : ∑ x, p x = 1) : ProbabilityMeasure ℝ :=
  ⟨((pmf p hp total).map X).toMeasure,inferInstance⟩

private theorem law_integral {α E : Type*} [Fintype α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (p X : α → ℝ) (hp : ∀ x, 0 ≤ p x) (total : ∑ x, p x = 1)
    (f : ℝ → E) (hf : Measurable f) :
    ∫ x, f x ∂(lawOf p X hp total : Measure ℝ) = ∑ a, p a • f (X a) := by
  letI : MeasurableSpace α := ⊤
  haveI : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  have hX : Measurable X := fun _ _ => trivial
  change (∫ x, f x ∂((pmf p hp total).map X).toMeasure) = _
  rw [← PMF.toMeasure_map X _ hX,integral_map hX.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable,
    PMF.integral_eq_sum]
  simp [pmf,ENNReal.toReal_ofReal (hp _)]

private theorem law_integrable {α : Type*} [Fintype α] (p X : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (total : ∑ x, p x = 1) (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable f (lawOf p X hp total : Measure ℝ) := by
  letI : MeasurableSpace α := ⊤
  haveI : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  have hX : Measurable X := fun _ _ => trivial
  change Integrable f ((pmf p hp total).map X).toMeasure
  rw [← PMF.toMeasure_map X _ hX, integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable]
  exact Integrable.of_finite

private theorem law_char {α : Type*} [Fintype α] (p X : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (total : ∑ x, p x = 1) (t : ℝ) :
    charFun (lawOf p X hp total : Measure ℝ) t = finiteChar p X t := by
  rw [charFun_apply_real, law_integral p X hp total _ (by fun_prop)]
  unfold finiteChar
  apply Finset.sum_congr rfl
  intro x _
  change _ = (p x:ℂ)*Complex.exp (((t*X x:ℝ):ℂ)*Complex.I)
  simp only [Complex.real_smul, Complex.ofReal_mul]

/-- The finite absolute first moments converge to the Gaussian value,
including at a degenerate threshold. All moments on the hypotheses are
computed under the original finite weights. -/
theorem finite_abs_gaussian_limit {α : ℕ → Type*} [∀ i, Fintype (α i)]
    (p X : (i : ℕ) → α i → ℝ) (hp : ∀ i x, 0 ≤ p i x) (total : ∀ i, ∑ x, p i x = 1)
    (s : ℝ≥0)
    (chars : ∀ t : ℝ, Tendsto (fun i => finiteChar (p i) (X i) t) atTop
      (𝓝 ((Real.exp (-(s:ℝ)*t^2/2)):ℂ)))
    (C : ℝ) (bound : ∀ i, mean (p i) (fun x => X i x^2) ≤ C) :
    Tendsto (fun i => mean (p i) (fun x => |X i x|)) atTop
      (𝓝 (Real.sqrt (2/Real.pi)*Real.sqrt s)) := by
  let μ i := lawOf (p i) (X i) (hp i) (total i)
  let ν : ProbabilityMeasure ℝ := ⟨gaussianReal 0 s,inferInstance⟩
  have weak (t : ℝ) : Tendsto (fun i => charFun (μ i : Measure ℝ) t) atTop
      (𝓝 (charFun (ν : Measure ℝ) t)) := by
    simp only [μ,law_char]
    change Tendsto (fun i => finiteChar (p i) (X i) t) atTop (𝓝 (charFun (gaussianReal 0 s) t))
    rw [charFun_gaussianReal]
    have exponent : ((Real.exp (-(s:ℝ)*t^2/2)):ℂ) =
        Complex.exp ((t:ℂ)*(0:ℝ)*Complex.I-(s:ℝ)*(t:ℂ)^2/2) := by
      rw [Complex.ofReal_exp]
      push_cast
      congr 1
      ring
    exact exponent ▸ chars t
  have gm : MemLp id 2 (gaussianReal 0 s) := memLp_id_gaussianReal 2
  have gsm : Integrable (fun x : ℝ => x^2) (gaussianReal 0 s) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).1 gm
  have ga : Integrable (fun x : ℝ => |x|) (gaussianReal 0 s) := (gm.integrable (by norm_num)).abs
  have calcLim := abs_moment_tendsto_of_charFun μ ν weak
    (fun i => law_integrable _ _ _ _ _ (by fun_prop))
    (fun i => law_integrable _ _ _ _ _ (by fun_prop)) ga gsm C (fun i => by
      simpa [μ,law_integral _ _ _ _ _ (show Measurable (fun x : ℝ => x^2) by fun_prop),
        smul_eq_mul,mean] using bound i)
  rw [← integral_abs_gaussian]
  apply calcLim.congr
  intro i
  rw [show (μ i : Measure ℝ) = (lawOf (p i) (X i) (hp i) (total i) : Measure ℝ) from rfl,
    law_integral _ _ _ _ _ (by fun_prop)]
  rfl


/-- Lyapunov comparison specialized to the finite product weights that arise by
conditioning the original slots. The summands may vary with both row and source. -/
theorem independent_abs_limit {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {α : (n : ℕ) → ι n → Type*} [∀ n i, Fintype (α n i)]
    (p X : (n : ℕ) → (i : ι n) → α n i → ℝ)
    (hp : ∀ n i x, 0 ≤ p n i x) (total : ∀ n i, ∑ x, p n i x = 1)
    (cent : ∀ n i, mean (p n i) (X n i) = 0) (s : ℝ≥0)
    (varLim : Tendsto (fun n => ∑ i, mean (p n i) (fun x => X n i x^2)) atTop (𝓝 (s:ℝ)))
    (third : Tendsto (fun n => ∑ i, mean (p n i) (fun x => |X n i x|^3)) atTop (𝓝 0))
    (small : Tendsto (fun n => ∑ i, (mean (p n i) (fun x => X n i x^2))^2) atTop (𝓝 0)) :
    Tendsto (fun n => mean (productWeight (p n)) (fun z => |∑ i, X n i (z i)|))
      atTop (𝓝 (Real.sqrt (2/Real.pi)*Real.sqrt s)) := by
  let A n i := mean (p n i) (fun x => X n i x^2)
  let V n := ∑ i, A n i
  let P n := productWeight (p n)
  let Y n (z : ∀ i, α n i) := ∑ i, X n i (z i)
  have equal (n) : mean (P n) (fun z => Y n z ^ 2) = V n := by
    have add := productWeight_variance_sum (p n) (X n) (total n)
    have mu := productWeight_mean_sum (p n) (X n) (total n)
    simp only [cent,Finset.sum_const_zero] at mu
    simp only [centeredSecond,mu,cent,sub_zero] at add
    exact add
  obtain ⟨C,upper⟩ := varLim.bddAbove_range
  apply finite_abs_gaussian_limit P Y (fun n => productWeight_nonneg _ (hp n))
    (fun n => productWeight_sum _ (total n)) s _ C
    (fun n => (equal n).le.trans (upper (Set.mem_range_self n)))
  intro t
  have err := (third.const_mul (4*|t|^3)).add (small.const_mul ((t^2/2)^2))
  simp only [mul_zero,add_zero] at err
  have diff : Tendsto (fun n => finiteChar (P n) (Y n) t -
      ((Real.exp (-(V n)*t^2/2)):ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ err
    intro n
    exact independent_sum_gaussian_error (p n) (X n) (hp n) (total n) (cent n) t
  have normal : Tendsto (fun n => ((Real.exp (-(V n)*t^2/2)):ℂ)) atTop
      (𝓝 ((Real.exp (-(s:ℝ)*t^2/2)):ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp ((varLim.neg.mul_const (t^2)).div_const 2))
  simpa using diff.add normal
end Shellsort.F09
end
