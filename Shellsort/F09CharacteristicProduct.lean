import Shellsort.ProductWeights
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Third-moment comparison of products of characteristic functions for
independent, non-identically distributed finite sources. -/
noncomputable section
namespace Shellsort.F09
open scoped BigOperators
open Complex
private def phaseExp (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*I)
private def quadratic (x : ℝ) : ℂ := 1+(x:ℂ)*I-(x:ℂ)^2/2

private theorem phase_quadratic (x : ℝ) :
    ‖phaseExp x - quadratic x‖ ≤ 4*|x|^3 := by
  let u : ℂ := (x:ℂ)*I
  have un : ‖u‖ = |x| := by simp [u,Complex.norm_real,Real.norm_eq_abs]
  by_cases small : |x| ≤ 1
  · have bound := Complex.exp_bound (x := u) (by simpa only [un] using small) (n := 3) (by decide)
    have eq : (∑ m ∈ Finset.range 3, u^m/m.factorial) = quadratic x := by
      simp [u,quadratic,Finset.sum_range_succ,mul_pow]; ring
    rw [eq,un] at bound
    change ‖Complex.exp u - _‖ ≤ _
    exact bound.trans (by norm_num [Nat.factorial]; nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3])
  · have big : 1 ≤ |x| := le_of_not_ge small
    have step := norm_sub_le (phaseExp x) (quadratic x)
    have q₁ := norm_sub_le (1+u) ((x:ℂ)^2/2)
    have q₂ := norm_add_le (1:ℂ) u
    change ‖(1+u)-(x:ℂ)^2/2‖ ≤ _ at q₁
    simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat] at q₁
    rw [un,norm_one] at q₂
    have nrm : ‖phaseExp x‖ = 1 := Complex.norm_exp_ofReal_mul_I x
    rw [nrm] at step
    change _ ≤ 1 + ‖(1+u)-(x:ℂ)^2/2‖ at step
    have sq := mul_le_mul_of_nonneg_left big (abs_nonneg x)
    have cube := mul_le_mul_of_nonneg_left big (sq_nonneg |x|)
    nlinarith only [step,q₁,q₂,big,sq,cube]

private theorem exp_neg_quadratic (a : ℝ) (ha : 0 ≤ a) :
    |Real.exp (-a) - (1-a)| ≤ a^2 := by
  by_cases small : a ≤ 1
  · have x := Real.norm_exp_sub_one_sub_id_le (x := -a) (by simpa [Real.norm_eq_abs,abs_of_nonneg ha])
    convert x using 2 <;> simp [Real.norm_eq_abs,abs_of_nonneg ha] <;> ring_nf
  · have big : 1 ≤ a := le_of_not_ge small
    have hex := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
    rw [abs_of_nonneg (by linarith [Real.exp_pos (-a)])]
    nlinarith [mul_le_mul_of_nonneg_left big ha]

def finiteChar {α : Type*} [Fintype α] (p X : α → ℝ) (t : ℝ) : ℂ :=
  ∑ x, (p x:ℂ)*phaseExp (t*X x)

theorem finiteChar_norm {α : Type*} [Fintype α] (p X : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (total : ∑ x, p x = 1) (t : ℝ) : ‖finiteChar p X t‖ ≤ 1 := by
  unfold finiteChar
  apply (norm_sum_le ..).trans
  simpa only [norm_mul,phaseExp,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (hp _)] using total.le

theorem finiteChar_gaussian_error {α : Type*} [Fintype α] (p X : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (total : ∑ x, p x = 1) (center : mean p X = 0) (t : ℝ) :
    let s := mean p (fun x => X x ^ 2)
    ‖finiteChar p X t - (Real.exp (-(s*t^2/2)):ℂ)‖ ≤
      4*|t|^3*mean p (fun x => |X x|^3) + (s*t^2/2)^2 := by
  dsimp only
  let s := mean p (fun x => X x^2)
  have spos : 0 ≤ s := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  let a := s*t^2/2
  have ap : 0 ≤ a := by dsimp [a]; positivity
  have term : (∑ x, (p x:ℂ)*quadratic (t*X x)) = 1-(a:ℂ) := by
    have item (x) : (p x:ℂ)*quadratic (t*X x) =
        (p x:ℂ)+ (t:ℂ)*I*(p x*X x:ℝ) - ((t:ℂ)^2/2)*(p x*X x^2:ℝ) := by
      simp only [quadratic,ofReal_mul,ofReal_pow]; ring
    simp_rw [item, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hcenter : ∑ x, p x*X x = 0 := center
    change (∑ x, (p x:ℂ)) + _ - _ = _
    push_cast [a,s,mean]
    norm_cast at *
    push_cast [← Complex.ofReal_sum,total,hcenter]
    ring
  have err : ‖finiteChar p X t - (1-(a:ℂ))‖ ≤ 4*|t|^3*mean p (fun x => |X x|^3) := by
    rw [← term]
    unfold finiteChar mean
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (norm_sum_le ..).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp x)]
    calc p x*‖phaseExp (t*X x)-quadratic (t*X x)‖ ≤ p x*(4*|t*X x|^3) :=
           mul_le_mul_of_nonneg_left (phase_quadratic _) (hp x)
         _ = _ := by rw [abs_mul, mul_pow]; ring
  have e := exp_neg_quadratic a ap
  have ec : ‖(1-(a:ℂ))-(Real.exp (-a):ℂ)‖ ≤ a^2 := by
    rw [show (1-(a:ℂ))-(Real.exp (-a):ℂ) = ((1-a-Real.exp (-a):ℝ):ℂ) by push_cast; ring,
      Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
    exact e
  exact (norm_sub_le_norm_sub_add_norm_sub _ (1-(a:ℂ)) _).trans (add_le_add err ec)


/-- Characteristic function of the sum under the actual independent product law. -/
theorem finiteChar_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (p X : (i : ι) → α i → ℝ) (t : ℝ) :
    finiteChar (productWeight p) (fun a => ∑ i, X i (a i)) t = ∏ i, finiteChar (p i) (X i) t := by
  classical
  unfold finiteChar
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  have e : phaseExp (t*∑ i, X i (a i)) = ∏ i, phaseExp (t*X i (a i)) := by
    unfold phaseExp
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]; push_cast; rw [Finset.sum_mul]
  unfold productWeight
  rw [e, Complex.ofReal_prod, Finset.prod_mul_distrib]

private theorem prod_diff {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i-g i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    let P := ∏ j ∈ s, f j
    let Q := ∏ j ∈ s, g j
    have small : ‖Q‖ ≤ 1 := by
      change ‖∏ j ∈ s, g j‖ ≤ 1
      calc _ ≤ ∏ j ∈ s, ‖g j‖ := Finset.norm_prod_le _ _
           _ ≤ 1 := Finset.prod_le_one₀ (fun j _ => norm_nonneg _) (fun j _ => hg j)
    change ‖f i*P - g i*Q‖ ≤ _
    rw [show f i*P-g i*Q = (f i-g i)*Q + f i*(P-Q) by ring]
    apply (norm_add_le ..).trans
    simp only [norm_mul]
    exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) small)
      ((mul_le_of_le_one_left (norm_nonneg _) (hf i)).trans ih)

/-- Uniform estimate valid for zero-variance summands as well. The quantities
on the right are third absolute moments and squared variances of the already
normalized summands. -/
theorem independent_sum_gaussian_error {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (p X : (i : ι) → α i → ℝ)
    (hp : ∀ i x, 0 ≤ p i x) (total : ∀ i, ∑ x, p i x = 1) (cent : ∀ i, mean (p i) (X i) = 0)
    (t : ℝ) :
    let s := fun i => mean (p i) (fun x => X i x ^ 2)
    ‖finiteChar (productWeight p) (fun a => ∑ i, X i (a i)) t -
        (Real.exp (-(∑ i, s i)*t^2/2):ℂ)‖ ≤
      4*|t|^3*(∑ i, mean (p i) (fun x => |X i x|^3)) + (t^2/2)^2*(∑ i, (s i)^2) := by
  classical
  dsimp only
  let s i := mean (p i) (fun x => X i x^2)
  let f i := finiteChar (p i) (X i) t
  let g i : ℂ := Real.exp (-(s i*t^2/2))
  have sg (i) : ‖g i‖ ≤ 1 := by
    have a : 0 ≤ s i := Finset.sum_nonneg fun x _ => mul_nonneg (hp _ _) (sq_nonneg _)
    simp only [g, Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have eq : (∏ i, g i) = ((Real.exp (-(∑ i, s i)*t^2/2)):ℂ) := by
    unfold g
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    calc (∑ i, -(s i*t^2/2)) = ∑ i, s i*(-t^2/2) := by
           apply Finset.sum_congr rfl; intro i _; ring
         _ = _ := by rw [← Finset.sum_mul]; ring
  rw [finiteChar_product, ← eq]
  refine (prod_diff Finset.univ f g (fun i => finiteChar_norm _ _ (hp i) (total i) _) sg).trans ?_
  calc (∑ i, ‖f i-g i‖) ≤ ∑ i, (4*|t|^3*mean (p i) (fun x => |X i x|^3)+(s i*t^2/2)^2) :=
         Finset.sum_le_sum fun i _ => finiteChar_gaussian_error _ _ (hp i) (total i) (cent i) t
       _ = _ := by
         simp only [Finset.sum_add_distrib, Finset.mul_sum]
         congr 1
         apply Finset.sum_congr rfl; intro i _; dsimp [s]; ring
end Shellsort.F09
end
