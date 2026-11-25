import Shellsort.BernoulliMixture
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Central

/-! The beta-averaged absolute difference of two independent binomial
counts. We use an exact recurrence, so no central limit theorem is needed. -/
noncomputable section
namespace Shellsort.F09Second
open Finset Filter Topology MeasureTheory

private def A (k : ℕ) : ℝ := (2*k+1:ℝ)*k.centralBinom
private def conv (n : ℕ) := ∑ k ∈ range (n+1), A k*A (n-k)

private theorem A_succ (k : ℕ) : (k+1:ℝ)*A (k+1) = (4*k+6)*A k := by
  have h : (k+1:ℝ)*(k+1).centralBinom = 2*(2*k+1)*k.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  unfold A
  push_cast
  linear_combination (2*(k:ℝ)+3)*h

private theorem conv_moment (n : ℕ) :
    2*(∑ k ∈ range (n+1), (k:ℝ)*(A k*A (n-k))) = n*conv n := by
  let f (k : ℕ) := (k:ℝ)*(A k*A (n-k))
  have reflect : (∑ k ∈ range (n+1), f k) =
      ∑ k ∈ range (n+1), ((n:ℝ)-k)*(A k*A (n-k)) := by
    rw [← Finset.sum_range_reflect f (n+1)]
    apply sum_congr rfl
    intro k hk
    have H : k ≤ n := by simpa using mem_range.mp hk
    simp only [f, Nat.add_sub_cancel, Nat.sub_sub_self H, Nat.cast_sub H]
    ring
  change 2*(∑ k ∈ range (n+1), f k) = _
  rw [two_mul]
  nth_rw 2 [reflect]
  rw [← sum_add_distrib]
  unfold conv
  rw [mul_sum]
  apply sum_congr rfl
  intro k _
  dsimp [f]
  ring

private theorem conv_succ (n : ℕ) : (n+1:ℝ)*conv (n+1) = (4*n+12)*conv n := by
  have m := conv_moment (n+1)
  push_cast at m
  have step : (∑ k ∈ range (n+1+1), (k:ℝ)*(A k*A (n+1-k))) =
      ∑ k ∈ range (n+1), (4*k+6)*(A k*A (n-k)) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply sum_congr rfl
    intro k _
    rw [Nat.add_sub_add_right, Nat.cast_add_one, ← mul_assoc, A_succ, mul_assoc]
  rw [step] at m
  have expand : (∑ k ∈ range (n+1), (4*k+6)*(A k*A (n-k))) =
      4*(∑ k ∈ range (n+1), (k:ℝ)*(A k*A (n-k)))+6*conv n := by
    simp [conv, mul_sum, ← sum_add_distrib, add_mul, mul_assoc]
  rw [expand] at m
  linarith [conv_moment n]

private theorem conv_closed (n : ℕ) :
    conv n = (4:ℝ)^n*(n+1)*(n+2)/2 := by
  induction n with
  | zero => norm_num [conv, A, Nat.centralBinom]
  | succ n ih =>
    have hs := conv_succ n
    rw [ih] at hs
    apply mul_left_cancel₀ (a := (n+1:ℝ)) (by positivity)
    rw [hs, pow_succ, Nat.cast_add_one]
    ring

/-- Binomial point mass as a polynomial; valid at both endpoints. -/
def countMass (n k : ℕ) (t : ℝ) : ℝ := (n.choose k:ℝ)*t^k*(1-t)^(n-k)

private theorem integral_collision_term (n k : ℕ) (hk : k ≤ n) :
    (∫ t : ℝ in 0..1, 2*t*(1-t)*(countMass n k t)^2) =
      2*(n.factorial:ℝ)^2/(2*n+3).factorial*(A k*A (n-k)) := by
  have term : (fun t : ℝ => 2*t*(1-t)*(countMass n k t)^2) =
      (fun t : ℝ => 2*(n.choose k:ℝ)^2*(t^(2*k+1)*(1-t)^(2*(n-k)+1))) := by
    ext t
    simp only [countMass, mul_pow, pow_add, pow_one, mul_comm 2 k, mul_comm 2 (n-k), pow_mul]
    ring
  rw [term, intervalIntegral.integral_const_mul, integer_beta_integral]
  rw [show 2*k+1+(2*(n-k)+1)+1 = 2*n+3 by omega]
  have chooseF (j : ℕ) : (j.centralBinom:ℝ)*(j.factorial:ℝ)^2 = (2*j).factorial := by
    have hh := Nat.add_choose_mul_factorial_mul_factorial j j
    rw [← two_mul] at hh
    exact_mod_cast (show j.centralBinom*j.factorial^2 = (2*j).factorial by
      simpa [Nat.centralBinom_eq_two_mul_choose, pow_two, mul_assoc] using hh)
  have ck : (n.choose k:ℝ)*k.factorial*(n-k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  rw [← chooseF, ← chooseF, ← ck]
  unfold A
  push_cast
  ring

/-- Exact integrated tie probability with the factor from adding two
independent Bernoulli trials. -/
theorem integrated_collision_increment (n : ℕ) :
    (∫ t : ℝ in 0..1, ∑ k ∈ range (n+1), 2*t*(1-t)*(countMass n k t)^2) =
      (n.factorial:ℝ)^2/(2*n+3).factorial*4^n*(n+1)*(n+2) := by
  rw [intervalIntegral.integral_finsetSum]
  · calc
      _ = 2*(n.factorial:ℝ)^2/(2*n+3).factorial*conv n := by
        unfold conv
        rw [mul_sum]
        exact sum_congr rfl fun k hk => integral_collision_term n k (by simpa using mem_range.mp hk)
      _ = _ := by rw [conv_closed]; ring
  · intro k _
    apply Continuous.intervalIntegrable
    unfold countMass
    fun_prop

def countAverage (n : ℕ) (t : ℝ) (F : ℕ → ℝ) : ℝ :=
  mean (bernoulliVectorWeight t n) (fun z => F (bitCount z))

private def countFin {n : ℕ} (z : Fin n → Bool) : Fin (n+1) :=
  ⟨bitCount z, by have b := finiteBitCount_le_card z; simpa [bitCount, finiteBitCount] using Nat.lt_succ_of_le b⟩

private theorem countFin_card {n : ℕ} (k : Fin (n+1)) :
    Fintype.card {z : Fin n → Bool // countFin z = k} = n.choose k := by
  let e : {z : Fin n → Bool // countFin z = k} ≃ {s : Finset (Fin n) // s.card = k} :=
    { toFun := fun z => ⟨univ.filter (fun i => z.val i = true), by
        have h := congrArg Fin.val z.property
        simpa [countFin, bitCount] using h⟩
      invFun := fun s => ⟨fun i => decide (i ∈ s.val), by
        apply Fin.ext
        simpa [countFin, bitCount] using s.property⟩
      left_inv := by intro z; ext i; simp
      right_inv := by intro s; ext i; simp }
  simpa using Fintype.card_congr e

theorem countAverage_eq_sum (n : ℕ) (t : ℝ) (F : ℕ → ℝ) :
    countAverage n t F = ∑ k ∈ range (n+1), countMass n k t * F k := by
  let f (k : Fin (n+1)) := t^(k:ℕ)*(1-t)^(n-k)*F k
  have each (z : Fin n → Bool) : bernoulliVectorWeight t n z * F (bitCount z) = f (countFin z) := by
    simp [bernoulliVectorWeight, bernoulli_product_weight_eq, bitCount, f, countFin, finiteBitCount]
  unfold countAverage mean
  simp_rw [each]
  rw [← Fintype.sum_fiberwise' countFin f, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro k _
  simp [countFin_card, f, countMass, mul_assoc]

private theorem average_mix (n : ℕ) (t a b : ℝ) (F G : ℕ → ℝ) :
    countAverage n t (fun k => a*F k+b*G k) = a*countAverage n t F+b*countAverage n t G := by
  simp only [countAverage, mean, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intros <;> ring

private theorem average_succ (n : ℕ) (t : ℝ) (F : ℕ → ℝ) :
    countAverage (n+1) t F = countAverage n t (fun k => (1-t)*F k + t*F (k+1)) := by
  rw [average_mix]
  exact bernoulli_count_succ_mean t n F

/-- Conditional absolute difference of two independent count variables at the same threshold. -/
def countDifference (n m : ℕ) (t : ℝ) :=
  countAverage n t fun k => countAverage m t fun j => |(k:ℝ)-j|

private theorem two_steps (k j : ℕ) (t : ℝ) :
    (1-t)*((1-t)*|(k:ℝ)-j|+t*|(k:ℝ)-(j+1)|) +
    t*((1-t)*|(k+1:ℝ)-j|+t*|(k+1:ℝ)-(j+1)|) =
      1*|(k:ℝ)-j| + (2*t*(1-t))*(if k=j then 1 else 0) := by
  rcases lt_trichotomy k j with h|rfl|h
  · have hb : (k+1:ℝ) ≤ j := by exact_mod_cast h
    simp only [ite_eq_right_iff.mpr (fun h' => (h.ne h').elim)]
    repeat' rw [abs_of_nonpos (by linarith)]
    ring
  · simp
    ring
  · have hb : (j+1:ℝ) ≤ k := by exact_mod_cast h
    simp only [ite_eq_right_iff.mpr (fun h' => (h.ne' h').elim)]
    repeat' rw [abs_of_nonneg (by linarith)]
    ring

theorem countDifference_succ (n : ℕ) (t : ℝ) :
    countDifference (n+1) (n+1) t = countDifference n n t +
      ∑ k ∈ range (n+1), 2*t*(1-t)*(countMass n k t)^2 := by
  unfold countDifference
  rw [average_succ]
  simp_rw [average_succ n]
  conv_lhs =>
    enter [3,k]
    rw [← average_mix]
  simp_rw [Nat.cast_add_one, two_steps, average_mix]
  simp only [one_mul, add_right_inj]
  rw [countAverage_eq_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [countAverage_eq_sum]
  simp [Finset.sum_ite_eq, hk, mul_ite, pow_two, mul_assoc]

private theorem diff_continuous (n m : ℕ) : Continuous (countDifference n m) := by
  unfold countDifference
  simp_rw [countAverage_eq_sum]
  unfold countMass
  fun_prop

def integratedDifference (m : ℕ) := ∫ t : ℝ in 0..1, countDifference m m t

theorem integratedDifference_exact (m : ℕ) :
    integratedDifference m = (m:ℝ)*4^m/(2*(2*m+1)*m.centralBinom) := by
  induction m with
  | zero => simp [integratedDifference, countDifference, countAverage_eq_sum, countMass]
  | succ m ih =>
    have inc : integratedDifference (m+1) = integratedDifference m +
        (m.factorial:ℝ)^2/(2*m+3).factorial*4^m*(m+1)*(m+2) := by
      unfold integratedDifference
      simp_rw [countDifference_succ]
      rw [intervalIntegral.integral_add, integrated_collision_increment]
      · exact (diff_continuous _ _).intervalIntegrable _ _
      · apply Continuous.intervalIntegrable
        unfold countMass
        fun_prop
    have fac : (m.centralBinom:ℝ)*(m.factorial:ℝ)^2 = (2*m).factorial := by
      exact_mod_cast (show m.centralBinom*m.factorial^2 = (2*m).factorial by
        simpa [Nat.centralBinom_eq_two_mul_choose, two_mul, pow_two, mul_assoc] using
          Nat.add_choose_mul_factorial_mul_factorial m m)
    have cc : (m+1:ℝ)*(m+1).centralBinom = 2*(2*m+1)*m.centralBinom := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ m
    have cb : (0:ℝ) < m.centralBinom := by exact_mod_cast Nat.centralBinom_pos m
    have fpos : (0:ℝ) < m.factorial := by positivity
    have cnext : ((m+1).centralBinom:ℝ) = 2*(2*m+1)*m.centralBinom/(m+1) := by
      apply (eq_div_iff (by positivity)).2
      linarith
    rw [inc, ih, cnext, pow_succ]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]
    rw [← fac]
    push_cast
    field_simp
    ring

/-- Wallis' product evaluates the limiting integrated absolute difference. -/
theorem integratedDifference_limit :
    Tendsto (fun m : ℕ => integratedDifference m / Real.sqrt m) atTop (𝓝 (Real.sqrt Real.pi/4)) := by
  have square (m : ℕ) (hm : 0 < m) :
      (integratedDifference m / Real.sqrt m)^2 =
        ((m:ℝ)/(2*m+1))*Real.Wallis.W m/4 := by
    have mp : (0:ℝ) < m := by exact_mod_cast hm
    have fac : (m.centralBinom:ℝ)*(m.factorial:ℝ)^2 = (2*m).factorial := by
      exact_mod_cast (show m.centralBinom*m.factorial^2 = (2*m).factorial by
        simpa [Nat.centralBinom_eq_two_mul_choose, two_mul, pow_two, mul_assoc] using
          Nat.add_choose_mul_factorial_mul_factorial m m)
    have cb : (0:ℝ) < m.centralBinom := by exact_mod_cast Nat.centralBinom_pos m
    have powers : (2:ℝ)^(4*m) = (4^m:ℝ)^2 := by
      calc
        (2:ℝ)^(4*m) = (2^4:ℝ)^m := pow_mul _ _ _
        _ = (4^2:ℝ)^m := by norm_num
        _ = (4^m:ℝ)^2 := by
          simpa only [pow_mul] using congrArg (fun k : ℕ => (4:ℝ)^k) (Nat.mul_comm 2 m)
    rw [integratedDifference_exact, div_pow, Real.sq_sqrt mp.le, Real.Wallis.W_eq_factorial_ratio,
      ← fac, powers]
    field_simp
    ring
  have lim := (Stirling.tendsto_self_div_two_mul_self_add_one.mul Real.Wallis.tendsto_W_nhds_pi_div_two).div_const 4
  have eqval : Real.sqrt ((1/2)*(Real.pi/2)/4) = Real.sqrt Real.pi/4 := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  rw [← eqval]
  refine (Real.continuous_sqrt.continuousAt.tendsto.comp lim).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  change Real.sqrt (_*_/4) = _
  rw [← square m hm, Real.sqrt_sq]
  rw [integratedDifference_exact]
  positivity

end Shellsort.F09Second
