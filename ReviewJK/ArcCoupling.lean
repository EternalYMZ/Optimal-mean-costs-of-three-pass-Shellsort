import Shellsort.PoissonBinomialDeviation
import Shellsort.ProductVariance

/-! Comparing two finite Bernoulli sums by the monotone coordinatewise coupling. -/
noncomputable section
namespace Shellsort
namespace JK
open scoped BigOperators

private def joint (a b : ℝ) (z : Bool × Bool) : ℝ :=
  if z.1 then (if z.2 then min a b else a - min a b)
  else (if z.2 then b - min a b else 1 - a - b + min a b)

private theorem joint_nonneg (a b : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (z : Bool × Bool) : 0 ≤ joint a b z := by
  rcases z with ⟨x,y⟩
  rcases le_total a b with h | h <;> cases x <;> cases y <;>
    simp [joint, h] <;> linarith [ha.1, ha.2, hb.1, hb.2]

private theorem joint_sum (a b : ℝ) : ∑ z, joint a b z = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, joint, Bool.false_eq_true, ite_false, ite_true]
  ring

private theorem joint_fst (a b : ℝ) : eventMarginal (joint a b) Prod.fst = a := by
  simp [eventMarginal, Fintype.sum_prod_type, joint]

private theorem joint_snd (a b : ℝ) : eventMarginal (joint a b) Prod.snd = b := by
  simp [eventMarginal, Fintype.sum_prod_type, joint]

private def diff (z : Bool × Bool) : ℝ := (if z.1 then 1 else 0) - (if z.2 then 1 else 0)

private theorem joint_mean (a b : ℝ) : mean (joint a b) diff = a - b := by
  simp [mean, Fintype.sum_prod_type, joint, diff]

private theorem joint_second (a b : ℝ) : secondMoment (joint a b) diff = |a - b| := by
  rcases le_total a b with h | h
  · simp [secondMoment, Fintype.sum_prod_type, joint, diff, min_eq_left h,
      abs_of_nonpos (sub_nonpos.mpr h)]
  · simp [secondMoment, Fintype.sum_prod_type, joint, diff, min_eq_right h,
      abs_of_nonneg (sub_nonneg.mpr h)]

/-- Independent Bernoulli hits with probabilities pᵢ versus m Bernoulli(q) hits.
The total drift is at most two, and every marginal error is at most δ.
The estimate holds for every real center K and for the empty product. -/
theorem bernoulli_arc_coupling {m : ℕ} (p : Fin m → ℝ) (q δ K : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (hδ : ∀ i, |p i - q| ≤ δ) (drift : |∑ i, (p i - q)| ≤ 2) :
    |mean (productWeight (fun i => bernoulliWeight (p i))) (fun z => |(bitCount z : ℝ) - K|) -
      mean (bernoulliVectorWeight q m) (fun z => |(bitCount z : ℝ) - K|)| ≤
      Real.sqrt (3 * (m : ℝ) * δ) := by
  classical
  let w := fun i : Fin m => joint (p i) q
  let v := fun (_ : Fin m) => diff
  let D := fun z : Fin m → Bool × Bool => ∑ i, diff (z i)
  let W := productWeight w
  have normalized (i : Fin m) : ∑ z, w i z = 1 := joint_sum _ _
  have hW : ∑ z, W z = 1 := productWeight_sum w normalized
  have hWpos (z) : 0 ≤ W z := productWeight_nonneg w (fun i => joint_nonneg _ _ (hp i) hq) z
  have meanD : mean W D = ∑ i, (p i - q) := by
    simpa only [W, D, w, v, joint_mean] using productWeight_mean_sum w v normalized
  have varD : centeredSecond W D ≤ ∑ i, |p i - q| := by
    change centeredSecond (productWeight w) (fun z => ∑ i, v i (z i)) ≤ _
    rw [productWeight_variance_sum w v normalized]
    apply Finset.sum_le_sum
    intro i _
    rw [centeredSecond_identity (w i) (v i) (normalized i)]
    change secondMoment (joint (p i) q) diff - (mean (joint (p i) q) diff)^2 ≤ _
    rw [joint_second, joint_mean]
    linarith [sq_nonneg (p i - q)]
  have total : ∑ i, |p i - q| ≤ (m : ℝ) * δ := by
    calc
      _ ≤ ∑ _i : Fin m, δ := Finset.sum_le_sum fun i _ => hδ i
      _ = _ := by simp
  have absDrift : |∑ i, (p i - q)| ≤ (m : ℝ) * δ :=
    (Finset.abs_sum_le_sum_abs _ _).trans total
  have meanSq : (∑ i, (p i - q))^2 ≤ 2 * ((m : ℝ) * δ) := by
    calc
      _ = |∑ i, (p i - q)| * |∑ i, (p i - q)| := by rw [← sq, sq_abs]
      _ ≤ _ := mul_le_mul drift absDrift (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have product_nonnegative : 0 ≤ 3 * (m : ℝ) * δ := by
    have := (abs_nonneg _).trans absDrift
    linarith
  have boundD : mean W (fun z => |D z|) ≤ Real.sqrt (3 * (m : ℝ) * δ) := by
    apply absMean_le_of_second W D hWpos hW _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt product_nonnegative]
    rw [centeredSecond_identity W D hW, meanD] at varD
    linarith
  let reward := fun z : Fin m → Bool => |(bitCount z : ℝ) - K|
  have left := productWeight_event_projection w (fun _ => Prod.fst) normalized reward
  have right := productWeight_event_projection w (fun _ => Prod.snd) normalized reward
  simp only [w, joint_fst] at left
  simp only [w, joint_snd] at right
  change |mean _ reward - mean (productWeight (fun _ : Fin m => bernoulliWeight q)) reward| ≤ _
  rw [← left, ← right]
  let f := fun z : Fin m → Bool × Bool => reward (fun i => (z i).1)
  let g := fun z : Fin m → Bool × Bool => reward (fun i => (z i).2)
  change |mean W f - mean W g| ≤ _
  rw [← mean_sub]
  apply le_trans _ boundD
  change |∑ z, W z * (f z - g z)| ≤ ∑ z, W z * |D z|
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro z _
  rw [abs_mul, abs_of_nonneg (hWpos z)]
  apply mul_le_mul_of_nonneg_left _ (hWpos z)
  have hD : D z = (bitCount (fun i => (z i).1) : ℝ) - (bitCount (fun i => (z i).2) : ℝ) := by
    simp only [D, diff, Finset.sum_sub_distrib, bitCount, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  rw [hD]
  simpa only [f, g, reward, sub_sub_sub_cancel_right] using abs_abs_sub_abs_le
    ((bitCount (fun i => (z i).1) : ℝ) - K) ((bitCount (fun i => (z i).2) : ℝ) - K)

end JK
end Shellsort
end
