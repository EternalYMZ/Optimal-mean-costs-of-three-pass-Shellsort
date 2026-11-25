import Shellsort.F09CertificateEvaluator

/-! Sine-squared enclosures on every dyadic grid, by reflection and exact
half-angle identities. Only integer square roots are required on grid nodes. -/
namespace Shellsort.F09.Eval

private def folded (q m : ℕ) := if m ≤ q then m else 2*q-m

private def halfBox (positive : Bool) (b : Box) : Box :=
  let c := root (pack (1-hiQ b) (1-loQ b))
  if positive then pack ((1-hiQ c)/2) ((1-loQ c)/2)
  else pack ((1+loQ c)/2) ((1+hiQ c)/2)

private theorem halfBox_covers (x : ℝ) {b : Box} (hb : Covers b (Real.sin x ^2))
    (sign : Bool) (hc : if sign then 0 ≤ Real.cos x else Real.cos x ≤ 0) :
    Covers (halfBox sign b) (Real.sin (x/2) ^2) := by
  let c := root (pack (1-hiQ b) (1-loQ b))
  have complement : Covers (pack (1-hiQ b) (1-loQ b)) (1-Real.sin x^2) := by
    apply pack_covers
    · nlinarith [Real.sin_sq_add_cos_sq x,sq_nonneg (Real.cos x)]
    · push_cast; linarith only [hb.2]
    · push_cast; linarith only [hb.1]
  have bound : Covers c |Real.cos x| := by
    rw [Real.abs_cos_eq_sqrt_one_sub_sin_sq]
    exact root_covers complement
  have half : Real.sin (x/2)^2 = (1-Real.cos x)/2 := by rw [Real.sin_sq_eq_half_sub]; ring_nf
  have low := bound.1
  have high := bound.2
  cases sign with
  | true =>
    change 0 ≤ Real.cos x at hc
    rw [abs_of_nonneg hc] at low high
    apply pack_covers (sq_nonneg _)
    · push_cast; linarith only [half,high]
    · push_cast; linarith only [half,low]
  | false =>
    change Real.cos x ≤ 0 at hc
    rw [abs_of_nonpos hc] at low high
    apply pack_covers (sq_nonneg _)
    · push_cast; linarith only [half,low]
    · push_cast; linarith only [half,high]

def sinGrid : ℕ → ℕ → Box
  | 0,_ => ⟨0,0⟩
  | k+1,m =>
    let p := folded (2^k) m
    halfBox (decide (2*p ≤ 2^k)) (sinGrid k p)

private noncomputable def angle (k m : ℕ) := Real.pi*m/(2:ℝ)^k

private theorem folded_sound (k m : ℕ) (hm : m ≤ 2^(k+1)) :
    folded (2^k) m ≤ 2^k ∧
    Real.sin (angle (k+1) m)^2 = Real.sin (angle k (folded (2^k) m)/2)^2 := by
  let q : ℕ := 2^k
  have maxm : m ≤ 2*q := by simpa [q,pow_succ,Nat.mul_comm] using hm
  have qp : 0 < (q:ℝ) := by dsimp [q]; positivity
  have cq : (q:ℝ) = (2:ℝ)^k := by simp [q]
  change folded q m ≤ q ∧ _
  by_cases test : m ≤ q
  · refine ⟨by simp [folded,test],?_⟩
    apply congrArg (fun t : ℝ => Real.sin t ^2)
    rw [show folded (2^k) m = m from ite_eq_left test]
    unfold angle
    rw [pow_succ,div_div]
  · have fold : folded (2^k) m = 2*q-m := ite_eq_right test
    refine ⟨by change folded q m ≤ q; rw [show folded q m = 2*q-m from fold]; omega,?_⟩
    have eql : angle k (folded (2^k) m)/2 = Real.pi - angle (k+1) m := by
      rw [fold]
      simp only [angle,pow_succ,← cq,Nat.cast_sub maxm,Nat.cast_mul,Nat.cast_ofNat]
      field_simp
    rw [eql,Real.sin_pi_sub]

theorem sinGrid_covers (k m : ℕ) (hm : m ≤ 2^k) :
    Covers (sinGrid k m) (Real.sin (Real.pi*m/(2:ℝ)^k)^2) := by
  change Covers (sinGrid k m) (Real.sin (angle k m)^2)
  induction k generalizing m with
  | zero =>
    have : m = 0 ∨ m = 1 := by norm_num at hm; omega
    rcases this with rfl | rfl <;> simp [angle,sinGrid,Covers,loQ,hiQ]
  | succ k ih =>
    let p := folded (2^k) m
    obtain ⟨hp,ha⟩ := folded_sound k m hm
    rw [ha]
    apply halfBox_covers _ (ih p hp)
    change (if decide (2*p ≤ 2^k) then 0 ≤ Real.cos (angle k p) else Real.cos (angle k p) ≤ 0)
    by_cases h : 2*p ≤ 2^k
    · simp only [h,decide_true,ite_true]
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      · have nn : 0 ≤ angle k p := by unfold angle; positivity
        linarith [Real.pi_pos]
      · unfold angle
        have h' : 2*(p:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast h
        apply (div_le_iff₀ (by positivity)).2
        nlinarith only [mul_le_mul_of_nonneg_left h' Real.pi_pos.le]
    · simp only [h,decide_false]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · unfold angle
        have h' : (2:ℝ)^k ≤ 2*p := by exact_mod_cast (le_of_not_ge h)
        apply (le_div_iff₀ (by positivity)).2
        nlinarith only [mul_le_mul_of_nonneg_left h' Real.pi_pos.le]
      · unfold angle
        have h' : (p:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast hp
        apply (div_le_iff₀ (by positivity)).2
        nlinarith [mul_le_mul_of_nonneg_left h' Real.pi_pos.le, show 0 ≤ Real.pi*(2:ℝ)^k by positivity]

/-- All Fourier modes at endpoints and midpoints of the 128-cell quadratic grid
have denominator 65536, including those with unreduced numerator. -/
def sin65536 (u : ℕ) : Box := sinGrid 16 (u%65536)

theorem sin65536_covers (u : ℕ) :
    Covers (sin65536 u) (Real.sin (Real.pi*u/65536)^2) := by
  have he : Real.pi*u/65536 = Real.pi*(u%65536:ℕ)/65536 + (u/65536:ℕ)*Real.pi := by
    have h : ((u%65536:ℕ):ℝ)+65536*((u/65536:ℕ):ℝ) = u := by exact_mod_cast Nat.mod_add_div u 65536
    linarith only [congrArg (fun x : ℝ => x*Real.pi) h]
  have sign : ((-1:ℝ)^(u/65536))^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm _ 2,pow_mul]; norm_num
  have wave : Real.sin (Real.pi*u/65536)^2 = Real.sin (Real.pi*(u%65536:ℕ)/65536)^2 := by
    rw [he,Real.sin_add_nat_mul_pi,mul_pow,sign,one_mul]
  have grid := sinGrid_covers 16 (u%65536) (show u%65536 ≤ 2^16 from (Nat.mod_lt u (by decide)).le)
  norm_num only [show (2:ℝ)^16 = 65536 by norm_num] at grid
  exact wave.symm ▸ grid

end Shellsort.F09.Eval
