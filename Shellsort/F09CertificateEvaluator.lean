import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! Outward fixed-point arithmetic for the finite Fourier quadrature. Every
enclosure has real-number semantics, independently of numerical evaluation. -/
namespace Shellsort.F09.Eval
def S : ℕ := 2^160
theorem S_pos : 0 < S := by decide

structure Box where
  lo : ℕ
  hi : ℕ
deriving DecidableEq, Repr

def loQ (b : Box) : ℚ := b.lo / (S:ℚ)
def hiQ (b : Box) : ℚ := b.hi / (S:ℚ)
def Covers (b : Box) (x : ℝ) := (loQ b:ℝ) ≤ x ∧ x ≤ (hiQ b:ℝ)

private theorem sp : 0 < (S:ℝ) := by exact_mod_cast S_pos

theorem covers_iff (b : Box) (x : ℝ) :
    Covers b x ↔ (b.lo:ℝ) ≤ x*S ∧ x*S ≤ (b.hi:ℝ) := by
  simp only [Covers, loQ, hiQ, Rat.cast_div, Rat.cast_natCast, div_le_iff₀ sp, le_div_iff₀ sp]

def pack (l u : ℚ) : Box := ⟨⌊max 0 l * S⌋₊,⌈u*S⌉₊⟩

theorem pack_covers {l u : ℚ} {x : ℝ} (h0 : 0 ≤ x) (hl : (l:ℝ) ≤ x) (hu : x ≤ (u:ℝ)) :
    Covers (pack l u) x := by
  apply (covers_iff ..).2
  have L : (⌊max 0 l * S⌋₊:ℚ) ≤ max 0 l * S :=
    Nat.floor_le (mul_nonneg (le_max_left ..) (Nat.cast_nonneg _))
  have U := Nat.le_ceil (u*(S:ℚ))
  have left : (⌊max 0 l * S⌋₊:ℝ) ≤ max 0 (l:ℝ) * S := by exact_mod_cast L
  have right : (u:ℝ)*S ≤ (⌈u*(S:ℚ)⌉₊:ℝ) := by exact_mod_cast U
  exact ⟨left.trans (mul_le_mul_of_nonneg_right (max_le h0 hl) sp.le),
    (mul_le_mul_of_nonneg_right hu sp.le).trans right⟩

private def sqrtSteps (n : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | k+1, a => sqrtSteps n k ((a + n/a)/2)

/-- A Newton proposal is checked using two exact integer squares. The
standard integer square root also handles arbitrary precision outside the
quadrature range. -/
def checkedSqrt (n : ℕ) : ℕ :=
  let p := sqrtSteps n 9 (2^(n.log2/2+1))
  let a := min p (n/p)
  if a*a ≤ n && n < (a+1)*(a+1) then a else n.sqrt

theorem checkedSqrt_eq (n : ℕ) : checkedSqrt n = n.sqrt := by
  unfold checkedSqrt
  dsimp only
  split
  · rename_i h; exact Nat.eq_sqrt.mpr (by simpa only [Bool.and_eq_true,decide_eq_true_eq] using h)
  · rfl

def root (b : Box) : Box := ⟨checkedSqrt (b.lo*S),checkedSqrt (b.hi*S)+1⟩

theorem root_covers {b : Box} {x : ℝ} (hb : Covers b x) :
    Covers (root b) (Real.sqrt x) := by
  obtain ⟨hl,hu⟩ := (covers_iff ..).1 hb
  have x0 : 0 ≤ x := by
    have := (Nat.cast_nonneg b.lo : (0:ℝ) ≤ b.lo); nlinarith [sp]
  have monoL := mul_le_mul_of_nonneg_right hl sp.le
  have monoU := mul_le_mul_of_nonneg_right hu sp.le
  have L : (((b.lo*S).sqrt:ℝ))^2 ≤ (b.lo:ℝ)*S := by exact_mod_cast Nat.sqrt_le' (b.lo*S)
  have U : (b.hi:ℝ)*S < (((b.hi*S).sqrt:ℝ)+1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' (b.hi*S)
  have sq : (Real.sqrt x * S)^2 = x*S*S := by rw [mul_pow,Real.sq_sqrt x0]; ring
  apply (covers_iff ..).2
  simp only [root,checkedSqrt_eq]
  push_cast
  exact ⟨le_of_sq_le_sq (L.trans (monoL.trans_eq sq.symm)) (mul_nonneg (Real.sqrt_nonneg _) sp.le),
    le_of_sq_le_sq (sq.le.trans (monoU.trans U.le)) (by positivity)⟩

def sqr (b : Box) := pack (loQ b ^2) (hiQ b ^2)

theorem sqr_covers {b : Box} {x : ℝ} (hb : Covers b x) : Covers (sqr b) (x^2) := by
  have l0 : 0 ≤ (loQ b:ℝ) := by unfold loQ; positivity
  apply pack_covers (sq_nonneg _)
  · exact_mod_cast pow_le_pow_left₀ l0 hb.1 2
  · exact_mod_cast pow_le_pow_left₀ (l0.trans hb.1) hb.2 2

def squares : ℕ → Box → Box
  | 0, b => b
  | n+1, b => sqr (squares n b)

theorem squares_covers (n : ℕ) {b : Box} {x : ℝ} (hb : Covers b x) :
    Covers (squares n b) (x^(2^n)) := by
  induction n with
  | zero => simpa [squares] using hb
  | succ n ih => simpa only [squares,pow_succ (2:ℕ),pow_mul] using sqr_covers ih

/-- The tangent at zero bounds exp(-y) from below. Its reciprocal counterpart
bounds it from above. Sixty squarings reduce the error at Fourier arguments. -/
def expNeg (q : ℚ) : Box :=
  let y := q/(2^60)
  squares 60 (pack (1-y) (1/(1+y)))

theorem expNeg_covers {q : ℚ} (hq : 0 ≤ q) : Covers (expNeg q) (Real.exp (-(q:ℝ))) := by
  let y : ℚ := q/(2^60)
  have y0 : 0 ≤ (y:ℝ) := by dsimp [y]; positivity
  have base : Covers (pack (1-y) (1/(1+y))) (Real.exp (-(y:ℝ))) := by
    apply pack_covers (Real.exp_pos _).le
    · push_cast
      linarith only [Real.add_one_le_exp (-(y:ℝ))]
    · push_cast
      rw [Real.exp_neg,← one_div]
      exact one_div_le_one_div_of_le (by linarith) (by linarith only [Real.add_one_le_exp (y:ℝ)])
  have e := squares_covers 60 base
  have target : Real.exp (-(y:ℝ)) ^ (2^60:ℕ) = Real.exp (-(q:ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [y,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,Nat.cast_pow,Nat.cast_ofNat]
    field_simp
  exact target ▸ e

end Shellsort.F09.Eval
