import Shellsort.F09CertificateEvaluator

/-! Integer products and powers, for repeated evaluation of Fourier weights. -/
namespace Shellsort.F09.Eval

def prod (a b : Box) : Box :=
  ⟨a.lo*b.lo/S, a.hi*b.hi/S+1⟩

theorem prod_covers {a b : Box} {x y : ℝ} (ha : Covers a x) (hb : Covers b y) :
    Covers (prod a b) (x*y) := by
  obtain ⟨al,au⟩ := (covers_iff ..).1 ha
  obtain ⟨bl,bu⟩ := (covers_iff ..).1 hb
  have s0 : 0 < (S:ℝ) := by exact_mod_cast S_pos
  have x0 : 0 ≤ x*S := (Nat.cast_nonneg _).trans al
  have y0 : 0 ≤ y*S := (Nat.cast_nonneg _).trans bl
  have L : ((a.lo*b.lo/S:ℕ):ℝ)*S ≤ (a.lo:ℝ)*b.lo := by exact_mod_cast Nat.div_mul_le_self (a.lo*b.lo) S
  have U : (a.hi:ℝ)*b.hi ≤ S*(((a.hi*b.hi/S:ℕ):ℝ)+1) := by
    exact_mod_cast (Nat.lt_mul_div_succ (a.hi*b.hi) S_pos).le
  apply (covers_iff ..).2
  change ((a.lo*b.lo/S:ℕ):ℝ) ≤ _ ∧ _ ≤ ((a.hi*b.hi/S+1:ℕ):ℝ)
  push_cast
  constructor
  · apply le_of_mul_le_mul_right (a := (S:ℝ)) _ s0
    nlinarith only [L,mul_le_mul al bl (Nat.cast_nonneg _) x0]
  · apply le_of_mul_le_mul_right (a := (S:ℝ)) _ s0
    nlinarith only [U,mul_le_mul au bu y0 (Nat.cast_nonneg _)]

def unit : Box := ⟨S,S⟩
theorem unit_covers : Covers unit 1 := (covers_iff ..).2 (by simp [unit])

/-- Exponentiation by squaring with outward rounding after every multiplication. -/
def powBox (b : Box) (n : ℕ) : Box :=
  if n = 0 then unit else
    let s := powBox b (n/2)
    let v := prod s s
    if n%2 = 0 then v else prod v b
termination_by n

theorem powBox_covers {b : Box} {x : ℝ} (h : Covers b x) (n : ℕ) :
    Covers (powBox b n) (x^n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rw [powBox]
    split_ifs with hn even
    · simpa [hn] using unit_covers
    · have hrec := ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      have hn' : n/2+n/2 = n := by omega
      simpa only [← pow_add,hn'] using prod_covers hrec hrec
    · have hrec := ih (n/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))
      have hn' : n/2+n/2+1 = n := by omega
      simpa only [← pow_add,← pow_succ,hn'] using prod_covers (prod_covers hrec hrec) h

end Shellsort.F09.Eval
