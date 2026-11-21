import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Cost interfaces and algebra. These are conditional consequences of explicit
state bounds, not end-to-end Shellsort average complexity theorems. -/
namespace Shellsort

theorem cost_upper_interface (m₁ m₂ m₃ F₁ F₂ n h g : ℝ)
    (hh : 0 < h) (hg : 0 < g)
    (hm₁ : m₁ ≤ n^2 / (4*h)) (hm₂ : m₂ ≤ 2*F₁/g) (hm₃ : m₃ ≤ F₂) :
    m₁ + m₂ + m₃ ≤ n^2/(4*h) + 2*F₁/g + F₂ := by
  linarith

/-- Three separate lower certificates are combined without double charging. -/
theorem combine_lower_certificates (M U V W c : ℝ)
    (hU : c*U ≤ M) (hV : c*V ≤ M) (hW : c*W ≤ M) :
    c/3*(U+V+W) ≤ M := by linarith

/-- A product certificate forces one of three nonnegative quantities above t.
The stronger sharp AM-GM constant is unnecessary for exponent certification. -/
theorem three_product_lower (U V W t : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (ht : 0 ≤ t)
    (hp : t^3 ≤ U*V*W) : t ≤ U+V+W := by
  by_contra hn
  have hs : U+V+W < t := lt_of_not_ge hn
  have htpos : 0 < t := lt_of_le_of_lt (by positivity : 0 ≤ U+V+W) hs
  have hu : U < t := by linarith
  have hv : V < t := by linarith
  have hw : W < t := by linarith
  have huv : U*V < t*t := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_of_lt hu) hv hV htpos
  have hprod : U*V*W < t*t*t :=
    mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_of_lt huv) hw hW (mul_pos htpos htpos)
  nlinarith

theorem four_product_lower (U V W t : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (ht : 0 ≤ t)
    (hp : t^4 ≤ U*V*W^2) : t ≤ U+V+W := by
  by_contra hn
  have hs : U+V+W < t := lt_of_not_ge hn
  have htpos : 0 < t := lt_of_le_of_lt (by positivity : 0 ≤ U+V+W) hs
  have hu : U < t := by linarith
  have hv : V < t := by linarith
  have hw : W < t := by linarith
  have huv : U*V < t*t := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_of_lt hu) hv hV htpos
  have hww : W*W < t*t := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_of_lt hw) hw hW htpos
  have hprod : (U*V)*(W*W) < (t*t)*(t*t) :=
    mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (le_of_lt huv) hww (mul_nonneg hW hW) (mul_pos htpos htpos)
  nlinarith

theorem coprime_lower_assembly (U V W₁ W₂ t c M : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂)
    (ht : 0 ≤ t) (hc : 0 ≤ c)
    (hp₁ : t^3 ≤ U*V*W₁) (hp₂ : t^4 ≤ U*V*W₂^2)
    (hcost : c*(U+V+min W₁ W₂) ≤ M) : c*t ≤ M := by
  have hl : t ≤ U+V+min W₁ W₂ := by
    rcases le_total W₁ W₂ with h | h
    · rw [min_eq_left h]
      exact three_product_lower U V W₁ t hU hV hW₁ ht hp₁
    · rw [min_eq_right h]
      exact four_product_lower U V W₂ t hU hV hW₂ ht hp₂
  exact le_trans (mul_le_mul_of_nonneg_left hl hc) hcost

end Shellsort
