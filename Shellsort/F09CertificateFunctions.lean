import Shellsort.CriticalGapApproximation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Scalar functions in the fixed-divisor critical law (P01, Sections 2–3).
The summation index starts at zero and the Fourier mode is k + 1. -/
noncomputable section
namespace Shellsort.F09
open Real Set

def c : ℝ := Real.sqrt Real.pi / 8
def v (t : ℝ) := t*(1-t)

def V (δ x : ℝ) : ℝ :=
  x*(1-x) - 2/Real.pi^2 * ∑' k : ℕ, Real.exp (-4*Real.pi^2*((k:ℝ)+1)^2*δ) *
    Real.sin (Real.pi*((k:ℝ)+1)*x)^2 / ((k:ℝ)+1)^2

def W (δ : ℝ) : ℝ :=
  1/12 - 1/(2*Real.pi^2) * ∑' k : ℕ,
    Real.exp (-4*Real.pi^2*((k:ℝ)+1)^2*δ) / ((k:ℝ)+1)^2

def J (lam : ℝ) : ℝ :=
  (∫ t in (0:ℝ)..1, ∫ x in (0:ℝ)..1, Real.sqrt (V (lam*v t) x)) / Real.sqrt (2*Real.pi)

def L (lam : ℝ) : ℝ :=
  (∫ t in (0:ℝ)..1, Real.sqrt (lam*v t + W (lam*v t))) / Real.sqrt Real.pi

def shape (d : ℕ) (a b : ℝ) := b*Real.sqrt a/d

def K (d : ℕ) (a b : ℝ) :=
  let lam := (d:ℝ)^2/(a*b^2)
  1/(4*a) + c*Real.sqrt a/b +
    b*Real.sqrt a/(d*Real.sqrt d)*(J lam + ((d:ℝ)-1)*L lam)

def H (z : ℝ) := Real.sqrt (c/z) + z*J (1/z^2)
def B (z : ℝ) := z*L (1/z^2)
def reduced (d : ℕ) (z : ℝ) := (H z + ((d:ℝ)-1)*B z) / Real.sqrt d
def kappa := sInf (H '' Ioi 0)

theorem c_pos : 0 < c := by unfold c; positivity

end Shellsort.F09
