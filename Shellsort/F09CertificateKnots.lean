import Shellsort.F09CertificateAttainment
import Shellsort.F09CertificateWitnessScale
import Shellsort.F09CertificateLowerJ1d2
import Shellsort.F09CertificateLowerJ3d4
import Shellsort.F09CertificateLowerJ1
import Shellsort.F09CertificateLowerJ5d4
import Shellsort.F09CertificateLowerJ11d8
import Shellsort.F09CertificateLowerJ23d16
import Shellsort.F09CertificateLowerJ3d2
import Shellsort.F09CertificateLowerJ7d4
import Shellsort.F09CertificateLowerJ2
import Shellsort.F09CertificateLowerJ3
import Shellsort.F09CertificateLowerJ5
import Shellsort.F09CertificateLowerJ10

/-! Final rational enclosure and strict coprime separation for the actual
critical coefficient. All thirteen signed integrals are checked by the kernel. -/
noncomputable section
namespace Shellsort.F09

theorem verifiedQuadratureBounds : QuadratureBounds where
  j1_2 := by convert Quad.LowerJ1d2.knot using 1 <;> norm_num
  j3_4 := by convert Quad.LowerJ3d4.knot using 1 <;> norm_num
  j1 := by convert Quad.LowerJ1.knot using 1 <;> norm_num
  j5_4 := by convert Quad.LowerJ5d4.knot using 1 <;> norm_num
  j11_8 := by convert Quad.LowerJ11d8.knot using 1 <;> norm_num
  j23_16 := by convert Quad.LowerJ23d16.knot using 1 <;> norm_num
  j3_2 := by convert Quad.LowerJ3d2.knot using 1 <;> norm_num
  j7_4 := by convert Quad.LowerJ7d4.knot using 1 <;> norm_num
  j2 := by convert Quad.LowerJ2.knot using 1 <;> norm_num
  j3 := by convert Quad.LowerJ3.knot using 1 <;> norm_num
  j5 := by convert Quad.LowerJ5.knot using 1 <;> norm_num
  j10 := by convert Quad.LowerJ10.knot using 1 <;> norm_num
  witness := witness_upper

/-- The shape infimum of the actual coprime double integral. -/
theorem verified_kappa_enclosure : (6082215:ℝ)/10000000 ≤ kappa ∧ kappa < (608275:ℝ)/1000000 :=
  kappa_enclosure verifiedQuadratureBounds

theorem verified_kappa_precise :
    (60822153:ℝ)/100000000 ≤ kappa ∧ kappa < (60827485406:ℝ)/100000000000 :=
  ⟨kappa_lower_sharp verifiedQuadratureBounds,kappa_witness_upper⟩

/-- Uniform separation on all positive scales of every noncoprime divisor. -/
theorem verified_noncoprime_separation {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (61546:ℝ)/100000 ≤ K d a b := K_noncoprime_sharp verifiedQuadratureBounds hd ha hb

/-- A coprime positive pair attains the global minimum over all integer divisors
and all positive real scales. -/
theorem verified_global_scale_minimum :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ K 1 a b = kappa ∧
      ∀ d : ℕ, 0 < d → ∀ x y : ℝ, 0 < x → 0 < y → kappa ≤ K d x y :=
  positiveScale_minimum verifiedQuadratureBounds

end Shellsort.F09

