import Shellsort.F09CertificateFunctions

/-! Exact elimination of the scale variable in the F09 integral functional. -/
noncomputable section
namespace Shellsort.F09
open Real Set

private def remainder (d : ℕ) (z : ℝ) :=
  z*(J (1/z^2) + ((d:ℝ)-1)*L (1/z^2))/Real.sqrt d

theorem shape_pos {d : ℕ} (hd : 0 < d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < shape d a b := by unfold shape; positivity

private theorem K_eq {d : ℕ} (hd : 0 < d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    K d a b = 1/(4*a) + c*Real.sqrt a/b + remainder d (shape d a b) := by
  have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
  have s : (d:ℝ)^2/(a*b^2) = 1/(shape d a b)^2 := by
    unfold shape
    field_simp
    nlinarith [Real.sq_sqrt ha.le]
  unfold K
  dsimp only
  rw [s]
  unfold remainder
  unfold shape
  ring

private theorem reduced_eq {d : ℕ} (hd : 0 < d) {z : ℝ} (hz : 0 < z) :
    reduced d z = Real.sqrt (c/(d*z)) + remainder d z := by
  have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
  have h : c/((d:ℝ)*z) = (c/z)/d := by ring
  rw [h, Real.sqrt_div (div_nonneg c_pos.le hz.le)]
  unfold reduced H B remainder
  ring

/-- The minimum on each positive shape fiber is attained, for the literal two
integrals in the critical coefficient. -/
theorem K_slice {d : ℕ} (hd : 0 < d) {z : ℝ} (hz : 0 < z) :
    IsLeast {x : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ shape d a b = z ∧ x = K d a b}
      (reduced d z) := by
  have hdr : 0 < (d:ℝ) := by exact_mod_cast hd
  obtain ⟨⟨a,b,ha,hb,hshape,hval⟩, hlow⟩ :=
    Shellsort.critical_variational_slice c d z c_pos hdr hz (remainder d)
  constructor
  · exact ⟨a,b,ha,hb,hshape,by rw [reduced_eq hd hz, K_eq hd ha hb, show shape d a b = z from hshape, hval]⟩
  · rintro x ⟨a,b,ha,hb,hshape,rfl⟩
    rw [reduced_eq hd hz]
    exact hlow ⟨a,b,ha,hb,hshape,by rw [K_eq hd ha hb,hshape]⟩

theorem K_lowerBounds {d : ℕ} (hd : 0 < d) (x : ℝ) :
    (∀ a b : ℝ, 0 < a → 0 < b → x ≤ K d a b) ↔
    (∀ z : ℝ, 0 < z → x ≤ reduced d z) := by
  constructor
  · intro h z hz
    obtain ⟨a,b,ha,hb,_,he⟩ := (K_slice hd hz).1
    rw [he]
    exact h a b ha hb
  · intro h a b ha hb
    have hs := shape_pos hd ha hb
    exact (h _ hs).trans ((K_slice hd hs).2 ⟨a,b,ha,hb,rfl,rfl⟩)

theorem reduced_one (z : ℝ) : reduced 1 z = H z := by simp [reduced]

end Shellsort.F09

