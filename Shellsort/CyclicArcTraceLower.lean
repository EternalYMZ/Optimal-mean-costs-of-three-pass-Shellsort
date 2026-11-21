import Shellsort.CyclicArcTrace
import Shellsort.TruncatedBinomialWindow

noncomputable section
namespace Shellsort

/-- Finite central-threshold lower bound for the sum of all phase variances
of a shifted binomial arc. The scale is uniform over all positive arc widths. -/
theorem canonicalArcTrace_lower (g ell m : ℕ) (t : ℝ) (hg : 0 < g)
    (hell : 0 < ell) (hl : ell < g) (hm : 0 < m) (htl : 1/4 ≤ t) (htu : t ≤ 3/4) :
    min (↑(min ell (g-ell)) : ℝ) (Real.sqrt m)/48 ≤ canonicalArcTrace g ell m t := by
  have hr : 0 < min ell (g-ell) := lt_min hell (by omega)
  obtain ⟨k,hkm,H⟩ := truncated_binomial_window_lower m _ t hm hr htl htu
  exact H.trans (truncated_binomial_le_trace g ell k m t hg hl.le hkm ⟨by linarith,by linarith⟩)

end Shellsort
end
