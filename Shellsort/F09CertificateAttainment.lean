import Shellsort.F09CertificateCover
import Mathlib.Analysis.Convex.Continuous

/-! Attainment and divisor selection for the unbounded positive scale domain. -/
noncomputable section
namespace Shellsort.F09
open Set Real

theorem H_continuousOn : ContinuousOn H (Ioi 0) := by
  have hc : ContinuousOn J (Ioi 0) := by simpa only [interior_Ici] using J_concave.continuousOn_interior
  have invsq : ContinuousOn (fun z : ℝ => 1/z^2) (Ioi 0) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun z hz => show z^2 ≠ 0 from
      pow_ne_zero 2 (ne_of_gt (show 0 < z from hz)))
  have jcomp := hc.comp invsq (fun z hz => show 0 < 1/z^2 from by
    have : 0 < z := hz; positivity)
  exact (Real.continuous_sqrt.continuousOn.comp
    (continuousOn_const.div continuousOn_id (fun _ h => ne_of_gt h)) (mapsTo_univ _ _)).add
    (continuousOn_id.mul jcomp)

/-- Only the last sampled lower Fourier ordinate is required for attainment:
it excludes all shapes above ten. -/
theorem H_attained (j10 : (7830839:ℝ)/100000000 ≤ J (1/(10:ℝ)^2)) :
    ∃ z ∈ Icc (1/2:ℝ) 10, H z = kappa ∧ ∀ w : ℝ, 0 < w → H z ≤ H w := by
  have outer {z : ℝ} (hz : 0 < z) (hout : z ∉ Icc (1/2:ℝ) 10) : 617/1000 ≤ H z := by
    by_cases low : z ≤ 1/2
    · linarith only [H_small hz low]
    have hi : 10 ≤ z := by by_contra! bad; exact hout ⟨le_of_not_ge low,bad.le⟩
    have tm := shape_J_monotone (show (10:ℝ) ∈ Ioi 0 by norm_num) hz hi
    change 10*J (1/(10:ℝ)^2) ≤ z*J (1/z^2) at tm
    unfold H
    linarith only [j10,tm,Real.sqrt_nonneg (c/z)]
  have hne : (H '' Ioi 0).Nonempty := ⟨H 1,1,by change (0:ℝ)<1; norm_num,rfl⟩
  obtain ⟨_,⟨w,hw,rfl⟩,wlt⟩ := exists_lt_of_csInf_lt hne kappa_lt_617
  have win : w ∈ Icc (1/2:ℝ) 10 := by by_contra bad; exact (not_le.mpr wlt) (outer hw bad)
  have sub : Icc (1/2:ℝ) 10 ⊆ Ioi 0 := fun z hz => show 0 < z by linarith only [hz.1]
  obtain ⟨z,hz,hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num : (1/2:ℝ) ≤ 10))
    (H_continuousOn.mono sub)
  have all (a : ℝ) (ha : 0 < a) : H z ≤ H a := by
    by_cases inside : a ∈ Icc (1/2:ℝ) 10
    · exact hm inside
    · exact (hm win).trans (wlt.le.trans (outer ha inside))
  have bdd : BddBelow (H '' Ioi 0) := ⟨0,by rintro _ ⟨t,ht,rfl⟩; exact H_nonneg ht⟩
  refine ⟨z,hz,le_antisymm ?_ (csInf_le bdd ⟨z,sub hz,rfl⟩),all⟩
  apply le_csInf hne
  rintro _ ⟨t,ht,rfl⟩
  exact all _ ht

theorem positiveScale_minimum (q : QuadratureBounds) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ K 1 a b = kappa ∧
      ∀ d : ℕ, 0 < d → ∀ x y : ℝ, 0 < x → 0 < y → kappa ≤ K d x y := by
  obtain ⟨z,hz,he,hmin⟩ := H_attained q.j10
  have zp : 0 < z := by linarith only [hz.1]
  obtain ⟨a,b,ha,hb,_,hK⟩ := (K_slice (d:=1) (by decide) zp).1
  rw [reduced_one,he] at hK
  refine ⟨a,b,ha,hb,hK.symm,?_⟩
  intro d hd x y hx hy
  by_cases h1 : d=1
  · subst d
    apply (K_lowerBounds (d:=1) (by decide) _).mpr _ x y hx hy
    intro w hw
    rw [reduced_one,← he]
    exact hmin _ hw
  · have h := K_noncoprime q (by omega : 2 ≤ d) hx hy
    linarith only [h,(kappa_enclosure q).2]

end Shellsort.F09

