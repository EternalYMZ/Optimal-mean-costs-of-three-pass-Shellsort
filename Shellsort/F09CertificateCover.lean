import Shellsort.F09CertificateAnalysis
import Shellsort.F09CertificateReduction
import Shellsort.F09CertificateDivisors
import Shellsort.F09CertificateFourier
import Shellsort.F09CertificateCross

/-! A rational supporting tangent for each Fourier quadrature chord. -/
noncomputable section
namespace Shellsort.F09
open Real Set

private def q : ℝ := 47069813/100000000
private def tangent (A P s t : ℝ) :=
  q*(2/s-t/s^2) + A*(2*s*t-s^2) + P*(3/s^2-2*t/s^3)

private theorem tangent_le {A P s t : ℝ} (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hs : 0 < s) (ht : 0 < t) :
    tangent A P s t ≤ q/t + A*t^2 + P/t^2 := by
  have h1 : 2/s-t/s^2 ≤ 1/t := by
    field_simp
    nlinarith [sq_nonneg (t-s)]
  have h2 : 2*s*t-s^2 ≤ t^2 := by nlinarith [sq_nonneg (t-s)]
  have h3 : 3/s^2-2*t/s^3 ≤ 1/t^2 := by
    field_simp
    nlinarith [mul_nonneg (sq_nonneg (t-s)) (show 0 ≤ 2*t+s by linarith)]
  unfold tangent
  convert add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 (show 0 ≤ q by norm_num [q]))
    (mul_le_mul_of_nonneg_left h2 hA)) (mul_le_mul_of_nonneg_left h3 hP) using 1 <;> ring

private theorem chord_le {lo hi x A P : ℝ} (conc : ConcaveOn ℝ (Ici 0) J)
    (hlo : 0 ≤ lo) (hx : x ∈ Icc lo hi)
    (jlo : A+P*lo ≤ J lo) (jhi : A+P*hi ≤ J hi) : A+P*x ≤ J x := by
  have horder := hx.1.trans hx.2
  rw [← segment_eq_Icc (hx.1.trans hx.2)] at hx
  obtain ⟨a,b,ha,hb,hs,hx⟩ := hx
  have hj := conc.2 (show lo ∈ Ici 0 from hlo)
    (show hi ∈ Ici 0 from hlo.trans horder) ha hb hs
  simp only [smul_eq_mul] at hj hx
  rw [hx] at hj
  have eq : A+P*x = a*(A+P*lo)+b*(A+P*hi) := by
    rw [← hx]; linear_combination -A*hs
  exact eq.le.trans ((add_le_add (mul_le_mul_of_nonneg_left jlo ha)
    (mul_le_mul_of_nonneg_left jhi hb)).trans hj)

private theorem cell {a b jl jr A P l r s target z : ℝ}
    (conc : ConcaveOn ℝ (Ici 0) J) (left : jl ≤ J (1/a^2)) (right : jr ≤ J (1/b^2))
    (hza : a ≤ z) (hzb : z ≤ b)
    (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) (hs : 0 < s)
    (hr : 0 ≤ r) (hl2 : l^2 ≤ a) (hr2 : b ≤ r^2)
    (cl : A+P*(1/a^2) ≤ jl) (cr : A+P*(1/b^2) ≤ jr)
    (tl : target ≤ tangent A P s l) (tr : target ≤ tangent A P s r) : target ≤ H z := by
  have hz := ha.trans_le hza
  have hb := hz.trans_le hzb
  have ht := Real.sqrt_pos.mpr hz
  let t := Real.sqrt z
  have ht2 : t^2 = z := Real.sq_sqrt hz.le
  have htl : l ≤ t := Real.le_sqrt_of_sq_le (hl2.trans hza)
  have htr : t ≤ r := Real.sqrt_le_iff.mpr ⟨hr,hzb.trans hr2⟩
  have ix : 1/z^2 ∈ Icc (1/b^2) (1/a^2) := by
    constructor <;> apply one_div_le_one_div_of_le (by positivity) <;> gcongr
  have ch := chord_le conc (by positivity) ix (cr.trans right) (cl.trans left)
  have th : target ≤ tangent A P s t := by
    let m := -(q/s^2)+2*A*s-2*P/s^3
    have eq (u w : ℝ) : tangent A P s u - tangent A P s w = m*(u-w) := by
      unfold tangent m; ring
    by_cases hm : 0 ≤ m
    · linarith [eq t l,mul_nonneg hm (sub_nonneg.mpr htl)]
    · linarith [eq t r,mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hm) (sub_nonpos.mpr htr)]
  have sq := sqrt_c_bounds.1.le
  have hq : q/t ≤ Real.sqrt c/t := div_le_div_of_nonneg_right sq ht.le
  have hc : z*(A+P*(1/z^2)) = A*t^2+P/t^2 := by rw [ht2]; field_simp
  have hj := mul_le_mul_of_nonneg_left ch hz.le
  rw [hc] at hj
  unfold H
  rw [Real.sqrt_div c_pos.le]
  exact (th.trans (tangent_le hA hP hs ht)).trans (by linarith)

/-- Outward-rounded entries from the archived thirteen two-sided quadratures.
Only the direction used by the proof is required at each knot. -/
structure QuadratureBounds : Prop where
  j1_2 : (15594707/100000000:ℝ) ≤ J (1/(1/2:ℝ)^2)
  j3_4 : (1937887/12500000:ℝ) ≤ J (1/(3/4:ℝ)^2)
  j1 : (7684911/50000000:ℝ) ≤ J (1/(1:ℝ)^2)
  j5_4 : (15183639/100000000:ℝ) ≤ J (1/(5/4:ℝ)^2)
  j11_8 : (7533711/50000000:ℝ) ≤ J (1/(11/8:ℝ)^2)
  j23_16 : (1875377/12500000:ℝ) ≤ J (1/(23/16:ℝ)^2)
  j3_2 : (1866811/12500000:ℝ) ≤ J (1/(3/2:ℝ)^2)
  j7_4 : (14622049/100000000:ℝ) ≤ J (1/(7/4:ℝ)^2)
  j2 : (7134197/50000000:ℝ) ≤ J (1/(2:ℝ)^2)
  j3 : (6400487/50000000:ℝ) ≤ J (1/(3:ℝ)^2)
  j5 : (5309131/50000000:ℝ) ≤ J (1/(5:ℝ)^2)
  j10 : (7830839/100000000:ℝ) ≤ J (1/(10:ℝ)^2)
  witness : J (1/(291/200:ℝ)^2) ≤ (14986499:ℝ)/100000000

private theorem cell_j1_2_j3_4 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (1/2:ℝ) ≤ z) (hr : z ≤ (3/4:ℝ)) : (32989429/50000000:ℝ) ≤ H z := by
  apply cell (A := (15429807/100000000:ℝ)) (P := (5153/12500000:ℝ)) (l := (35355339/50000000:ℝ)) (r := (86602541/100000000:ℝ)) (s := (86602541/100000000:ℝ)) conc h.j1_2 h.j3_4 hl hr <;> norm_num [tangent,q]

private theorem cell_j1_2_j1 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (1/2:ℝ) ≤ z) (hr : z ≤ (1:ℝ)) : (31219817/50000000:ℝ) ≤ H z := by
  apply cell (A := (764743/5000000:ℝ)) (P := (74961/100000000:ℝ)) (l := (35355339/50000000:ℝ)) (r := (1:ℝ)) (s := (1:ℝ)) conc h.j1_2 h.j1 hl hr <;> norm_num [tangent,q]

private theorem cell_j3_4_j1 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (3/4:ℝ) ≤ z) (hr : z ≤ (1:ℝ)) : (31219817/50000000:ℝ) ≤ H z := by
  apply cell (A := (15198469/100000000:ℝ)) (P := (21419/12500000:ℝ)) (l := (4330127/5000000:ℝ)) (r := (1:ℝ)) (s := (1:ℝ)) conc h.j3_4 h.j1 hl hr <;> norm_num [tangent,q]

private theorem cell_j1_j5_4 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (1:ℝ) ≤ z) (hr : z ≤ (5/4:ℝ)) : (61080069/100000000:ℝ) ≤ H z := by
  apply cell (A := (14852647/100000000:ℝ)) (P := (20687/4000000:ℝ)) (l := (1:ℝ)) (r := (111803399/100000000:ℝ)) (s := (111803399/100000000:ℝ)) conc h.j1 h.j5_4 hl hr <;> norm_num [tangent,q]

private theorem cell_j5_4_j11_8 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (5/4:ℝ) ≤ z) (hr : z ≤ (11/8:ℝ)) : (2434359/4000000:ℝ) ≤ H z := by
  apply cell (A := (14514007/100000000:ℝ)) (P := (523149/50000000:ℝ)) (l := (55901699/50000000:ℝ)) (r := (58630197/50000000:ℝ)) (s := (58630197/50000000:ℝ)) conc h.j5_4 h.j11_8 hl hr <;> norm_num [tangent,q]

private theorem cell_j11_8_j23_16 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (11/8:ℝ) ≤ z) (hr : z ≤ (23/16:ℝ)) : (60825771/100000000:ℝ) ≤ H z := by
  apply cell (A := (14310293/100000000:ℝ)) (P := (286289/20000000:ℝ)) (l := (117260393/100000000:ℝ)) (r := (119895789/100000000:ℝ)) (s := (119895789/100000000:ℝ)) conc h.j11_8 h.j23_16 hl hr <;> norm_num [tangent,q]

private theorem cell_j23_16_j3_2 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (23/16:ℝ) ≤ z) (hr : z ≤ (3/2:ℝ)) : (60822153/100000000:ℝ) ≤ H z := by
  apply cell (A := (14163183/100000000:ℝ)) (P := (347087/20000000:ℝ)) (l := (29973947/25000000:ℝ)) (r := (15309311/12500000:ℝ)) (s := (120807587/100000000:ℝ)) conc h.j23_16 h.j3_2 hl hr <;> norm_num [tangent,q]

private theorem cell_j3_2_j7_4 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (3/2:ℝ) ≤ z) (hr : z ≤ (7/4:ℝ)) : (6083219/10000000:ℝ) ≤ H z := by
  apply cell (A := (13756833/100000000:ℝ)) (P := (2649723/100000000:ℝ)) (l := (122474487/100000000:ℝ)) (r := (66143783/50000000:ℝ)) (s := (123139307/100000000:ℝ)) conc h.j3_2 h.j7_4 hl hr <;> norm_num [tangent,q]

private theorem cell_j7_4_j2 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (7/4:ℝ) ≤ z) (hr : z ≤ (2:ℝ)) : (61170019/100000000:ℝ) ≤ H z := by
  apply cell (A := (13113121/100000000:ℝ)) (P := (1155273/25000000:ℝ)) (l := (26457513/20000000:ℝ)) (r := (141421357/100000000:ℝ)) (s := (26457513/20000000:ℝ)) conc h.j7_4 h.j2 hl hr <;> norm_num [tangent,q]

private theorem cell_j2_j3 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (2:ℝ) ≤ z) (hr : z ≤ (3:ℝ)) : (61820171/100000000:ℝ) ≤ H z := by
  apply cell (A := (5813519/50000000:ℝ)) (P := (660339/6250000:ℝ)) (l := (35355339/25000000:ℝ)) (r := (173205081/100000000:ℝ)) (s := (35355339/25000000:ℝ)) conc h.j2 h.j3 hl hr <;> norm_num [tangent,q]

private theorem cell_j3_j5 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (3:ℝ) ≤ z) (hr : z ≤ (5:ℝ)) : (65578689/100000000:ℝ) ≤ H z := by
  apply cell (A := (4695243/50000000:ℝ)) (P := (30694387/100000000:ℝ)) (l := (4330127/2500000:ℝ)) (r := (111803399/50000000:ℝ)) (s := (4330127/2500000:ℝ)) conc h.j3 h.j5 hl hr <;> norm_num [tangent,q]

private theorem cell_j5_j10 (h : QuadratureBounds) (conc : ConcaveOn ℝ (Ici 0) J)
    {z : ℝ} (hl : (5:ℝ) ≤ z) (hr : z ≤ (10:ℝ)) : (7414157/10000000:ℝ) ≤ H z := by
  apply cell (A := (3450849/50000000:ℝ)) (P := (929141/1000000:ℝ)) (l := (223606797/100000000:ℝ)) (r := (316227767/100000000:ℝ)) (s := (223606797/100000000:ℝ)) conc h.j5 h.j10 hl hr <;> norm_num [tangent,q]

/-- The small shape tail uses only nonnegativity of the actual J integral. -/
theorem H_small {z : ℝ} (hz : 0 < z) (hsmall : z ≤ 1/2) : (665:ℝ)/1000 ≤ H z := by
  unfold H
  have hc : (665/1000:ℝ)^2 ≤ c/z := (le_div_iff₀ hz).mpr (by linarith [c_lower])
  exact (Real.le_sqrt_of_sq_le hc).trans (le_add_of_nonneg_right (mul_nonneg hz.le (J_nonneg _)))

/-- Exact rational tangent checks on ten chords cover all positive real shapes. -/
theorem H_lower_sharp (h : QuadratureBounds) {z : ℝ} (hz : 0 < z) :
    (60822153:ℝ)/100000000 ≤ H z := by
  by_cases h0 : z ≤ 1/2
  · linarith [H_small hz h0]
  have left : (1/2:ℝ) ≤ z := le_of_not_ge h0
  by_cases hr0 : z ≤ (1:ℝ)
  · linarith [cell_j1_2_j1 h J_concave left hr0]
  have left : (1:ℝ) ≤ z := le_of_not_ge hr0
  by_cases hr1 : z ≤ (5/4:ℝ)
  · linarith [cell_j1_j5_4 h J_concave left hr1]
  have left : (5/4:ℝ) ≤ z := le_of_not_ge hr1
  by_cases hr2 : z ≤ (11/8:ℝ)
  · linarith [cell_j5_4_j11_8 h J_concave left hr2]
  have left : (11/8:ℝ) ≤ z := le_of_not_ge hr2
  by_cases hr3 : z ≤ (23/16:ℝ)
  · linarith [cell_j11_8_j23_16 h J_concave left hr3]
  have left : (23/16:ℝ) ≤ z := le_of_not_ge hr3
  by_cases hr4 : z ≤ (3/2:ℝ)
  · linarith [cell_j23_16_j3_2 h J_concave left hr4]
  have left : (3/2:ℝ) ≤ z := le_of_not_ge hr4
  by_cases hr5 : z ≤ (7/4:ℝ)
  · linarith [cell_j3_2_j7_4 h J_concave left hr5]
  have left : (7/4:ℝ) ≤ z := le_of_not_ge hr5
  by_cases hr6 : z ≤ (2:ℝ)
  · linarith [cell_j7_4_j2 h J_concave left hr6]
  have left : (2:ℝ) ≤ z := le_of_not_ge hr6
  by_cases hr7 : z ≤ (3:ℝ)
  · linarith [cell_j2_j3 h J_concave left hr7]
  have left : (3:ℝ) ≤ z := le_of_not_ge hr7
  by_cases hr8 : z ≤ (5:ℝ)
  · linarith [cell_j3_j5 h J_concave left hr8]
  have left : (5:ℝ) ≤ z := le_of_not_ge hr8
  by_cases hr9 : z ≤ (10:ℝ)
  · linarith [cell_j5_j10 h J_concave left hr9]
  have left : (10:ℝ) ≤ z := le_of_not_ge hr9
  have tm := shape_J_monotone (show (10:ℝ) ∈ Ioi 0 by norm_num) hz left
  change 10*J (1/(10:ℝ)^2) ≤ z*J (1/z^2) at tm
  unfold H
  linarith only [h.j10,tm,Real.sqrt_nonneg (c/z)]

theorem H_lower (h : QuadratureBounds) {z : ℝ} (hz : 0 < z) :
    (6082215:ℝ)/10000000 ≤ H z := by linarith only [H_lower_sharp h hz]

theorem kappa_lower_sharp (h : QuadratureBounds) : (60822153:ℝ)/100000000 ≤ kappa := by
  apply le_csInf (show (H '' Ioi 0).Nonempty from ⟨H 1,1,by change (0:ℝ)<1; norm_num,rfl⟩)
  rintro _ ⟨z,hz,rfl⟩; exact H_lower_sharp h hz

theorem kappa_enclosure (h : QuadratureBounds) :
    (6082215:ℝ)/10000000 ≤ kappa ∧ kappa < (608275:ℝ)/1000000 := by
  have hne : (H '' Ioi 0).Nonempty := ⟨H 1,⟨1,by change (0:ℝ) < 1; norm_num,rfl⟩⟩
  have lb : ∀ x ∈ H '' Ioi 0, (6082215:ℝ)/10000000 ≤ x := by
    rintro _ ⟨z,hz,rfl⟩; exact H_lower h hz
  refine ⟨le_csInf hne lb, ?_⟩
  apply lt_of_le_of_lt (csInf_le (show BddBelow (H '' Ioi 0) from ⟨_,lb⟩)
    (show H (291/200) ∈ H '' Ioi 0 from ⟨_,by norm_num,rfl⟩))
  have hz : 0 < (291/200:ℝ) := by norm_num
  have s : (12062338:ℝ)/10000000 ≤ Real.sqrt (291/200) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  unfold H
  rw [Real.sqrt_div c_pos.le]
  have hq : Real.sqrt c/Real.sqrt (291/200) < (47069814/100000000:ℝ)/(12062338/10000000) :=
    lt_of_lt_of_le (div_lt_div_of_pos_right sqrt_c_bounds.2 (Real.sqrt_pos.mpr hz))
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) s)
  linarith [h.witness]


private theorem small_pair {z : ℝ} (hz : 0 < z) {m n : ℝ}
    (hH : m ≤ H z) (hB : n ≤ B z)
    (h2 : (61546/100000:ℝ)*(141422/100000) ≤ m+n)
    (h3 : (63674/100000:ℝ)*(173206/100000) ≤ m+2*n) :
    (61546:ℝ)/100000 ≤ reduced 2 z ∧ (63674:ℝ)/100000 ≤ reduced 3 z := by
  have s2 : Real.sqrt 2 ≤ (141422:ℝ)/100000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have s3 : Real.sqrt 3 ≤ (173206:ℝ)/100000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  unfold reduced
  norm_num only [Nat.cast_ofNat,show (2:ℝ)-1 = 1 by norm_num,
    show (3:ℝ)-1 = 2 by norm_num,one_mul]
  constructor <;> rw [le_div_iff₀ (by positivity)] <;> linarith

theorem reduced_two_three (h : QuadratureBounds)
    {z : ℝ} (hz : 0 < z) :
    (61546:ℝ)/100000 ≤ reduced 2 z ∧ (63674:ℝ)/100000 ≤ reduced 3 z := by
  by_cases ha : z ≤ 1/2
  · apply small_pair hz (H_small hz ha) (show 22155/100000 ≤ B z by linarith [c_le_B hz,c_lower])
      <;> norm_num
  have a : 1/2 ≤ z := le_of_not_ge ha
  by_cases hb : z ≤ 3/4
  · apply small_pair hz (cell_j1_2_j3_4 h J_concave a hb)
      (show 22155/100000 ≤ B z by linarith [c_le_B hz,c_lower]) <;> norm_num
  have b : 3/4 ≤ z := le_of_not_ge hb
  by_cases hc : z ≤ 1
  · apply small_pair hz (cell_j3_4_j1 h J_concave b hc)
      (B_three_quarters.trans (B_monotone (by norm_num) hz b)) <;> norm_num
  have d : 1 ≤ z := le_of_not_ge hc
  apply small_pair hz (H_lower h hz)
    (B_one.trans (B_monotone (by norm_num) hz d)) <;> norm_num

/-- Uniform strict separation for the actual two-scale integral at every
positive pair, conditional only on the archived finite J quadrature. -/
theorem K_noncoprime_sharp (h : QuadratureBounds)
    {d : ℕ} (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (61546:ℝ)/100000 ≤ K d a b := by
  apply (K_lowerBounds (by omega : 0 < d) _).mpr _ a b ha hb
  intro z hz
  by_cases h4 : 4 ≤ d
  · have := reduced_from_four h4 hz (by linarith [H_lower h hz])
    linarith
  · have h23 : d = 2 ∨ d = 3 := by omega
    rcases h23 with rfl | rfl
    · exact (reduced_two_three h hz).1
    · linarith only [(reduced_two_three h hz).2]

theorem K_noncoprime (h : QuadratureBounds) {d : ℕ} (hd : 2 ≤ d) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : (61501:ℝ)/100000 ≤ K d a b := by
  linarith only [K_noncoprime_sharp h hd ha hb]

/-- The large-divisor exclusion relative to the actual infimum uses no
numerical quadrature premise. -/
theorem kappa_lt_K_large_divisor {d : ℕ} (hd : 10 ≤ d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    kappa < K d a b := by linarith [kappa_lt_617,K_large_divisor hd ha hb]

end Shellsort.F09

