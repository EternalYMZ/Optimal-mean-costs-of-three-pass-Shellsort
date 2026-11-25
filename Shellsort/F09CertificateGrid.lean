import Shellsort.F09CertificateQuadrature
import Shellsort.F09CertificateNode

/-! Integer-weight form of the 128-cell rules and their real semantics. -/
namespace Shellsort.F09.Quad
open Real Set Shellsort.F09.Eval
open scoped BigOperators
set_option maxRecDepth 4096
attribute [local irreducible] node

def left (i : ℕ) := 2*i^2
def right (i : ℕ) := 2*(i+1)^2
def middle (i : ℕ) := i^2+(i+1)^2

def weighted (u : Bool) (f : ℕ → ℕ) : ℕ := ∑ i ∈ Finset.range 128,
  (2*i+1)*(if u then 2*f (middle i) else f (left i)+f (right i))

noncomputable def weightedReal (u : Bool) (f : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range 128,
  (2*(i:ℝ)+1)*(if u then 2*f (middle i) else f (left i)+f (right i))

private theorem cast_weighted (u : Bool) (f : ℕ → ℕ) :
    (weighted u f:ℝ) = weightedReal u (fun k => (f k:ℝ)) := by
  unfold weighted weightedReal
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases u <;> simp

private theorem weighted_smul (u : Bool) (s : ℝ) (f : ℕ → ℝ) :
    weightedReal u (fun i => s*f i) = s*weightedReal u f := by
  unfold weightedReal; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; cases u <;> simp <;> ring

private theorem weighted_mono (u : Bool) {f g : ℕ → ℝ} (h : ∀ k ≤ 65536, f k ≤ g k) :
    weightedReal u f ≤ weightedReal u g := by
  apply Finset.sum_le_sum
  intro i hi
  have rr : i+1 ≤ 128 := by exact Finset.mem_range.mp hi
  have r2 : (i+1)^2 ≤ 128^2 := by gcongr
  have l2 : i^2 ≤ 128^2 := by gcongr; omega
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  cases u
  · exact add_le_add (h _ (by unfold left; omega)) (h _ (by unfold right; omega))
  · exact mul_le_mul_of_nonneg_left (h _ (by unfold middle; omega)) (by norm_num)

private theorem rule_as_weighted (u : Bool) (f : ℝ → ℝ) :
    quadRule u 128 f = weightedReal u (fun k => f ((k:ℝ)/65536))/65536 := by
  unfold quadRule weightedReal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have a : quadPoint 128 i=(left i:ℝ)/65536 := by unfold quadPoint left; push_cast; ring
  have b : quadPoint 128 (i+1)=(right i:ℝ)/65536 := by unfold quadPoint right; push_cast; ring
  have m : (quadPoint 128 i+quadPoint 128 (i+1))/2=(middle i:ℝ)/65536 := by
    unfold quadPoint middle; push_cast; ring
  have d : quadPoint 128 (i+1)-quadPoint 128 i=(2*(i:ℝ)+1)/32768 := by unfold quadPoint; push_cast; ring
  cases u
  · simp only [Bool.false_eq_true,ite_false,d]
    rw [a,b]; ring
  · simp only [ite_true,d,m]; ring

def delta (lam : ℚ) (t : ℕ) := lam*((t:ℚ)/65536)*(1-(t:ℚ)/65536)

def endpoint (u : Bool) (b : Box) := if u then b.hi else b.lo

private theorem endpoint_bounds {b : Box} {x : ℝ} (h : Covers b x) :
    (endpoint false b:ℝ) ≤ x*S ∧ x*S ≤ (endpoint true b:ℝ) := (covers_iff b x).1 h

def height (u : Bool) (lam : ℚ) (t x : ℕ) : ℕ :=
  endpoint u (root (node (delta lam t) x))

def rowValue (u : Bool) (lam : ℚ) (t : ℕ) := weighted u (height u lam t)
def total (u : Bool) (lam : ℚ) := weighted u (rowValue u lam)

private theorem height_bound {lam : ℚ} (hl : 0 ≤ lam) {t x : ℕ} (ht : t ≤ 65536) (hx : x ≤ 65536) :
    (height false lam t x:ℝ) ≤ profile lam ((t:ℝ)/65536,(x:ℝ)/65536)*S ∧
    profile lam ((t:ℝ)/65536,(x:ℝ)/65536)*S ≤ (height true lam t x:ℝ) := by
  have htr : (t:ℝ) ≤ 65536 := by exact_mod_cast ht
  have htq : (t:ℚ) ≤ 65536 := by exact_mod_cast ht
  have d0 : 0 ≤ delta lam t := by unfold delta; apply mul_nonneg (by positivity) (by linarith)
  unfold height
  apply endpoint_bounds
  have de : (delta lam t:ℝ) = (lam:ℝ)*v ((t:ℝ)/65536) := by unfold delta v; push_cast; ring
  rw [profile_eq (by exact_mod_cast hl) (show (t:ℝ)/65536 ∈ Icc 0 1 from ⟨by positivity,by linarith⟩),← de]
  exact node_root_covers d0 x hx

private noncomputable def doubleReal (u : Bool) (lam : ℚ) :=
  weightedReal u (fun t => weightedReal u (fun x => profile lam ((t:ℝ)/65536,(x:ℝ)/65536)))

private theorem total_lower {lam : ℚ} (hl : 0 ≤ lam) :
    (total false lam:ℝ) ≤ (S:ℝ)*doubleReal false lam := by
  unfold total rowValue doubleReal
  simp_rw [cast_weighted]
  rw [← weighted_smul]
  apply weighted_mono
  intro t ht
  rw [← weighted_smul]
  apply weighted_mono
  intro x hx
  simpa only [mul_comm (S:ℝ)] using (height_bound hl ht hx).1

private theorem total_upper {lam : ℚ} (hl : 0 ≤ lam) :
    (S:ℝ)*doubleReal true lam ≤ (total true lam:ℝ) := by
  unfold total rowValue doubleReal
  simp_rw [cast_weighted]
  rw [← weighted_smul]
  apply weighted_mono
  intro t ht
  rw [← weighted_smul]
  apply weighted_mono
  intro x hx
  simpa only [mul_comm (S:ℝ)] using (height_bound hl ht hx).2

private theorem rule_form (u : Bool) (lam : ℚ) :
    fourierQuadrature u 128 lam =
      (4/Real.sqrt (2*Real.pi))*(doubleReal u lam/65536^2) := by
  unfold fourierQuadrature doubleReal
  simp_rw [rule_as_weighted]
  have e (t : ℕ) : weightedReal u (fun x => profile lam ((t:ℝ)/65536,(x:ℝ)/65536))/65536 =
      (1/65536)*weightedReal u (fun x => profile lam ((t:ℝ)/65536,(x:ℝ)/65536)) := by ring
  simp_rw [e]
  rw [weighted_smul]
  ring

def normalizer (u : Bool) : ℚ :=
  let b := root (pack (2*piLo) (2*piHi))
  if u then 4/loQ b else 4/hiQ b

def bound (u : Bool) (lam : ℚ) : ℚ :=
  normalizer u*(total u lam)/(S*65536^2)

theorem bound_sound {lam : ℚ} (hl : 0 ≤ lam) :
    (bound false lam:ℝ) ≤ J lam ∧ J lam ≤ (bound true lam:ℝ) := by
  have rr := fourierQuadrature_bounds (by exact_mod_cast hl : 0 ≤ (lam:ℝ)) 128 (by decide)
  rw [rule_form,rule_form] at rr
  have norm := root_covers (pack_covers (l:=2*piLo) (u:=2*piHi)
    (by positivity : 0 ≤ 2*Real.pi) (by push_cast; linarith only [pi_lower])
    (by push_cast; linarith only [pi_upper]))
  have hp := Real.sqrt_pos.mpr (by positivity : 0 < 2*Real.pi)
  have hn : 0 < (loQ (root (pack (2*piLo) (2*piHi))):ℝ) := by
    exact_mod_cast (show (0:ℚ) < loQ (root (pack (2*piLo) (2*piHi))) by decide +kernel)
  have sp : (0:ℝ) < S := by exact_mod_cast S_pos
  have l := total_lower hl
  have h := total_upper hl
  have pos (u : Bool) (f : ℕ → ℝ) (p : ∀ k, 0 ≤ f k) : 0 ≤ weightedReal u f := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (by positivity)
    cases u
    · exact add_nonneg (p _) (p _)
    · exact mul_nonneg (by norm_num) (p _)
  have nonneg (u : Bool) : 0 ≤ doubleReal u lam :=
    pos u _ (fun t => pos u _ (fun x => Real.sqrt_nonneg _))
  constructor
  · apply le_trans _ rr.1
    simp only [bound,normalizer,Bool.false_eq_true,ite_false,Rat.cast_div,Rat.cast_mul,
      Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow]
    have c := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hp norm.2
    have d : (total false lam:ℝ)/(S*65536^2) ≤ doubleReal false lam/65536^2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [l]
    convert mul_le_mul c d (by positivity) (by positivity) using 1 <;> ring
  · apply rr.2.trans
    simp only [bound,normalizer,ite_true,Rat.cast_div,Rat.cast_mul,
      Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow]
    have c := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hn norm.1
    have d : doubleReal true lam/65536^2 ≤ (total true lam:ℝ)/(S*65536^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith only [h]
    convert mul_le_mul c d (div_nonneg (nonneg _) (by norm_num)) (by positivity) using 1 <;> ring

end Shellsort.F09.Quad

