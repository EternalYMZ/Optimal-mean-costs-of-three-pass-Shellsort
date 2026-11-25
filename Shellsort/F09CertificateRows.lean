import Shellsort.F09CertificateGrid

/-! Split the exact integer cubature into independently checked spatial rows. -/
namespace Shellsort.F09.Quad
open Shellsort.F09.Eval
open scoped BigOperators
set_option maxRecDepth 8192

def scoreScale : ℕ := 10^12

def RowCert (u : Bool) (lam : ℚ) (t score : ℕ) : Prop :=
  if u then rowValue u lam t*scoreScale ≤ score*65536*S
  else score*65536*S ≤ rowValue u lam t*scoreScale

def cachedRow (u : Bool) (d : ℚ) (es : Array Box) : ℕ :=
  weighted u (fun x => endpoint u (root (nodeFrom d x es)))

theorem row_cached {d lam : ℚ} {u : Bool} {t : ℕ} {seed : Box} {es : Array Box}
    (hd : delta lam t=d) (he : baseExp d=seed) (hb : bank seed (cutoff d)=es) :
    rowValue u lam t = cachedRow u d es := by
  unfold rowValue height cachedRow
  rw [hd]
  simp_rw [node_cached,he,hb]

def coord (u : Bool) (i : ℕ) := if u then middle i else left i
def scoreTotal (u : Bool) (score : ℕ → ℕ) := ∑ i ∈ Finset.range 128,
  (2*i+1)*(if u then 2*score i else score i + score (i+1))

def approximate (u : Bool) (score : ℕ → ℕ) : ℚ :=
  normalizer u * scoreTotal u score / (scoreScale*65536)

private theorem total_eq (u : Bool) (lam : ℚ) :
    total u lam = scoreTotal u (fun i => rowValue u lam (coord u i)) := by
  unfold total scoreTotal weighted
  apply Finset.sum_congr rfl
  intro i hi
  cases u
  · simp only [coord,Bool.false_eq_true,ite_false,show right i = left (i+1) by rfl]
  · simp only [coord,ite_true]

private theorem scaled_scores {u : Bool} (f g : ℕ → ℕ) (a b : ℕ)
    (h : ∀ i < (if u then 128 else 129), f i*a ≤ g i*b) :
    scoreTotal u f*a ≤ scoreTotal u g*b := by
  unfold scoreTotal
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have h0 := Finset.mem_range.mp hi
  cases u
  · have ha := h i (by simp; omega)
    have hb := h (i+1) (by simp; omega)
    convert Nat.mul_le_mul_left (2*i+1) (add_le_add ha hb) using 1 <;> simp <;> ring
  · have ha := h i h0
    convert Nat.mul_le_mul_left ((2*i+1)*2) ha using 1 <;> simp <;> ring

theorem lower_of_rows {lam target : ℚ} (hl : 0 ≤ lam) (score : ℕ → ℕ)
    (checked : ∀ i < 129, RowCert false lam (left i) (score i))
    (value : target ≤ approximate false score) : (target:ℝ) ≤ J lam := by
  apply le_trans _ (bound_sound hl).1
  apply Rat.cast_le.mpr
  apply value.trans
  have h : scoreTotal false score*(65536*S) ≤ total false lam*scoreScale := by
    rw [total_eq]
    apply scaled_scores
    intro i hi
    have h := checked i hi
    change score i*65536*S ≤ rowValue false lam (left i)*scoreScale at h
    simpa only [Nat.mul_assoc,coord,Bool.false_eq_true,ite_false] using h
  have norm : 0 ≤ normalizer false := by
    change 0 ≤ 4/hiQ _
    apply div_nonneg (by norm_num)
    unfold hiQ; positivity
  have fixed : (0:ℚ) < S := by exact_mod_cast S_pos
  unfold approximate bound
  have hr : (scoreTotal false score:ℚ)*(65536*S) ≤ (total false lam:ℚ)*scoreScale := by exact_mod_cast h
  rw [div_le_div_iff₀ (by norm_num [scoreScale]) (by positivity)]
  convert mul_le_mul_of_nonneg_left hr (mul_nonneg norm (show 0 ≤ (65536:ℚ) by norm_num)) using 1 <;> ring

theorem upper_of_rows {lam target : ℚ} (hl : 0 ≤ lam) (score : ℕ → ℕ)
    (checked : ∀ i < 128, RowCert true lam (middle i) (score i))
    (value : approximate true score ≤ target) : J lam ≤ (target:ℝ) := by
  apply (bound_sound hl).2.trans
  apply Rat.cast_le.mpr
  apply le_trans _ value
  have h : total true lam*scoreScale ≤ scoreTotal true score*(65536*S) := by
    rw [total_eq]
    apply scaled_scores
    intro i hi
    have h := checked i hi
    change rowValue true lam (middle i)*scoreScale ≤ score i*65536*S at h
    simpa only [Nat.mul_assoc,coord,ite_true] using h
  have norm : 0 ≤ normalizer true := by
    change 0 ≤ 4/loQ _
    apply div_nonneg (by norm_num)
    unfold loQ; positivity
  have fixed : (0:ℚ) < S := by exact_mod_cast S_pos
  unfold approximate bound
  have hr : (total true lam:ℚ)*scoreScale ≤ (scoreTotal true score:ℚ)*(65536*S) := by exact_mod_cast h
  rw [div_le_div_iff₀ (by positivity) (by norm_num [scoreScale])]
  convert mul_le_mul_of_nonneg_left hr (mul_nonneg norm (show 0 ≤ (65536:ℚ) by norm_num)) using 1 <;> ring

def cellValue (u : Bool) (d : ℚ) (es : Array Box) (i : ℕ) : ℕ :=
  let h := fun x => endpoint u (root (nodeFrom d x es))
  (2*i+1)*(if u then 2*h (middle i) else h (left i)+h (right i))

def rowChunk (u : Bool) (d : ℚ) (es : Array Box) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 8, cellValue u d es (j*8+i)

theorem cachedRow_chunks (u : Bool) (d : ℚ) (es : Array Box) :
    cachedRow u d es = ∑ j ∈ Finset.range 16, rowChunk u d es j := by
  have H (n : ℕ) : (∑ i ∈ Finset.range (n*8), cellValue u d es i) =
      ∑ j ∈ Finset.range n,rowChunk u d es j := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ (n:=n)]
      rfl
  exact H 16

theorem cachedRow_value (u : Bool) (d : ℚ) (es : Array Box) (vals : Array ℕ)
    (checks : ∀ i : Fin 16, rowChunk u d es i = vals[i.val]?.getD 0) :
    cachedRow u d es = ∑ i ∈ Finset.range 16, vals[i]?.getD 0 := by
  rw [cachedRow_chunks]
  apply Finset.sum_congr rfl
  intro i hi
  exact checks ⟨i,Finset.mem_range.mp hi⟩

end Shellsort.F09.Quad

