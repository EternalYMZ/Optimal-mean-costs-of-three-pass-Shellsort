import Shellsort.F09CertificateModes
import Shellsort.F09CertificateSinTable
import Shellsort.F09CertificateEvaluatorNat
import Shellsort.F09CertificateHeat

/-! Certified finite Fourier evaluation at the rational quadrature nodes. -/
namespace Shellsort.F09.Quad
open Real Set Shellsort.F09.Eval
open scoped BigOperators

def piLo : ℚ := 314159265358979323846/100000000000000000000
def piHi : ℚ := 314159265358979323847/100000000000000000000
theorem pi_lower : (piLo:ℝ) ≤ Real.pi := by
  norm_num [piLo]; linarith [Real.pi_gt_d20]
theorem pi_upper : Real.pi ≤ (piHi:ℝ) := by
  norm_num [piHi]; linarith [Real.pi_lt_d20]

def span (A B : Box) : Box := ⟨A.lo,B.hi⟩

private theorem span_covers (A B : Box) {a b x : ℝ} (al : Covers A a) (bu : Covers B b)
    (h1 : a ≤ x) (h2 : x ≤ b) : Covers (span A B) x :=
  ⟨al.1.trans h1,h2.trans bu.2⟩

def baseExp (δ : ℚ) : Box := span (expNeg (4*piHi^2*δ)) (expNeg (4*piLo^2*δ))

attribute [local irreducible] expNeg

set_option maxHeartbeats 1500000 in
theorem baseExp_covers {δ : ℚ} (hd : 0 ≤ δ) : Covers (baseExp δ) (Real.exp (-4*Real.pi^2*(δ:ℝ))) := by
  have dr : 0 ≤ (δ:ℝ) := by exact_mod_cast hd
  apply span_covers _ _ (expNeg_covers (q:=4*piHi^2*δ) (by positivity))
    (expNeg_covers (q:=4*piLo^2*δ) (by positivity))
  · apply Real.exp_le_exp.mpr
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ Real.pi_pos.le pi_upper 2) dr]
  · apply Real.exp_le_exp.mpr
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num [piLo] : 0 ≤ (piLo:ℝ)) pi_lower 2) dr]

private theorem lower_div (m d : ℕ) (hd : 0 < d) : ((m/d:ℕ):ℝ) ≤ (m:ℝ)/d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast Nat.div_mul_le_self m d

private theorem upper_div (m d : ℕ) (hd : 0 < d) : (m:ℝ)/d ≤ ((m/d+1:ℕ):ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  have h := Nat.mod_add_div m d
  have l := Nat.mod_lt m hd
  exact_mod_cast (show m ≤ (m/d+1)*d by rw [Nat.add_mul,one_mul,Nat.mul_comm (m/d) d]; omega)

def coeff (b : Box) (k : ℕ) : Box := powBox b ((k+1)^2)

theorem coeff_covers {δ : ℚ} (hd : 0 ≤ δ) (k : ℕ) :
    Covers (coeff (baseExp δ) k) (Real.exp (-4*Real.pi^2*((k:ℝ)+1)^2*(δ:ℝ))) := by
  have e := powBox_covers (baseExp_covers hd) ((k+1)^2)
  rw [← Real.exp_nat_mul] at e
  convert e using 2
  congr 1
  push_cast
  ring

def modeFrom (e : Box) (u k : ℕ) : Box :=
  let v := prod e (SinTable.lookup ((k+1)*u))
  ⟨v.lo / (k+1)^2, v.hi/(k+1)^2+1⟩

def modeBox (b : Box) (u k : ℕ) := modeFrom (coeff b k) u k

theorem modeBox_covers {δ : ℚ} (hd : 0 ≤ δ) (u k : ℕ) :
    Covers (modeBox (baseExp δ) u k) (mode k δ ((u:ℝ)/65536)) := by
  have b := prod_covers (coeff_covers hd k) (SinTable.lookup_covers ((k+1)*u))
  have eq : Real.pi*((k+1)*u:ℕ)/65536=Real.pi*((k:ℝ)+1)*((u:ℝ)/65536) := by push_cast; ring
  rw [eq] at b
  let c := prod (coeff (baseExp δ) k) (SinTable.lookup ((k+1)*u))
  have bounds := (covers_iff c _).mp b
  apply (covers_iff ..).mpr
  unfold mode
  constructor
  · apply (lower_div c.lo ((k+1)^2) (by positivity)).trans
    push_cast
    rw [div_le_iff₀ (by positivity)]
    convert bounds.1 using 1
    field_simp
  · apply le_trans _ (upper_div c.hi ((k+1)^2) (by positivity))
    push_cast
    rw [le_div_iff₀ (by positivity)]
    convert bounds.2 using 1
    field_simp

/-- A short list of Fourier cutoffs is sufficient for all eligible heat nodes. -/
def cutoff (δ : ℚ) : ℕ :=
  if 59 ≤ 36*δ*3^2 then 2 else if 59 ≤ 36*δ*5^2 then 4 else
  if 59 ≤ 36*δ*9^2 then 8 else if 59 ≤ 36*δ*17^2 then 16 else
  if 59 ≤ 36*δ*33^2 then 32 else if 59 ≤ 36*δ*65^2 then 64 else 128

theorem cutoff_spec {δ : ℚ} (hd : 1/10000 ≤ δ) :
    (59:ℝ) ≤ 36*(δ:ℝ)*((cutoff δ:ℝ)+1)^2 := by
  have rr : (59:ℚ) ≤ 36*δ*((cutoff δ:ℚ)+1)^2 := by
    unfold cutoff
    split_ifs <;> norm_num at * <;> linarith
  exact_mod_cast rr

def addBox (A B : Box) : Box := ⟨A.lo+B.lo,A.hi+B.hi⟩
def zeroBox : Box := ⟨0,0⟩

private theorem add_covers {A B : Box} {x y : ℝ} (hA : Covers A x) (hB : Covers B y) :
    Covers (addBox A B) (x+y) := by
  obtain ⟨al,au⟩ := (covers_iff ..).mp hA
  obtain ⟨bl,bu⟩ := (covers_iff ..).mp hB
  apply (covers_iff ..).mpr
  simp only [addBox,Nat.cast_add,add_mul]
  exact ⟨add_le_add al bl,add_le_add au bu⟩

def sumBox (f : ℕ → Box) : ℕ → Box
  | 0 => zeroBox
  | n+1 => addBox (sumBox f n) (f n)

theorem sumBox_covers {f : ℕ → Box} {g : ℕ → ℝ} (h : ∀ i, Covers (f i) (g i)) (n : ℕ) :
    Covers (sumBox f n) (∑ k ∈ Finset.range n, g k) := by
  induction n with
  | zero => simp [sumBox,zeroBox,Covers,loQ,hiQ]
  | succ n ih => simpa only [sumBox,Finset.sum_range_succ] using add_covers ih (h n)

def varianceFrom (δ X : ℚ) (sum : Box) : Box :=
  let w := X*(1-X)
  pack (w-2/piLo^2*hiQ sum-1/2^59) (w-2/piHi^2*loQ sum)

def seedNode (δ X : ℚ) : Box :=
  let w := X*(1-X)
  let sq := root (pack δ δ)
  let piRt := root (pack piLo piHi)
  pack 0 (min w (2*hiQ sq/loQ piRt))

private theorem root_pi_pos : (0:ℝ) < (loQ (root (pack piLo piHi)):ℝ) := by
  exact_mod_cast (show (0:ℚ) < loQ (root (pack piLo piHi)) by decide +kernel)

theorem seedNode_covers {δ X : ℚ} (hd : 0 ≤ δ) (hx : (X:ℝ) ∈ Icc 0 1) :
    Covers (seedNode δ X) (V δ X) := by
  have dr : 0 ≤ (δ:ℝ) := by exact_mod_cast hd
  have hrt := root_covers (pack_covers (l:=δ) (u:=δ) dr le_rfl le_rfl)
  have hpi := root_covers (pack_covers Real.pi_pos.le pi_lower pi_upper)
  apply pack_covers (V_nonneg dr hx) (by simpa using V_nonneg dr hx)
  push_cast
  apply le_min
  · have := V_truncated_upper dr (X:ℝ) 0
    simpa [v] using this
  · apply (V_gaussian_upper dr hx).trans
    exact div_le_div₀ (mul_nonneg (by norm_num) ((Real.sqrt_nonneg _).trans hrt.2))
      (by linarith only [hrt.2]) root_pi_pos hpi.1

theorem varianceFrom_covers {δ X : ℚ} (hd : 1/10000 ≤ δ) (hx : (X:ℝ) ∈ Icc 0 1)
    {sum : Box} (valid : Covers sum (∑ k ∈ Finset.range (cutoff δ),mode k δ X)) :
    Covers (varianceFrom δ X sum) (V δ X) := by
  have dr : 0 ≤ (δ:ℝ) := by exact_mod_cast (show 0 ≤ δ by linarith)
  have low := V_truncated_lower dr (X:ℝ) (cutoff δ) (cutoff_spec hd)
  have up := V_truncated_upper dr (X:ℝ) (cutoff δ)
  have pl : 0 < (piLo:ℝ) := by norm_num [piLo]
  have ph : 0 < (piHi:ℝ) := Real.pi_pos.trans_le pi_upper
  have loNonneg : 0 ≤ (loQ sum:ℝ) := by unfold loQ; positivity
  have sumNonneg := loNonneg.trans valid.1
  have left : 2/Real.pi^2 ≤ 2/(piLo:ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos pl) (pow_le_pow_left₀ pl.le pi_lower 2)
  have right : 2/(piHi:ℝ)^2 ≤ 2/Real.pi^2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos Real.pi_pos) (pow_le_pow_left₀ Real.pi_pos.le pi_upper 2)
  apply pack_covers (V_nonneg dr hx)
  · push_cast
    apply le_trans _ low
    unfold v
    linarith only [mul_le_mul left valid.2 sumNonneg (by positivity : 0 ≤ 2/(piLo:ℝ)^2)]
  · push_cast
    apply up.trans
    unfold v
    linarith only [mul_le_mul right valid.1 loNonneg (by positivity : 0 ≤ 2/Real.pi^2)]

def node (δ : ℚ) (u : ℕ) : Box :=
  let X := (u:ℚ)/65536
  if δ < 1/10000 then seedNode δ X else
    varianceFrom δ X (sumBox (modeBox (baseExp δ) u) (cutoff δ))

def bank (e : Box) (n : ℕ) := Array.ofFn (fun k : Fin n => coeff e k)

/-- The column uses the same exponent coefficients for every spatial node. -/
def nodeFrom (δ : ℚ) (u : ℕ) (es : Array Box) : Box :=
  let x := (u:ℚ)/65536
  if δ < 1/10000 then seedNode δ x else
    varianceFrom δ x (sumBox (fun k => modeFrom (es[k]?.getD zeroBox) u k) (cutoff δ))

private theorem sumBox_congr (n : ℕ) (f g : ℕ → Box) (h : ∀ k < n, f k = g k) :
    sumBox f n = sumBox g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBox,sumBox,ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),h n (Nat.lt_succ_self n)]

theorem node_cached (δ : ℚ) (u : ℕ) :
    node δ u = nodeFrom δ u (bank (baseExp δ) (cutoff δ)) := by
  unfold node nodeFrom
  split
  · rfl
  · apply congrArg (varianceFrom δ ((u:ℚ)/65536))
    apply sumBox_congr
    intro k hk
    simp [bank,hk,modeBox]

theorem node_root_covers {δ : ℚ} (hd : 0 ≤ δ) (u : ℕ) (hu : u ≤ 65536) :
    Covers (root (node δ u)) (Real.sqrt (V δ ((u:ℝ)/65536))) := by
  apply root_covers
  have hx : (((u:ℚ)/65536:ℚ):ℝ) ∈ Icc 0 1 := by
    push_cast
    have h : (u:ℝ) ≤ 65536 := by exact_mod_cast hu
    exact ⟨by positivity,by linarith⟩
  unfold node
  split
  · simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using seedNode_covers hd hx
  · rename_i h
    have valid := sumBox_covers (modeBox_covers hd u) (cutoff δ)
    have v' : Covers (sumBox (modeBox (baseExp δ) u) (cutoff δ))
        (∑ k ∈ Finset.range (cutoff δ),mode k δ (((u:ℚ)/65536:ℚ):ℝ)) := by
      simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using valid
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using varianceFrom_covers (le_of_not_gt h) hx v'

end Shellsort.F09.Quad

