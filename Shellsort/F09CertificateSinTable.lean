import Shellsort.F09CertificateSinTableData

/-! Constant-depth evaluation on the whole grid from two independently
checked small grids, using sine addition in the first quadrant. -/
namespace Shellsort.F09.Eval.SinTable

private theorem widen {a b : Box} {x : ℝ} (h : contains a b = true) (hb : Covers b x) :
    Covers a x := by
  simp only [contains,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨l,u⟩ := (covers_iff ..).1 hb
  exact (covers_iff ..).2 ⟨(by exact_mod_cast h.1 : (a.lo:ℝ) ≤ b.lo).trans l,
    u.trans (by exact_mod_cast h.2)⟩

private noncomputable def angle (m : ℕ) := Real.pi*m/65536

private theorem atom_sound {m : ℕ} {p : ℕ × ℕ} (hm : m ≤ 32768) (ok : valid m p = true) :
    Covers (atom p.1) (Real.sin (angle m)) ∧ Covers (atom p.2) (Real.cos (angle m)) := by
  simp only [valid,Bool.and_eq_true] at ok
  have pos : 0 ≤ angle m := by dsimp [angle]; positivity
  have bound : angle m ≤ Real.pi/2 := by
    have h : (m:ℝ) ≤ 32768 := by exact_mod_cast hm
    dsimp [angle]; nlinarith only [mul_le_mul_of_nonneg_left h Real.pi_pos.le]
  have sn := Real.sin_nonneg_of_nonneg_of_le_pi pos (bound.trans (by linarith [Real.pi_pos]))
  have cn := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) bound
  have eql : angle (32768-m) = Real.pi/2 - angle m := by
    unfold angle; rw [Nat.cast_sub hm]; push_cast; ring
  have sinr := root_covers (sin65536_covers m)
  change Covers _ (Real.sqrt (Real.sin (angle m)^2)) at sinr
  rw [Real.sqrt_sq sn] at sinr
  have cosr := root_covers (sin65536_covers (32768-m))
  change Covers _ (Real.sqrt (Real.sin (angle (32768-m))^2)) at cosr
  rw [eql,Real.sin_pi_div_two_sub,Real.sqrt_sq cn] at cosr
  exact ⟨widen ok.1 sinr,widen ok.2 cosr⟩

private def add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
private theorem add_covers {a b : Box} {x y : ℝ} (h : Covers a x) (k : Covers b y) :
    Covers (add a b) (x+y) := by
  obtain ⟨hl,hu⟩ := (covers_iff ..).1 h
  obtain ⟨kl,ku⟩ := (covers_iff ..).1 k
  apply (covers_iff ..).2
  change ((a.lo+b.lo:ℕ):ℝ) ≤ _ ∧ _ ≤ ((a.hi+b.hi:ℕ):ℝ)
  push_cast; rw [add_mul]; exact ⟨add_le_add hl kl,add_le_add hu ku⟩

private def reflect (u : ℕ) := min (u%65536) (65536-u%65536)

private theorem reflect_spec (u : ℕ) :
    reflect u ≤ 32768 ∧ Real.sin (angle u)^2 = Real.sin (angle (reflect u))^2 := by
  let m := u%65536
  have mlo : m < 65536 := Nat.mod_lt _ (by decide)
  have angle_add : angle u = angle m + (u/65536:ℕ)*Real.pi := by
    have eq : (m:ℝ)+65536*((u/65536:ℕ):ℝ) = u := by exact_mod_cast Nat.mod_add_div u 65536
    unfold angle; linarith only [congrArg (fun x : ℝ => x*Real.pi) eq]
  have sign : ((-1:ℝ)^(u/65536))^2 = 1 := by rw [← pow_mul,Nat.mul_comm _ 2,pow_mul]; norm_num
  rw [angle_add,Real.sin_add_nat_mul_pi,mul_pow,sign,one_mul]
  by_cases h : m ≤ 32768
  · have eq : reflect u = m := min_eq_left (by change m ≤ 65536-m; omega)
    simp [eq,h]
  · have eq : reflect u = 65536-m := min_eq_right (by change 65536-m ≤ m; omega)
    have right : angle (65536-m) = Real.pi-angle m := by
      unfold angle; rw [Nat.cast_sub mlo.le]; push_cast; ring
    rw [eq,right,Real.sin_pi_sub]; exact ⟨by omega,rfl⟩

/-- Three outward integer products suffice after the two small lookups. -/
def lookup (u : ℕ) : Box :=
  let m := reflect u
  let a := coarse (m/256)
  let b := fine (m%256)
  let s := add (prod (atom a.1) (atom b.2)) (prod (atom a.2) (atom b.1))
  prod s s

theorem lookup_covers (u : ℕ) : Covers (lookup u) (Real.sin (Real.pi*u/65536)^2) := by
  obtain ⟨hm,hs⟩ := reflect_spec u
  let m := reflect u
  let a := m/256
  let b := m%256
  have amax : a < 129 := by change m/256 < 129; change m ≤ 32768 at hm; omega
  have bmax : b < 256 := Nat.mod_lt _ (by decide)
  have ha := atom_sound (m:=256*a) (by omega) (coarse_valid ⟨a,amax⟩)
  have hb := atom_sound (m:=b) (by omega) (fine_valid ⟨b,bmax⟩)
  have wave := add_covers (prod_covers ha.1 hb.2) (prod_covers ha.2 hb.1)
  have eq : angle m = angle (256*a)+angle b := by
    have h : (b:ℝ)+256*(a:ℝ) = m := by exact_mod_cast Nat.mod_add_div m 256
    unfold angle; push_cast; linarith only [congrArg (fun x : ℝ => x*Real.pi) h]
  change Covers (lookup u) (Real.sin (angle u)^2)
  rw [hs]
  change Covers _ (Real.sin (angle m)^2)
  rw [eq,Real.sin_add,pow_two]
  exact prod_covers wave wave

end Shellsort.F09.Eval.SinTable
