import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! The integer realization step in the critical three-pass variational problem. -/
namespace Shellsort
open Filter Topology

/-- Every positive pair of normalized gap parameters can be realized at every
sufficiently large array size with any prescribed fixed positive gcd. -/
theorem critical_gap_realization (d : ℕ) (hd : 0 < d) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ h g : ℕ → ℕ, (∀ n, Nat.gcd (h n) (g n) = d) ∧
      (∀ᶠ n in atTop, 2 ≤ g n ∧ g n < h n ∧ h n < n) ∧
      Tendsto (fun n => (h n : ℝ)/Real.sqrt n) atTop (𝓝 a) ∧
      Tendsto (fun n => (g n : ℝ)/Real.sqrt (Real.sqrt n)) atTop (𝓝 b) := by
  let s (n : ℕ) := Real.sqrt (n : ℝ)
  let t (n : ℕ) := Real.sqrt (s n)
  let u (n : ℕ) := ⌊(b/d)*t n⌋₊
  let v (n : ℕ) := ⌊(a/b)*t n⌋₊
  let g (n : ℕ) := d*u n
  let h (n : ℕ) := d*(u n*v n+1)
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  have stop : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have ttop : Tendsto t atTop atTop := Real.tendsto_sqrt_atTop.comp stop
  have ulim : Tendsto (fun n => (u n:ℝ)/t n) atTop (𝓝 (b/d)) :=
    (tendsto_nat_floor_mul_div_atTop (div_pos hb dp).le).comp ttop
  have vlim : Tendsto (fun n => (v n:ℝ)/t n) atTop (𝓝 (a/b)) :=
    (tendsto_nat_floor_mul_div_atTop (div_pos ha hb).le).comp ttop
  have ht (n : ℕ) : t n ^ 2 = s n := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs (n : ℕ) : s n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have slim : Tendsto (fun n => (1:ℝ)/s n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop stop
  have hlim : Tendsto (fun n => (h n : ℝ)/s n) atTop (𝓝 a) := by
    have f := ((ulim.mul vlim).add slim).const_mul (d:ℝ)
    rw [show (d:ℝ)*((b/d)*(a/b)+0) = a by field_simp; ring] at f
    refine f.congr (fun n => ?_)
    simp only [h, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [← ht]
    ring
  have glim : Tendsto (fun n => (g n : ℝ)/t n) atTop (𝓝 b) := by
    have f := ulim.const_mul (d:ℝ)
    rw [show (d:ℝ)*(b/d) = b by field_simp] at f
    refine f.congr fun n => ?_
    simp only [g, Nat.cast_mul]
    ring
  refine ⟨h,g,?_,?_,hlim,glim⟩
  · intro n
    simp [h, g, Nat.gcd_mul_left, Nat.mul_comm (u n) (v n), Nat.gcd_comm]
  · have utop : Tendsto u atTop atTop :=
      tendsto_nat_floor_atTop.comp (ttop.const_mul_atTop (div_pos hb dp))
    have vtop : Tendsto v atTop atTop :=
      tendsto_nat_floor_atTop.comp (ttop.const_mul_atTop (div_pos ha hb))
    have small : Tendsto (fun n => (h n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
      refine (hlim.div_atTop stop).congr fun n => ?_
      rw [← hs n]
      ring
    filter_upwards [utop.eventually_ge_atTop 2, vtop.eventually_ge_atTop 1,
      small.eventually_lt_const (by norm_num : (0:ℝ) < 1), eventually_ge_atTop 1] with n hu hv hratio hn
    have gr : 2 ≤ g n := (Nat.le_mul_of_pos_left (u n) hd) |> hu.trans
    have gh : g n < h n := Nat.mul_lt_mul_of_pos_left
      (by have hbase := Nat.le_mul_of_pos_right (u n) (by omega : 0 < v n); omega) hd
    have nr : (0:ℝ) < n := by exact_mod_cast hn
    have hh : (h n : ℝ) < n := by simpa using (div_lt_iff₀ nr).mp hratio
    exact ⟨gr, gh, by exact_mod_cast hh⟩

/-- At fixed `z = b * sqrt a / d` the rest of the variational formula is
constant. This eliminates the positive variable `a` for every remainder
function, and gives both the lower bound and an attaining pair. -/
theorem critical_variational_slice (c d z : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hz : 0 < z) (R : ℝ → ℝ) :
    IsLeast {x : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b*Real.sqrt a/d = z ∧
      x = 1/(4*a) + c*Real.sqrt a/b + R z} (Real.sqrt (c/(d*z)) + R z) := by
  let r := Real.sqrt (c/(d*z))
  have rp : 0 < r := by dsimp [r]; positivity
  have r2 : r^2*(d*z) = c := (eq_div_iff (by positivity)).mp (Real.sq_sqrt (by positivity))
  have coord {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b*Real.sqrt a/d = z) :
      c*Real.sqrt a/b = r^2*a := by
    apply (div_eq_iff hb.ne').2
    have zcoord := (div_eq_iff hd.ne').mp h
    calc
      c*Real.sqrt a = r^2*(d*z)*Real.sqrt a := by rw [r2]
      _ = r^2*(b*Real.sqrt a)*Real.sqrt a := by rw [zcoord, mul_comm z d]
      _ = r^2*(Real.sqrt a)^2*b := by ring
      _ = _ := by rw [Real.sq_sqrt ha.le]
  constructor
  · let a := 1/(2*r)
    let b := d*z/Real.sqrt a
    have ap : 0 < a := by dsimp [a]; positivity
    have bp : 0 < b := by dsimp [b]; positivity
    have coord' : b*Real.sqrt a/d = z := by dsimp [b]; field_simp
    refine ⟨a, b, ap, bp, coord', ?_⟩
    rw [coord ap bp coord']
    change r + R z = 1/(4*(1/(2*r)))+r^2*(1/(2*r))+R z
    field_simp
    ring
  · rintro x ⟨a,b,ap,bp,coord',rfl⟩
    rw [coord ap bp coord']
    apply add_le_add_left
    change r ≤ 1/(4*a)+r^2*a
    rw [← sub_le_iff_le_add, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2*a*r-1)]

/-- The two-variable and reduced one-variable problems have exactly the
same lower bounds, including when the reduced infimum is not attained. -/
theorem critical_variational_lowerBounds (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (R : ℝ → ℝ) (x : ℝ) :
    (∀ a b : ℝ, 0 < a → 0 < b →
      x ≤ 1/(4*a) + c*Real.sqrt a/b + R (b*Real.sqrt a/d)) ↔
    (∀ z : ℝ, 0 < z → x ≤ Real.sqrt (c/(d*z)) + R z) := by
  constructor
  · intro all z hz
    obtain ⟨a,b,ap,bp,coord,attain⟩ := (critical_variational_slice c d z hc hd hz R).1
    rw [attain, ← coord]
    exact all a b ap bp
  · intro all a b ap bp
    let z := b*Real.sqrt a/d
    have zp : 0 < z := by dsimp [z]; positivity
    exact (all z zp).trans ((critical_variational_slice c d z hc hd zp R).2 ⟨a,b,ap,bp,rfl,rfl⟩)

end Shellsort
