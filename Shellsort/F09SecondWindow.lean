import Shellsort.ResidueCount
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat

/-! The common-binomial comparison for the second pass uses one physical
predecessor interval at a time. Counting backwards from its endpoint removes
all but one rounding error, irrespective of the gcd of the two gaps. -/
namespace Shellsort.F09Second
open Finset

def windowSlots (h g pos z : ℕ) : Finset ℕ :=
  (range pos).filter (fun j => j % g = pos % g ∧ z ≤ j/h)

def otherWindow (h g r pos z : ℕ) :=
  (windowSlots h g pos z).filter (fun j => j % h ≠ r)

/-- The predecessors of the pivot are precisely its backward multiples of g
which have not crossed the threshold level hz. -/
theorem window_card (h g pos z : ℕ) (hh : 0 < h) (hg : 0 < g) :
    (windowSlots h g pos z).card = (pos-h*z)/g := by
  let q := (pos-h*z)/g
  have bij : (Icc 1 q).card = (windowSlots h g pos z).card := by
    apply Finset.card_bij (fun k _ => pos-g*k)
    · intro k hk
      obtain ⟨kp,kq⟩ := Finset.mem_Icc.mp hk
      have cap : k*g ≤ pos-h*z := (Nat.le_div_iff_mul_le hg).mp kq
      rw [Nat.mul_comm k g] at cap
      have positive := Nat.mul_pos hg kp
      have le : g*k ≤ pos := by omega
      have sub : pos-(pos-g*k) = g*k := by omega
      simp only [windowSlots,mem_filter,mem_range]
      refine ⟨by omega, (Nat.modEq_iff_dvd' (Nat.sub_le ..)).mpr (by rw [sub]; exact dvd_mul_right ..),?_⟩
      apply (Nat.le_div_iff_mul_le hh).mpr
      rw [Nat.mul_comm z h]
      omega
    · intro k hk l hl eq
      have A := (Nat.le_div_iff_mul_le hg).mp (Finset.mem_Icc.mp hk).2
      have B := (Nat.le_div_iff_mul_le hg).mp (Finset.mem_Icc.mp hl).2
      rw [Nat.mul_comm k g] at A
      rw [Nat.mul_comm l g] at B
      apply Nat.eq_of_mul_eq_mul_left hg
      omega
    · intro j hj
      simp only [windowSlots,mem_filter,mem_range] at hj
      obtain ⟨less,same,ord⟩ := hj
      obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' less.le).mp same
      have ord' := (Nat.le_div_iff_mul_le hh).mp ord
      rw [Nat.mul_comm z h] at ord'
      refine ⟨k,Finset.mem_Icc.mpr ⟨?_,?_⟩,?_⟩
      · by_contra! bad; have : k = 0 := by omega
        simp [this] at hk
        omega
      · apply (Nat.le_div_iff_mul_le hg).mpr
        rw [Nat.mul_comm k g, ← hk]; omega
      · omega
  simpa [q,Nat.card_Icc] using bij.symm

private theorem owner_count (h g r y z : ℕ) (hh : 0 < h) (hr : r < h) :
    (((windowSlots h g (r+h*y) z).filter (fun j => j%h = r)).card) ≤ y-z := by
  let pos := r+h*y
  have le : ((windowSlots h g pos z).filter (fun j => j%h=r)).card ≤ (Ico z y).card := by
    apply Finset.card_le_card_of_injOn (fun j => j/h)
    · intro j hj
      simp only [mem_coe, mem_filter,windowSlots,mem_range] at hj
      change j/h ∈ Ico z y
      apply mem_Ico.mpr
      have reconstruct := Nat.mod_add_div j h
      have strict : h*(j/h) < h*y := by dsimp [pos] at hj; omega
      exact ⟨hj.1.2.2,(Nat.mul_lt_mul_left hh).mp strict⟩
    · intro i hi j hj eq
      simp only [mem_coe,mem_filter] at hi hj
      have a := Nat.mod_add_div i h
      have b := Nat.mod_add_div j h
      change i/h = j/h at eq
      rw [hi.2,eq] at a
      omega
  simpa [pos] using le

theorem window_bounds (h g r y z : ℕ) (hh : 0 < h) (hg : 0 < g) (hr : r < h) :
    ((windowSlots h g (r+h*y) z).card:ℝ) ≤ (h:ℝ)/g*((y-z:ℕ):ℝ)+h/g ∧
    ((h:ℝ)/g-1)*((y-z:ℕ):ℝ)-h/g-1 ≤ (otherWindow h g r (r+h*y) (z+1)).card := by
  let pos := r+h*y
  let W (t : ℕ) := (windowSlots h g pos t).card
  let O := (otherWindow h g r pos (z+1)).card
  have gp : (0:ℝ) < g := by exact_mod_cast hg
  have flo (t) : W t*g ≤ pos-h*t := by
    dsimp [W]; rw [window_card _ _ _ _ hh hg]; exact Nat.div_mul_le_self _ _
  have fhi (t) : pos-h*t < (W t+1)*g := by
    dsimp [W]; rw [window_card _ _ _ _ hh hg]; have decomp := Nat.mod_add_div (pos-h*t) g
    have rem := Nat.mod_lt (pos-h*t) hg
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm ((pos-h*t)/g) g]
    omega
  have A : W z*g ≤ h*(y-z)+h := by
    have c := flo z
    dsimp [pos] at c
    by_cases zy : z ≤ y
    · rw [Nat.mul_sub]; omega
    · have v := Nat.mul_le_mul_left h (show y+1 ≤ z by omega)
      rw [Nat.mul_add,Nat.mul_one] at v
      omega
  have B : h*(y-z) ≤ (W (z+1)+1)*g+h := by
    have c := fhi (z+1)
    dsimp [pos] at c
    rw [Nat.mul_add,Nat.mul_one] at c
    rw [Nat.mul_sub]
    omega
  have rem := owner_count h g r y (z+1) hh hr
  have both := Finset.card_filter_add_card_filter_not (s := windowSlots h g pos (z+1))
    (fun j => j%h=r)
  have lost : W (z+1) ≤ O+(y-z) := by dsimp [O,otherWindow,W,pos] at *; omega
  change (W z:ℝ) ≤ _ ∧ _ ≤ (O:ℝ)
  constructor
  · have a : (W z:ℝ)*g ≤ h*((y-z:ℕ):ℝ)+h := by exact_mod_cast A
    field_simp; linarith
  · have b : (h:ℝ)*((y-z:ℕ):ℝ) ≤ ((W (z+1):ℝ)+1)*g+h := by exact_mod_cast B
    have c : (W (z+1):ℝ)*g ≤ ((O:ℝ)+((y-z:ℕ):ℝ))*g :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast lost) gp.le
    field_simp; nlinarith only [b,c]

end Shellsort.F09Second
