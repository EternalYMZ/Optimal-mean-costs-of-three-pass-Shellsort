import Shellsort.F09PhaseCost

/-! Exact reduction of physical target-prefix counts to their own common
divisor class, including a pivot and target from different classes. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

private theorem scaled_target_mod (d G z c : ℕ) (_hd : 0 < d) (hG : 0 < G) (hc : c < d) :
    (d*z+c) % (d*G) = d*(z%G) + c := by
  have he : d*(z%G)+c < d*G := by
    have step := Nat.mul_le_mul_left d (show z%G + 1 ≤ G from Nat.mod_lt _ hG)
    rw [Nat.mul_add, Nat.mul_one] at step
    omega
  have hl : c < d*G := by
    have := Nat.mul_le_mul_left d (show 1 ≤ G by omega)
    omega
  rw [Nat.add_mod, Nat.mul_mod_mul_left, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt he]

/-- The exact cross-class zero for a single source; within its own class
the very same sequence of marked positions follows the reduced gaps. -/
theorem sourcePrefixCount_scale_classes (d H G r j c s b : ℕ) (hd : 0 < d) (hG : 0 < G)
    (hr : r < d) (hc : c < d) :
    sourcePrefixCount (d*H) (d*G) (d*j+r) (d*s+c) b =
      if c = r then sourcePrefixCount H G j s b else 0 := by
  have test (v : ℕ) : ((d*s+c)+d*H*v)%(d*G) = d*j+r ↔
      c=r ∧ (s+H*v)%G=j := by
    rw [show (d*s+c)+d*H*v = d*(s+H*v)+c by ring, scaled_target_mod d G _ c hd hG hc]
    constructor
    · intro he
      have rem := congrArg (fun a => a%d) he
      simp only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hr] at rem
      have eq := Nat.add_right_cancel (rem ▸ he)
      exact ⟨rem, Nat.eq_of_mul_eq_mul_left hd eq⟩
    · rintro ⟨rfl, eq⟩; rw [eq]
  by_cases e : c = r
  · subst r
    simp [sourcePrefixCount, test]
  · simp [sourcePrefixCount, test, e]

/-- A full physical target count depends on precisely one divisor class.
The full collection of source lengths b is arbitrary. -/
theorem targetPrefixCount_scale_class (d H G r j : ℕ) (b : ℕ → ℕ)
    (hd : 0 < d) (hG : 0 < G) (hr : r < d) :
    (∑ s ∈ Finset.range (d*H), sourcePrefixCount (d*H) (d*G) (d*j+r) s (b s)) =
      ∑ u ∈ Finset.range H, sourcePrefixCount H G j u (b (d*u+r)) := by
  let f := fun s => sourcePrefixCount (d*H) (d*G) (d*j+r) s (b s)
  let k := fun u => sourcePrefixCount H G j u (b (d*u+r))
  have stripe (u : ℕ) : ∑ c ∈ Finset.range d, f (d*u+c) = k u := by
    calc
      _ = ∑ c ∈ Finset.range d, if c = r then k u else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        dsimp [f,k]
        rw [sourcePrefixCount_scale_classes _ _ _ _ _ _ _ _ hd hG hr (Finset.mem_range.mp hc)]
        split_ifs with e <;> simp_all
      _ = _ := by simp [hr]
  have rows (N : ℕ) : ∑ s ∈ Finset.range (d*N), f s = ∑ u ∈ Finset.range N, k u := by
    induction N with
    | zero => simp
    | succ N ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, stripe, Finset.sum_range_succ]
  exact rows H

/-- Direct comparison of two reduced prefix counts at the true selected
target. Its class is recorded independently of the target r's class. -/
theorem finalPivotPrefixCost_eq_reduced_classes {n : ℕ} (d H G r : ℕ) (hd : 0 < d) (hG : 0 < G)
    (i : Fin n) (B : TaggedSubset i) :
    let h := d*H
    let b := chainLowerCount B.val h
    let s := i.val % h
    let j := (s+h*b s) % (d*G)
    let N := fun a => ∑ u ∈ Finset.range H,
      sourcePrefixCount H G (a/d) u (b (d*u+a%d))
    finalPivotPrefixCost h (d*G) r i B =
      |((N j + if r < j then 1 else 0 : ℕ) : ℝ) - (N r : ℝ)| := by
  let b := chainLowerCount B.val (d*H)
  have target (a : ℕ) : (∑ s ∈ Finset.range (d*H), sourcePrefixCount (d*H) (d*G) a s (b s)) =
      ∑ u ∈ Finset.range H, sourcePrefixCount H G (a/d) u (b (d*u+a%d)) := by
    have eq := targetPrefixCount_scale_class d H G (a%d) (a/d) b hd hG (Nat.mod_lt _ hd)
    have reconstruct : d*(a/d)+a%d = a := by rw [Nat.add_comm, Nat.mod_add_div]
    rwa [reconstruct] at eq
  unfold finalPivotPrefixCost
  dsimp only
  simp only [← show b = chainLowerCount B.val (d*H) from rfl, target]

end Shellsort
end
