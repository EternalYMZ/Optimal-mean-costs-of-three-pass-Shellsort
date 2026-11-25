import Shellsort.ThreePassGapScales
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fintype

/-! A single residue class of a uniformly permuted array gives a lower bound
on the executed three-pass mean at the reduced coprime gaps. -/
noncomputable section
namespace Shellsort
namespace F09
open scoped BigOperators

/-- The first residue class has all the slots divisible by the divisor,
including the last slot when the array length is not a multiple of it. -/
abbrev classSize (n d : ℕ) := sourceTrialLength (n/d) (n%d) 0

def slot (n d : ℕ) (hd : 0 < d) : Fin (classSize n d) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨d*i.val, by simpa using actual_chain_prefix_lt n d hd ⟨0,hd⟩ i⟩)
    (fun _ _ h => Nat.mul_lt_mul_of_pos_left h hd)

@[simp] theorem slot_val (n d : ℕ) (hd : 0 < d) (i : Fin (classSize n d)) :
    (slot n d hd i).val = d*i.val := rfl

private theorem slot_exists {n d : ℕ} (hd : 0 < d) (x : Fin n) (hx : x.val % d = 0) :
    ∃ i, slot n d hd i = x := by
  refine ⟨⟨x.val/d, ?_⟩, Fin.ext ?_⟩
  · simpa [classSize, hx] using actual_chain_quotient_lt hd x
  · simpa [slot_val, hx] using Nat.mod_add_div x.val d

/-- Sort the distinct ranks occupying the selected slots to recover the
order embedding from local ranks to global ranks. -/
theorem exists_rank_chart {m n : ℕ} (e : Fin m ↪o Fin n) (p : RankPlacement n) :
    ∃ (r : Fin m ↪o Fin n) (q : RankPlacement m), ∀ x, p (r x) = e (q x) := by
  let f : Fin m → Fin n := fun i => p.symm (e i)
  let q := Tuple.sort f
  have inj : Function.Injective (f ∘ q) := (p.symm.injective.comp e.injective).comp q.injective
  let r := OrderEmbedding.ofStrictMono (f ∘ q) ((Tuple.monotone_sort f).strictMono_of_injective inj)
  refine ⟨r,q,?_⟩
  intro x
  exact p.apply_symm_apply _

private theorem mod_scaled {d k a b : ℕ} (hd : 0 < d) :
    d*a % (d*k) = d*b % (d*k) ↔ a % k = b % k := by
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
  exact Nat.mul_right_inj hd.ne'

/-- A scaled pass, restricted to the zero class, has exactly the sorted
placement of the reduced pass, with the original relative rank labels. -/
theorem gapSort_on_class {n d : ℕ} (hd : 0 < d) (k : ℕ)
    (p : RankPlacement n) (r : Fin (classSize n d) ↪o Fin n)
    (q : RankPlacement (classSize n d))
    (chart : ∀ x, p (r x) = slot n d hd (q x)) (x : Fin (classSize n d)) :
    gapSort p (d*k) (r x) = slot n d hd (gapSort q k x) := by
  let e := slot n d hd
  let P := gapSort p (d*k)
  have pos (y : Fin (classSize n d)) : (P (r y)).val % d = 0 := by
    have h := congrArg (fun z : ℕ => z % d) (gapSort_preserves_residue p (d*k) (r y))
    simpa [P, Nat.mod_mod_of_dvd _ (dvd_mul_right d k), chart, slot_val] using h
  choose u hu using fun y => slot_exists hd (P (r y)) (pos y)
  have ui : Function.Injective u := fun i j h => r.injective (P.injective
    ((hu i).symm.trans ((congrArg e h).trans (hu j))))
  let Q : RankPlacement (classSize n d) := Equiv.ofBijective u (Finite.injective_iff_bijective.mp ui)
  have sq (y) : e (Q y) = P (r y) := hu y
  have res (y) : (Q y).val % k = (q y).val % k := by
    apply (mod_scaled hd).mp
    have h := gapSort_preserves_residue p (d*k) (r y)
    rw [chart y, ← sq y] at h
    exact h
  have good : gapSort q k = Q := gapSort_unique q Q k res (by
    intro i j same
    have h : (P (r i)).val % (d*k) = (P (r j)).val % (d*k) := by
      rw [← sq i, ← sq j]
      exact (mod_scaled hd).mpr ((res i).trans (same.trans (res j).symm))
    calc Q i < Q j ↔ e (Q i) < e (Q j) := e.lt_iff_lt.symm
         _ ↔ P (r i) < P (r j) := by rw [sq,sq]
         _ ↔ r i < r j := gapSort_sorted p (d*k) _ _ h
         _ ↔ i < j := r.lt_iff_lt)
  rw [good]
  exact (sq x).symm


/-- Ordered embeddings carry every reduced inversion to a distinct actual
inversion if the selected chains are contained in physical target chains. -/
theorem gapCost_le_of_chart {m n : ℕ} (e r : Fin m ↪o Fin n)
    (q : RankPlacement m) (p : RankPlacement n) (k K : ℕ) (hk : 0 < k) (hK : 0 < K)
    (chart : ∀ x, p (r x) = e (q x))
    (cong : ∀ i j : Fin m, i.val % k = j.val % k → (e i).val % K = (e j).val % K) :
    gapInsertionCost q k hk ≤ gapInsertionCost p K hK := by
  classical
  simp only [gapInsertionCost_eq_gapInversions, gapInversions]
  apply Finset.card_le_card_of_injOn (fun ij : Fin m × Fin m => (e ij.1, e ij.2))
  · intro ⟨i,j⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, gapPositionPairs, Finset.mem_univ,
      true_and] at h ⊢
    have inv (v) : p.symm (e v) = r (q.symm v) := by
      apply p.injective
      simpa using (chart (q.symm v)).symm
    exact ⟨⟨e.strictMono h.1.1,cong _ _ h.1.2⟩, by rw [inv,inv]; exact r.strictMono h.2⟩
  · intro a _ b _ h
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))

theorem threePassCost_class_le {n d : ℕ} (hd : 0 < d) (h g : ℕ) (hh : 0 < h) (hg : 0 < g)
    (p : RankPlacement n) (r : Fin (classSize n d) ↪o Fin n)
    (q : RankPlacement (classSize n d)) (chart : ∀ x, p (r x) = slot n d hd (q x)) :
    threePassInsertionCost q h g hh hg ≤
      threePassInsertionCost p (d*h) (d*g) (by positivity) (by positivity) := by
  let e := slot n d hd
  have c₁ := gapSort_on_class hd h p r q chart
  have c₂ := gapSort_on_class hd g _ r _ c₁
  unfold threePassInsertionCost
  exact Nat.add_le_add (Nat.add_le_add
    (gapCost_le_of_chart e r q p h (d*h) hh (by positivity) chart
      (fun _ _ hj => (mod_scaled hd).2 hj))
    (gapCost_le_of_chart e r _ _ g (d*g) hg (by positivity) c₁
      (fun _ _ hj => (mod_scaled hd).2 hj)))
    (gapCost_le_of_chart e r _ _ 1 1 (by decide) (by decide) c₂ (fun i j _ => (Nat.mod_one _).trans (Nat.mod_one _).symm))

private theorem average_right_trans {n : ℕ} (v : RankPlacement n) (f : RankPlacement n → ℝ) :
    uniformAverage (fun p => f (p.trans v)) = uniformAverage f := by
  unfold uniformAverage
  exact congrArg (fun x : ℝ => x / n.factorial) (Equiv.sum_comp (Equiv.mulLeft v) f)

private theorem average_left_trans {n : ℕ} (q : RankPlacement n) (f : RankPlacement n → ℝ) :
    uniformAverage (fun v => f (q.trans v)) = uniformAverage f := by
  unfold uniformAverage
  exact congrArg (fun x : ℝ => x / n.factorial) (Equiv.sum_comp (Equiv.mulRight q) f)

private theorem average_swap {n m : ℕ} (f : RankPlacement n → RankPlacement m → ℝ) :
    uniformAverage (fun p => uniformAverage (f p)) =
      uniformAverage (fun q => uniformAverage (fun p => f p q)) := by
  unfold uniformAverage
  simp_rw [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

/-- A real-cost comparison of two uniform means. Permute the chosen slots
independently of the global input. Their relative ranks are uniformly permuted
for each fixed global input, and the full permuted input is still uniform. -/
theorem uniform_threePass_class_le (n d h g : ℕ) (hd : 0 < d) (hh : 0 < h) (hg : 0 < g) :
    uniformAverage (fun q : RankPlacement (classSize n d) =>
      (threePassInsertionCost q h g hh hg : ℝ)) ≤
    uniformAverage (fun p : RankPlacement n =>
      (threePassInsertionCost p (d*h) (d*g) (by positivity) (by positivity) : ℝ)) := by
  classical
  let e := slot n d hd
  let localCost (q : RankPlacement (classSize n d)) : ℝ := threePassInsertionCost q h g hh hg
  let fullCost (p : RankPlacement n) : ℝ :=
    threePassInsertionCost p (d*h) (d*g) (by positivity) (by positivity)
  let mix (p : RankPlacement n) (v : RankPlacement (classSize n d)) :=
    p.trans (v.viaFintypeEmbedding e.toEmbedding)
  have bound (p : RankPlacement n) : uniformAverage localCost ≤
      uniformAverage (fun v => fullCost (mix p v)) := by
    obtain ⟨r,q,chart⟩ := exists_rank_chart e p
    rw [← average_left_trans q localCost]
    apply uniformAverage_mono
    intro v
    apply Nat.cast_le.mpr
    apply threePassCost_class_le hd h g hh hg _ r _
    intro x
    change v.viaFintypeEmbedding e.toEmbedding (p (r x)) = e (v (q x))
    rw [chart]
    exact v.viaFintypeEmbedding_apply_image e.toEmbedding _
  calc uniformAverage localCost = uniformAverage (n := n) (fun _ => uniformAverage localCost) :=
         (uniformAverage_const n _).symm
       _ ≤ uniformAverage (fun p => uniformAverage (fun v => fullCost (mix p v))) :=
         uniformAverage_mono _ _ bound
       _ = uniformAverage fullCost := by
         rw [average_swap]
         change uniformAverage (fun v : RankPlacement (classSize n d) =>
           uniformAverage (fun p => fullCost (p.trans (v.viaFintypeEmbedding e.toEmbedding)))) = _
         simp_rw [average_right_trans]
         exact uniformAverage_const _ _

private theorem size_bounds (n d : ℕ) (hd : 0 < d) :
    n ≤ d * classSize n d ∧ classSize n d ≤ n := by
  have cover := Nat.mod_add_div n d
  have rem := Nat.mod_lt n hd
  have divle := Nat.div_le_self n d
  unfold classSize sourceTrialLength
  split_ifs with hp
  · rw [Nat.mul_add, Nat.mul_one]
    have mulge := Nat.le_mul_of_pos_left (n/d) hd
    omega
  · omega

/-- For any fixed uniform cost budget, all admissible gap pairs have
normalized coordinates in a single compact positive rectangle. This includes
unbounded candidate divisors before the budget is imposed. -/
theorem threePass_budget_rectangle (K : ℝ) (kp : 0 < K) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ n h g : ℕ, ∀ (ln : h < n) (lh : g < h) (lg : 2 ≤ g),
      uniformAverage (fun p : RankPlacement n =>
        (threePassInsertionCost p h g (by omega) (by omega) : ℝ)) ≤ K*n*Real.sqrt n →
      Real.sqrt n ≤ L*h ∧ (h:ℝ) ≤ L*Real.sqrt n ∧
      Real.sqrt (Real.sqrt n) ≤ L*g ∧ (g:ℝ) ≤ L*Real.sqrt (Real.sqrt n) := by
  let D := 1+(2048*K)^2
  have D1 : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg (2048*K)]
  have Dp : 0 < D := by linarith
  let R := K*D^2
  have Rp : 0 < R := by dsimp [R]; positivity
  let U := max (32000*R) ((32000*R)^2)
  have Up : 0 ≤ U := (sq_nonneg _).trans (le_max_right ..)
  let A := 2048*R*U
  let B := Real.sqrt (4*R+1)*U
  let lowG := Real.sqrt (4*K+1)*(2048*K)
  let L := max (max (max 1 (4*K+1)) lowG)
    (max (max D ((2048*K*D)^2)) (max (D*A) (D*B)))
  have L1 : 1 ≤ L := (le_max_left ..).trans ((le_max_left ..).trans (le_max_left ..))
  refine ⟨L,L1,?_⟩
  intro n h g ln lh lg budget
  let d := Nat.gcd h g
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
  have ds : (d:ℝ) ≤ D := by
    by_cases two : 2 ≤ d
    · have root := threePass_common_divisor_budget n h g d ln lh lg two
        (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_right ..) K budget
      have squared := mul_self_le_mul_self (Real.sqrt_nonneg _) root
      dsimp [D]; nlinarith [Real.sq_sqrt (Nat.cast_nonneg d)]
    · have : d = 1 := by omega
      simpa [this] using D1
  have prior := threePass_gap_lower_scales n h g ln lh lg K budget
  have hlow : Real.sqrt n ≤ L*h := prior.1.trans (mul_le_mul_of_nonneg_right
    ((le_max_right ..).trans ((le_max_left ..).trans (le_max_left ..))) (Nat.cast_nonneg _))
  have glow : Real.sqrt (Real.sqrt n) ≤ L*g := by
    have a := Real.sqrt_le_sqrt prior.1
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4*K+1)] at a
    have b := a.trans (mul_le_mul_of_nonneg_left prior.2 (Real.sqrt_nonneg _))
    have c : lowG ≤ L := (le_max_right ..).trans (le_max_left ..)
    exact (by simpa [lowG,mul_assoc] using b : Real.sqrt (Real.sqrt n) ≤ lowG*g) |>.trans
      (mul_le_mul_of_nonneg_right c (Nat.cast_nonneg _))
  have sn : 1 ≤ Real.sqrt (n:ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast (show 1 ≤ n by omega))
  have tn : 1 ≤ Real.sqrt (Real.sqrt (n:ℝ)) := Real.one_le_sqrt.2 sn
  have hm : d*(h/d) = h := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have gm : d*(g/d) = g := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  by_cases gr : 2 ≤ g/d
  · let N := classSize n d
    have sizes : n ≤ d*N ∧ N ≤ n := size_bounds n d hd
    have hN : h/d < N := by
      by_contra! bad
      have := Nat.mul_le_mul_left d bad
      omega
    have hgh : g/d < h/d := by
      apply (Nat.mul_lt_mul_left hd).mp
      simpa only [hm,gm] using lh
    have cop : Nat.Coprime (h/d) (g/d) := Nat.coprime_div_gcd_div_gcd hd
    have nf : (n:ℝ) ≤ D*N := (show (n:ℝ) ≤ d*N by exact_mod_cast sizes.1).trans
      (mul_le_mul_of_nonneg_right ds (Nat.cast_nonneg _))
    have rs : Real.sqrt (n:ℝ) ≤ D*Real.sqrt (N:ℝ) := by
      have b := Real.sqrt_le_sqrt nf
      rw [Real.sqrt_mul Dp.le] at b
      exact b.trans (mul_le_mul_of_nonneg_right ((Real.sqrt_le_left Dp.le).2 (by nlinarith [mul_nonneg Dp.le (sub_nonneg.mpr D1)])) (Real.sqrt_nonneg _))
    have red := uniform_threePass_class_le n d (h/d) (g/d) hd (by omega) (by omega)
    simp only [hm,gm] at red
    have rb : _ ≤ R*N*Real.sqrt N := (red.trans budget).trans (by
      have v := mul_le_mul nf rs (Real.sqrt_nonneg _) (by positivity)
      calc K*n*Real.sqrt n = K*(n*Real.sqrt n) := by ring
           _ ≤ K*((D*N)*(D*Real.sqrt N)) := mul_le_mul_of_nonneg_left v kp.le
           _ = R*N*Real.sqrt N := by dsimp [R]; ring)
    obtain ⟨_,uh,_,ug⟩ := threePass_coprime_gap_scales N (h/d) (g/d) hN hgh gr cop R Rp rb
    have small : (N:ℝ) ≤ n := by exact_mod_cast sizes.2
    have ds0 : 0 ≤ (d:ℝ) := Nat.cast_nonneg _
    have AA : 0 ≤ A := by dsimp [A]; positivity
    have BB : 0 ≤ B := by dsimp [B]; positivity
    have a : ((h/d:ℕ):ℝ) ≤ A*Real.sqrt n := uh.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt small) AA)
    have b : ((g/d:ℕ):ℝ) ≤ B*Real.sqrt (Real.sqrt n) := ug.trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt small)) BB)
    have la : D*A ≤ L := (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
    have lb : D*B ≤ L := (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
    have hr : (h:ℝ) = d*((h/d:ℕ):ℝ) := by exact_mod_cast hm.symm
    have gr' : (g:ℝ) = d*((g/d:ℕ):ℝ) := by exact_mod_cast gm.symm
    refine ⟨hlow,?_,glow,?_⟩
    · rw [hr]
      calc (d:ℝ)*((h/d:ℕ):ℝ) ≤ D*(A*Real.sqrt n) :=
             mul_le_mul ds a (Nat.cast_nonneg _) Dp.le
           _ ≤ L*Real.sqrt n := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right la (Real.sqrt_nonneg _)
    · rw [gr']
      calc (d:ℝ)*((g/d:ℕ):ℝ) ≤ D*(B*Real.sqrt (Real.sqrt n)) :=
             mul_le_mul ds b (Nat.cast_nonneg _) Dp.le
           _ ≤ L*Real.sqrt (Real.sqrt n) := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right lb (Real.sqrt_nonneg _)
  · have gd : g ≤ d := calc g = d*(g/d) := gm.symm
                            _ ≤ d*1 := Nat.mul_le_mul_left d (by omega)
                            _ = d := Nat.mul_one _
    have gD : (g:ℝ) ≤ D := (show (g:ℝ) ≤ d by exact_mod_cast gd).trans ds
    have hs := prior.2.trans (mul_le_mul_of_nonneg_left gD (by positivity : 0 ≤ 2048*K))
    have hh := mul_self_le_mul_self (Real.sqrt_nonneg _) hs
    have capped : (h:ℝ) ≤ (2048*K*D)^2 := by nlinarith only [Real.sq_sqrt (Nat.cast_nonneg h),hh]
    have la : (2048*K*D)^2 ≤ L := (le_max_right ..).trans ((le_max_left ..).trans (le_max_right ..))
    have lb : D ≤ L := (le_max_left ..).trans ((le_max_left ..).trans (le_max_right ..))
    exact ⟨hlow,(capped.trans la).trans (le_mul_of_one_le_right (by linarith) sn),
      glow,(gD.trans lb).trans (le_mul_of_one_le_right (by linarith) tn)⟩
end F09
end Shellsort
end
