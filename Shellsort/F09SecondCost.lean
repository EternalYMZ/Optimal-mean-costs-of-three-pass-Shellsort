import Shellsort.F09SecondAverage
import Shellsort.F09SecondWindow

noncomputable section
namespace Shellsort.F09Second
open Finset

private theorem slot_sums (n h g r y z : ℕ) (cap : r+h*y ≤ n) :
    (∑ j : Fin n, slotReward h g r j.val y z) = (windowSlots h g (r+h*y) z).card ∧
    (∑ j : Fin n, if j.val%h=r then 0 else slotReward h g r j.val y z) =
      (otherWindow h g r (r+h*y) z).card := by
  let pos := r+h*y
  let Q (j : ℕ) := j<pos ∧ j%g=pos%g ∧ z ≤ j/h
  have card₁ : (range n).filter Q = windowSlots h g pos z := by
    ext j; simp only [windowSlots, mem_filter, mem_range, Q]; omega
  have card₂ : (range n).filter (fun j => Q j ∧ j%h≠r) = otherWindow h g r pos z := by
    ext j; simp only [otherWindow, windowSlots, mem_filter, mem_range, Q]; omega
  constructor
  · change (∑ j : Fin n, if Q j.val then (1:ℝ) else 0) = _
    rw [Fin.sum_univ_eq_sum_range (fun j => if Q j then (1:ℝ) else 0), sum_boole, card₁]
  · have eqv (j : Fin n) : (if j.val%h=r then 0 else slotReward h g r j.val y z) =
        (if Q j.val ∧ j.val%h≠r then (1:ℝ) else 0) := by
      unfold slotReward; dsimp [Q,pos]; split_ifs <;> grind
    simp_rw [eqv]
    rw [Fin.sum_univ_eq_sum_range (fun j => if Q j ∧ j%h≠r then (1:ℝ) else 0), sum_boole, card₂]

private theorem nonowner_bounds (n h g r y : ℕ) (t : ℝ) (hh : 0<h) (hg : 0<g)
    (hr : r<h) (cap : r+h*y ≤ n) (ht : 0≤t ∧ t≤1) :
    let H := (h:ℝ)/g
    (H-1)*positiveCount (n/h) t y-H-1 ≤ nonownerMean n h g r y t ∧
    nonownerMean n h g r y t ≤ H*positiveCount (n/h) t y+H := by
  let H := (h:ℝ)/g
  have window := common_count_window n h g r y t ht
  have lo := countAverage_mono (n:=n/h) ht (f:=fun z => (H-1)*((y-z:ℕ):ℝ)+(-H-1))
    (g:=fun z => ∑ j : Fin n, if j.val%h=r then 0 else slotReward h g r j.val y (z+1))
    (fun z => by rw [(slot_sums _ _ _ _ _ _ cap).2]; linarith only [(window_bounds h g r y z hh hg hr).2])
  have hi := countAverage_mono (n:=n/h) ht (f:=fun z => ∑ j : Fin n, slotReward h g r j.val y z)
    (g:=fun z => H*((y-z:ℕ):ℝ)+H)
    (fun z => by rw [(slot_sums _ _ _ _ _ _ cap).1]; exact (window_bounds h g r y z hh hg hr).1)
  have lower := lo.trans window.1
  have upper := window.2.trans hi
  unfold countAverage at lower upper
  rw [mean_affine _ _ (bernoulliVectorWeight_sum _ _)] at lower upper
  change (H-1)*positiveCount (n/h) t y+(-H-1) ≤ _ at lower
  exact ⟨by linarith only [lower], upper⟩

theorem tagSourceMean_bounds (n h g : ℕ) (hh : 0<h) (hg : 0<g) (gh : g≤h)
    (i : Fin n) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let H := (h:ℝ)/g
    (H-1)*(countDifference (n/h) (n/h) t/2)-2*H ≤ tagSourceMean n h g hh i t ∧
      tagSourceMean n h g hh i t ≤ H*(countDifference (n/h) (n/h) t/2)+2*H := by
  let H := (h:ℝ)/g
  let coord := positionChainEquiv n h hh i
  let Y := ownerBitCount coord.2
  let w := sourceCoordinateWeight h (n/h) (n%h) t coord.1
  let F := positiveCount (n/h) t
  have normalized : ∑ z, w z = 1 := sourceCoordinateWeight_sum _ _ _ _ _
  have nonneg := sourceCoordinateWeight_nonneg h (n/h) (n%h) t ht coord.1
  have cond z := nonowner_bounds n h g coord.1.val (Y z) t hh hg coord.1.isLt
    (actual_chain_prefix_lt n h hh coord.1 ⟨Y z,(owner_bit_bounds coord.2 z).2.2⟩).le ht
  have lower := mean_mono' nonneg (f:=fun z => (H-1)*F (Y z)+(-H-1))
    (g:=fun z => nonownerMean n h g coord.1.val (Y z) t) (fun z => by
      have ll : (H-1)*F (Y z)-H-1 ≤ _ := (cond z).1
      linarith only [ll])
  have upper := mean_mono' nonneg (fun z => (cond z).2)
  rw [mean_affine _ _ normalized] at lower upper
  let P := countDifference (n/h) (n/h) t/2
  have own := owner_positiveCount_bounds h (n/h) (n%h) coord.1 coord.2 t ht
  change P-1 ≤ mean w (fun z => F (Y z)) ∧ mean w (fun z => F (Y z)) ≤ P+1 at own
  change _ ≤ tagSourceMean n h g hh i t at lower
  change tagSourceMean n h g hh i t ≤ H*mean w (fun z => F (Y z))+H at upper
  change (H-1)*P-2*H ≤ _ ∧ _ ≤ H*P+2*H
  have ge : 1 ≤ H := (one_le_div (by exact_mod_cast hg)).mpr (by exact_mod_cast gh)
  constructor
  · linarith only [lower, mul_le_mul_of_nonneg_left own.1 (sub_nonneg.mpr ge)]
  · linarith only [upper, mul_le_mul_of_nonneg_left own.2 (by linarith : 0 ≤ H)]

end Shellsort.F09Second
