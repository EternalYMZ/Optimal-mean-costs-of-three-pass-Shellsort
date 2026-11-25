import Shellsort.F09PhaseCrossCostLimit
import Shellsort.ChainBitCounts
import Shellsort.F09PhaseIntegration

/-! The target phase is chosen by the real, omitted-bit owner. Only its
count field is replaced in the two-class reference law. -/
noncomputable section
namespace Shellsort
open Filter Real Set
open scoped BigOperators Topology

def phasePairPinnedAbs (h g j r m a b : ℕ) (owner : Fin h) (y : ℕ) (t carry : ℝ) :=
  mean (productWeight (phasePairWeight (h:=h) m a b t)) (fun z =>
    |(∑ s : PhasePairSource h, if s = Sum.inl owner then (sourcePrefixCount h g j owner.val y : ℝ)
      else phasePairVisit g j r m a b s (z s)) + carry|)

theorem phase_abs_mean_diff {α : Type*} [Fintype α] (w f z : α → ℝ) (h0 : ∀ x, 0≤w x) :
    |mean w f-mean w z| ≤ mean w (fun x => |f x-z x|) := by
  rw [← mean_sub]; unfold mean
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (le_of_eq (Finset.sum_congr rfl (fun i _ => by rw [abs_mul,abs_of_nonneg (h0 i)])))

theorem phase_one_source_replacement (h g j s x y : ℕ)
    (gp : 0<g) (cop : Nat.Coprime h g) (jr : j<g) :
    |(sourcePrefixCount h g j s y:ℝ)-sourcePrefixCount h g j s x| ≤ 1+|(y:ℝ)-x|/g := by
  have gp' : (0:ℝ)<g := by exact_mod_cast gp
  let D := (sourcePrefixCount h g j s y:ℝ)-sourcePrefixCount h g j s x
  have err := source_prefix_pair_scaled h g j s y x gp cop jr
  change |(g:ℝ)*D-((y:ℝ)-x)|≤g at err
  have tri := abs_add_le ((g:ℝ)*D-((y:ℝ)-x)) ((y:ℝ)-x)
  rw [sub_add_cancel,abs_mul,abs_of_pos gp'] at tri
  have bound : |D| ≤ ((g:ℝ)+|(y:ℝ)-x|)/g := by
    apply (le_div_iff₀ gp').mpr; linarith only [tri,err,mul_comm (g:ℝ) |D|]
  simpa only [add_div,div_self gp'.ne'] using bound

theorem phase_owner_count_decomposition {l : ℕ} (slot : Fin l) (u : Fin l → Bool) :
    bitCount u = ownerBitCount slot u + (if u slot then 1 else 0) := by
  classical
  unfold bitCount ownerBitCount
  have pt (x : Fin l) : (if u x then 1 else 0 : ℕ) =
      (if x ≠ slot ∧ u x = true then 1 else 0) + (if x=slot then (if u slot then 1 else 0) else 0) := by
    by_cases e : x=slot <;> simp [e]
  calc
    _ = ∑ x, ((if x ≠ slot ∧ u x = true then 1 else 0) + (if x=slot then (if u slot then 1 else 0) else 0)) := Finset.sum_congr rfl (fun x _ => pt x)
    _ = _ := by simp [Finset.sum_add_distrib]

private theorem phase_count_abs_center (L : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    mean (bernoulliVectorWeight t L) (fun z => |(bitCount z:ℝ)-(L:ℝ)*t|) ≤ sqrt L := by
  let w := bernoulliVectorWeight t L
  apply absMean_le_of_second w (fun z => (bitCount z:ℝ)-(L:ℝ)*t)
    (bernoulliVectorWeight_nonneg t ht L) (bernoulliVectorWeight_sum t L) _ (sqrt_nonneg _)
  rw [sq_sqrt (Nat.cast_nonneg L)]
  have eq := phase_bitCount_exact_variance L t
  unfold centeredSecond at eq
  rw [phase_bitCount_mean] at eq
  change (∑ z, w z*((bitCount z:ℝ)-(L:ℝ)*t)^2) ≤ L
  change (∑ z, w z*((bitCount z:ℝ)-(L:ℝ)*t)^2) = _ at eq
  rw [eq]
  have v : t*(1-t)≤1 := by nlinarith [sq_nonneg (t-1/2)]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left v (Nat.cast_nonneg (α:=ℝ) L)

/-- Conditional on any chosen owner count, the complete-reference error
depends only on the owner's count deviation and a single source variance. -/
theorem phase_pinned_diff (h g j r m a b : ℕ) (o : Fin h) (y : ℕ) (t carry : ℝ)
    (ht : t ∈ Icc 0 1) (gp : 0<g) (cop : h.Coprime g) (jr : j<g) :
    let L := sourceTrialLength m a o.val
    |phasePairPinnedAbs h g j r m a b o y t carry - phasePairAbs h g j r m a b t carry| ≤
      1 + (|(y:ℝ)-(L:ℝ)*t|+sqrt L)/g := by
  classical
  let L := sourceTrialLength m a o.val
  let p := phasePairWeight (h:=h) m a b t
  let w := productWeight p
  let k : PhasePairSource h := .inl o
  let F := phasePairVisit (h:=h) g j r m a b
  let U : ℝ := sourcePrefixCount h g j o.val y
  let V (z : ∀ s, Fin (phasePairLength m a b s) → Bool) := ∑ s : PhasePairSource h, F s (z s)
  have w0 := productWeight_nonneg p (fun s => bernoulliVectorWeight_nonneg t ht _)
  have w1 := productWeight_sum p (fun s => bernoulliVectorWeight_sum t _)
  let A := |(y:ℝ)-(L:ℝ)*t|
  let C (s : PhasePairSource h) (z : Fin (phasePairLength m a b s) → Bool) := |(bitCount z:ℝ)-(L:ℝ)*t|
  have marginal : mean w (fun z => C k (z k)) ≤ sqrt L :=
    (productWeight_mean_coordinate p C (fun _ => bernoulliVectorWeight_sum t _) k).le.trans
      (phase_count_abs_center L t ht)
  have pt (z : ∀ s : PhasePairSource h, Fin (phasePairLength m a b s) → Bool) :
      abs (abs ((∑ s, if s=k then U else F s (z s))+carry) - abs (V z+carry)) ≤ 1+(A+C k (z k))/g := by
    have add (s : PhasePairSource h) : (if s=k then U else F s (z s)) =
        F s (z s)+(if s=k then U-F k (z k) else 0) := by
      by_cases e : s=k
      · subst s; simp
      · simp [e]
    have eq := Finset.sum_congr (s₁:=Finset.univ) rfl (fun s _ => add s)
    rw [eq,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change abs (abs (V z+(U-F k (z k))+carry) - abs (V z+carry)) ≤ _
    have ident : V z+(U-F k (z k))+carry-(V z+carry) = U-F k (z k) := by ring
    apply (abs_abs_sub_abs_le_abs_sub _ _).trans
    rw [ident]
    apply (phase_one_source_replacement h g j o.val (bitCount (z k)) y gp cop jr).trans
    gcongr
    exact (abs_sub_le (y:ℝ) ((L:ℝ)*t) (bitCount (z k))).trans_eq (by rw [abs_sub_comm ((L:ℝ)*t)])
  have bound := (phase_abs_mean_diff w _ _ w0).trans (phaseMean_mono w w0 pt)
  simp only [mean_add,phaseMean_div,mean_const w w1] at bound
  exact bound.trans (by gcongr)

/-- The complete owner variable is drawn independently for evaluation
of each conditional reference field. The outer true owner bits may select
both targets and the order correction. -/
theorem phase_owner_averaged_error {L : ℕ} (h g m a b : ℕ) (o : Fin h) (slot : Fin L)
    (len : L = sourceTrialLength m a o.val) (j r : (Fin L → Bool) → ℕ)
    (carry : (Fin L → Bool) → ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) (gp : 0<g) (cop : h.Coprime g)
    (jr : ∀ u, j u<g) :
    let w := bernoulliVectorWeight t L
    |mean w (fun u => phasePairPinnedAbs h g (j u) (r u) m a b o (ownerBitCount slot u) t (carry u)) -
      mean w (fun u => phasePairAbs h g (j u) (r u) m a b t (carry u))| ≤ 1 + (1+2*sqrt L)/g := by
  let w := bernoulliVectorWeight t L
  have w0 := bernoulliVectorWeight_nonneg t ht L
  have w1 := bernoulliVectorWeight_sum t L
  have pt (u : Fin L → Bool) :
      |(ownerBitCount slot u:ℝ)-(L:ℝ)*t| ≤ 1+|(bitCount u:ℝ)-(L:ℝ)*t| := by
    have e := phase_owner_count_decomposition slot u
    have r : |(ownerBitCount slot u:ℝ)-(bitCount u:ℝ)| ≤ 1 := by
      cases he : u slot <;> simp only [he,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] at e
      · rw [e]; simp
      · rw [e,Nat.cast_add,Nat.cast_one]; rw [show (ownerBitCount slot u:ℝ)-((ownerBitCount slot u:ℝ)+1) = -1 by ring]; norm_num
    exact (abs_sub_le _ (bitCount u:ℝ) _).trans (add_le_add r le_rfl)
  have on (u : Fin L → Bool) := phase_pinned_diff h g (j u) (r u) m a b o (ownerBitCount slot u) t (carry u) ht gp cop (jr u)
  simp only [←len] at on
  have e := (phase_abs_mean_diff w _ _ w0).trans (phaseMean_mono w w0 on)
  have centered := (phaseMean_mono w w0 pt)
  simp only [mean_add,phaseMean_div,mean_const w w1] at centered e
  have C := phase_count_abs_center L t ht
  change mean w (fun z => |(bitCount z:ℝ)-(L:ℝ)*t|) ≤ sqrt L at C
  apply e.trans; apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg g)
  linarith only [centered,C]

theorem actual_cross_owner_abs_limit {G H m a b L : ℕ → ℕ} (o : ∀ n, Fin (H n)) (slot : ∀ n, Fin (L n))
    (len : ∀ n, L n = sourceTrialLength (m n) (a n) (o n).val)
    (j r : ∀ n, (Fin (L n) → Bool) → ℕ) (carry : ∀ n, (Fin (L n) → Bool) → ℝ)
    {t : ℕ → ℝ} {lam T : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop) (hH : Tendsto (fun n => (H n:ℝ)) atTop atTop)
    (hGH : Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0))
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (ht01 : ∀ n, t n ∈ Icc 0 1)
    (hc : ∀ n, Nat.Coprime (H n) (G n)) (hj : ∀ n z, j n z < G n) (hr : ∀ n z, r n z < G n)
    (hh : ∀ n, 0 < H n) (ha : ∀ n, a n ≤ H n) (hb : ∀ n, b n ≤ H n)
    (near : ∀ n, |(a n:ℝ)-(b n:ℝ)| ≤ 1) (order : ∀ n z, |carry n z| ≤ 1) :
    Tendsto (fun n => mean (bernoulliVectorWeight (t n) (L n)) (fun z =>
      phasePairPinnedAbs (H n) (G n) (j n z) (r n z) (m n) (a n) (b n) (o n)
        (ownerBitCount (slot n) z) (t n) (carry n z))/sqrt (H n)) atTop
      (𝓝 (sqrt (2/π)*sqrt (2*(lam*F09.v T+F09.W (lam*F09.v T))))) := by
  let w n := bernoulliVectorWeight (t n) (L n)
  let raw n z := phasePairPinnedAbs (H n) (G n) (j n z) (r n z) (m n) (a n) (b n) (o n)
    (ownerBitCount (slot n) z) (t n) (carry n z)
  let ref n z := phasePairAbs (H n) (G n) (j n z) (r n z) (m n) (a n) (b n) (t n) (carry n z)
  have refLim := F09.phase_pivot_average_limit w (fun n z => ref n z/sqrt (H n))
    (sqrt (2/π)*sqrt (2*(lam*F09.v T+F09.W (lam*F09.v T))))
    (fun n => bernoulliVectorWeight_nonneg _ (ht01 n) _) (fun n => bernoulliVectorWeight_sum _ _)
    (fun choice => reference_cross_abs_limit hG hH hGH hm ht ht01 hc (fun n => hj n (choice n))
      (fun n => hr n (choice n)) hh ha hb near (fun n => order n (choice n)))
  simp only [phaseMean_div] at refLim
  obtain ⟨K,hK⟩ := (critical_plus_one_source_length hG hm).bddAbove_range
  have bound (n) : 1+(1+2*sqrt (L n))/(G n:ℝ) ≤ 2+2*sqrt K := by
    have gpNat : 0<G n := by have := hj n (fun _ => false); omega
    have gp : (0:ℝ)<G n := by exact_mod_cast gpNat
    have g1 : 1≤(G n:ℝ) := by exact_mod_cast gpNat
    have l : L n≤m n+1 := by rw [len n]; unfold sourceTrialLength; split <;> omega
    have ratio := (div_le_div_of_nonneg_right (show (L n:ℝ)≤(m n+1:ℕ) by exact_mod_cast l) (sq_nonneg (G n:ℝ))).trans (hK (Set.mem_range_self n))
    have root := Real.sqrt_le_sqrt ratio
    rw [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_sq gp.le] at root
    have inv : 1/(G n:ℝ) ≤ 1 := (div_le_one gp).mpr g1
    rw [add_div,mul_div_assoc]; linarith
  have err (n) := phase_owner_averaged_error (H n) (G n) (m n) (a n) (b n) (o n) (slot n)
    (len n) (j n) (r n) (carry n) (t n) (ht01 n) (by have := hj n (fun _ => false); omega) (hc n) (hj n)
  have cap : Tendsto (fun n => (2+2*sqrt K)/sqrt (H n)) atTop (𝓝 0) := by
    simpa only [mul_zero,div_eq_mul_inv,Function.comp_apply] using
      (tendsto_const_nhds (x:=2+2*sqrt K)).mul (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hH))
  have diff : Tendsto (fun n => mean (w n) (raw n)/sqrt (H n) - mean (w n) (ref n)/sqrt (H n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ cap
    intro n
    rw [Real.norm_eq_abs,←sub_div,abs_div,abs_of_nonneg (sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right ((err n).trans (bound n)) (sqrt_nonneg _)
  simpa only [sub_add_cancel,zero_add] using diff.add refLim

end Shellsort
