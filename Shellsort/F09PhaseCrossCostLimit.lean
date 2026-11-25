import Shellsort.F09PhaseArcCostLimit
import Shellsort.F09PhaseVisitMoments

/-! Conditional Gaussian first moment for a pair of complete independent
physical divisor classes. Their source lengths can differ at the class cut. -/
noncomputable section
namespace Shellsort
open Filter Real Set
open scoped Topology BigOperators NNReal

abbrev PhasePairSource (h : ℕ) := Fin h ⊕ Fin h

abbrev phasePairLength {h : ℕ} (m a b : ℕ) (s : PhasePairSource h) : ℕ :=
  s.elim (fun u => sourceTrialLength m a u.val) (fun u => sourceTrialLength m b u.val)

abbrev phasePairWeight {h : ℕ} (m a b : ℕ) (t : ℝ) (s : PhasePairSource h) :=
  bernoulliVectorWeight t (phasePairLength m a b s)

def phasePairVisit {h : ℕ} (g j r m a b : ℕ) (s : PhasePairSource h)
    (x : Fin (phasePairLength m a b s) → Bool) : ℝ :=
  match s with
  | .inl u => (sourcePrefixCount h g j u.val (bitCount x):ℝ)
  | .inr u => -(sourcePrefixCount h g r u.val (bitCount x):ℝ)

def phasePairAbs (h g j r m a b : ℕ) (t carry : ℝ) :=
  mean (productWeight (phasePairWeight (h:=h) m a b t)) (fun z =>
    |(∑ s : PhasePairSource h, phasePairVisit g j r m a b s (z s)) + carry|)

private theorem phaseMean_neg {α : Type*} [Fintype α] (w f : α → ℝ) :
    mean w (fun x => -f x) = -mean w f := by simp [mean, Finset.sum_neg_distrib]

private theorem phase_center_neg (a b : ℝ) : -a - (-b) = -(a-b) := by ring

private theorem fourier_source_moment_cap (h g j s M : ℕ) (t K : ℝ) (ht : t ∈ Icc 0 1)
    (hg : 0<g) (hc : Nat.Coprime h g) (hj : j<g) (bound : (M:ℝ)/(g:ℝ)^2 ≤ K) :
    let w := bernoulliVectorWeight t M
    let F := fun x => (sourcePrefixCount h g j s (bitCount x):ℝ)
    mean w (fun x => (F x-mean w F)^2) ≤ 10+2*K+8*(12*K^2+2*K) ∧
      mean w (fun x => |F x-mean w F|^3) ≤ 10+2*K+8*(12*K^2+2*K) := by
  have gp : 0 < (g:ℝ) := by exact_mod_cast hg
  have g1 : 1 ≤ (g:ℝ)^2 := by
    have a : 1 ≤ (g:ℝ) := by exact_mod_cast hg
    nlinarith [sq_nonneg ((g:ℝ)-1)]
  have ratio : 0 ≤ (M:ℝ)/(g:ℝ)^2 := by positivity
  have k0 := ratio.trans bound
  have sq := pow_le_pow_left₀ ratio bound 2
  have lin := (div_le_self ratio g1).trans bound
  have ident : (12*(M:ℝ)^2+2*M)/(g:ℝ)^4 =
      12*((M:ℝ)/(g:ℝ)^2)^2 + 2*((M:ℝ)/(g:ℝ)^2)/(g:ℝ)^2 := by field_simp
  have second := source_visit_variance_bound h g j s M t hg hc hj ht
  have third := source_visit_third_centered_bound h g j s M t hg hc hj ht
  constructor
  · apply second.trans
    rw [mul_div_assoc]; nlinarith [sq_nonneg K]
  · apply third.trans
    rw [mul_div_assoc, ident, mul_div_assoc]
    linarith

/-- Two complete class fields have the sum of their local variances. -/
theorem phasePair_variance (h g j r m a b : ℕ) (t : ℝ) :
    (∑ s : PhasePairSource h, centeredSecond (phasePairWeight m a b t s) (phasePairVisit g j r m a b s)) =
      referenceVisitVariance h g j m a t+referenceVisitVariance h g r m b t := by
  rw [Fintype.sum_sum_type]
  let A := fun R j' (s : Fin h) (x : Fin (sourceTrialLength m R s.val) → Bool) =>
    (sourcePrefixCount h g j' s.val (bitCount x):ℝ)
  let w := fun R (s : Fin h) => bernoulliVectorWeight t (sourceTrialLength m R s.val)
  change (∑ s : Fin h, centeredSecond (w a s) (A a j s)) +
    (∑ s : Fin h, centeredSecond (w b s) (fun x => -(A b r s x))) = _
  have neg {α : Type} [Fintype α] (p f : α → ℝ) : centeredSecond p (fun x => -f x) = centeredSecond p f := by
    unfold centeredSecond
    rw [phaseMean_neg]
    simp only [phase_center_neg,neg_sq]
  have step (s : Fin h) : centeredSecond (w b s) (fun x => -A b r s x) = centeredSecond (w b s) (A b r s) := neg _ _
  simp_rw [step]
  congr 1 <;> exact Fin.sum_univ_eq_sum_range (fun s : ℕ => centeredSecond
    (bernoulliVectorWeight t (sourceTrialLength m _ s)) (fun x => (sourcePrefixCount h g _ s (bitCount x):ℝ))) h

theorem phasePair_mean (h g j r m a b : ℕ) (t : ℝ) :
    (∑ s : PhasePairSource h, mean (phasePairWeight m a b t s) (phasePairVisit g j r m a b s)) =
      referenceVisitMean h g j m a t-referenceVisitMean h g r m b t := by
  rw [Fintype.sum_sum_type]
  change (∑ s : Fin h, mean (bernoulliVectorWeight t (sourceTrialLength m a s.val)) _) +
    (∑ s : Fin h, mean (bernoulliVectorWeight t (sourceTrialLength m b s.val))
      (fun x => -(sourcePrefixCount h g r s.val (bitCount x):ℝ))) = _
  simp only [phaseMean_neg, Finset.sum_neg_distrib,← sub_eq_add_neg]
  congr 1 <;> exact Fin.sum_univ_eq_sum_range (fun s : ℕ => mean
    (bernoulliVectorWeight t (sourceTrialLength m _ s)) (fun x => (sourcePrefixCount h g _ s (bitCount x):ℝ))) h

/-- A pair of complete fields with true neighboring class sizes has the
cross-class absolute-moment limit. Their fixed physical targets and order
correction may vary with the row. -/
theorem reference_cross_abs_limit {G H m a b j r : ℕ → ℕ} {t carry : ℕ → ℝ} {lam T : ℝ}
    (hG : Tendsto (fun n => (G n:ℝ)) atTop atTop) (hH : Tendsto (fun n => (H n:ℝ)) atTop atTop)
    (hGH : Tendsto (fun n => (G n:ℝ)/(H n:ℝ)) atTop (𝓝 0))
    (hm : Tendsto (fun n => (m n:ℝ)/(G n:ℝ)^2) atTop (𝓝 lam))
    (ht : Tendsto t atTop (𝓝 T)) (ht01 : ∀ n, t n ∈ Icc 0 1)
    (hc : ∀ n, Nat.Coprime (H n) (G n)) (hj : ∀ n, j n < G n) (hR : ∀ n, r n < G n)
    (hh : ∀ n, 0 < H n) (ha : ∀ n, a n ≤ H n) (hb : ∀ n, b n ≤ H n)
    (near : ∀ n, |(a n:ℝ)-(b n:ℝ)| ≤ 1) (order : ∀ n, |carry n| ≤ 1) :
    Tendsto (fun n => phasePairAbs (H n) (G n) (j n) (r n) (m n) (a n) (b n) (t n) (carry n)/sqrt (H n))
      atTop (𝓝 (sqrt (2/π)*sqrt (2*(lam*F09.v T+F09.W (lam*F09.v T))))) := by
  let p := fun n => phasePairWeight (h:=H n) (m n) (a n) (b n) (t n)
  let f := fun n => phasePairVisit (h:=H n) (G n) (j n) (r n) (m n) (a n) (b n)
  let mu := fun n s => mean (p n s) (f n s)
  let X := fun n s z => f n s z-mu n s
  let V := lam*F09.v T+F09.W (lam*F09.v T)
  have p0 (n s z) : 0 ≤ p n s z := bernoulliVectorWeight_nonneg _ (ht01 n) _ _
  have p1 (n s) : ∑ z, p n s z = 1 := bernoulliVectorWeight_sum _ _
  have cent (n s) : mean (p n s) (X n s) = 0 := by
    dsimp only [X]; rw [mean_sub, mean_const (p n s) (p1 n s)]; exact sub_self _
  have one := critical_plus_one_source_length hG hm
  obtain ⟨K, hK⟩ := one.bddAbove_range
  have ratio (n) : (((m n+1:ℕ):ℝ)/(G n:ℝ)^2) ≤ K := hK (Set.mem_range_self n)
  have k0 : 0 ≤ K := (show 0 ≤ (((m 0+1:ℕ):ℝ)/(G 0:ℝ)^2) by positivity).trans (ratio 0)
  let D := 10+2*K+8*(12*K^2+2*K)
  have per (n s) : mean (p n s) (fun z => X n s z^2) ≤ D ∧ mean (p n s) (fun z => |X n s z|^3) ≤ D := by
    have hg : 0 < G n := by have := hj n; omega
    have cap (j' R s' : ℕ) (hj' : j'<G n) :=
      fourier_source_moment_cap (H n) (G n) j' s' (sourceTrialLength (m n) R s') (t n) K (ht01 n) hg (hc n) hj'
        ((div_le_div_of_nonneg_right (by exact_mod_cast (show sourceTrialLength (m n) R s' ≤ m n+1 by
          unfold sourceTrialLength; split <;> omega)) (sq_nonneg (G n:ℝ))).trans (ratio n))
    cases s with
    | inl s => exact cap _ (a n) s.val (hj n)
    | inr s =>
      have co := cap _ (b n) s.val (hR n)
      let W := bernoulliVectorWeight (t n) (sourceTrialLength (m n) (b n) s.val)
      let A := fun z : Fin (sourceTrialLength (m n) (b n) s.val) → Bool =>
        (sourcePrefixCount (H n) (G n) (r n) s.val (bitCount z):ℝ)
      change (mean W (fun z => (-A z - mean W (fun y => -A y))^2) ≤ D) ∧
        (mean W (fun z => |-A z - mean W (fun y => -A y)|^3) ≤ D)
      simp only [phaseMean_neg,phase_center_neg,neg_sq,abs_neg]
      exact co
  have va := mixed_reference_visit_critical_limit hG hGH hm ht ht01 hc hj hh ha
  have vb := mixed_reference_visit_critical_limit hG hGH hm ht ht01 hc hR hh hb
  have variance : Tendsto (fun n => (∑ s, mean (p n s) (fun z => X n s z^2))/(H n:ℝ)) atTop (𝓝 (2*V)) := by
    have vs := va.add vb
    simp only [← add_div, ← phasePair_variance, ← two_mul] at vs
    exact vs
  have vpos : 0 ≤ 2*V := le_of_tendsto_of_tendsto' tendsto_const_nhds variance fun n =>
    div_nonneg (Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun z _ => mul_nonneg (p0 n s z) (sq_nonneg _)) (Nat.cast_nonneg _)
  have CL := F09.independent_abs_limit_scaled p X p0 p1 cent (fun n => (H n:ℝ))
    (fun n => by exact_mod_cast hh n) hH 2 D (by dsimp [D]; positivity)
    (.of_forall fun n => by simp [PhasePairSource,Fintype.card_sum]; linarith) (.of_forall per) ⟨2*V,vpos⟩ variance
  let d := fun n => (∑ s, mu n s)+carry n
  have drift (n) : |d n| ≤ 4 := by
    have hg : 0 < G n := by have := hj n; omega
    have dEq : d n = referenceVisitMean (H n) (G n) (j n) (m n) (a n) (t n) -
        referenceVisitMean (H n) (G n) (r n) (m n) (b n) (t n) + carry n :=
      congrArg (· + carry n) (phasePair_mean _ _ _ _ _ _ _ _)
    have aj := abs_le.mp (reference_visit_mean_near (H n) (G n) (j n) (m n) (a n) (t n) (ht01 n) (ha n) hg (hj n))
    have br := abs_le.mp (reference_visit_mean_near (H n) (G n) (r n) (m n) (b n) (t n) (ht01 n) (hb n) hg (hR n))
    have dt : |((a n:ℝ)-(b n:ℝ))*(t n)/(G n:ℝ)| ≤ 1 := by
      rw [abs_div, abs_mul, abs_of_nonneg (ht01 n).1, abs_of_nonneg (Nat.cast_nonneg (G n) : (0:ℝ) ≤ G n),
        div_le_one (by exact_mod_cast hg)]
      have := mul_le_mul (near n) (ht01 n).2 (ht01 n).1 zero_le_one
      have gp : (1:ℝ) ≤ G n := by exact_mod_cast hg
      linarith
    have distEq : (((H n:ℝ)*m n+a n)*t n/(G n:ℝ))-(((H n:ℝ)*m n+b n)*t n/(G n:ℝ)) =
        ((a n:ℝ)-b n)*t n/(G n:ℝ) := by ring
    rw [← distEq] at dt
    rw [dEq]
    exact abs_le.mpr ⟨by linarith [aj.1,br.2,(abs_le.mp dt).1,(abs_le.mp (order n)).1],
      by linarith [aj.2,br.1,(abs_le.mp dt).2,(abs_le.mp (order n)).2]⟩
  let P := fun n => productWeight (p n)
  let F := fun n (z : ∀ s, Fin (phasePairLength (h:=H n) (m n) (a n) (b n) s) → Bool) => ∑ s, X n s (z s)
  have shifted := phase_abs_shift_limit P F (fun n => productWeight_nonneg _ (p0 n)) (fun n => productWeight_sum _ (p1 n))
    (fun n => (H n:ℝ)) d hH 4 _ drift CL
  have eq (n) (z) : F n z+d n = (∑ s, f n s (z s))+carry n := by
    simp only [F,X,d,Finset.sum_sub_distrib]; ring
  simp only [eq] at shifted
  exact shifted

end Shellsort
end
