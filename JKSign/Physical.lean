import JKSign.Smoothing

/-! Exact disintegration of each actual marked-key arc, with the pivot removed from the
independent Bernoulli product. The owner's rank within its own source selects all marginals. -/
noncomputable section
namespace Shellsort.JK
open scoped BigOperators
open MeasureTheory

/-- Split off the genuinely observed owner coordinate and project each remaining
independent coordinate to its hit indicator. The owner may choose the hit sets.
The formula retains exactly m independent nonowner coordinates. -/
theorem owner_nonowner_count_law {m : ℕ} {β : Fin (m+1) → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (hw : ∀ i, ∑ y, w i y=1) (o : Fin (m+1))
    (E : β o → (s : Fin m) → β (o.succAbove s) → Bool) (f : ℕ → ℝ) :
    mean (productWeight w) (fun x => f (bitCount (fun s => E (x o) s (x (o.succAbove s))))) =
    mean (w o) (fun a => mean (productWeight (fun s =>
      bernoulliWeight (eventMarginal (w (o.succAbove s)) (E a s)))) (fun z => f (bitCount z))) := by
  let v := fun s : Fin m => w (o.succAbove s)
  have split : mean (productWeight w)
      (fun x => f (bitCount (fun s => E (x o) s (x (o.succAbove s))))) =
      mean (w o) (fun a => mean (productWeight v)
        (fun z => f (bitCount (fun s => E a s (z s))))) := by
    unfold mean
    rw [← (Fin.insertNthEquiv β o).sum_comp]
    simp only [Fintype.sum_prod_type,Fin.insertNthEquiv_apply,Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    have ww : productWeight w (o.insertNth a z) = w o a * productWeight v z := by
      unfold productWeight
      rw [Fin.prod_univ_succAbove _ o]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, v]
    rw [ww,mul_assoc]
  rw [split]
  congr 1
  funext a
  exact productWeight_event_projection v (E a) (fun s => hw (o.succAbove s)) (fun z => f (bitCount z))

private theorem omit_false_owner {m : ℕ} (o : Fin (m+1)) (z : Fin (m+1) → Bool) (hz : z o=false) :
    bitCount z = bitCount (fun s => z (o.succAbove s)) := by
  unfold bitCount
  rw [Fin.sum_univ_succAbove _ o, hz]
  simp

/-- Hit probability of the sth nonowner chain of a real original pivot slot.
Its length is the physical ragged-chain length and its cyclic arc is chosen by the owner's count. -/
def physicalHitProbability {n m : ℕ} (g ell : ℕ) (i : Fin n) (t : ℝ) (y : ℕ) (s : Fin m) : ℝ :=
  let h := m+1
  let o := ((positionChainEquiv n h (Nat.succ_pos m)) i).1
  let j := o.succAbove s
  eventMarginal (sourceCoordinateWeight h (n/h) (n%h) t j)
    (fun z => pivotArcHit h g o.val ell y j.val (bitCount z))

/-- At a fixed threshold, average the Poisson-binomial count law over the actual owner bits. -/
def physicalArcAtThreshold {n : ℕ} (m g ell : ℕ) (i : Fin n) (t : ℝ) (f : ℕ → ℝ) : ℝ :=
  let h := m+1
  let c := positionChainEquiv n h (Nat.succ_pos m) i
  mean (sourceCoordinateWeight h (n/h) (n%h) t c.1) fun a =>
    mean (productWeight (fun s : Fin m =>
      bernoulliWeight (physicalHitProbability g ell i t (ownerBitCount c.2 a) s)))
      (fun z => f (bitCount z))

theorem physicalArc_threshold_law {n : ℕ} (m g ell : ℕ) (i : Fin n) (t : ℝ) (f : ℕ → ℝ) :
    mean (bernoulliVectorWeight t n)
      (fun z => f (taggedSubsetArcCount (m+1) g ell i (fullBitsSubset i z))) =
      physicalArcAtThreshold m g ell i t f := by
  let h := m+1
  let hh : 0 < h := Nat.succ_pos m
  let c := positionChainEquiv n h hh i
  let o := c.1
  let w := sourceCoordinateWeight h (n/h) (n%h) t
  let E (a : Fin (sourceTrialLength (n/h) (n%h) o.val) → Bool)
        (s : Fin m) (z : Fin (sourceTrialLength (n/h) (n%h) (o.succAbove s).val) → Bool) :=
    pivotArcHit h g o.val ell (ownerBitCount c.2 a) (o.succAbove s).val (bitCount z)
  have hw (s : Fin h) := sourceCoordinateWeight_sum h (n/h) (n%h) t s
  have res : o.val = i.val%h := rfl
  have actual (z : Fin n → Bool) : taggedSubsetArcCount h g ell i (fullBitsSubset i z) =
      bitCount (fun s : Fin m => E (chainBits hh z o) s (chainBits hh z (o.succAbove s))) := by
    unfold taggedSubsetArcCount
    rw [← res,owner_fullBits_chain_count hh i z]
    let H (s : Fin h) := pivotArcHit h g o.val ell (ownerBitCount c.2 (chainBits hh z o))
      s.val (chainLowerCount (fullBitsSubset i z) h s.val)
    have hz : H o = false := by simp [H,pivotArcHit]
    change bitCount H = _
    rw [omit_false_owner o H hz]
    apply congrArg bitCount
    funext s
    have ne : (o.succAbove s).val ≠ i.val%h :=
      fun e => Fin.succAbove_ne o s (Fin.ext (e.trans res.symm))
    simp only [H,E,nonowner_fullBits_chain_count hh i z (o.succAbove s) ne]
  let F := fun (x : ∀ s : Fin h, Fin (sourceTrialLength (n/h) (n%h) s.val) → Bool) =>
    f (bitCount (fun s : Fin m => E (x o) s (x (o.succAbove s))))
  change mean (bernoulliVectorWeight t n) (fun z => f (taggedSubsetArcCount h g ell i
    (fullBitsSubset i z))) = _
  simp_rw [actual]
  change mean (productWeight (fun _ : Fin n => bernoulliWeight t)) (fun z => F (chainBits hh z)) = _
  rw [fullBits_mean_chainBits n h hh t F]
  exact owner_nonowner_count_law w hw o E f

/-- Unconditional identity for the signed or unsigned reward of an arc on uniform permutations. -/
theorem uniform_arc_physical_integral {n : ℕ} (m g ell : ℕ) (i : Fin n) (f : ℕ → ℝ) :
    uniformAverage (fun p : RankPlacement n =>
      f (taggedSubsetArcCount (m+1) g ell i (tagLowerState p i).val)) =
      ∫ t : ℝ in 0..1, physicalArcAtThreshold m g ell i t f := by
  let F := fun b : TaggedSubset i => f (taggedSubsetArcCount (m+1) g ell i b.val)
  rw [show uniformAverage _ = _ from uniform_tagged_bernoulli_mixture i F]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← bernoulli_mean_add_dummy i t (fun z => F ((omittedBitsSubsetEquiv i) z))]
  exact physicalArc_threshold_law m g ell i t f


/-- Each explicitly defined hit probability is a true probability on the source of
length floor(n/h) or ceil(n/h); no constraint on the owner's count is needed here. -/
theorem physicalHitProbability_mem_unit {n m : ℕ} (g ell : ℕ) (i : Fin n) (t : ℝ)
    (ht : t ∈ Set.Icc 0 1) (y : ℕ) (s : Fin m) :
    physicalHitProbability g ell i t y s ∈ Set.Icc 0 1 := by
  let h := m+1
  let o := ((positionChainEquiv n h (Nat.succ_pos m)) i).1
  let j := o.succAbove s
  let w := sourceCoordinateWeight h (n/h) (n%h) t j
  let event := fun (z : Fin (sourceTrialLength (n/h) (n%h) j.val) → Bool) =>
    pivotArcHit h g o.val ell y j.val (bitCount z)
  change eventMarginal w event ∈ Set.Icc 0 1
  have pos := sourceCoordinateWeight_nonneg h (n/h) (n%h) t ht j
  have norm := sourceCoordinateWeight_sum h (n/h) (n%h) t j
  unfold eventMarginal
  constructor
  · apply Finset.sum_nonneg
    intro z _
    split <;> simp [w,pos]
  · exact (Finset.sum_le_sum (g := w) (fun z _ => by split <;> simp [w,pos])).trans norm.le

/-- Sufficient marginal criteria at an attainable owner sample. The first alternative is exact
mean balance. The second permits a nonzero drift paid for by the quantitative atom bound. -/
def arcMarginalBudget {m : ℕ} (p : Fin m → ℝ) (q : ℝ) (K : ℕ) : Prop :=
  (∑ j, p j = (m:ℝ)*q) ∨
    ∃ r e : ℝ, 0 ≤ e ∧ (∀ j, p j ∈ Set.Icc e (1-e)) ∧ r ∈ Set.Icc e (1-e) ∧
      (∑ j, p j = (m:ℝ)*r) ∧ 0 < K ∧
      (m:ℝ)*|r-q| ≤ (((m-2).choose (K-1)):ℝ)*e^(m-2) * (∑ j, (p j-r)^2)

/-- From the actual slot, threshold and attainable owner configurations to a signed upper
bound on the real permutation arc. The only extra premise is the displayed marginal budget. -/
theorem observedArc_le_of_physical_budget {n : ℕ} (m g ell : ℕ) (i : Fin n)
    (hg : 0 < g) (hl : ell < g)
    (budget : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      let h := m+1
      let c := positionChainEquiv n h (Nat.succ_pos m) i
      ∀ a : Fin (sourceTrialLength (n/h) (n%h) c.1.val) → Bool,
        arcMarginalBudget (fun s : Fin m => physicalHitProbability g ell i t (ownerBitCount c.2 a) s)
          ((ell:ℝ)/g) (h*ell/g)) :
    observedArc (m+1) g ell i ≤ referenceArc (m+1) g ell := by
  let h := m+1
  let c := positionChainEquiv n h (Nat.succ_pos m) i
  let K := h*ell/g
  let q := (ell:ℝ)/g
  let f := fun k : ℕ => |(k:ℝ)-(K:ℝ)|
  have gp : 0 < (g:ℝ) := by exact_mod_cast hg
  have qok : q ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (by positivity) gp.le,(div_le_one gp).mpr (by exact_mod_cast hl.le)⟩
  have b (t : ℝ) (ht : t ∈ Set.Icc 0 1) : physicalArcAtThreshold m g ell i t f ≤ referenceArc h g ell := by
    let w := sourceCoordinateWeight h (n/h) (n%h) t c.1
    let p := fun a (s : Fin m) => physicalHitProbability g ell i t (ownerBitCount c.2 a) s
    have localBound (a) : mean (productWeight (fun j => bernoulliWeight (p a j)))
        (fun z => f (bitCount z)) ≤ referenceArc h g ell := by
      rcases budget t ht a with matched | ⟨r,e,he,hp,hr,hm,hK,hbudget⟩
      · exact referenceArc_dominates_at_matched_mean h g ell (p a)
          (fun j => physicalHitProbability_mem_unit g ell i t ht _ j) qok matched
      · exact referenceArc_dominates_of_drift_budget h g ell (p a) r e he hp hr qok hm hK hbudget
    have pos := sourceCoordinateWeight_nonneg h (n/h) (n%h) t ht c.1
    have norm := sourceCoordinateWeight_sum h (n/h) (n%h) t c.1
    calc
      _ ≤ mean w (fun _ => referenceArc h g ell) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (localBound a) (pos a)
      _ = _ := mean_const w norm _
  let F := fun b : TaggedSubset i => f (taggedSubsetArcCount h g ell i b.val)
  apply uniform_tagged_mean_le_of_full_bernoulli_bound i F _
  intro t h0 h1
  change mean (bernoulliVectorWeight t n) (fun z => f (taggedSubsetArcCount (m+1) g ell i
    (fullBitsSubset i z))) ≤ _
  rw [physicalArc_threshold_law]
  exact b t ⟨h0,h1⟩

/-- A sufficient condition entirely in physical finite source marginals for the conjectured
zero-addition bound on the actual final insertion cost under uniform permutations. -/
theorem lastCost_le_psi_of_physical_budget {n : ℕ} (m g : ℕ)
    (hg : 0 < g) (hc : Nat.Coprime (m+1) g)
    (budget : ∀ (i : Fin n) (ell : ℕ), 0 < ell → ell < g → ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      let h := m+1
      let c := positionChainEquiv n h (Nat.succ_pos m) i
      ∀ a : Fin (sourceTrialLength (n/h) (n%h) c.1.val) → Bool,
        arcMarginalBudget (fun s : Fin m => physicalHitProbability g ell i t (ownerBitCount c.2 a) s)
          ((ell:ℝ)/g) (h*ell/g)) :
    uniformAverage (fun p : RankPlacement n =>
      (gapInsertionCost (gapSort (gapSort p (m+1)) g) 1 (by decide) : ℝ)) ≤ n*psi (m+1) g := by
  have ident := two_mul_lastCost_error (n:=n) (Nat.succ_pos m) hg hc
  have noGain : (∑ i : Fin n, ∑ ell ∈ (Finset.range g).erase 0,
      (observedArc (m+1) g ell i - referenceArc (m+1) g ell)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro ell he
    obtain ⟨nz,mem⟩ := Finset.mem_erase.mp he
    have hl := Finset.mem_range.mp mem
    exact sub_nonpos.mpr (observedArc_le_of_physical_budget m g ell i hg hl
      (budget i ell (Nat.pos_of_ne_zero nz) hl))
  linarith

end Shellsort.JK
end
