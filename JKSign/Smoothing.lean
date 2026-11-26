import JKSign.Variance
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic

/-! Averaging unequal Bernoulli marginals, with the exact gain for an integer
absolute-deviation reward. All expectations are finite sums. -/
noncomputable section
namespace Shellsort.JK
open scoped BigOperators

/-- Apply one independent Bernoulli trial to an observable of a count. -/
def trialStep (a : ℝ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (1-a)*f k + a*f (k+1)

/-- Expectation of f of the number of successes using the listed probabilities. -/
def trialExpectation : List ℝ → (ℕ → ℝ) → ℝ
  | [], f => f 0
  | a :: ps, f => trialExpectation ps (trialStep a f)

private theorem step_comm (a b : ℝ) (f : ℕ → ℝ) :
    trialStep b (trialStep a f) = trialStep a (trialStep b f) := by
  funext k
  simp only [trialStep]
  ring

private theorem trialExpectation_perm {ps ts : List ℝ} (h : ps.Perm ts) (f : ℕ → ℝ) :
    trialExpectation ps f = trialExpectation ts f := by
  induction h generalizing f with
  | nil => rfl
  | cons x h ih => exact ih (trialStep x f)
  | swap x y l =>
    change trialExpectation l (trialStep x (trialStep y f)) =
      trialExpectation l (trialStep y (trialStep x f))
    rw [step_comm]
  | trans _ _ ih jh => exact (ih f).trans (jh f)

private theorem trialExpectation_mono (ps : List ℝ) (hp : ∀ a ∈ ps, a ∈ Set.Icc 0 1)
    {f g : ℕ → ℝ} (h : ∀ k, f k ≤ g k) :
    trialExpectation ps f ≤ trialExpectation ps g := by
  induction ps generalizing f g with
  | nil => exact h 0
  | cons a ps ih =>
    have ha := hp a (by simp)
    exact ih (fun b hb => hp b (by simp [hb]))
      (fun k => add_le_add (mul_le_mul_of_nonneg_left (h k) (sub_nonneg.mpr ha.2))
        (mul_le_mul_of_nonneg_left (h (k+1)) ha.1))

private theorem trialExpectation_linear (ps : List ℝ) (α β : ℝ) (f g : ℕ → ℝ) :
    trialExpectation ps (fun k => α*f k+β*g k) =
      α*trialExpectation ps f+β*trialExpectation ps g := by
  induction ps generalizing f g with
  | nil => rfl
  | cons a ps ih =>
    change trialExpectation ps (trialStep a (fun k => α*f k+β*g k)) = _
    have move : trialStep a (fun k => α*f k+β*g k) =
        fun k => α*trialStep a f k+β*trialStep a g k := by
      funext k
      simp only [trialStep]
      ring
    rw [move, ih]
    rfl

/-- Replacing a,b by q,a+b−q keeps the sum fixed. For an arbitrary reward the
pointwise gain factors into a quadratic parameter difference and a discrete curvature. -/
theorem pair_transfer_gain (a b q : ℝ) (f : ℕ → ℝ) (k : ℕ) :
    trialStep (a+b-q) (trialStep q f) k - trialStep b (trialStep a f) k =
      (q-a)*(b-q)*(f k-2*f (k+1)+f (k+2)) := by
  simp only [trialStep]
  ring

private theorem abs_discrete_curvature (k K : ℕ) :
    |(k : ℝ)-(K : ℝ)| - 2*|((k+1 : ℕ) : ℝ)-(K : ℝ)| +
      |((k+2 : ℕ) : ℝ)-(K : ℝ)| = if k+1=K then 2 else 0 := by
  rcases lt_trichotomy (k+1) K with h | h | h
  · rw [ite_eq_right h.ne]
    have h0 : (k:ℝ) ≤ K := by exact_mod_cast (by omega : k ≤ K)
    have h1 : ((k+1:ℕ):ℝ) ≤ K := by exact_mod_cast h.le
    have h2 : ((k+2:ℕ):ℝ) ≤ K := by exact_mod_cast (by omega : k+2 ≤ K)
    rw [abs_of_nonpos (sub_nonpos.mpr h0), abs_of_nonpos (sub_nonpos.mpr h1),
      abs_of_nonpos (sub_nonpos.mpr h2)]
    push_cast
    ring
  · subst K
    simp
    norm_num
  · rw [ite_eq_right h.ne']
    have h0 : (K:ℝ) ≤ k := by exact_mod_cast (by omega : K ≤ k)
    have h1 : (K:ℝ) ≤ ((k+1:ℕ):ℝ) := by exact_mod_cast h.le
    have h2 : (K:ℝ) ≤ ((k+2:ℕ):ℝ) := by exact_mod_cast (by omega : K ≤ k+2)
    rw [abs_of_nonneg (sub_nonneg.mpr h0), abs_of_nonneg (sub_nonneg.mpr h1),
      abs_of_nonneg (sub_nonneg.mpr h2)]
    push_cast
    ring

/-- Exact smoothing gain. The multiplier is the probability that among the
remaining trials exactly K−1 succeed. This also handles K=0. -/
theorem abs_pair_transfer_gain (ps : List ℝ) (a b q : ℝ) (K : ℕ) :
    trialExpectation (q::(a+b-q)::ps) (fun k => |(k:ℝ)-K|) -
      trialExpectation (a::b::ps) (fun k => |(k:ℝ)-K|) =
      2*(q-a)*(b-q)*trialExpectation ps (fun k => if k+1=K then 1 else 0) := by
  let f := fun k : ℕ => |(k:ℝ)-(K:ℝ)|
  let old := trialStep b (trialStep a f)
  let newf := trialStep (a+b-q) (trialStep q f)
  let atom := fun k : ℕ => if k+1=K then (1 : ℝ) else 0
  have eqv : newf = fun k => 1*old k+(2*(q-a)*(b-q))*atom k := by
    funext k
    have fact := pair_transfer_gain a b q f k
    change newf k-old k = (q-a)*(b-q)*(_-2*_+_) at fact
    have curv := abs_discrete_curvature k K
    change f k-2*f (k+1)+f (k+2) = _ at curv
    rw [curv] at fact
    by_cases hk : k+1=K <;> simp [hk, atom] at fact ⊢ <;> linarith
  change trialExpectation ps newf - trialExpectation ps old = _
  rw [eqv,trialExpectation_linear]
  dsimp only [atom]
  ring

/-- The list expectation agrees with the product weights already used for executed arcs. -/
theorem product_eq_trialExpectation {m : ℕ} (p : Fin m → ℝ) (f : ℕ → ℝ) :
    mean (productWeight (fun i => bernoulliWeight (p i))) (fun z => f (bitCount z)) =
      trialExpectation (List.ofFn p) f := by
  induction m generalizing f with
  | zero => simp [mean, productWeight, bitCount, trialExpectation]
  | succ m ih =>
    rw [List.ofFn_succ]
    change _ = trialExpectation _ (trialStep (p 0) f)
    rw [← ih]
    unfold mean
    rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp]
    simp only [Fintype.sum_prod_type,Fin.consEquiv_apply,productWeight,Fin.prod_univ_succ,
      bitCount_cons,Fin.cons_zero,Fin.cons_succ,Fintype.sum_bool,bernoulliWeight,
      Bool.false_eq_true,ite_false,ite_true,zero_add,Nat.add_comm 1,trialStep]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring



private def curvature (f : ℕ → ℝ) (k : ℕ) : ℝ := f k-2*f (k+1)+f (k+2)

private theorem curvature_step (a : ℝ) (f : ℕ → ℝ) :
    curvature (trialStep a f) = trialStep a (curvature f) := by
  funext k
  simp only [curvature,trialStep]
  ring

private theorem trialExpectation_const (ps : List ℝ) (c : ℝ) :
    trialExpectation ps (fun _ => c) = c := by
  induction ps with
  | nil => rfl
  | cons a ps ih =>
    change trialExpectation ps (trialStep a (fun _ => c)) = c
    have eqv : trialStep a (fun _ => c) = fun _ => c := by funext k; simp [trialStep]; ring
    rw [eqv,ih]

private theorem transfer_gain_expectation (ps : List ℝ) (a b q : ℝ) (f : ℕ → ℝ) :
    trialExpectation (q::(a+b-q)::ps) f - trialExpectation (a::b::ps) f =
     (q-a)*(b-q)*trialExpectation ps (curvature f) := by
  let old := trialStep b (trialStep a f)
  let newf := trialStep (a+b-q) (trialStep q f)
  have eqv : newf = fun k => 1*old k+((q-a)*(b-q))*curvature f k := by
    funext k
    have h := pair_transfer_gain a b q f k
    change newf k-old k = (q-a)*(b-q)*curvature f k at h
    linarith
  change trialExpectation ps newf - trialExpectation ps old = _
  rw [eqv,trialExpectation_linear]
  ring
private theorem one_sided_sum (ps : List ℝ) (q : ℝ) :
    ((∀ x ∈ ps, q ≤ x) → (ps.length : ℝ)*q ≤ ps.sum) ∧
    ((∀ x ∈ ps, x ≤ q) → ps.sum ≤ (ps.length : ℝ)*q) := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    constructor
    · intro h
      have := ih.1 (fun x hx => h x (by simp [hx]))
      have ha := h a (by simp)
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.sum_cons]
      linarith
    · intro h
      have := ih.2 (fun x hx => h x (by simp [hx]))
      have ha := h a (by simp)
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.sum_cons]
      linarith

private theorem at_mean_of_one_side (ps : List ℝ) (q : ℝ)
    (hs : ps.sum = (ps.length : ℝ)*q)
    (side : (∀ x ∈ ps, q ≤ x) ∨ (∀ x ∈ ps, x ≤ q)) :
    ∀ x ∈ ps, x=q := by
  classical
  intro a ha
  let ts := ps.erase a
  have perm : ps.Perm (a::ts) := List.perm_cons_erase ha
  have hL := perm.length_eq
  have hS := perm.sum_eq
  rw [hS,hL] at hs
  simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at hs
  have hmem (x : ℝ) (hx : x ∈ ts) : x ∈ ps := List.mem_of_mem_erase hx
  rcases side with h | h
  · have hx := (one_sided_sum ts q).1 (fun x hx => h x (hmem x hx))
    exact le_antisymm (by linarith) (h a ha)
  · have hx := (one_sided_sum ts q).2 (fun x hx => h x (hmem x hx))
    exact le_antisymm (h a ha) (by linarith)

private theorem comparison_on_interval (ps : List ℝ) (q lo hi : ℝ)
    (hq : q ∈ Set.Icc lo hi) (hp : ∀ a ∈ ps, a ∈ Set.Icc lo hi)
    (hs : ps.sum = (ps.length : ℝ)*q) {f : ℕ → ℝ}
    (curve : ∀ (ts : List ℝ), ts.length+2=ps.length →
      (∀ x ∈ ts, x ∈ Set.Icc lo hi) → 0 ≤ trialExpectation ts (curvature f)) :
    trialExpectation ps f ≤ trialExpectation (List.replicate ps.length q) f := by
  classical
  by_cases all : ∀ x ∈ ps, x=q
  · exact le_of_eq (congrArg (fun l => trialExpectation l f) (List.eq_replicate_length.mpr all))
  have low : ∃ a ∈ ps, a < q := by
    by_contra! h
    exact all (at_mean_of_one_side ps q hs (Or.inl h))
  have high : ∃ b ∈ ps, q < b := by
    by_contra! h
    exact all (at_mean_of_one_side ps q hs (Or.inr h))
  obtain ⟨a,ha,haq⟩ := low
  obtain ⟨b,hb,hqb⟩ := high
  have hba : b ≠ a := ne_of_gt (lt_trans haq hqb)
  let rem := (ps.erase a).erase b
  have pb : b ∈ ps.erase a := (List.mem_erase_of_ne hba).mpr hb
  have perm : ps.Perm (a::b::rem) :=
    (List.perm_cons_erase ha).trans ((List.perm_cons_erase pb).cons a)
  have hmem (x : ℝ) (hx : x ∈ rem) : x ∈ ps :=
    List.mem_of_mem_erase (List.mem_of_mem_erase hx)
  have hL := perm.length_eq
  have hS := perm.sum_eq
  have newS : ((a+b-q)::rem).sum = (((a+b-q)::rem).length : ℝ)*q := by
    rw [hL,hS] at hs
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at hs ⊢
    linarith
  have newP : ∀ x ∈ ((a+b-q)::rem), x ∈ Set.Icc lo hi := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · subst x
      exact ⟨by linarith [(hp a ha).1], by linarith [(hp b hb).2]⟩
    · exact hp x (hmem x h)
  have newCurve (ts : List ℝ) (hlen : ts.length+2 = ((a+b-q)::rem).length)
      (ht : ∀ x ∈ ts, x ∈ Set.Icc lo hi) :
      0 ≤ trialExpectation ts (curvature (trialStep q f)) := by
    have h1 : (q::ts).length+2=ps.length := by
      rw [hL]
      simp only [List.length_cons] at hlen ⊢
      omega
    have h2 : ∀ x ∈ (q::ts), x ∈ Set.Icc lo hi := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | h
      · exact hq
      · exact ht x h
    rw [curvature_step]
    exact curve (q::ts) h1 h2
  have ih := comparison_on_interval ((a+b-q)::rem) q lo hi hq newP newS newCurve
  calc
    trialExpectation ps f = trialExpectation (a::b::rem) f := trialExpectation_perm perm f
    _ ≤ trialExpectation (q::(a+b-q)::rem) f := by
      have h1 : rem.length+2=ps.length := by rw [hL]; rfl
      have positive := mul_nonneg (mul_nonneg (sub_nonneg.mpr haq.le) (sub_nonneg.mpr hqb.le))
        (curve rem h1 (fun x hx => hp x (hmem x hx)))
      exact sub_nonneg.mp ((transfer_gain_expectation rem a b q f).symm ▸ positive)
    _ = trialExpectation ((a+b-q)::rem) (trialStep q f) := rfl
    _ ≤ trialExpectation (List.replicate ((a+b-q)::rem).length q) (trialStep q f) := ih
    _ = trialExpectation (List.replicate ps.length q) f := by
      rw [hL]
      rfl
termination_by ps.length
decreasing_by
  change rem.length + 1 < ps.length
  rw [hL]
  simp

/-- Finite convex order at a matched mean, proved by fixing at least one parameter at q
per transfer. All product distributions and the binomial reference are explicit. -/
theorem bernoulli_convex_order {m : ℕ} (p : Fin m → ℝ) (q : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (hmean : ∑ i, p i = (m : ℝ)*q) (f : ℕ → ℝ)
    (convex : ∀ k, 0 ≤ f k-2*f (k+1)+f (k+2)) :
    mean (productWeight (fun i => bernoulliWeight (p i))) (fun z => f (bitCount z)) ≤
      mean (bernoulliVectorWeight q m) (fun z => f (bitCount z)) := by
  change _ ≤ mean (productWeight (fun _ : Fin m => bernoulliWeight q)) _
  rw [product_eq_trialExpectation p f, product_eq_trialExpectation (fun _ => q) f, List.ofFn_const]
  have hv : ∀ x ∈ List.ofFn p, x ∈ Set.Icc 0 1 := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hp i
  have hsum : (List.ofFn p).sum = ((List.ofFn p).length : ℝ)*q := by
    simpa only [List.sum_ofFn, List.length_ofFn] using hmean
  have curve (ts : List ℝ) (_hlen : ts.length+2=(List.ofFn p).length)
      (ht : ∀ x ∈ ts, x ∈ Set.Icc 0 1) : 0 ≤ trialExpectation ts (curvature f) := by
    calc
      0 = trialExpectation ts (fun _ => 0) := (trialExpectation_const ts 0).symm
      _ ≤ trialExpectation ts (curvature f) := trialExpectation_mono ts ht convex
  simpa using comparison_on_interval (List.ofFn p) q 0 1 hq hv hsum curve

/-- If the nonowner hit probabilities have exactly the reference mean, their absolute
discrepancy is dominated by the actual Janson–Knuth binomial reference arc. -/
theorem referenceArc_dominates_at_matched_mean (h g ell : ℕ) (p : Fin (h-1) → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc 0 1) (hq : (ell : ℝ)/g ∈ Set.Icc 0 1)
    (hmean : ∑ i, p i = ((h-1 : ℕ) : ℝ)*((ell : ℝ)/g)) :
    mean (productWeight (fun i => bernoulliWeight (p i)))
      (fun z => |(bitCount z : ℝ) - ((h*ell/g : ℕ) : ℝ)|) ≤ referenceArc h g ell := by
  apply bernoulli_convex_order p ((ell : ℝ)/g) hp hq hmean (fun k => |(k : ℝ) - (h*ell/g : ℕ)|)
  intro k
  rw [abs_discrete_curvature]
  split <;> norm_num


private theorem trialExpectation_cons_split (a : ℝ) (ps : List ℝ) (f : ℕ → ℝ) :
    trialExpectation (a::ps) f =
      (1-a)*trialExpectation ps f + a*trialExpectation ps (fun k => f (k+1)) :=
  trialExpectation_linear ps (1-a) a f (fun k => f (k+1))

/-- Every bit string of length m has mass at least e^m when the individual
marginals lie in [e,1−e]. Grouping the strings of a common count gives this atom bound. -/
theorem count_atom_lower (ps : List ℝ) (e : ℝ) (he : 0 ≤ e)
    (hp : ∀ x ∈ ps, x ∈ Set.Icc e (1-e)) (k : ℕ) :
    (ps.length.choose k : ℝ)*e^ps.length ≤
      trialExpectation ps (fun j => if j=k then 1 else 0) := by
  induction ps generalizing k with
  | nil =>
    cases k <;> simp [trialExpectation]
  | cons a ps ih =>
    have ha := hp a (by simp)
    have htail (x : ℝ) (hx : x ∈ ps) := hp x (by simp [hx])
    have lo : e ≤ a := ha.1
    have hi : e ≤ 1-a := by linarith [ha.2]
    rw [trialExpectation_cons_split]
    cases k with
    | zero =>
      simp only [List.length_cons, Nat.choose_zero_right, Nat.cast_one, one_mul,
        Nat.succ_ne_zero, ite_false, trialExpectation_const, mul_zero, add_zero]
      have h := ih htail 0
      simp only [Nat.choose_zero_right,Nat.cast_one,one_mul] at h
      rw [pow_succ, mul_comm]
      exact mul_le_mul hi h (pow_nonneg he _) (le_trans he hi)
    | succ k =>
      simp only [List.length_cons,Nat.choose_succ_succ,Nat.cast_add,Nat.succ.injEq]
      have h1 := ih htail (k+1)
      have h0 := ih htail k
      have b1 := mul_le_mul hi h1 (by positivity) (le_trans he hi)
      have b0 := mul_le_mul lo h0 (by positivity) (le_trans he lo)
      rw [pow_succ]
      nlinarith

private theorem curvature_discount (K : ℕ) (c : ℝ) :
    curvature (fun k : ℕ => |(k:ℝ)-K|-c*(k:ℝ)^2) =
      fun k => 2*(if k+1=K then 1 else 0) + (-2*c)*1 := by
  funext k
  have v := abs_discrete_curvature k K
  simp only [curvature]
  rw [show |(k:ℝ)-K|-c*(k:ℝ)^2-2*(|((k+1:ℕ):ℝ)-K|-c*((k+1:ℕ):ℝ)^2)
       +(|((k+2:ℕ):ℝ)-K|-c*((k+2:ℕ):ℝ)^2) =
     (|(k:ℝ)-K|-2*|((k+1:ℕ):ℝ)-K|+|((k+2:ℕ):ℝ)-K|) - 2*c by push_cast; ring, v]
  split <;> ring

private theorem mean_scale {α : Type*} [Fintype α] (w f : α → ℝ) (c : ℝ) :
    mean w (fun x => c*f x) = c*mean w f := by
  simp only [mean, Finset.mul_sum, mul_left_comm]

/-- Explicit quantitative convex-order gain at the integer center K. All marginals
lie in [ε,1−ε] and q is their mean. The lower bound multiplies the squared
heterogeneity by the mass floor of the K−1 atom of the remaining m−2 trials.
If ε>0 and 0<K<m this gives strict comparison for any unequal marginals. -/
theorem bernoulli_abs_heterogeneity_discount {m : ℕ} (p : Fin m → ℝ) (q e : ℝ) (K : ℕ)
    (he : 0 ≤ e) (hp : ∀ i, p i ∈ Set.Icc e (1-e)) (hq : q ∈ Set.Icc e (1-e))
    (hmean : ∑ i, p i = (m : ℝ)*q) (hK : 0 < K) :
    ((m-2).choose (K-1) : ℝ)*e^(m-2) * (∑ i, (p i-q)^2) ≤
       mean (bernoulliVectorWeight q m) (fun z => |(bitCount z : ℝ)-K|) -
       mean (productWeight (fun i => bernoulliWeight (p i))) (fun z => |(bitCount z : ℝ)-K|) := by
  let c : ℝ := ((m-2).choose (K-1) : ℝ)*e^(m-2)
  let f := fun k : ℕ => |(k:ℝ)-K|-c*(k:ℝ)^2
  have valid : ∀ x ∈ List.ofFn p, x ∈ Set.Icc e (1-e) := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hp i
  have sumP : (List.ofFn p).sum = ((List.ofFn p).length : ℝ)*q := by
    simpa only [List.sum_ofFn,List.length_ofFn] using hmean
  have curve (ts : List ℝ) (hlen : ts.length+2=(List.ofFn p).length)
      (ht : ∀ x ∈ ts, x ∈ Set.Icc e (1-e)) : 0 ≤ trialExpectation ts (curvature f) := by
    have len : ts.length = m-2 := by simp only [List.length_ofFn] at hlen; omega
    have lb := count_atom_lower ts e he ht (K-1)
    rw [len] at lb
    change c ≤ _ at lb
    have same (j : ℕ) : (j+1=K) ↔ (j=K-1) := by omega
    rw [show f = _ from rfl, curvature_discount, trialExpectation_linear, trialExpectation_const]
    simp only [same, mul_one]
    linarith
  have hlist := comparison_on_interval (List.ofFn p) q e (1-e) hq valid sumP curve
  have bound : mean (productWeight (fun i => bernoulliWeight (p i))) (fun z => f (bitCount z)) ≤
      mean (bernoulliVectorWeight q m) (fun z => f (bitCount z)) := by
    change _ ≤ mean (productWeight (fun _ : Fin m => bernoulliWeight q)) _
    rw [product_eq_trialExpectation p f, product_eq_trialExpectation (fun _ => q) f, List.ofFn_const]
    simpa only [List.length_ofFn] using hlist
  simp only [f, mean_sub, mean_scale] at bound
  have gap := bernoulli_second_moment_gap p q hmean
  change c * _ ≤ _
  rw [← gap]
  linarith


private theorem trialExpectation_difference_le (ps : List ℝ)
    (hp : ∀ x ∈ ps, x ∈ Set.Icc 0 1) (f g : ℕ → ℝ) (B : ℝ)
    (bounds : ∀ k, f k-g k ≤ B) :
    trialExpectation ps f - trialExpectation ps g ≤ B := by
  have subeq : trialExpectation ps (fun k => f k - g k) =
      trialExpectation ps f - trialExpectation ps g := by
    simpa [sub_eq_add_neg] using trialExpectation_linear ps 1 (-1) f g
  rw [← subeq]
  exact (trialExpectation_mono ps hp bounds).trans_eq (trialExpectation_const ps B)

private theorem trialExpectation_lipschitz (n : ℕ) (a b : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1)
    (f : ℕ → ℝ) (h : ∀ k, |f (k+1)-f k| ≤ 1) :
    trialExpectation (List.replicate n a) f - trialExpectation (List.replicate n b) f ≤
      (n:ℝ)*|a-b| := by
  induction n generalizing f with
  | zero => simp [trialExpectation]
  | succ n ih =>
    have stepL (k : ℕ) : |trialStep a f (k+1)-trialStep a f k| ≤ 1 := by
      have expand : trialStep a f (k+1)-trialStep a f k =
          (1-a)*(f (k+1)-f k) + a*(f (k+2)-f (k+1)) := by simp only [trialStep]; ring
      rw [expand]
      calc
        _ ≤ |(1-a)*(f (k+1)-f k)| + |a*(f (k+2)-f (k+1))| := abs_add_le _ _
        _ ≤ (1-a)*1 + a*1 := by
          rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ha.2),abs_of_nonneg ha.1]
          exact add_le_add (mul_le_mul_of_nonneg_left (h k) (sub_nonneg.mpr ha.2))
            (mul_le_mul_of_nonneg_left (h (k+1)) ha.1)
        _ = 1 := by ring
    have δ (k : ℕ) : trialStep a f k-trialStep b f k ≤ |a-b| := by
      have eqv : trialStep a f k - trialStep b f k = (a-b)*(f (k+1)-f k) := by
        simp only [trialStep]
        ring
      rw [eqv]
      exact (le_abs_self _).trans (by rw [abs_mul]
                                      simpa using mul_le_mul_of_nonneg_left (h k) (abs_nonneg (a-b)))
    have htail : ∀ x ∈ List.replicate n b, x ∈ Set.Icc (0:ℝ) 1 := by
      intro x hx
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp hx
      exact hb
    have changed := trialExpectation_difference_le (List.replicate n b) htail
      (trialStep a f) (trialStep b f) _ δ
    have rest := ih _ stepL
    simp only [List.replicate_succ,trialExpectation,Nat.cast_add,Nat.cast_one]
    linarith

/-- A computable sufficient condition allows nonzero drift at a true arc:
the squared heterogeneity discount compensates the whole reference-mean mismatch. -/
theorem referenceArc_dominates_of_drift_budget (h g ell : ℕ) (p : Fin (h-1) → ℝ)
    (r e : ℝ) (he : 0 ≤ e) (hp : ∀ i, p i ∈ Set.Icc e (1-e)) (hr : r ∈ Set.Icc e (1-e))
    (hq : (ell:ℝ)/g ∈ Set.Icc 0 1) (hm : ∑ i, p i = ((h-1:ℕ):ℝ)*r)
    (hK : 0 < h*ell/g)
    (budget : ((h-1:ℕ):ℝ)*|r-(ell:ℝ)/g| ≤
      (((h-1-2).choose (h*ell/g-1)):ℝ)*e^(h-1-2) * (∑ i, (p i-r)^2)) :
    mean (productWeight (fun i => bernoulliWeight (p i)))
      (fun z => |(bitCount z:ℝ)-((h*ell/g:ℕ):ℝ)|) ≤ referenceArc h g ell := by
  let f := fun k : ℕ => |(k:ℝ)-((h*ell/g:ℕ):ℝ)|
  let q := (ell:ℝ)/g
  have hr' : r ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans he hr.1, by linarith [hr.2]⟩
  have hf (k : ℕ) : |f (k+1)-f k| ≤ 1 := by
    apply (abs_abs_sub_abs_le _ _).trans
    simp [Nat.cast_add,sub_sub_sub_cancel_right]
  have lip := trialExpectation_lipschitz (h-1) r q hr' hq f hf
  rw [← List.ofFn_const (h-1) r,← List.ofFn_const (h-1) q, ← product_eq_trialExpectation,
    ← product_eq_trialExpectation] at lip
  have disc := bernoulli_abs_heterogeneity_discount p r e (h*ell/g) he hp hr hm hK
  change mean _ (fun z => f (bitCount z)) ≤ mean (bernoulliVectorWeight q (h-1))
    (fun z => f (bitCount z))
  change mean (bernoulliVectorWeight r (h-1)) (fun z => f (bitCount z)) -
    mean (bernoulliVectorWeight q (h-1)) (fun z => f (bitCount z)) ≤ _ at lip
  change _ ≤ mean (bernoulliVectorWeight r (h-1)) (fun z => f (bitCount z)) -
    mean (productWeight (fun i => bernoulliWeight (p i))) (fun z => f (bitCount z)) at disc
  dsimp only [q] at *
  linarith

end Shellsort.JK
end
