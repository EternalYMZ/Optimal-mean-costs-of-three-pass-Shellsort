import Shellsort.TaggedUpper
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Set

/-! Exact finite marginalization of original positions into one or two
gcd classes, retaining the original owner count outside the remaining product. -/
noncomputable section
namespace Shellsort.F09
open scoped BigOperators
open Set

def tagReducedOwner {n : ℕ} (d H : ℕ) (dp : 0<d) (hp : 0<H) (i : Fin n) : Fin H :=
  ⟨(i.val%(d*H))/d, (Nat.div_lt_iff_lt_mul dp).mpr (by simpa only [Nat.mul_comm H d] using Nat.mod_lt i.val (Nat.mul_pos dp hp))⟩

theorem phase_scaled_target (d G z c : ℕ) (gp : 0<G) (cp : c<d) :
    (d*z+c)%(d*G) = d*(z%G)+c := by
  have e : d*(z%G)+c < d*G := by
    have l := Nat.mul_le_mul_left d (show z%G+1 ≤ G from Nat.mod_lt _ gp)
    rw [Nat.mul_add,Nat.mul_one] at l; omega
  have l : c < d*G := by have := Nat.mul_le_mul_left d (show 1≤G from gp); omega
  rw [Nat.add_mod,Nat.mul_mod_mul_left,Nat.mod_eq_of_lt l,Nat.mod_eq_of_lt e]

def classEmb {d : ℕ} (H : ℕ) (c : Fin d) : Fin H ↪ Fin (d*H) where
  toFun s := ⟨d*s.val+c.val, by
    have a := Nat.mul_le_mul_left d (show s.val+1 ≤ H from s.isLt)
    rw [Nat.mul_add,Nat.mul_one] at a
    omega⟩
  inj' a b e := Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt c.isLt)
    (Nat.add_right_cancel (congrArg Fin.val e)))

def pairEmb {d : ℕ} (H : ℕ) (c r : Fin d) (hne : c ≠ r) : (Fin H ⊕ Fin H) ↪ Fin (d*H) where
  toFun := Sum.elim (classEmb H c) (classEmb H r)
  inj' := by
    have dis (a b : Fin H) : classEmb H c a ≠ classEmb H r b := by
      intro eq
      have v := congrArg (fun x : Fin (d*H) => x.val % d) eq
      change (d*a.val+c.val)%d = (d*b.val+r.val)%d at v
      simp only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt c.isLt,Nat.mod_eq_of_lt r.isLt] at v
      exact hne (Fin.ext v)
    rintro (a|a) (b|b) e
    · exact congrArg Sum.inl ((classEmb H c).injective e)
    · exact (dis _ _ e).elim
    · exact (dis _ _ e.symm).elim
    · exact congrArg Sum.inr ((classEmb H r).injective e)

def classRem (R d c : ℕ) := sourceTrialLength (R/d) (R%d) c

theorem classRem_le {R d H c : ℕ} (hR : R < d*H) : classRem R d c ≤ H := by
  have d0 : 0<d := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hR
  have lt : R/d < H := (Nat.div_lt_iff_lt_mul d0).2 (by simpa [Nat.mul_comm] using hR)
  unfold classRem sourceTrialLength
  split <;> omega

theorem classEmb_length {d : ℕ} (n H : ℕ) (c : Fin d) (s : Fin H) :
    sourceTrialLength (n/(d*H)) (n%(d*H)) (classEmb H c s).val =
    sourceTrialLength (n/(d*H)) (classRem (n%(d*H)) d c.val) s.val := by
  let R := n%(d*H)
  have d0 : 0 < d := Nat.zero_lt_of_lt c.isLt
  have q := Nat.mod_add_div R d
  have rem := Nat.mod_lt R d0
  have rule : d*s.val+c.val < R ↔ s.val < classRem R d c.val := by
    unfold classRem sourceTrialLength
    rcases lt_trichotomy s.val (R/d) with lt|eq|gt
    · have h := Nat.mul_le_mul_left d (show s.val+1 ≤ R/d from lt)
      rw [Nat.mul_succ] at h
      split <;> omega
    · rw [eq]; split <;> omega
    · have h := Nat.mul_le_mul_left d (show R/d+1 ≤ s.val from gt)
      rw [Nat.mul_succ] at h
      split <;> omega
  change (if d*s.val+c.val < R then _ else _) = (if s.val < classRem R d c.val then _ else _)
  simp only [rule]

private theorem mean_restrict_subtype {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (w : ∀ i, β i → ℝ) (ws : ∀ i, ∑ x, w i x = 1)
    (p : ι → Prop) [DecidablePred p] (F : (∀ i : Subtype p, β i.val) → ℝ) :
    mean (productWeight w) (fun z => F (fun s => z s.val)) =
      mean (productWeight (fun s : Subtype p => w s.val)) F := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p β
  let w1 := productWeight (fun s : Subtype p => w s.val)
  let w2 := productWeight (fun s : {s // ¬p s} => w s.val)
  have he := mean_transport_equiv e (productWeight w) (fun y => w1 y.1 * w2 y.2) (fun y => F y.1)
    (fun x => (Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (x i))).symm)
  change mean (productWeight w) (fun x => F (e x).1) = _
  rw [he]; unfold mean
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  have sum : ∑ y, w2 y = 1 := productWeight_sum _ (fun s => ws _)
  simp only [mul_right_comm (w1 x) _ (F x),← Finset.mul_sum,sum,mul_one,w1]

theorem product_embedding_mean {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {β : ι → Type*} [∀ i, Fintype (β i)] (w : ∀ i, β i → ℝ) (ws : ∀ i, ∑ x, w i x = 1)
    (e : κ ↪ ι) (F : (∀ s, β (e s)) → ℝ) :
    mean (productWeight w) (fun x => F (fun s => x (e s))) = mean (productWeight (fun s => w (e s))) F := by
  classical
  letI : Fintype (range e) := Subtype.fintype (fun i => i ∈ range e)
  let j := Equiv.ofInjective e e.injective
  let E := (Equiv.piCongrLeft (fun i : range e => β i.val) j).symm
  have eq := mean_restrict_subtype w ws (fun a => a ∈ range e) (fun x => F (E x))
  have re := mean_transport_equiv E (productWeight (fun i : range e => w i.val))
    (productWeight (fun i => w (e i))) F (fun x => by
      change (∏ i : range e,w i.val (x i)) = ∏ i, w (e i) (E x i)
      simp only [E,Equiv.piCongrLeft_symm_apply]
      exact (j.prod_comp (fun i => w i.val (x i))).symm)
  exact eq.trans re

theorem tagged_projected_mean {n h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (i : Fin n) (hh : 0<h)
    (t : ℝ) (e : κ ↪ Fin h) (L : κ → ℕ)
    (len : ∀ s, sourceTrialLength (n/h) (n%h) (e s).val = L s)
    (F : ℕ → (κ → ℕ) → ℝ) :
    let co := positionChainEquiv n h hh i
    mean (productWeight (fun _j : {j : Fin n // j ≠ i} => bernoulliWeight t))
      (fun x => let b := chainLowerCount ((omittedBitsSubsetEquiv i) x).val h
                F (b co.1.val) (fun s => b (e s).val)) =
    mean (sourceCoordinateWeight h (n/h) (n%h) t co.1) (fun a =>
      let y := ownerBitCount co.2 a
      mean (productWeight (fun s => bernoulliVectorWeight t (L s))) (fun z =>
        F y (fun s => if e s = co.1 then y else bitCount (z s)))) := by
  classical
  let co := positionChainEquiv n h hh i
  let m := n/h
  let R := n%h
  let w := sourceCoordinateWeight h m R t
  let f (a : Fin (sourceTrialLength m R co.1.val) → Bool)
      (x : ∀ s : Fin h, Fin (sourceTrialLength m R s.val) → Bool) :=
    F (ownerBitCount co.2 a) (fun s => if e s = co.1 then ownerBitCount co.2 a else bitCount (x (e s)))
  dsimp only
  rw [← bernoulli_mean_add_dummy i t]
  have point (z : Fin n → Bool) :
      F (chainLowerCount (fullBitsSubset i z) h co.1.val)
        (fun s => chainLowerCount (fullBitsSubset i z) h (e s).val) =
        f (chainBits hh z co.1) (chainBits hh z) := by
    have own := owner_fullBits_chain_count hh i z
    unfold f
    rw [show chainLowerCount (fullBitsSubset i z) h co.1.val = _ from own]
    congr 1
    funext s
    split_ifs with eq
    · rw [eq]; exact own
    · exact nonowner_fullBits_chain_count hh i z (e s) (fun er => eq (Fin.ext er))
  change mean _ (fun z => F (chainLowerCount (fullBitsSubset i z) h co.1.val)
    (fun s => chainLowerCount (fullBitsSubset i z) h (e s).val)) = _
  simp_rw [point]
  rw [fullBits_mean_chainBits n h hh t (fun x => f (x co.1) x)]
  change mean (productWeight w) (fun x => f (x co.1) x) = _
  rw [productWeight_owner_diagonal w co.1 (sourceCoordinateWeight_sum ..) f (by
    intro a x z agree
    unfold f; congr 1; funext s; split_ifs with h <;> first | rfl | rw [agree _ h])]
  apply Finset.sum_congr rfl; intro a _
  congr 1
  have len' : (fun s => sourceTrialLength m R (e s).val) = L := funext len
  subst L
  exact product_embedding_mean w (sourceCoordinateWeight_sum h m R t) e
    (fun z => F (ownerBitCount co.2 a) (fun s => if e s = co.1 then ownerBitCount co.2 a else bitCount (z s)))

end Shellsort.F09
end
