import Shellsort.BernoulliCounts
import Shellsort.BalancedPhaseVariance

noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Arc-hit probability on the cyclic interval with residues 0,...,ell-1. -/
def canonicalArcProb (g ell m : ℕ) (t : ℝ) (s : ℕ) : ℝ :=
  mean (bernoulliVectorWeight t m) fun z => if (s+bitCount z)%g < ell then 1 else 0

def canonicalArcTrace (g ell m : ℕ) (t : ℝ) : ℝ :=
  ∑ s : Fin g, canonicalArcProb g ell m t s.val * (1-canonicalArcProb g ell m t s.val)

end Shellsort
end
