/-
Frozen stage-two review entry point. Build with `lake build Shellsort.Stage2`.
The original Shellsort.lean entry point remains the stage-one snapshot.

This file joins genuine sorting-state identities and explicit finite source-law
bounds. It does not assert the remaining uniform-permutation law bridge or an
end-to-end Shellsort cost theorem.
-/
import Shellsort
import Shellsort.GapSort
import Shellsort.ThresholdSort
import Shellsort.TagPosition
import Shellsort.TagThreshold
import Shellsort.SourceDecomposition
import Shellsort.ProductWeights
import Shellsort.ProductVariance
import Shellsort.CoprimePhase
import Shellsort.PrefixMean
import Shellsort.SourceVariance
import Shellsort.BernoulliCounts
import Shellsort.ConditionalSource
