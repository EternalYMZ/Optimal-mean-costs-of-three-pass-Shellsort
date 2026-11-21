/-
Frozen stage-three review entry point. Build with `lake build Shellsort.Stage3`.
The original Shellsort.lean and Stage2.lean entry points remain unchanged.

The new modules identify the actual fixed-position tagged state under a
uniform permutation with a Bernoulli-bit mixture. Grouping those bits into
the conditional source model, and actual insertion-cost bounds, remain to
be connected. This entry point asserts no end-to-end Shellsort cost theorem.
-/
import Shellsort.Stage2
import Shellsort.IntegerBeta
import Shellsort.FiberEquivalences
import Shellsort.TaggedFibers
import Shellsort.BernoulliMixture
import Shellsort.TaggedLaw
import Shellsort.SubsetBits
import Shellsort.TaggedBernoulli
