/-
Frozen stage-four review entry point. Build with `lake build Shellsort.Stage4`.
Earlier review entry points are unchanged.

The actual uniform-permutation two-pass footrule upper bound is now connected
to the concrete local sorting operator. Actual insertion-cost inequalities and
unrestricted three-pass lower certificates are separate unfinished targets.
-/
import Shellsort.Stage3
import Shellsort.ChainCoordinates
import Shellsort.ChainBitCounts
import Shellsort.ProductTransport
import Shellsort.OwnerSlice
import Shellsort.TaggedDisplacement
import Shellsort.TaggedUpper
