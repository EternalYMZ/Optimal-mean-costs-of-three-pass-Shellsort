# Project S paper and repository directory

Project S groups proofs by the paper whose mathematical question they address. Each paper has a permanent identifier (`P00`, `P01`, …). The repository name describes the subject in English, with words separated by hyphens. Its README and GitHub description start with `Project S · Pxx`. The established P01 URL also serves as the model for this convention. Identifiers survive title changes. If two papers merge, the older entries point to the paper that takes over the work.

As of 2026-11-21, P01 is public at the link below. The other entries reserve names. Their scope and evidence describe the local research record. Each is linked here when its first public version is available.

| Paper | Repository | Mathematical question and current coverage |
|---|---|---|
| P00 | `Chain-displacement-in-Shellsort` | How do chain inversions, chain displacement $F_k$, physical displacement, and right shifts relate in one pass? Lean covers these deterministic identities and inequalities. |
| P01 | [Three-pass-Shellsort-in-Lean](https://github.com/EternalYMZ/Three-pass-Shellsort-in-Lean) | What are the optimal mean shift and comparison counts for exactly three predetermined passes? The public Lean sources cover the natural upper-bound construction, the lower bound for every legal pair, and the two minima. |
| P02 | `Three-pass-Shellsort-inversion-error` | For coprime first gaps, how far is the expected final inversion count from the Janson–Knuth main term? The analytical argument bounds the absolute error. The one-sided result has a separate proof for $g=2$. Its generalization remains open. |
| P03 | `Four-pass-Shellsort-bounds` | Four-pass constructions and mean shift lower bounds. The analytical lower bound has a restricted gcd range. Lean covers component lemmas. The unrestricted exponent $25/18$ is a candidate. |
| P04 | `Optimal-mean-comparisons-in-Shellsort` | How many key comparisons suffice on uniform permutations when a gap table may depend on input length? Local Lean proofs cover the $\Theta(n\log n)$ optimal mean for ordinary Shellsort. Finding the table is charged separately in P09. |
| P05 | `Four-pass-Shellsort-reachability` | For the fixed table $(m,4,2,1)$, how does allowing independent choices of reachable keys in each slot change the last-pass cost? Analytical separation and finite checks. |
| P06 | `Two-stage-partition-sorting` | Optimize a predetermined first partition before a final full insertion sort. Analytical results and finite checks cover layouts and mean costs. |
| P07 | `Rank-informed-pair-sorting` | Compare predetermined and rank-informed choices of disjoint pairs before a final insertion pass. Analytical results and finite checks cover specified cost models. |
| P08 | `Shellsort-checkpoint-writes` | If every prescribed pass output must appear in the same array, how many record writes are necessary? Model A permits rank acquisition and cycle writes. The analytical running-time theorem takes the worst predetermined gap table. |
| P09 | `Shellsort-gap-table-generation` | How much planning does it take to produce a table with a target average cost, or to find all exact minimizers? Analytical planning bounds and local Lean lemmas. Cheap exact generation remains open. |
| P10 | `Two-large-gaps-in-Shellsort` | Which three-pass table minimizes mean comparisons when both initial gaps are at least $\lceil n/2\rceil$? Lean covers the exact cost formula and a restricted winner. The full $n\ge237$ result has an analytical argument. |
| P11 | `Rank-windows-in-Shellsort` | What discrepancies survive a short prefix under a movement budget? Analytical estimates give necessary conditions for a suffix. The broader exclusion claim is a candidate. |

Each public proof repository identifies its top-level statements, inputs, cost model, and replay commands. Shared lemmas may travel with a pinned paper release so readers can build it independently. Credit and audit entries refer to the originating declaration and revision. Analytical proofs, finite checks, and open extensions are identified at the level of each claim.
