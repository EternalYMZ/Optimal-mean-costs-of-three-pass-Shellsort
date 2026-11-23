# Cost and Displacement: Deterministic Lemmas

This chapter establishes combinatorial facts that do not depend on randomness. The conclusions below hold pointwise for every input permutation.

Positions and ranks are indexed from $0$ throughout.

- The input is a permutation of $\{0,1,\dots,n-1\}$, written $A=(A_0,\dots,A_{n-1})$, where $A_i$ is the rank of the key at position $i$.
- One pass of insertion sort with gap $k$: for each residue $s\in\{0,\dots,k-1\}$, apply ordinary insertion sort without a sentinel separately to the chain of positions $\equiv s \pmod k$. Denote the result by $S_kA$.
- $P_A(x)$: the position of the key of rank $x$ in $A$; $Q_{k,A}(x)=P_{S_kA}(x)$: its position after this gap-sorting pass.
- $I_k(A)$: the gap-$k$ inversion count, namely the number of pairs satisfying $i<j$, $i\equiv j\pmod k$, and $A_i>A_j$.
- $M_k(A)$: the number of successful right shifts in this pass; $C_k(A)$: the number of key comparisons in this pass, including a terminating unsuccessful comparison when one occurs.

## 1. Cost Identity and Bounds for Ordinary Insertion Sort

**Proposition 1.0.** Let $1\le k\le n$. For one pass of insertion sort with gap $k$, the following holds for every input:

$$
M_k(A)=I_k(A),\qquad I_k(A)\ \le\ C_k(A)\ \le\ I_k(A)+(n-k). \tag{1.1}
$$

**Proof.** When a key is inserted, each time it passes a larger predecessor within its chain, exactly one successful comparison and one right shift occur, and exactly one within-chain inversion is eliminated. Insertion sort sorts every chain, eliminating all within-chain inversions. Thus the total number of right shifts is $I_k(A)$.

Each insertion ends either with an unsuccessful comparison or by reaching the beginning of the chain. The first key in each chain requires no comparison; every other key contributes at most one unsuccessful comparison. Since $k\le n$, all $k$ chains are nonempty and contain $n$ keys in total, so the total number of unsuccessful comparisons is at most $n-k$. Every right shift is accompanied by a successful comparison, yielding $I_k(A)\le C_k(A)\le I_k(A)+n-k$. $\square$

## 2. Global and Local Footrule Displacement

$$
F(A)=\sum_{x=0}^{n-1}|P_A(x)-x|,\qquad
F_k(A)=\frac1k\sum_{x=0}^{n-1}\big|P_A(x)-Q_{k,A}(x)\big|. \tag{1.2}
$$

$F(A)$ measures the global net displacement of the current state relative to the fully sorted state. $F_k(A)$ measures the sum, over all keys, of their net changes in position along their respective chains during one $k$-sorting pass; division by $k$ converts distances in the original array into numbers of positions within a chain. These quantities measure net displacement; the total distance traveled by an individual key may be greater (see the remark in §4).

In particular, $S_1A$ is the sorted array and $Q_{1,A}(x)=x$, so

$$
F_1(A)=F(A). \tag{1.3}
$$

## 3. A One-Sided Diaconis–Graham Inequality

**Lemma 1.1.** For any permutation $\pi$ of length $L$, its inversion count $I(\pi)$ and global positional distance $F(\pi)=\sum_x|P_x-x|$ satisfy

$$
I(\pi)\ \le\ F(\pi).
$$

This lemma is a consequence of the left-hand side of the classical Diaconis–Graham inequality $I+T\le F\le 2I$, where $T$ is the minimum number of arbitrary transpositions required to transform the permutation into the sorted permutation ([DG77, Theorem 2](05_Related_Work_and_References.md)).

**Proof.** Starting from $\pi$, move each key to its final position by a swap, proceeding in rank order $i=0,1,\dots,L-1$. When rank $i$ is processed, ranks $0,\dots,i-1$ are already in place at positions $0,\dots,i-1$, so the current position $j$ of rank $i$ satisfies $j\ge i$; if $j=i$, no swap is needed. Otherwise, position $i$ contains a key of some rank $v>i$. Swap the two keys at positions $i$ and $j$.

**(a) Change in the footrule.** Before the swap, rank $i$ is at position $j$ and contributes $j-i$; rank $v$ is at position $i$ and contributes $v-i$. After the swap, rank $i$ is in place (contributing $0$), and rank $v$ is at position $j$ (contributing $|j-v|$). All other keys remain fixed. Hence

$$
\Delta F=(j-i)+(v-i)-|j-v|=2\min(j-i,\ v-i)\ \ge\ 2,
$$

using the identity $a+b-|a-b|=2\min(a,b)$ ($a=j-i\ge1$, $b=v-i\ge1$).

**(b) Change in the inversion count.** The swap changes the left-to-right order only of key pairs with at least one endpoint at position $i$ or $j$. We examine the cases in turn:

- **The two swapped keys $(v,i)$**: before the swap, $v$ is on the left and $v>i$, so the pair is an inversion; after the swap, $i$ is on the left and $i<v$, so it is not an inversion. The net decrease is $1$.
- **A key $w=A_r$ at an intermediate position $r$ ($i<r<j$)**. The two pairs involving $w$ are:
  - The pair $(v,w)$: before the swap, $v$ is at position $i$ (to the left of $w$), and the pair is an inversion if and only if $v>w$; after the swap, $v$ is at position $j$ (to the right of $w$), and the pair is an inversion if and only if $w>v$. Thus, when $w<v$, this pair changes from an inversion to a non-inversion ($-1$); when $w>v$, it changes from a non-inversion to an inversion ($+1$).
  - The pair $(w,i)$: before the swap, $i$ is at position $j$ (to the right of $w$), and the pair is an inversion if and only if $w>i$; after the swap, $i$ is at position $i$ (to the left of $w$), and the pair is an inversion if and only if $i>w$. Thus, when $w>i$, this pair changes from an inversion to a non-inversion ($-1$); when $w<i$, it changes from a non-inversion to an inversion ($+1$).

  Combining the three possible order relations gives the following table:

  | Range of $w$ | Change in $(v,w)$ | Change in $(w,i)$ | Net change |
  |---|---|---|---|
  | $w<i$ | $-1$ | $+1$ | $0$ |
  | $i<w<v$ | $-1$ | $-1$ | $-2$ |
  | $w>v$ | $+1$ | $-1$ | $0$ |

- **All other key pairs are unchanged**: both the left-to-right order and the values of two intermediate keys remain unchanged; keys at positions $<i$ have ranks $<i$ and remain to the left of, and smaller than, both swapped keys, so they form no inversion with either key before or after the swap; keys at positions $>j$ remain to the right of both swapped keys, so their left-to-right order is unchanged, and their inversion status depends only on the comparison of values and is therefore unchanged as well.

In total,

$$
\Delta I=1+2\,\#\{r:\ i<r<j,\ i<A_r<v\}.
$$

**(c) Comparison of the two changes.** There are $j-i-1$ intermediate positions, so the count is $\le j-i-1$; there are at most $v-i-1$ ranks in the open interval $(i,v)$, so the count is also $\le v-i-1$. Therefore

$$
\Delta I\ \le\ 1+2\big(\min(j-i,v-i)-1\big)=2\min(j-i,v-i)-1\ <\ \Delta F.
$$

At each swap, the decrease in $I$ is strictly smaller than the decrease in $F$. The procedure terminates at the identity permutation, where $I=F=0$; summing the decreases over all steps gives $I(\pi)\le F(\pi)$ for the initial permutation. $\square$

## 4. Two-Sided Bounds for Local Displacement

**Lemma 1.2 (Local footrule bounds).** For any permutation $A$ and $1\le k\le n$,

$$
\boxed{\ I_k(A)\ \le\ F_k(A)\ \le\ 2\,I_k(A).\ } \tag{1.4}
$$

**Proof.** For the left-hand inequality, fix a residue $s$; the positions in its chain are $s,s+k,s+2k,\dots$. Relabel the positions within the chain as $0,1,\dots,L_s-1$ (subtract $s$ from the actual position and divide by $k$), and replace the key values by their relative ranks within this chain. This gives an ordinary permutation: its inversion count is exactly the original inversion count of the chain; the sum of the keys' net changes in position before and after sorting, measured in positions within the chain, is precisely this chain's contribution to $F_k(A)$ (an actual distance of $k$ corresponds to a distance of $1$ within the chain). Applying Lemma 1.1 to each chain and summing gives $I_k\le F_k$.

For the right-hand inequality, a pass of insertion sort within the chains can be decomposed into exactly $I_k(A)$ swaps of adjacent inverted pairs within chains (each swap eliminates exactly one inversion; see Proposition 1.0). Each swap moves two keys through an actual distance of $k$ each, so the total distance traveled by all keys is exactly $2k\,I_k(A)$. The net displacement of each key from its starting position to its final position is at most its own total distance traveled. The triangle inequality therefore gives

$$
k\,F_k(A)=\sum_x\big|P_A(x)-Q_{k,A}(x)\big|\ \le\ 2k\,I_k(A),
$$

and canceling $k$ yields $F_k\le2I_k$. $\square$

**Remark.** Sorting the permutation $(2,1,0)$ with gap $1$ gives $F_1=2+0+2=4$ and $I_1=3$, whereas the total distance traveled is $2I_1=6$. The middle key participates in two inversions but has zero net displacement.

## 5. Monotonicity of the Global Footrule and Transfer Between Passes

**Lemma 1.3 (Global footrule does not increase under chain sorting).** For every $1\le k\le n$,

$$
F(S_kA)\ \le\ F(A). \tag{1.5}
$$

**Proof.** Decompose chain sorting into swaps of adjacent inverted pairs within chains. A swap moves the larger key (of rank $a$) from position $i$ to $j$ and the smaller key (of rank $b<a$) from $j$ to $i<j$. The rearrangement inequality for absolute distances on the real line ($a>b$, $i<j$) gives

$$
|a-i|+|b-j|\ \ge\ |a-j|+|b-i|.
$$

Thus each swap leaves $F$ unchanged or decreases it, and successive application proves the claim. $\square$

**Remark.** The distance of an individual key from its target can increase. For example, when the first insertion in the permutation $(3,2,1,0)$ swaps the two leftmost keys, rank $2$ moves from position $1$ to position $0$, increasing its distance from its target position $2$ from $1$ to $2$; the sum of the two keys' distances nevertheless does not increase.

**Lemma 1.4 (Transfer between passes).** For every $1\le k\le n$,

$$
\big|F(A)-F(S_kA)\big|\ \le\ k\,F_k(A)\ \le\ F(A)+F(S_kA). \tag{1.6}
$$

**Proof.** Apply the reverse triangle inequality $\big||P_A(x)-x|-|Q_{k,A}(x)-x|\big|\le|P_A(x)-Q_{k,A}(x)|$ to each key and sum to obtain the left-hand inequality; apply the triangle inequality $|P_A(x)-Q_{k,A}(x)|\le|P_A(x)-x|+|x-Q_{k,A}(x)|$ to each key and sum to obtain the right-hand inequality. $\square$

**Corollary.** Substituting Lemmas 1.2 and 1.3 into (1.6) gives

$$
\boxed{\ I_k(A)\ \le\ F_k(A)\ \le\ \frac{F(A)+F(S_kA)}{k}\ \le\ \frac{2F(A)}{k},\ } \tag{1.7}
$$

$$
\boxed{\ F(A)\ \le\ 2k\,I_k(A)+F(S_kA).\ } \tag{1.8}
$$

Equation (1.7) bounds the right-shift cost of the next sorting pass in terms of the current global displacement. Equation (1.8) controls the reduction in global displacement attainable in a single sorting pass; it follows from $F(A)-F(S_kA)\le kF_k\le2kI_k$.

## 6. Immediate Consequences for Three-Pass Shellsort

Consider the gap sequence $(h,g,1)$, with $n>h>g\ge2$; write $B=S_hA$ and $D=S_gB$, let $M_1,M_2,M_3$ be the numbers of successful right shifts in the three passes, let $M$ be their total, and let $C$ be the total number of comparisons.

**Cost upper bounds.** By (1.7), (1.3), and Proposition 1.0,

$$
M_2=I_g(B)\ \le\ F_g(B)\ \le\ \frac2g\,F(B),\qquad
M_3=I_1(D)\ \le\ F_1(D)=F(D). \tag{1.9}
$$

**Displacement–cost inequality.** Apply (1.8) first to the $g$-sorting pass on $B$ and then to the $1$-sorting pass on $D$, noting that $F(S_1D)=0$:

$$
F(B)\le2g\,I_g(B)+F(D)=2gM_2+F(D),\qquad F(D)\le2\,I_1(D)+0=2M_3,
$$

$$
\boxed{\ F(S_hA)\ \le\ 2g\,M_2+2M_3.\ } \tag{1.10}
$$

**Comparisons and right shifts.** Applying Proposition 1.0 separately to the three passes (the third pass has $k=1$, with the number of unsuccessful comparisons $\le n-1$) gives

$$
M\ \le\ C\ \le\ M+(n-h)+(n-g)+(n-1)\ \le\ M+3n. \tag{1.11}
$$

Also, $M=I_h(A)+I_g(S_hA)+I_1(S_gS_hA)$.

For the correspondence with and differences from the Lean formalization, see [Appendix A](06_Analytic_Proof_and_Lean_Formalization.md).

Next chapter: [First-Pass Estimates and the Two-Pass Displacement Theorem](02_First_Pass_Estimates_and_the_Two_Pass_Displacement_Theorem.md).
