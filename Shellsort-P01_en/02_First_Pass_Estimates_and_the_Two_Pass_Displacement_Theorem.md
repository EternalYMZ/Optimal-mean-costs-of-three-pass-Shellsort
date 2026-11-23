# First-Pass Estimates and the Two-Pass Displacement Theorem

This chapter gives an estimate for the global displacement of a uniform random permutation after the first sorting pass, together with an upper bound on displacement after sorting with two coprime gaps.

## 0. Randomization Conventions

Generate the random input as follows: at the $n$ original positions $0,1,\dots,n-1$, place independent uniform random keys $X_0,\dots,X_{n-1}\sim U(0,1)$; replace key values by ranks when needed. Their relative order is a uniform random permutation.

Throughout the following argument, the pivot is specified by its original position. After fixing an original position as the pivot and conditioning on its key value being $t$, the indicators that the other keys are smaller than the pivot are mutually independent Bernoulli$(t)$ variables. If the pivot were specified by its global rank, the sum of these indicators would be fixed, and they would in general no longer be independent. All binomial distribution statements below are used under this convention of conditioning on a pivot specified by its original position.

Positions and ranks are indexed from $0$ throughout: positions are $x\in\{0,\dots,n-1\}$, a key's rank is the number of keys smaller than it, and its signed displacement is its position after sorting minus its rank.

## 1. Lemma 2.1: First-Pass Estimates

**Lemma 2.1.** Let $1\le h<n$, with $n=mh+r$ ($0\le r<h$), and let the chain lengths be $L_s=m+1$ ($s<r$) or $L_s=m$ ($s\ge r$). Then

$$
\frac{n^2}{4h}-\frac n4\ \le\ \mathbb E I_h(A)\ \le\ \frac{n^2}{4h}, \tag{2.1}
$$

$$
\mathbb E F(S_hA)\ \le\ A_h:=n\Big(h-1+\frac\pi8\sqrt{nh}\Big). \tag{2.2}
$$

**Proof.** We estimate the expected inversion count and the global displacement separately.

### 1.1 Expected Inversion Count (2.1)

Under a uniform random permutation, any pair of keys within the same chain forms an inversion with probability exactly $1/2$. Chain $s$ contains $\binom{L_s}2$ pairs, so

$$
\mathbb E I_h=\frac12\sum_s\binom{L_s}2=\frac14\sum_s L_s(L_s-1).
$$

By the Cauchy–Schwarz inequality, $\sum_s L_s^2\ge n^2/h$, hence $\mathbb E I_h\ge \frac14(n^2/h-n)$, giving the lower bound.

On the other hand, $L_s\le\lceil n/h\rceil$ implies $L_s-1\le n/h$, so $\sum_s L_s(L_s-1)\le \frac nh\sum_s L_s=\frac{n^2}h$, giving the upper bound.

### 1.2 Conditional Moments of a Single Key's Displacement

Fix the pivot's original position, suppose it lies in chain $s$ of length $L$, and condition on its key value being $t$. Let

$$
\begin{aligned}
U&=\#\{\text{keys in this chain smaller than the pivot}\}\sim\mathrm{Bin}(L-1,t),\\
V&=\#\{\text{keys outside this chain smaller than the pivot}\}\sim\mathrm{Bin}(n-L,t),
\end{aligned}
$$

which are independent conditional on $t$ under the convention in §0. After the first pass, the pivot occupies slot $U$ in its chain (indexed from $0$), so its new position is $s+hU$; its global rank is $U+V$. Its signed displacement is therefore

$$
D_h=(s+hU)-(U+V)=s+(h-1)U-V. \tag{2.3}
$$

**Conditional mean.** Write $e=s+h(L-1)$ for the last position in the chain. Then

$$
\mathbb E(D_h\mid t)=s+t\big[(h-1)(L-1)-(n-L)\big]=(1-t)s+t\big(e-(n-1)\big).
$$

This is a linear function of $t$, with endpoint values $s$ and $e-(n-1)$. Since $0\le s\le h-1$ and $e\in[n-h,\,n-1]$ (the last position in the chain is at most $h-1$ positions from the end of the array), both endpoint values lie in $[-(h-1),\,h-1]$. Hence

$$
\big|\mathbb E(D_h\mid t)\big|\le h-1\qquad(\forall t). \tag{2.4}
$$

**Conditional variance.** By independence,

$$
\mathrm{Var}(D_h\mid t)=t(1-t)\big[(h-1)^2(L-1)+(n-L)\big].
$$

The expression in brackets satisfies the identity

$$
(h-1)^2(L-1)+n-L=n-1+h(h-2)(L-1).
$$

Since the last position in the chain satisfies $e=s+h(L-1)\le n-1$, we have

$$
h(L-1)\ \le\ n-1. \tag{2.4a}
$$

Thus, when $h\ge2$,

$$
(h-1)^2(L-1)+(n-L)=n-1+(h-2)\,h(L-1)\ \le\ n-1+(h-2)(n-1)=(n-1)(h-1)\ \le\ nh,
$$

$$
\mathrm{Var}(D_h\mid t)\ \le\ (n-1)(h-1)\,t(1-t)\ \le\ nh\,t(1-t). \tag{2.5}
$$

When $h=1$, the displacement is identically $0$, and (2.2) also holds.

### 1.3 Integration Estimate

The inequality $\mathbb E|W|\le|\mathbb E W|+\mathbb E|W-\mathbb E W|\le|\mathbb E W|+\sqrt{\mathrm{Var}\,W}$, together with (2.4) and (2.5), gives

$$
\mathbb E(|D_h|\mid t)\le (h-1)+\sqrt{nh}\,\sqrt{t(1-t)}.
$$

Integrating over $t\sim U(0,1)$ and using

$$
\int_0^1\sqrt{t(1-t)}\,dt=\frac\pi8
$$

(the area of a semicircle of radius $1/2$), we obtain, for each key,

$$
\mathbb E|D_h|\le h-1+\frac\pi8\sqrt{nh}.
$$

Summing over the $n$ original positions proves (2.2). $\square$

**Remark.** By (2.5), $\sqrt{nh}$ in (2.2) may be replaced by $\sqrt{(n-1)(h-1)}$. Using $t(1-t)\le1/4$ before integrating instead gives the coarser upper bound with coefficient $1/2$.

## 2. Theorem B: Displacement After Two Passes with Coprime Gaps

**Theorem B.** Let $n>h>g\ge1$ and $\gcd(h,g)=1$. Then

$$
\mathbb E F(S_gS_hA)\ \le\ \frac{n(g-1)}2\sqrt{h+3}.
$$

**Proof.** When $g=1$, the second pass sorts the array completely, so $F=0$; henceforth assume $g\ge2$. Write $n=mh+r$, with $0\le r<h$.

### 2.1 Conditioning and an Exact Position Identity

Fix the pivot's original position (in chain $s_*$) and condition on its key value being $t$. Let $Y_s$ be the number of keys smaller than the pivot in original chain $s$ (excluding the pivot itself):

$$
Y_{s_*}\sim\mathrm{Bin}(L_{s_*}-1,t),\qquad Y_s\sim\mathrm{Bin}(L_s,t)\ (s\ne s_*),
$$

which are mutually independent conditional on $t$. Condition further on $Y_{s_*}=y$. After the first pass, the pivot is at position $s_*+hy$, so the $g$-chain containing it in the second pass is

$$
j=(s_*+hy)\bmod g. \tag{2.6}
$$

The remaining $Y_s$ ($s\ne s_*$) retain the independent binomial distributions specified above. All expectations and variances below are computed under this double conditioning; reference quantities are identified separately.

Define, for integers $b\ge0$,

$$
C_{j,s}(b)=\#\{0\le a<b:\ s+ha\equiv j\pmod g\},\qquad z_{j,s}(b)=g\,C_{j,s}(b)-b. \tag{2.7}
$$

After the first pass, the keys smaller than the pivot in chain $s$ occupy exactly the first $Y_s$ slots. Thus the number of keys smaller than the pivot in its $g$-chain is $\sum_s C_{j,s}(Y_s)$, its position after the second pass is $j+g\sum_s C_{j,s}(Y_s)$, and its global rank is $\sum_s Y_s$. Subtraction gives the identity, valid for every input,

$$
\boxed{\ D_{hg}=j+\sum_{s=0}^{h-1}z_{j,s}(Y_s).\ } \tag{2.8}
$$

### 2.2 Residual Intervals

Since $\gcd(h,g)=1$, for each $s$ there is a unique $a_s\in\{0,\dots,g-1\}$ such that $s+ha_s\equiv j\pmod g$. Write $b=ug+v$ ($0\le v<g$): each of the first $u$ complete periods contains exactly one hit, and the remaining segment contains a hit if and only if $v>a_s$. Hence

$$
C_{j,s}(b)=u+\mathbf 1_{\{v>a_s\}},\qquad z_{j,s}(b)=g\,\mathbf 1_{\{v>a_s\}}-v.
$$

It follows that

$$
-a_s\ \le\ z_{j,s}(b)\ \le\ g-1-a_s. \tag{2.9}
$$

This interval has width $g-1$. A random variable taking values in an interval of width $w$ has variance at most $w^2/4$: if $c$ is the midpoint of the interval, then $\mathrm{Var}\,W\le\mathbb E(W-c)^2\le w^2/4$. Thus each residual has variance at most $(g-1)^2/4$.

### 2.3 An Exact Identity for the Reference Mean

Introduce reference variables $Y_s^*\sim\mathrm{Bin}(L_s,t)$ for all chains (including $s_*$, for which the number of trials is one greater than in the actual pivot chain). These are used only to compute the sum of marginal expectations

$$
S_j(t)=\sum_{s=0}^{h-1}\mathbb E\,z_{j,s}(Y_s^*),
$$

where $j$ is fixed at its conditional value in (2.6). Define the discrepancy for a complete prefix by

$$
T_j(\ell)=g\,\#\{0\le a<\ell:\ a\equiv j\pmod g\}-\ell\qquad(\ell\ge0).
$$

Direct counting (write $\ell=ug+w$, so that $T_j=g\mathbf 1_{\{w>j\}}-w$) gives

$$
-j\ \le\ T_j(\ell)\ \le\ g-1-j. \tag{2.10}
$$

**Prefix identities.** For a common integer $b\ge0$, the position set $\{s+ha:\ 0\le s<h,\ 0\le a<b\}$ fills $[0,hb)$ exactly; taking one additional position for each $s<r$ fills $[0,hb+r)$ exactly. Hence

$$
\sum_{s=0}^{h-1}z_{j,s}(b)=T_j(hb), \tag{2.11a}
$$

$$
\sum_{s<r}z_{j,s}(b+1)+\sum_{s\ge r}z_{j,s}(b)=T_j(hb+r). \tag{2.11b}
$$

Let $W\sim\mathrm{Bin}(m,t)$ and $\xi\sim\mathrm{Bernoulli}(t)$ be independent. For each $s$, $W+\xi\mathbf 1_{\{s<r\}}$ has the same distribution as $Y_s^*$. By linearity of expectation (first rewrite $\sum_s\mathbb E$ as $\mathbb E\sum_s$, then condition on $\xi$), (2.11a) and (2.11b) give

$$
S_j(t)=(1-t)\,\mathbb E\,T_j(hW)+t\,\mathbb E\,T_j(hW+r). \tag{2.12}
$$

**Remark.** The common variables $W,\xi$ are used only to compute the sum of expectations; this step relies solely on the marginal distributions of the variables and on linearity of expectation. The variance calculation continues to use the conditionally independent actual counts from §2.1.

By (2.10), each term in (2.12) lies in $[-j,\,g-1-j]$, as does their convex combination:

$$
0\ \le\ j+S_j(t)\ \le\ g-1. \tag{2.13}
$$

### 2.4 Restoring the Pivot Chain: A One-Sided Correction $\delta$

By (2.6), the hit index for chain $s_*$ in (2.9) is $a_{s_*}=y\bmod g$. The argument of the actual residual is exactly $b=y$, so $v=y\bmod g=a_{s_*}$, which lies on the side where the indicator function is zero:

$$
z_{j,s_*}(y)=-a_{s_*}. \tag{2.14}
$$

This is precisely the lower endpoint of interval (2.9).
The reference expectation $\mathbb E\,z_{j,s_*}(Y_{s_*}^*)$ lies in the same interval. Thus the correction

$$
\delta=z_{j,s_*}(y)-\mathbb E\,z_{j,s_*}(Y_{s_*}^*)\quad\text{satisfies}\quad -(g-1)\le\delta\le0. \tag{2.15}
$$

By (2.8), the conditional mean is $j+\sum_{s\ne s_*}\mathbb E z_{j,s}(Y_s)+z_{j,s_*}(y)=j+S_j(t)+\delta$. Combining (2.13) and (2.15) gives

$$
\big|\mathbb E(D_{hg}\mid t,\,Y_{s_*}=y)\big|=|j+S_j(t)+\delta|\le g-1. \tag{2.16}
$$

(Upper bound: $j+S_j(t)\le g-1$ and $\delta\le0$; lower bound: $j+S_j(t)\ge0$ and $\delta\ge-(g-1)$.)

**Conditional variance.** The pivot-chain term in (2.8) is fixed by the conditioning; the remaining $h-1$ terms are independent, each with variance $\le(g-1)^2/4$ (§2.2):

$$
\mathrm{Var}(D_{hg}\mid t,\,Y_{s_*}=y)\ \le\ \frac{(h-1)(g-1)^2}{4}. \tag{2.17}
$$

**Second-moment estimate.** Since the second moment equals the variance plus the square of the mean,

$$
\mathbb E(D_{hg}^2\mid t,y)\le \frac{(h-1)(g-1)^2}4+(g-1)^2=\frac{(g-1)^2(h+3)}4.
$$

By Cauchy–Schwarz ($\mathbb E|D|\le\sqrt{\mathbb E D^2}$),

$$
\mathbb E(|D_{hg}|\mid t,y)\ \le\ \frac{g-1}2\sqrt{h+3}.
$$

This bound holds uniformly over the pivot's original position, $t\in(0,1)$, and all feasible $y$. Removing the conditioning and summing over the $n$ original positions gives

$$
\mathbb E F(S_gS_hA)\le \frac{n(g-1)}2\sqrt{h+3}.\qquad\square
$$

Next chapter: [Two Fluctuation Lower Bounds](03_Two_Fluctuation_Lower_Bounds.md).
