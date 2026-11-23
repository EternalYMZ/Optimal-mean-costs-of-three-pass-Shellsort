# Two Fluctuation Lower Bounds

## 1. Lemma 3.1: An $L_1$ Displacement Lower Bound

**Lemma 3.1.** For $2\le h\le n$, $\mathbb E F(S_hA)\ge n\sqrt{nh}/1024$.

**Proof.** We consider two regimes. As before, the pivot is specified by its original position (see [First-Pass Estimates and the Two-Pass Displacement Theorem](02_First_Pass_Estimates_and_the_Two_Pass_Displacement_Theorem.md) §0), and we condition on its value $t$.

### 1.1 Regime One: $2h\le n$

**Bernoulli expansion of the displacement.** By (2.3), $D=b+\sum_j a_jB_j$, where the $B_j$ are independent Bernoulli$(t)$ variables (indicating whether each of the other keys is smaller), with coefficients

$$
a_j=\begin{cases}h-1,&j\text{ is another slot in the pivot's source chain},\\ -1,&j\text{ is outside the chain},\end{cases}\qquad b=\text{constant (source position)}.
$$

Write $S=\sum_j a_j^2$.

**Variance scale: $S\ge nh/12$.** The number of other slots in the source chain is $\ge\lfloor n/h\rfloor-1$. When $2h\le n<3h$, we have $\lfloor n/h\rfloor-1=1\ge n/(3h)$; when $n\ge3h$, we have $\lfloor n/h\rfloor-1\ge n/h-2\ge n/(3h)$. Thus the number of other slots is $\ge n/(3h)$, which, together with $(h-1)^2\ge h^2/4$ ($h\ge2$), gives

$$
S\ \ge\ \frac{n}{3h}\cdot\frac{h^2}4=\frac{nh}{12}. \tag{3.1}
$$

**Symmetrization and the fourth moment.** Take a conditionally independent, identically distributed copy $D'$, and put $W=D-D'=\sum_j a_jZ_j$, $Z_j=B_j-B_j'$. Then $\mathbb E Z_j=0$ and $\mathbb E Z_j^2=\mathbb E Z_j^4=2t(1-t)=:\sigma^2$ ($Z_j\in\{-1,0,1\}$, with each of $\pm1$ having probability $t(1-t)$). Write $v=\mathbb E W^2=\sigma^2S=2t(1-t)S$. The fourth-moment expansion has only two types of nonzero terms:

$$
\mathbb E W^4=\sigma^2\sum_j a_j^4+3\sigma^4\Big(S^2-\sum_j a_j^4\Big)\ \le\ 3v^2+\sigma^2\sum_j a_j^4.
$$

Since $a_j^4\le(h-1)^2a_j^2$ and $S\ge(h-1)^2(\lfloor n/h\rfloor-1)\ge(h-1)^2$ (the number of other slots is $\ge1$),

$$
\sum_j a_j^4\le(h-1)^2S\le S^2.
$$

On the central interval $t\in[1/4,3/4]$, we have $\sigma^2=2t(1-t)\ge3/8$, so $\sigma^2S^2\le\frac83\sigma^4S^2=\frac83v^2$. Combining these bounds gives

$$
\mathbb E W^4\ \le\ \Big(3+\frac83\Big)v^2=\frac{17}3v^2. \tag{3.2}
$$

**Lower bound on the first absolute moment.** Hölder's inequality and (3.2) give $\mathbb E|W|\ge v^{3/2}/\sqrt{(17/3)v^2}=\sqrt{3/17}\,\sqrt v$. On the central interval, $v\ge2\cdot\frac3{16}\cdot\frac{nh}{12}=\frac{nh}{32}$, and hence

$$
\mathbb E|W|\ \ge\ \sqrt{\tfrac3{17}}\cdot\sqrt{\tfrac{nh}{32}}\ \approx\ 0.074\sqrt{nh}.
$$

The triangle inequality $|W|\le|D|+|D'|$ gives $2\mathbb E|D|\ge\mathbb E|W|$. Integrating over $t$ on the central interval, whose length is $1/2$, then yields, for each key,

$$
\mathbb E|D|\ >\ \frac{\sqrt{nh}}{1024}.
$$

Summing over the $n$ keys proves the result in this regime.

### 1.2 Regime Two: $n<2h$ (Including $h=n$)

In this case, each key remains in its original residue class $b\bmod h$ after the first pass (permuting within a chain does not change the residue). For a key at a fixed original position, its global rank is uniform on $\{0,\dots,n-1\}$. Each residue class modulo $h$ contains at least one rank, so the probability that the rank lies in any specified residue class is $\ge1/n$.

The displacement is at least the circular distance between the position residue and the rank residue (the actual distance is at least the cyclic distance modulo $h$). From a fixed residue $b$, the sum of the circular distances to all $h$ residue classes is $\lfloor h^2/4\rfloor$. Therefore,

$$
\mathbb E|D|\ \ge\ \frac{\lfloor h^2/4\rfloor}{n}\ \ge\ \frac{h}{16}\ \ge\ \frac{\sqrt{nh}}{16\sqrt2}\ >\ \frac{\sqrt{nh}}{1024}.
$$

For the middle step, when $h\ge2$ we have $\lfloor h^2/4\rfloor\ge h^2/8$ (check $h=2,3$ directly; for $h\ge4$, use $h^2/4-1\ge h^2/8$), together with $n<2h$. The final step uses $\sqrt{nh}<\sqrt2\,h$. This argument also covers $h=n$ (the pass makes no changes, and $F(S_nA)=F(A)$). $\square$

## 2. Lemma 3.2: An Arc-Count Lower Bound

**Lemma 3.2.** Let $2\le g<h<n$, $\gcd(h,g)=1$, and $m=\lfloor n/h\rfloor$. Then the number of successful right shifts in the third pass satisfies

$$
\mathbb E M_3\ \ge\ \frac{ng}{25600}\sqrt{\frac hg\,\min\{g,\sqrt m\}}.
$$

**Proof.** We express the third-pass inversion count exactly as a sum of deviations of arc occupancy counts $U$ from deterministic benchmarks $K$, and then estimate the expected absolute value of each deviation.

### 2.1 The Arc-Count Identity

Fix a tagged key (with source chain $o$), and condition on $t$ and $Y_o=y$ (see [First-Pass Estimates and the Two-Pass Displacement Theorem](02_First_Pass_Estimates_and_the_Two_Pass_Displacement_Theorem.md) §2.1). In the second pass, the tagged key lies in chain $j=(o+hy)\bmod g$. Write $e_s=(s+hY_s)\bmod g$ for the endpoint phase of each source chain. For $1\le\ell<g$, take the arc

$$
H=\{(j+hv)\bmod g:\ 1\le v\le\ell\},\qquad j'=(j+h\ell)\bmod g,\qquad K=\lfloor h\ell/g\rfloor,
$$

and put $U=\sum_{s\ne o}\mathbf 1_{\{e_s\in H\}}$. Here $K$ is a deterministic integer determined by the gaps and the arc length; in general, it is not the conditional mean of $U$.

**(a) Inversions involving the tagged key and chain $j'$.** Before the second pass, let the number of keys in chain $b$ that are smaller than the tagged key be $N_b$. After the second pass, the tagged key lies in chain $j$ at slot $N_j$; the keys in chain $j'$ that are smaller than it occupy exactly the first $N_{j'}$ slots, while the number of slots in chain $j'$ preceding the tagged key's position is $N_j+\mathbf 1_{\{j'<j\}}$. The number of slots by which these two prefixes differ is precisely the associated inversion count:

$$
\big|N_j+\mathbf 1_{\{j'<j\}}-N_{j'}\big|.
$$

**(b) Telescoping.** Traverse the prefix $s,s+h,\dots,s+h(Y_s-1)$ of each source chain: the indicator of the arc $H$ changes on leaving $j$ by $+1$, and on leaving $j'$ by $-1$ (in the circular order with step $h$). Checking each source separately shows that the number of visits to $j$ minus the number of visits to $j'$ is $\mathbf 1_{\{e_s\in H\}}-\mathbf 1_{\{s\bmod g\in H\}}$. Summing over $s$ (note that $e_o=j\notin H$, so source $o$ contributes zero to $U$) gives

$$
N_j-N_{j'}=U-\#\{s<h:\ s\bmod g\in H\}.
$$

For the subtracted count, consider a step of size $h$ from $b$ to $b'=(b+h)\bmod g$: the number of source labels congruent to $b'$ is $(h+b-b')/g$. Summing over $\ell$ steps gives

$$
\#\{s<h:\ s\bmod g\in H\}=\frac{h\ell+j-j'}g=K+\mathbf 1_{\{j'<j\}}.
$$

Substituting into (a): the associated inversion count $=|U-K|$.

**(c) Summation.** Since $\gcd(h,g)=1$, the chain $j'$ runs, as $\ell=1,\dots,g-1$ varies, through all chains $\ne j$. Summing over all tagged keys and all arcs counts each third-pass inversion exactly twice (once at each endpoint):

$$
\boxed{\ 2M_3=\sum_{i=0}^{n-1}\sum_{\ell=0}^{g-1}\big|U_{i,\ell}-\lfloor h\ell/g\rfloor|\ }\tag{3.3}
$$

The $\ell=0$ term is zero. Equation (3.3) holds for every input.

This combinatorial counting structure originates in Janson–Knuth (1997, §1–2 and Lemma 1; see [Related Work and References](05_Related_Work_and_References.md)); equation (3.3) writes it in a symmetric form summed over both endpoints. We now use this structure to establish a fluctuation lower bound.

### 2.2 Fluctuations on the Circle

In standard circular coordinates, the arc is the contiguous interval $[0,\ell)$. Let $B\sim\mathrm{Bin}(m,t)$, and write

$$
p_v=\Pr\big((v+B)\bmod g<\ell\big),\qquad T_m=\sum_{v<g}p_v(1-p_v).
$$

**Monotonicity.** Adding one trial replaces $p_v$ by the mixture $(1-t)p_v+tp_{v+1}$. Since $p(1-p)$ is concave, summation gives $T_{m+1}\ge T_m$.

**Lower bound.** Write $r=\min(\ell,g-\ell)$, and let $t\in[1/4,3/4]$. For two independently translated arcs of equal length, the number of sites entering equals the number leaving; for independent $B,B'\sim\mathrm{Bin}(k,t)$ ($k\le m$), the expected number leaving is exactly $T_k$. When $|W|=|B-B'|\le r$, exactly $|W|$ sites leave.

If $r<4$, take $k=1$. Then $\mathbb E|W|=2t(1-t)\ge3/8$, so $T_m\ge T_1\ge3/8\ge\min(r,\sqrt m)/48$ (the right-hand side is $\le3/48$).

If $r\ge4$, take $k=\min(m,\lfloor r^2/16\rfloor)\ge1$. Put $v=2kt(1-t)=\mathbb EW^2$. The variable $W$ is a sum of $k$ independent $\{-1,0,1\}$-valued variables (all with coefficient $1$), and the fourth-moment expansion gives

$$
\mathbb EW^4\le v+3v^2.
$$

By Hölder's inequality, $\mathbb E|W|\ge v/\sqrt{1+3v}\ge\sqrt k/4$ (using $v\ge3k/8$, $k\ge1$, and the fact that the function $v/\sqrt{1+3v}$ is increasing). The truncation loss satisfies $\mathbb E[|W|\mathbf 1_{|W|>r}]\le\mathbb EW^2/r=v/r\le\sqrt k/8$ (using $v\le k/2$ and $k\le r^2/16$). Thus the expected number leaving satisfies

$$
T_k\ \ge\ \mathbb E[|W|\mathbf 1_{|W|\le r}]\ \ge\ \frac{\sqrt k}4-\frac{\sqrt k}8=\frac{\sqrt k}8.
$$

Moreover, $\sqrt k\ge\min(r,\sqrt m)/6$: this is immediate if $k=m$; otherwise, $k=\lfloor r^2/16\rfloor\ge r^2/32$ (for $r\ge4$, use $\lfloor x\rfloor\ge x/2$ for $x\ge1$), so $\sqrt k\ge r/\sqrt{32}>r/6$. By monotonicity,

$$
T_m\ \ge\ T_k\ \ge\ \frac{\min(r,\sqrt m)}{48}. \tag{3.4}
$$

### 2.3 A Variance Estimate for the Actual Source-Chain Lengths

The actual source phases are $e_s=(s+hY_s)\bmod g$. Multiplication by $h$ permutes the residues modulo $g$, so the sum of the variances over a complete set of $g$ source phases is exactly $T_m$ (by pulling the arc back to standard coordinates).

**Variance of a single phase: $\le T_m/2$.** For two independently translated arcs of equal length, a change in membership at a specified site must be accompanied by a second change elsewhere (the number entering equals the number leaving). The expected total number of sites whose membership changes is $2T_m$, so the probability of a change at any single site is $\le T_m$, that is, $p_v(1-p_v)\le T_m/2$.

**Variance lower bound.** The $h$ sources contain $\lfloor h/g\rfloor$ complete periods; remove the term for source $o$ (using its reference variance for length $m$, which is $\le T_m/2$). For sources of length $m+1$, conditioning on the extra trial retains at least $(1-t)$ times the variance for length $m$. Thus (removing the term before multiplying by $(1-t)$),

$$
\mathrm{Var}(U\mid t,y)\ \ge\ (1-t)\Big(\lfloor h/g\rfloor-\frac12\Big)T_m.
$$

Using $1-t\ge1/4$, $\lfloor x\rfloor-\frac12\ge x/4$ ($x\ge1$: when $x\ge2$, use $\lfloor x\rfloor\ge x-1$; when $1\le x<2$, the left-hand side $=1/2$), and (3.4), we obtain

$$
\mathrm{Var}(U\mid t,y)\ \ge\ \frac14\cdot\frac{h}{4g}\cdot\frac{\min(r,\sqrt m)}{48}=\frac{a}{768},\qquad a:=\frac hg\min\{r,\sqrt m\}. \tag{3.5}
$$

### 2.4 Poisson-Binomial Deviations

Conditioned on $(t,y)$, $U$ is a sum of independent Bernoulli variables. Write $V=\mathrm{Var}(U\mid t,y)$, and take an independent copy $U'$:

$$
\mathbb E(U-U')^2=2V,\qquad \mathbb E(U-U')^4\le2V+12V^2
$$

(each difference term $Z_i$ satisfies $\mathbb EZ_i^4=\mathbb EZ_i^2=\sigma_i^2$, with $\sum\sigma_i^2=2V$ and cross terms $3(\sum\sigma_i^2)^2$). By Hölder's inequality,

$$
\mathbb E|U-U'|\ \ge\ \frac{(2V)^{3/2}}{\sqrt{2V+12V^2}}=\frac{2V}{\sqrt{1+6V}}.
$$

For any deterministic $K$, the triangle inequality $2\mathbb E|U-K|\ge\mathbb E|U-U'|$ gives $\mathbb E|U-K|\ge V/\sqrt{1+6V}$. Since $a\ge1$ ($h>g$, $r\ge1$, $m\ge1$) and $V\ge a/768$, monotonicity of the function gives

$$
\mathbb E|U-K|\ \ge\ \frac{a/768}{\sqrt{1+a/128}}\ \ge\ \frac{\sqrt a}{800} \tag{3.6}
$$

(verification by squaring: $800^2a\ge768^2(1+a/128)$ holds for $a\ge1$).

**Removing the conditioning.** The right-hand side $\sqrt a/800$ of (3.6) depends only on $h,g,\ell,m$, not on $t,y$. Since, given $Y_o=y$, the conditional distribution of the pivot value $t$ is generally no longer uniform, we first sum over $y$, and then integrate over the original uniform variable $t$:

$$
\begin{aligned}
\mathbb E|U-K|
&=\int_0^1\sum_y\Pr(Y_o=y\mid t)\,\mathbb E\big(|U-K|\ \big|\ t,y\big)\,dt\\
&\ge\int_{1/4}^{3/4}\sum_y\Pr(Y_o=y\mid t)\,\frac{\sqrt a}{800}\,dt
=\frac12\cdot\frac{\sqrt a}{800}=\frac{\sqrt a}{1600}.
\end{aligned}
$$

The central half-interval contributes the factor $1/2$. This bound holds uniformly for every tagged key and every arc.

### 2.5 Combining the Constants

Take integer arc lengths $\ell$ in $[g/4,\,3g/4]$: there are at least $g/4$ such lengths, each satisfying $r=\min(\ell,g-\ell)\ge g/4$. Thus $\min(r,\sqrt m)\ge\min(g,\sqrt m)/4$, that is, $a\ge\frac hg\cdot\frac{\min(g,\sqrt m)}4$. Combining (3.3) with the preceding estimate after removing the conditioning gives

$$
2\,\mathbb EM_3\ \ge\ n\cdot\frac g4\cdot\frac1{1600}\cdot\frac12\sqrt{\frac hg\min\{g,\sqrt m\}},
$$

and dividing by $2$ yields

$$
\mathbb EM_3\ \ge\ \frac{ng}{25600}\sqrt{\frac hg\min\{g,\sqrt m\}}.
$$

$\square$

Next chapter: [Upper-Bound Construction and Four-Case Lower Bound](04_Upper_Bound_Construction_and_Four_Case_Lower_Bound.md).
