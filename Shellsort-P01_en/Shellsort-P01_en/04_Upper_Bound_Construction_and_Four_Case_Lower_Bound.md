# Upper-Bound Construction and Four-Case Lower Bound

This chapter completes the upper-bound construction and the lower-bound proof for Theorem A.

## 1. Upper Bound: A Gap Sequence Achieving $5n^{3/2}$

**Proof.** Let $n\ge16$, $s=\sqrt n$, and $q=\lfloor n^{1/4}\rfloor$, and take

$$
h=q^2+1,\qquad g=q.
$$

Admissibility follows from $q\ge2$; $q^2\le s<(q+1)^2\le4q^2$; $h=q^2+1\le s+1<n$; $h>g\ge2$; and $\gcd(q^2+1,q)=1$. We also have $2q\le q^2\le s$.

**First pass.** By (2.1) and $q^2>s/4$,

$$
\mathbb EM_1=\mathbb EI_h\le\frac{n^2}{4h}\le\frac{s^4}{4q^2}<\frac{s^4}{4\cdot(s/4)}=s^3.
$$

**Second pass.** By the first inequality in (1.9), $M_2\le\frac2gF(S_hA)$, and the coarse estimate in (2.2) (with coefficient $1/2$),

$$
\mathbb EM_2\le\frac2g\,\mathbb EF(S_hA)\le\frac2q\cdot n\Big(q^2+\frac12\sqrt{n(q^2+1)}\Big)=2s^2q+s^3\frac{\sqrt{q^2+1}}q.
$$

Using $2q\le s$ and $\sqrt{q^2+1}/q\le\sqrt5/2<5/4$ ($q\ge2$, and this ratio decreases with $q$), we obtain

$$
\mathbb EM_2\le\Big(1+\frac54\Big)s^3.
$$

**Third pass.** By the second inequality in (1.9), $M_3\le F(S_gS_hA)$, and Theorem B,

$$
\mathbb EM_3\le\mathbb EF(S_gS_hA)\le\frac12s^2(q-1)\sqrt{q^2+4}.
$$

Using $q-1\le q$, $\sqrt{q^2+4}\le3q/2$ (equivalently, $q^2\ge16/5$, which holds for $q\ge2$), and $q^2\le s$, we obtain

$$
\mathbb EM_3\le\frac12s^2\cdot q\cdot\frac{3q}2=\frac34s^2q^2\le\frac34s^3.
$$

**Total.** We have $\mathbb EM\le(1+\frac94+\frac34)s^3=4s^3$. The number of additional comparisons (equation (1.11)) is $\le3n=3s^2\le s^3$ ($s\ge4$). Hence

$$
\boxed{\ \mathbb EC\le5n^{3/2}\ }\qquad(n\ge16,\ \text{the same gap sequence}).
$$

$\square$

## 2. Lower Bound: $\mathbb EM\ge n^{3/2}/65536$ for Every Admissible Gap Sequence

**Proof.** Let the gap sequence $(h,g,1)$ satisfy $n>h>g\ge2$ and be fixed before the input is read. Write $s=\sqrt n$. We consider four cases.

### 2.1 Case One: $h^2\le n$

By (2.1) and $h\le s$,

$$
\mathbb EM\ge\mathbb EI_h\ge\frac{n^2}{4h}-\frac n4\ge\frac{s^3}4-\frac{s^2}4\ge\frac{s^3}8\qquad(s\ge2).
$$

### 2.2 Case Two: $g^2\le h$

By (1.10), for every input,

$$
F(S_hA)\ \le\ 2gM_2+2M_3\ \le\ 2gM.
$$

By Lemma 3.1 and $h\ge g^2$,

$$
\frac{n\sqrt{nh}}{1024}\le\mathbb EF(S_hA)\le2g\,\mathbb EM\ \Longrightarrow\ \mathbb EM\ge\frac{n\sqrt{nh}}{2048\,g}\ge\frac{n\sqrt{n g^2}}{2048\,g}=\frac{s^3}{2048}.
$$

### 2.3 Case Three: $d=\gcd(h,g)>1$

Both passes preserve the set of keys in each residue class modulo $d$. Within each residue class, matching ranks in sorted order to slots in sorted order minimizes displacement (the rearrangement inequality), so any state that preserves class membership satisfies

$$
F(S_gS_hA)\ \ge\ F(S_dA).
$$

For the third pass, apply the $k=1$ case of (1.8): $F(S_gS_hA)\le2I_1(S_gS_hA)=2M_3$, that is, $M_3\ge\frac12F(S_gS_hA)\ge\frac12F(S_dA)$. Applying Lemma 3.1 to $d$ ($2\le d\le g<n$) gives

$$
\mathbb EM\ge\mathbb EM_3\ge\frac12\,\mathbb EF(S_dA)\ge\frac{n\sqrt{nd}}{2048}\ge\frac{s^3}{2048}.
$$

### 2.4 Case Four: The Remaining Region $h^2>n$, $g^2>h$, $\gcd(h,g)=1$

Here $m=\lfloor n/h\rfloor\ge n/(2h)$ (since $\lfloor x\rfloor\ge x/2$ for $x\ge1$). There are two possibilities for the factor involving the square root in Lemma 3.2:

If $\min\{g,\sqrt m\}=g$, the factor $=g\sqrt h$. Since $g^2>h$ gives $g>\sqrt h$, we have $g\sqrt h>h>\sqrt n$ (using $h^2>n$).

If $\min\{g,\sqrt m\}=\sqrt m$, the factor $=\sqrt{gh}\,m^{1/4}\ge2^{-1/4}\sqrt g\,(nh)^{1/4}$. Since $g>\sqrt h$ gives $\sqrt g>h^{1/4}$,

$$
\sqrt g\,(nh)^{1/4}>h^{1/4}(nh)^{1/4}=(nh^2)^{1/4}>(n^2)^{1/4}=\sqrt n,
$$

and the factor $>2^{-1/4}\sqrt n>\sqrt n/2$.

Both possibilities establish $g\sqrt{\frac hg\min\{g,\sqrt m\}}>\sqrt n/2$. The right-hand side of Lemma 3.2 is exactly $\frac{n}{25600}\cdot g\sqrt{\frac hg\min\{g,\sqrt m\}}$, so

$$
\mathbb EM\ge\mathbb EM_3>\frac{n}{25600}\cdot\frac{\sqrt n}2=\frac{s^3}{51200}.
$$

### 2.5 A Uniform Constant and Small $n$

The smallest of the four case constants $\frac18,\ \frac1{2048},\ \frac1{2048},\ \frac1{51200}$ is $>\frac1{65536}$. Thus, for every admissible gap sequence,

$$
\mathbb EM\ \ge\ \frac{n^{3/2}}{65536}.
$$

For every input, $C\ge M$ (equation (1.11)), so the comparison count satisfies the same lower bound. The two minima in Theorem A are taken separately; the same gap sequence gives both upper bounds simultaneously, and the lower bound holds for every admissible gap sequence under both cost measures.

**Small sizes.** When $4\le n\le15$, the condition $h<n$ ensures that some $h$-chain has length $\ge2$, so $\mathbb EI_h=\frac14\sum L_s(L_s-1)\ge\frac12$; meanwhile, $n^{3/2}/65536\le15^{3/2}/65536<58.1/65536<1/2$. Thus the lower bound also holds. $\square$

For the related literature, see [Related Work and References](05_Related_Work_and_References.md).
