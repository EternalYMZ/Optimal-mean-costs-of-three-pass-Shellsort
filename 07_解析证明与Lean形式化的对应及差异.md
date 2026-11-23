# 附录 A 解析证明与 Lean 形式化的对应及差异

本附录说明正文与 Lean 形式化在定义、估计强度和证明方法上的对应与差异。

对应版本为 [Optimal-mean-costs-of-three-pass-Shellsort 仓库的固定提交 d2e146f81dc50e87b062088ebf3d514c4ece7040][repo]。以下沿用正文记号：$F$ 为全局位移，$F_k$ 为一次间隔 $k$ 排序的链内净位移，$I_k$ 为链内逆序数，$M_k$、$C_k$ 为该趟的成功右移数和键比较数；$M_2$、$M_3$ 在三趟表的讨论中分别表示第二、第三趟的成功右移数。

## A.1 主定理的对应

定理 A 的源码声明 [optimal_threePass_mean_bounds][lean-main] 分别对平均右移数和平均比较数取合法间隔表上的最小值，其中的条件 $n\ge16$ 以及常数 $65536$、$4$、$5$ 与正文相同。间隔表先于随机输入选定，两个目标分别取最小值。

定理 B 对应 [uniform_twoPass_footrule_bound][lean-two]。该声明只要求两个间隔为正且互素，适用范围包含正文的 $1\le g<h<n$。正文采用三趟算法所需的范围。

首趟位移估计的常数精化见 A.2；其余差异涉及定义的等价表达、初等化简、一般定理的特例以及证明方法。

## A.2 首趟位移估计的精细程度

正文式 (2.2) 给出

$$
\mathbb E F(S_hA)
\le
n\left(h-1+\frac{\pi}{8}\sqrt{nh}\right).
$$

Lean 声明 [uniform_onePass_footrule_bound][lean-first] 给出

$$
\mathbb E F(S_hA)
\le
n\left(h-1+\frac12\sqrt{nh}\right).
$$

由于 $\pi/8<1/2$，正文的解析估计更强。上述 Lean 声明给出 $1/2$ 版本，未包含 $\pi/8$ 精化。

定理 A 的上界推导只使用 $1/2$ 版本，因而平均右移数的常数 $4$ 和平均比较数的常数 $5$ 均不依赖这一精化。

## A.3 局部位移与比较成本的等价表达

### A.3.1 局部位移的定义

正文按每个键在一趟排序前后的实际位置定义

$$
F_k(A)
=
\frac1k\sum_x
\left|P_A(x)-P_{S_kA}(x)\right|.
$$

Lean 中的 [chainFootrule][lean-chain] 按各键的链内相对秩与原始链坐标之差求和。对 $k>0$，[gapSort_transport_eq_mul_chainFootrule][lean-chain] 证明实际位置距离之和恰为该量的 $k$ 倍。结合按键求和与按原始位置求和的换指标，两种定义相同。

夹逼 $I_k\le F_k\le2I_k$ 的两侧分别对应 [gapInversions_le_chainFootrule][lean-invchain] 与 [chainFootrule_le_twice_gapInsertionCost][lean-weighted]；后者再结合 [gapInsertionCost_eq_gapInversions][lean-cost] 得到右侧。

### A.3.2 比较开销的链长形式

正文在 $1\le k\le n$ 时写成

$$
I_k(A)\le C_k(A)\le I_k(A)+n-k.
$$

令 $L_s$ 为第 $s$ 条链的长度。Lean 的 [gapComparisonCost_upper_chains][lean-comparison] 采用链长形式

$$
C_k(A)
\le
M_k(A)+\sum_{s=0}^{k-1}(L_s-1).
$$

在正文范围内，每条链非空，且 [sum_actual_chain_lengths][lean-comparison] 给出 $\sum_sL_s=n$。因此

$$
\sum_{s=0}^{k-1}(L_s-1)=n-k.
$$

再结合 $M_k=I_k$ 和 [gapComparisonCost_lower][lean-comparison]，即得正文的比较夹逼。这是同一锐界的两种表达。仓库另有加 $n$ 的粗上界，用于更一般的正间隔范围。

## A.4 位移偿还式作为一般定理的特例

正文式 (1.8) 写出单趟关系

$$
F(A)\le2kI_k(A)+F(S_kA),
$$

并将它用于剩余两趟，得到式 (1.10)

$$
F(S_hA)\le2gM_2+2M_3.
$$

Lean 的 [footrule_le_wordShiftDistance][lean-weighted] 对任意正间隔序列证明加权偿还关系：初始位移不超过末态位移加上各趟“间隔乘以实际成功右移数”之和的两倍。每一趟成本均在该趟实际输入状态下计算。

对单趟使用这一关系，并代入 $M_k=I_k$，得到式 (1.8)。令 $B=S_hA$，对剩余间隔序列 $[g,1]$ 使用该关系；由于最后一趟将数组完全排好，末态位移为零，于是

$$
F(B)\le2(gM_2+M_3).
$$

因此，式 (1.10) 是该一般定理的直接特例。[threePass_checkpoint_transport][lean-checkpoint] 的证明使用这一锐式，然后将其放宽为总成本形式。正文由单趟关系逐次推导，Lean 形式化则通过一般的间隔序列统一表述。

## A.5 证明方法与求和记号

正文引理 1.1 用按秩递增就位的交换过程证明 $I\le F$，逐次计算逆序数与位移的减少量。Lean 的 [ordinaryInversions_le_footrule][lean-inversion] 采用计数收费证明。二者以不同方法证明同一不等式。

正文式 (3.3) 与 [two_mul_lastCost_eq_sum_taggedArc][lean-arc] 均对包含零长度圆弧的指标求和；零长度项的贡献为零。

[repo]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/tree/d2e146f81dc50e87b062088ebf3d514c4ece7040
[lean-main]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/ThreePassOptimalMean.lean
[lean-two]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/TaggedUpper.lean
[lean-first]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/FirstPassUpper.lean
[lean-chain]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/ChainTransport.lean
[lean-invchain]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/ChainInversionBound.lean
[lean-weighted]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/WordShiftDistance.lean
[lean-cost]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/GapInsertionBridge.lean
[lean-comparison]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/GapComparisonBridge.lean
[lean-checkpoint]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/AllGapThreePassLower.lean
[lean-inversion]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/InversionFootrule.lean
[lean-arc]: https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/d2e146f81dc50e87b062088ebf3d514c4ece7040/Shellsort/PivotArcCostBridge.lean
