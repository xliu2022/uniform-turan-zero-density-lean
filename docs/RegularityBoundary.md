# Claim 3.4、强正则性与主定理的完成边界

本文按 [Li–Liu, arXiv:2611.06964](https://arxiv.org/abs/2611.06964) 第 3 节、特别是纸面页 7–11 的定义、Theorem 3.1、Lemmas 3.2–3.3 和 Claim 3.4 记录实际证明链及其适用范围。`StrongRegularity/RegularityConstruction.lean` 已证明所需的强正则分割存在性；`Main.lean` 的 `paperMainTheorem` 及两个显式推论已经实际编译通过，无额外未证明的数学前提。完整源码重建和公理审计的最终结果以工程的验证日志为准，本页不预填模块数或声明数。

## 1. 已闭合的有限概率部分

`FiniteRamsey.lean` 和 `Probability/LawHomogenization.lean` 已证明 Claim 3.5 所需的一般有限 Ramsey 同质化以及从有限模型到 spreadable 模型的推导。`LawCompactness.lean` 给出有限维分布的共同收敛子列，并证明一致性、整组向量的相互独立性、禁图概率为零和边概率下界在极限中保持。因此 Claim 3.5 不再以“存在 spreadable 模型”为假设，也不依赖未经形式化的 Kolmogorov 扩张步骤。这里的 `SpreadableLaw` 是具有精确限制一致性的有限维分布族；工程没有另外构造无限超图样本空间上的一个概率测度。

Claim 3.4 的以下纯有限概率、计数和不等式部分也已证明：

| 论文中的作用 | 已有模块和关键结论 | 已由实际分割与后续证明提供的输入 |
|---|---|---|
| 高层标签独立生成边 | `HighFaceGenerator.law_shadowIndependent` | 从递归地址构造出的边规则确实只依赖该边内部的高层面标签 |
| 大部分完成地址的密度不低 | `RetentionBounds.expected_density_ge_of_near_uniform_weights` | 完成地址划分低层地址、低层地址密度至少 `7d/8`、完成大小近等 |
| 加权不规则质量转成不规则地址概率 | `RetentionBounds.irregularity_probability_le_of_near_uniform_weights` | 全局加权不规则质量至多 `σ`，所有完成地址大小在同一 `1 ± μ` 区间内 |
| 真正选择 `M` 个簇及低层标签 | `ClusterAveraging.exists_clusters_and_lower_labels_of_weighted_irregularity` | 上一行的几何输入，以及 `16σ binom(M,r)/d < 1/2` |
| 保留边概率至少 `d/2` | `RetentionBounds.retention_probability_ge_half` | 平均密度至少 `3d/4`，不规则完成概率至多 `d/8`，阈值 `d/8` |
| 点态禁图变成分布禁图 | `HighFaceGenerator.law_avoids_of_isFree` | `RetainedModel` 已证明每个完成标签实现均为 `F`-free |

最后一行所需的实际证明现已完成：`RetainedModel.isFree_retainedConfiguration` 从任意保留图副本抽取真实正则 complex，并调用已证明的 Lemma 3.3 得到宿主副本，导出矛盾；`retainedAddressLaw_avoids` 随后把点态禁图性转成分布禁图性。禁图结论没有被放进输入结构的字段。

## 2. 必须准确表示的分割、地址与正则性

### 2.1 簇和 crossing 集合

需要一组两两不交、覆盖宿主顶点集的簇 `V₁,…,V_t`，且每个簇大小为同一个正整数 `m`。Crossing 集合在每个簇中至多取一个顶点。若簇指标集 `J` 的大小为 `u`，则在这些簇中各取一个顶点得到的 crossing `u` 集合共有 `m^u` 个。

`UHypergraph` 是单一一致度的有限边集。实际的 `LabelSystem` 和 `PartitionState` 在此基础上记录不同一致度的层、簇限制、crossing clique 集以及有限划分的覆盖和两两不交性质。这里的超图层级分割包含这些额外数据与已证关系，不能用普通图的顶点划分替代。

`Regularity/CrossingTuples.lean` 现已证明 dependent crossing tuples 与无序 crossing 集的实际双射，保持簇指标集、限制映射和精确基数。`TupleComplex.lean` 的 `tupleGraph`、`boundaryGraph` 以及 `CliqueCounting.lean` 的 `layerGraph` 都由实际 cell 边集构造；不是带有计数结论的抽象占位结构。

`Regularity/RelativeRegularity.lean` 现已定义真正的 `crossingHost`：用顶点到簇指标的映射在一个边集上单射来表达 crossing。其 `cliqueRegion allowed B` 将普通 `cliqueSet` 与显式允许域相交。这一点在 `ℓ = 2` 必须保留：一元 polyad 的普通二元 clique 集本身仍包含同簇顶点对，不能直接当作 crossing clique 集。

### 2.2 Polyad 和分层单元

对 `|S| = ℓ` 的簇指标集，先在每个 `(ℓ−1)` 子集 `T ⊆ S` 上选取一个已经定义的分割单元 `P_T`，令 `B_S` 为这些单元的并。在 `K_ℓ(B_S)` 非空时，将它划分为恰好 `a_ℓ` 个非空单元，以 `1,…,a_ℓ` 编号。

标签只在已经确定的 polyad 内有意义。两个不同 polyad 中的相同整数标签不表示同一个单元。实现保留了这一依赖关系：`P_S` 由 `S`、其真子集上已经选好的类和当前标签共同确定。

`AddressSystem.lean` 与 `AddressGenerator.lean` 已证明以下实际有限结构接口：

- 分割单元的边集确实包含于对应低一层 polyad 的 clique 集。
- 对每个 crossing 集合，其所属地址唯一。
- 固定低层地址后，所有完成地址的集合 `C(ω)` 两两不交并覆盖 `C(α)`。
- 全局地址限制到较小的簇指标集，与在该指标集上单独递归计算地址一致。
- `P_S` 及其上层边规则只依赖 `S` 内部的标签。`configuration_carrierRule` 和 `uniformAddressLaw_shadowIndependent` 已由这一局部性推出真实地址生成器的高层独立性。

### 2.3 所有标签选择都必须可用

独立均匀取标签 `ξ_S ∈ Fin(a_|S|)` 之前，要证明每一步实际存在全部 `a_|S|` 个可选单元。仅对已经存在的地址声明正则性不够，因为随机乘积空间还包括所有标签组合。

论文用 dense counting 的正下界解决这一点：一个已选低层地址形成正则 complex，其 clique 集大小至少为

\[
(1-\mu)m^u\prod_{\ell=2}^{h}a_\ell^{-\binom u\ell}>0.
\]

对于 `h = 1`，直接使用精确值 `m^u`。因此每个下一层 polyad 都非空，可以继续选择任何标签。这个递归合法性证明现已完成：`AddressCounting.addressClass_nonempty_of_lowRegular` 对地址高度作强归纳，先证明下一层所需 polyad 非空，再应用只对非空 polyad 要求正则性的 `LowRegular`。它没有把任意 raw 地址非空作为输入字段。`addressClass_card_bounds` 随后给出真实地址类的双边大小界，`uniformTolerance` 的有限最小值同时处理所有 `u ≤ M` 和所需高度。

### 2.4 正则性的测试对象

论文的 `(δ,d,R)` 正则性是：对至多 `R` 个子 polyad 的 clique 集之并 `U`，只要 `|U| ≥ δ |K_ℓ(B)|`，就有

\[
\left|\frac{|A\cap U|}{|U|}-d\right|\le\delta.
\]

这里不是只测试单个子 polyad，也不是只测试顶点子集形成的笛卡尔积。低层 complex 正则性使用 `R = 1`，顶层嵌入使用多测试参数 `R`。

这一多测试定义现已在 `Regularity.IsRegular` 中实现。参数范围 `2 ≤ ℓ`、`0 < δ ≤ 1`、`d ∈ [0,1]`、`1 ≤ R`，非空的基底 clique 集，以及顶层边集包含于该 clique 集，都是明确的定义条件；`testUnion` 的输入是真正的有限子 polyad 族。

所需参数单调性也已证明：在合法参数范围内，若 `δ ≤ δ'` 且 `R' ≤ R`，则 `(δ,d,R)` 正则性推出 `(δ',d,R')` 正则性。应用中分别用它处理 `ε(a) ≤ ε₀` 和 `σ ≤ σ₀, R(a) ≥ R₀`。模块还证明全 polyad 的单测试给出实际密度与 `d` 的偏差至多 `δ`、所有有效测试都非空，以及实际密度为零或一时的空/满边界情形。`restrictToCliques` 允许从一般宿主截取一个 polyad 上的真实顶层图，并保持其局部密度。这些定义层引理本身不承担存在性结论；实际的 regularity、counting 和 embedding 证明分别在下述模块中给出。

## 3. 三个真正的正则性定理

### Theorem 3.1：强超图正则分割

其量词顺序必须保持为：给定 `s ≥ k ≥ 2`、`0 < σ ≤ 1`、函数 `ε(a) ∈ (0,1]` 和 `R(a) ∈ ℕ`，先得到统一的 `T,n₀`；随后对满足大小与整除条件的任意宿主和指定初始等分割，得到某个参数向量 `a = (t,a₂,…,a_{k−1})` 和整个层级分割。

输出包括：

1. 簇划分细化初始 `s` 类分割，`s ≤ t ≤ T`，各簇大小为 `n/t`，每个 `a_ℓ` 为正且至多 `T`。
2. 每个低层单元对其对应 polyad 都是 `(ε(a),1/a_ℓ)` 正则的。
3. 按 **crossing `k` 集合的个数加权**，至多 `σ` 的质量落入顶层不规则 polyad。

第三项不是“不规则 polyad 的个数比例至多 `σ`”。从加权质量到地址个数比例的转换使用 counting 给出的近等权重。`AddressSelection.lean` 已从实际地址分割证明加权期望等于实际坏 crossing 集合的质量，`FiniteModelConstruction.lean` 将其与 `RetentionBounds` 的不等式完整连接。

**Claim 3.4 所需的真实分割存在性现已证明。** `StrongRegularity.partitionExistence` 的结论就是 `Statement.lean` 中的 `PartitionExistence r`：先选统一 `T,n₀`，再对任意满足 `s T! ∣ n` 的充分大宿主，构造实际等大簇、完整低层标签系统、实际 `LowRegular` 和按 crossing 集合计数的坏质量界。该公开接口没有额外输入一个指定初始分割。内部更强的 `RegularityLemma r` 接受一个满足所选低层容忍度的实际初始 hierarchy，并保留其 exact refinement；本文将这一接口与纸面的指定初始分割表述区分记录，不声称已逐一形式化外部论文的所有加强版。

证明由以下实际有限构造闭合：

| 步骤 | 模块与已证明的声明 | 实际作用 |
|---|---|---|
| 图基例 | `GraphBaseCase.regularityLemma_two` | 多色、等大簇、实际初始划分细化及任意参数函数给出的测试数 |
| 固定复杂度的初始增长 | `InitialGrowthConstruction.initialGrowth_of_one_le` | `T` 先于输出容忍度选择，逐层继承旧 crossing cells 或真实随机分割旧 noncrossing 区域 |
| 两次 regularity 调用 | `ApproximationIterationBounds.exists_two_scale_regular_partitions` | 实际 coarse/fine hierarchies、足够多的 coarse 测试、真实 counting 体积与 slicing 尾界 |
| Regular approximation | `ApproximationConstruction.approximationLemma_of_regularityLemma` | 实际逐 polyad 修复、保持旧 cell decoder、逐色编辑界及每个 polyad 上的 perfect regularity |
| 等密度单元归一化 | `NormalizationConstruction.equitableNormalization_of_approximation` | 两轮真实 slicing、完整顶层划分、旧 hierarchy 的 exact refinement 及 repaired 观察的坏质量界 |
| 一致度归纳步 | `UniformPumping.regularityLemma_succ_of_normalization` | 实际 witness refinement、两项分别证明的能量损失及有限能量增量终止 |
| 全部一致度与最终版本 | `RegularityConstruction.regularityLemma_all`、`partitionExistence` | 从 `r = 2` 开始解除所有 construction 前提；将 ambient 坏质量转换成 crossing 坏质量 |

表中的文件名用于定位证明；这些公开声明位于 `UniformTuran.StrongRegularity` 命名空间。`RandomSlicing.lean`、`StateCoarseColoring.lean`、`StatePerfectPatching.lean` 和 `ApproximationPatchingBudget.lean` 中的划分、修复、覆盖、两两不交与质量求和均针对实际有限边集证明，没有把所需正则分割或修复结论放入输入结构。

论文引用 Rödl–Schacht [32, Theorem 2.3 与 Lemma 4.1]，采用 Lin–Sun–Wang–Zhou [20, Theorem 3.7] 的形式。只证明二元图正则性或 weak hypergraph regularity 不足以提供这个结论。

### Lemma 3.2：正则 complex 的 dense counting

给定 `2 ≤ h ≤ u`、`0 < μ < 1` 和正的密度下界 `d₀`，需得到 `ε₀,m₀`，使每个满足假设的 `h`-complex 都有

\[
|K_u(\mathcal H^{(h)})|
=(1\pm\mu)m^u\prod_{\ell=2}^{h}d_\ell^{\binom u\ell}.
\]

本工程需要它统一用于所有 `u ≤ M` 的相关地址，既用于证明标签可选，也用于地址大小估计。低层的 `d_ℓ = 1/a_ℓ` 是正则性参数；单元的实际相对密度可以与它相差至多 `ε(a)`，不能未经证明把实际密度替换成精确的 `1/a_ℓ`。

**这一 dense counting 定理现已给出实际 Lean 证明。** `Regularity/CliqueCounting.lean` 中的 `DenseCounting.dense_counting_lemma` 计数的是最高层实际无序 crossing clique 集 `crossingCliques`，并从各 cell 对其实际 codimension-one polyad 的 `IsRegular` 推出上述双边界。没有把目标计数、cut discrepancy 或 embedding 放入输入。底层空集与单点 cell 为全体，且每层的支撑包含条件直接来自正则性的定义。

证明首先由多测试正则性的单测试特例推出无条件计数误差：大测试用正则性，小测试用两个数量均介于 `0` 与测试大小之间。`SubpolyadTests.lean` 真正构造子 polyad：保留其所有子面满足指定谓词的 codimension-one 边。每个 proper 子面可扩成 codimension-one 面，因此该子 polyad 的 clique 集恰好施加所需的所有 proper-face 约束。固定当前 face 外的顶点后，其余同层 face 与当前 face 相交于 proper face，故这些约束确为允许的单测试。`TupleSplicing.lean` 的有限 Fubini 和 `DenseCountingCore.face_discrepancy` 给出每个替换的全局误差至多 `ε m^u`。`Telescoping.lean` 与 `CountingFactors.lean` 保留所有低层 Boolean 因子；重复约束通过实际指示函数的幂等性消去，未引入额外密度因子。

最后逐层替换得到显式绝对误差

\[
\left||K_u|-m^u\prod_{\ell=2}^{h}d_\ell^{\binom u\ell}\right|
\le N(u,h)\,\varepsilon\,m^u,
\qquad N(u,h)=\sum_{\ell=2}^{h}\binom u\ell.
\]

`DenseCounting.countingTolerance` 采用

\[
\varepsilon_0(u,h,\mu,d_0)
=\min\left(1,\frac{\mu d_0^{N(u,h)}}{N(u,h)+1}\right)>0.
\]

其正性、上界以及所需相对误差界均已证明；该有限证明对满足正则性假设的所有簇大小均适用，因而可取 `m₀ = 1`。`AddressCounting.lean` 还完成了所有 `u ≤ M` 的统一参数选择及其与 raw address 的逐高度非空性连接。这里的显式容忍度依赖全部低层密度；下一节的 embedding 采用单独的多测试论证，保证先选 `σ₀` 的量词顺序。

论文引用 Kohayakawa–Rödl–Skokan [16, Theorem 6.5]，采用 Rödl–Schacht [31, Theorem 2.1] 的形式。

### Lemma 3.3：允许不同顶层密度的 embedding

给定固定的 `k` 一致超图 `F` 和阈值 `d_* > 0`，先选取 `σ₀ > 0`。随后对各低层正密度 `d₂,…,d_{k−1}`（其倒数为整数），得到 `ε₀,R₀,m₀`。结论是：在 `v(F)` 个等大簇上的正则 `(k−1)`-complex 上，若每条 `e ∈ F` 对应的顶层宿主片满足

\[
d_e=\frac{|H\cap K_k(B_e)|}{|K_k(B_e)|}\ge d_*,
\]

并且对 `B_e` 是 `(σ₀,d_e,R₀)` 正则的，则宿主中存在普通的注入 `F` 副本。不同边可以有不同 `d_e`。

论文引用 Cooley–Fountoulakis–Kühn–Osthus [4, Theorem 2]，采用 Lin–Sun–Wang–Zhou [20, Theorem 3.8] 的后果。把“保留边构成的图是 `F`-free”作为输入，不能替代这一嵌入定理。

**保持上述量词顺序的实际嵌入结论现已完成。** `EmbeddingTheorem.lean` 中的 `DenseCounting.regular_complex_embedding` 只要求实际的低层及顶层 `IsRegular`、空集和单点层为全体，以及顶层密度下界；结论是真正存在满足所有所需 cell 的 crossing tuple。其输入中没有目标计数、extension moment、test discrepancy 或嵌入结论。允许各簇大小不同且非空，因此对于论文的等大簇情形可以取 `m₀ = 1`。`PartiteEmbedding.lean` 的 `regular_complex_host_embedding` 已把 tuple 接到实际宿主上的 `ContainsCopy`：顶层 cell 确实来自 `restrictToCliques`，且普通注入副本也包括孤立顶点。这个有限几何连接有独立证明。

证明使用有限多测试平均，避开把低层密度依赖偷偷放进 `σ₀`。固定当前顶层面 `S`，令 `K` 是其真实基底 clique 集；固定外部顶点 `z` 后，其余所需面给出一个真正的子 polyad 测试 `Q_z`。令 `p(y)=Pr_z[y∈K(Q_z)]`。`UnionTestAveraging.lean` 独立抽取 `t` 个外部样本，取实际测试的并，并由多测试正则性和二阶 Bonferroni 界证明

\[
t\left|\sum_{y\in K}(1_A(y)-d_S)p(y)\right|
\le \sigma |K|+\binom t2\sum_{y\in K}p(y)^2.
\]

测试样本可重复；证明对实际有限测试族去重，验证其基数不超过 `t ≤ R`。没有把该不等式作为额外正则性公理。`SlicePolyads.lean` 从 proper-face 约束构造实际 `Q_z`，并证明它确实是原 polyad 的子图。

删去其他顶层约束只会增加 `p`。`PatternDoubling.lean` 和 `PatternMoment.lean` 将剩余低层的二阶矩写成两份 complex 在 `S` 上共用顶点、其余顶点独立的真实计数。`PatternCounting.lean` 把已证明的低层 dense counting 推广到这一向下封闭模板；`RegularityTransport.lean` 证明所需的正则性迁移，簇投影只需在每个当前面上单射，允许两份外部顶点来自同一原簇。由此得到实际估计

\[
\sum_{y\in K}p(y)^2\le 2|K|W^2,\qquad
W=\prod_{\ell=2}^{k-1}a_\ell^{-(\binom u\ell-\binom k\ell)}.
\]

设 `q = binom(u,k)`、`d_eff = min(d_*,1)`，取

\[
\beta=\frac{d_{\rm eff}^{q}}{16(q+1)},\qquad
\sigma_0=\beta^2,\qquad
R_0(a)=\left\lceil\frac{\beta}{W(a)}\right\rceil.
\]

`EmbeddingParameters.lean` 证明这给出每个顶层替换的加权误差至多 `2β|K|W`；`EmbeddingMass.lean` 将其变成全局误差至多 `4β B₀`，其中 `B₀` 是完整低层 complex 的基准计数。`TopLayerCounting.lean` 对至多 `q` 个顶层面逐一替换，低层实际计数至少为 `3B₀/4`，于是最终计数严格为正。统一低层容忍度使用 `AddressCounting.uniformTolerance a (2u) (k−1) (1/4)`，覆盖原 complex、每个基底 polyad 和每个双份模板。

因此 `σ₀` 只依赖 `u,k,d_*`，`ε₀,R₀` 在给定 `a` 后选择。`regular_complex_embedding_of_parameters` 还处理实际输入满足 `ε≤ε₀`、`σ≤σ₀`、`R≥R₀` 的应用情形。该有限证明没有调用未形式化的 Cooley 或 Rödl–Schacht 嵌入定理。

## 4. 参数选择中的统一界

先选 `d_* = d/8`，再选 `0 < σ ≤ min(1,σ₀)` 满足

\[
\frac{16\sigma}{d}\binom Mr<\frac12.
\]

固定 `0 < μ ≤ 1/100`。在应用正则性之前，为每个正参数向量 `a` 选择足够小的 `ε(a)` 和足够大的 `R(a)`，以同时满足所有相关 counting 和 embedding 应用。正则性输出 `T` 后，只有有限多个可能的 `a`；这时对它们的簇大小阈值取有限最大值。不能先把 `a` 当作已知而后再选择正则性定理的输入函数。

一个可用的显式低层地址常数是

\[
K=r+\sum_{\ell=2}^{j}\binom r\ell,
\qquad c_T=\frac{1}{2T^K}>0.
\]

由 `m = n/t`、`t,a_ℓ ≤ T` 和 counting 可得每个 `r` 簇上的 `j` 层地址满足

\[
|C(\alpha)|\ge c_Tn^r.
\]

`j = 1` 时乘积为空，直接用 `m^r`。取 `0 < η ≤ dc_T/8` 后，坐标化稠密性给出每个低层地址的相对密度至少 `7d/8`。

对于顶层完成地址，所有簇指标集和所有标签实现共享同一个基准权重

\[
C_0=m^r\prod_{\ell=2}^{r-1}a_\ell^{-\binom r\ell}>0,
\]

并满足 `(1−μ)C₀ ≤ |C(ω)| ≤ (1+μ)C₀`。这正是 `RetentionBounds` 和 `ClusterAveraging` 所需的权重输入。

## 5. 从原始稠密性到地址密度的桥

本工程的 `UniformDense` 保留论文 (1.1) 的单个辅助 `j`-超图测试。Claim 3.4(iv) 使用的是 (3.2)：每个坐标位置 `I ∈ binom([r],j)` 都可指定不同的有序 `j` 元关系 `G_I`。

这两层需要分别处理：

- **`2 ≤ j ≤ r` 的宿主层转换现已证明。** `CoordinateConversion.uniformDense_to_coordinateDense` 在同一个宿主上把误差 `η` 变成 `r^r η`，保持密度参数 `d`。`admissible_coordinate_models` 已据此从原始 `Admissible … d` 构造任意大、保持禁图性且坐标化误差任意小的模型，无需只引用两个 supremum 相等。
- **`j = 1` 的诱导模型转换现已证明。** `CoordinateConversionOne.uniformDense_one_coordinate_induced` 经过真实有限 weak regularity、抽样与 Ramsey 同质化，取得足够大的诱导宿主并证明坐标化稠密性。`admissible_one_coordinate_models` 完成原始可达密度的包装，`admissible_coordinate_models_of_one_le` 统一全部 `1 ≤ j ≤ r`。这里确实允许换到诱导宿主，没有声称 `j = 1` 在同一宿主上自动满足所有坐标测试。
- **实际地址与坐标测试的连接现已证明。** `AddressCoordinateBridge.lean` 从真实低层地址构造位置关系，证明 `addressClass` 与有序坐标测试集双射，并识别宿主边计数。`coordinateDense_address_count` 和 `addressDensity_ge_seven_eighths` 给出需要的地址密度不等式。顶层 `j` 面条件对低层条件的覆盖使用实际地址兼容性，且精确保留有序元组与无序边的对应。

**原始可达密度的向下闭合与上确界闭合现已证明。** `AdmissibleClosure.lean` 首先证明 `cliqueSet` 的大小至多 `n^r`，进而证明把密度参数增加 `δ ≥ 0` 可由同样增加 `δ` 的误差支付。由此得到 `admissible_uniformTuranDensity`、`admissible_iff_mem_Icc_density` 和 `admissible_of_tendsto`：对每个成员都有边的禁图族，原始可达密度集合恰为闭区间 `[0,π]`。这些结论保留原始 `UniformDense` 和 `Admissible` 的定义，没有修改语义。

因此 `FiniteModelReduction` 对 `Admissible … d` 的陈述不需要在原始密度定义中额外丢失一个严格量。两个坐标化分支都已从原始可达模型直接构造实际坐标模型，保持同一 `d`；不是仅凭两个 supremum 相等跳过模型构造。

满足 Theorem 3.1 的 `M T! ∣ n` 所需有限删点步骤也已完成：`admissible_coordinate_models_divisible_of_one_le` 从充分大坐标模型得到指定正整数整除的宿主，并保持禁图性和所需误差。证明将测试关系扩展为不允许删去顶点参与的关系，并验证

\[
(\eta/2)(n+MT!)^r\le\eta n^r
\]

在充分大 `n` 时成立。禁图性在删点后保持。

## 6. 真正的离散平均桥已覆盖什么

每个 `r` 簇指标集支持恰好

\[
A=\prod_{\ell=2}^{r-1}a_\ell^{\binom r\ell}
\]

个完成地址，前提是第 2.3 节的标签可用性已证明。因此“均匀选择一个 `r` 簇集，再均匀选择其标签”确实给出全部完成地址上的均匀分布。若使用所有簇上的全局独立标签，已有 `DisjointCoordinates.expect_pi_restrict` 和 `expect_pi_reindex_injective` 给出相同的局部乘积分布。

`ClusterAveraging` 已对真正的均匀 `M` 元子集证明：每个固定宿主 `r` 元子集被选中的概率是 `binom(M,r)/binom(t,r)`，进而

\[
\mathbb E_{S,L}\sum_{e\subseteq S,\ |e|=r} b_e(L)
=\binom Mr\,\mathbb E_{e,L}b_e(L).
\]

这里 `L` 是独立选择的低层标签，`b_e(L)` 是对高层标签取期望后的不规则指标。结合高层 Fubini、近等权重转换和上述 `σ` 选择，已证明存在 `S,L` 使所有 `e ⊆ S` 都有 `b_e(L) ≤ d/8`。没有使用错误的“每个固定递增位置的像均匀分布”断言。

唯一地址、完成集合的划分、全局标签的局部规则和局部边缘分布已有真实证明。`AddressSelection.expect_size_mul_bad_eq_volume` 已把实际 crossing 集合的坏质量识别为加权实验的期望，`exists_clusters_and_global_lower_of_counted_partition` 由实际低层 counting 和该质量界选择簇与低层地址。`FiniteModelConstruction.exists_finite_model_of_regular_partition` 随后完成参数、保留规则与有限分布的整体连接。这些结论均从实际集合和概率计算导出。

## 7. 禁图性的实际闭合与主定理连接

`RetainedModel.isFree_retainedConfiguration` 对任意标签实现作如下反证：假设保留图中有一个注入 `φ : V(F) → [M]`，从实际分割中抽取 `φ(V(F))` 上的 complex，并逐项验证 Lemma 3.3 的假设：

1. 这些簇等大且大小至少 `m₀`。
2. 所选低层类形成真正的 complex，并满足所需低层正则性。
3. 对每条 `e ∈ F`，对应顶层 clique 集非空。
4. 保留规则给出真实相对密度 `d_{φ(e)} ≥ d/8` 和原参数的顶层正则性。
5. 参数单调性把它转换成 embedding lemma 所要求的 `σ₀,R₀`。

实际的 `regular_complex_host_embedding` 随后得到 `ContainsCopy F H`，与原宿主的 `IsFree F H` 矛盾。对 crossing 部分得到的副本，通过已证子图包含送回原宿主。完成这一反证后，`law_avoids_of_isFree` 给出生成分布的 `Avoids F`。

`FiniteModelConstruction.exists_finite_model_of_regular_partition` 完成整个 Claim 3.4 的实际分割到有限模型的组合；`StrongRegularityReduction.finiteModelReduction_of_strongRegularity` 再从正则分割存在性推出原始密度定义下的有限模型规约。此前保留为显式前提的 `PartitionExistence r`，现由 `StrongRegularity.partitionExistence` 的实际 uniformity 归纳证明提供。

最后 `Main.lean` 的 `paperMainTheorem` 将这个无条件存在性证明传入 `paperMainTheorem_of_strongRegularity`，解除最后的定理级前提。两个显式推论是 `uniformTuranDensity_eq_zero_iff_positionConsistentOrdering` 和 `uniformTuranDensity_gap`。原始 `Admissible` 的闭合性、全部 `j ≥ 1` 的坐标模型转换与整除处理、一般有限 Ramsey 和 Claim 3.5、dense-complex counting、raw 地址非空性与大小界、保留 `σ₀` 量词顺序的普通注入 embedding，以及每个标签实现的实际禁图性都在同一证明链中调用。

## 8. 宿主之前的参数与有限终止审查

以下审查针对实际声明与证明项的量词顺序，不把“参数足够小”作为未证明的选择原则。

### 8.1 两次 RL 与最后的有限包络

`exists_two_scale_regular_partitions` 先对每个候选 coarse 参数 `p = (t,a)` 选择第二次 RL 的 `μ₂(p),T₂(p),n₂(p)`。第二次的误差 `δ(p)` 此时已经由用户误差函数固定。第一次调用随后使用

\[
\varepsilon_1(p)=\min\{\varepsilon(p),\operatorname{countTol}(p),\mu_2(p)\},
\]

并让 `R₁(p)` 覆盖 `T₂(p)` 下全部实际 fine profiles 的数量。第一次 RL 给出 `T₁` 后，才在 canonical bounded parameter space 上取有限最小值和最大值，得到总 `μ,T,n₀`。这些选择全部发生在 `N`、初始 hierarchy 和宿主着色引入之前。

输出记录 `TwoScaleRegularData` 是两次 RL 实际构造的结果。代码分别证明 coarse `P` 和 fine `Q` 都受 `T₂(P)` 控制，因此同一个实际 polyad 体积下界可以支付两个层面的旧 cell 限制误差。`tests_enough` 也是真实的 `profileCountBound(Q) ≤ R₁(P)`，不是单独增加的假设。

### 8.2 Equitable normalization 的参数

`equitableNormalization_of_approximation` 先固定新分母 `A`、局部坏质量份额 `β/2`、增大的最小簇数，以及给 RAL 的完整低层误差函数。该函数已在 `appendLabels ... A` 上评估最终目标误差，所以没有假设用户函数对参数单调。RAL 输出 `T₀` 后，才选择统一 slicing 阈值与

\[
\mu\le\min\{\mu_{\mathrm{RAL}},\delta_{\min},\delta_{\min}\kappa_{T_0},1\}.
\]

其中 `κ` 是由真实 dense counting 得到的 ambient polyad 体积系数。这个后续缩小输入误差的步骤没有反馈进先前的 RAL 参数。`NormalizationEnvelope` 证明实际旧、新 clique 集之间的限制预算；`NormalizationCleanupBudget` 直接构造真实 cleanup 输入，所需纯数值不等式不是额外参数。

逐色 L1 编辑界与 repaired 观察的 approximate-refinement 界是两个分别证明的结论。证明没有把少量点的 L1 改动当成所有受影响细胞总质量很小的理由。

### 8.3 固定初始 hierarchy 与 pumping 终止

`initialGrowth_of_one_le` 在引入目标误差 `η` 前就固定 `T = o * start`；只有输入容忍度和最小宿主大小依赖 `η`。`UniformPumping` 先选出有限 complexity-bound 序列，再对所有阶段所需的输入误差取正最小值，随后用 initial growth 构造实际 `P₀`。

每个 pumping step 都把固定的 `P₀` 作为 normalization 的旧 hierarchy。证明没有要求当前 `P_i` 自动满足下一次调用可能更小的输入误差。所有阶段的能量都在同一个真实 crossing host `E(P₀)` 上比较；witness 增益、L1 修复损失和 repaired approximate-refinement 损失分别进入不等式。

`exists_regular_of_pumping` 对实际自然数步数归纳，构造有效有限状态。能量始终至多 `1`，而每个未停止步骤至少增加固定正数 `γ`；预先选择 `steps * γ > 1`，故有限步内必有 regular 状态。没有假定无限过程终止。

### 8.4 一致度归纳与前提解除

归纳基是已证明的 `regularityLemma_two`。每一步使用已有的 `RL(k)` 得到 `RAL(k)`，再得到 `EquitableNormalization(k)`，最后结合无条件的 `InitialGrowth(k)` 得到 `RL(k+1)`。两次 RL 调用都使用已存在的同阶归纳假设，没有调用正在证明的下一阶结论。

`RegularityConstruction.regularityLemma_all` 将 generic induction 的三个 construction 参数分别填入实际证明；`partitionExistence` 和 `Main.paperMainTheorem` 再完成接口组合。最终没有保留 `hregularity`、`hRAL`、局部 repair 存在性或能量增量假设作为论文主定理的附加前提。

## 9. 证明范围

本工程证明了主定理所用的精确有限 regularity、counting 和 embedding 版本，并完成整个主结论的连接。没有将外部论文中的同名定理或文献引用声明为公理，也没有声称已经形式化那些论文的全部附加版本、全部定量常数或一般有界度 embedding 结论。

无限概率部分采用一致的有限维 laws 完成所需论证；这不等于另行提供 Kolmogorov 扩张定理或无限随机超图样本空间的测度构造。该表示范围不再是主定理的证明缺口。

`Checks/Axioms.lean` 对工程声明递归收集公理并检查白名单；`Checks/CombinatorialAudit.lean` 列出关键组合、概率、regularity 及最终无条件定理的公理依赖。白名单仅包含 Lean 的 `propext`、`Classical.choice` 和 `Quot.sound`，不包含 regularity、counting、embedding 或论文主定理的专用公理。

## 参考来源

- [Li–Liu，本文，第 3 节](https://arxiv.org/abs/2611.06964)。上述定理编号以本文为准。
- [Lin–Sun–Wang–Zhou, *Uniform Turán densities of k-uniform hypergraphs*](https://arxiv.org/abs/2605.15105)，本文参考文献 [20]，用于 Theorems 3.7–3.8 的版本。
- [Reiher–Rödl–Schacht, *On a generalisation of Mantel’s theorem to uniformly dense hypergraphs*](https://doi.org/10.1093/imrn/rnx017)，本文 [28]，Proposition 2.5。
- [Rödl–Schacht, *Regular partitions of hypergraphs: regularity lemmas*](https://doi.org/10.1017/S0963548307008553)，本文 [32]。
- [Rödl–Schacht, *Regular partitions of hypergraphs: counting lemmas*](https://doi.org/10.1017/S0963548307008565)，本文 [31]。
- [Kohayakawa–Rödl–Skokan, *Hypergraphs, quasi-randomness, and conditions for regularity*](https://doi.org/10.1006/jcta.2001.3217)，本文 [16]。
- [Cooley–Fountoulakis–Kühn–Osthus, *Embeddings and Ramsey numbers of sparse k-uniform hypergraphs*](https://doi.org/10.1007/s00493-009-2356-y)，本文 [4]。

本次审查读取了本文的完整第 3 节和参考文献表，并结合上述实际 Lean 声明检查其依赖与参数顺序。上列外部定理的编号对应关系据本文陈述；工程对所需有限结论给出自己的证明项，没有把外部论文的引用当作已经通过 Lean 内核检查的证明。
