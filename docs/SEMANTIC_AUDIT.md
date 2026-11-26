# 语义审查：形式化对象与论文命题的对应

审查日期：2026-11-26。对照来源为 Li–Liu, *Hypergraphs with zero uniform Turán density at intermediate levels*, arXiv:2611.06964v1，特别是式 (1.1)、Definitions 2.1–2.3、Theorem 2.4、Claims 3.4–3.5 和 Theorem 1.1。此次审查检查数学陈述与量词；内核与公理依赖检查由项目的独立 audit 承担。

## 结论与完成边界

本次检查没有发现以下已证明部分通过改变密度定义、弱化量词、将相互独立改成两两独立、忽略任意顶点排列，或替换精确指数而得到较弱命题：

- 论文原始的均匀 Turán 密度定义及其零密度的有限嵌入等价形式；
- 位置一致性的定义与顶点秩等价形式；
- 随机位置调色板的必要方向及任意禁图族的定量下界；
- 第 2 节的相邻交换、拆点、逐点完全拆分以及精确的 Theorem 2.4 下界；
- Claim 3.5 的有限维表述：从各个有限大小的模型构造一致、spreadable 的有限维概率律族；
- 从原始 `Admissible` 到所有 `1 ≤ j ≤ r` 的坐标模型，包括 `j = 1` 的诱导子图步骤、相同密度的恢复，以及任意指定整除条件；
- Lemma 3.2 的实际稠密复形计数、真实地址非空和大小估计，以及 Lemma 3.3 从实际宿主 polyad 正则性推出普通复制的嵌入结论；
- 实际强正则分区的存在性、Claim 3.4 的完整有限模型构造，以及它们与原始密度和主定理的连接。

**Theorem 1.1 的两个结论现已具有无条件证明。** `Main.lean` 中的 `paperMainTheorem : PaperMainTheorem` 及两个明确推论已编译通过。证明调用 `StrongRegularity.partitionExistence` 消去此前保留的实际强正则分区前提；该存在性来自图基例、初始簇增长、两条实际归纳方向和有限能量迭代。主定理仍使用原来的密度、位置一致性与复制定义，参数范围为 `r ≥ 4`、`1 ≤ j ≤ r - 3`，任意禁图族的精确间隙为 `N⁻ᴺ`，其中 `N = choose(r,j+1)`。概率部分的有限维表示边界见第 4 节，不影响最终有限密度结论。

## 1. 原始密度与量词

`UniformDensity.lean` 中：

| 论文对象 | 实现 | 审查结果 |
|---|---|---|
| 一个辅助 `j`-图 `G` 的所有 `r`-团 | `cliqueSet r G` | 要求每个 `j`-子集均属于同一个 `G.edges`，与式 (1.1) 相符。 |
| 对每个辅助 `j`-图的单侧下界 | `UniformDense j d eta H` | 测试对象是单个 `UHypergraph j V`，并未直接换成更强的逐坐标关系族。 |
| 误差 `η n^r` | `(Fintype.card V : ℝ)^r` | 没有改成 `η * choose(n,r)`，也没有混入有序元组的 `r!` 因子。 |
| 任意小误差、任意大宿主 | `Admissible` | 保留完整的 `∀ eta > 0, ∀ n0, ∃ n ≥ n0, ∃ H` 量词顺序。 |
| `sup` 定义 | `uniformTuranDensity` | 是实际可达密度集合的 `sSup`，未预设组合刻画。 |
| 任意禁图族 | `ForbiddenFamily r := Set (Σ n, UHypergraph r (Fin n))` | 不要求有限、可枚举或统一顶点数。 |
| 所有禁图有边、族可空 | `HasEdges` | 空族时条件为空真；另已证明空族的密度等于 `1`。 |

实现允许 `Fin 0` 作为一个有限宿主，论文从非空有限顶点集开始。这不改变渐近密度：在 `Admissible` 的任意 `n0` 量词中使用 `max n0 1` 即可强制非空。主定理的参数范围 `r ≥ 4` 及禁图有边的条件也排除了有关禁图的空顶点退化情形。这是表示上的扩大，不是量词削弱。

`ContainsCopy` 使用任意顶点单射并只要求保边，因此对应普通非诱导复制。`FamilyFree` 同时排除整个族的这些复制。

### 1.1 坐标转换：禁止图族、密度和量词保持不变

`CoordinateDense j d eta H` 的测试对象是独立指定给每个坐标 `j`-集的关系，元组本身是 `Fin r ↪ V`，所以只计各坐标互异的有序元组。它没有被用来替换 `UniformDense` 或重新定义 `Admissible`。

`CoordinateConversion.lean` 已证明 `2 ≤ j ≤ r` 时的同宿主转换。对顶点独立分配 `r` 个角色颜色；`j ≥ 2` 确保辅助图的每个 `r`-团角色全异。每个有序元组与指定角色匹配的概率恰为 `r⁻ʳ`，期望求和给出误差因子 `r^r`。应用原始 `Admissible` 时先选择更小的输入误差，因此最终仍得到任意指定的坐标误差。

`CoordinateConversionOne.lean` 则实际完成 `j = 1` 所需的诱导子图构造，没有断言同宿主上的两个密度条件等价。`uniformDense_one_coordinate_induced` 先选择正数 `eta₀` 和整数 `N₀ ≥ 1`，然后才量化任意有限非空宿主 `W`、任意 `H` 以及 `UniformDense 1 d eta₀ H`。其结论是一个至少达到指定大小的非空顶点集 `U`，且真实诱导图满足目标坐标密度。

该构造的弱正则性输入不是待证假设。`FiniteConditional`、`BlockRegularity`、`Normalized` 和 `RamseyRegular` 从有限加权和、实际精细划分和有限 Ramsey 定理证明所需分区存在。取 `κ = min(d/2, eta/4)` 后，原始单集合密度排除所有选定簇间密度小于 `d - κ` 的分支；高密度分支给出诱导图上的坐标盒估计。`TupleKernel` 精确证明无序边与有序边元组之间的 `r!` 因子，并对重复元组赋零；因此两个计数归一化没有被混用。

中间模型的密度为 `d - κ`，最终定理的密度仍是 **`d`**。`coordinateTupleSet_card_le_pow` 证明每个接受元组集合至多有 `|U|^r` 个元素，`coordinateDense_add_density` 因而允许把密度提升 `κ` 的代价吸收到同样大小的误差中。参数选择保证总误差不超过调用者给定的 `eta`。这不是只证明所有 `d' < d` 可达后省略极限的陈述。

`admissible_one_coordinate_models` 的输出保持同一个任意禁止图族 `family`。宿主先由原来的 `Admissible 1 family d` 提供；`familyFree_induced` 沿所选顶点子集和随后的 `equivFin` 重标记两次应用。没有删改禁图、把普通复制换成诱导复制，也没有引入禁图族有限性。`d = 0` 分支直接使用原 `Admissible` 给出的 family-free 模型和零密度下界，不额外要求 `HasEdges family`。

统一接口 `admissible_coordinate_models_of_one_le` 保留

```lean
∀ eta : ℝ, 0 < eta → ∀ n₀ : ℕ,
  ∃ n, n₀ ≤ n ∧ ∃ H : UHypergraph r (Fin n),
    FamilyFree family H ∧ CoordinateDense j d eta H
```

的量词，参数范围为 `1 ≤ j ≤ r`。`admissible_coordinate_models_divisible_of_one_le` 另允许任何预先给定的正整数 `D` 满足 `D ∣ n`；其证明先缩小输入误差，再诱导删除少于 `D` 个顶点，使用明确的误差缩放不等式。以上步骤均先选参数、后请求大模型，没有让模型大小界反过来依赖一个尚未选定的宿主。

## 2. 位置一致性及精确指数

`PositionConsistent q H` 直接要求每个公共 `q`-子集在两条边里的 `facePositions` 相等。这就是论文定义，而不是作为额外假设引入的顶点逐项秩一致性。

`vertexRank` 从零开始计数。论文从一开始计数；给每个位置加一是单射，所以位置集合相等与否完全一致。

`positionConsistent_iff_sharedRankConsistent` 在 `1 ≤ q` 下证明原定义等价于：只要两条边的交至少有 `q` 个顶点，每个公共顶点在两条边里的秩相等。论文参数 `q = j + 1 ≥ 2` 满足此条件。

`HasPositionConsistentOrdering q F` 对 `Fin m` 的**全部排列**取存在量词。它没有固定原先的顶点标签顺序。任意复制在有序宿主中的拉回也通过单射的排序分解得到这样的排列。

Theorem 2.4 的指数实现为

```lean
∏ i : Fin r, (H.positionVertices i.val).card
```

这里 `positionVertices H i` 是曾在某条边中处于位置 `i` 的**不同原顶点**的集合。一个原顶点可以在多个位置集合里分别出现。`finitePositionClass_card` 证明完全拆分后的第 `i` 类顶点数恰好是这个数，所以指数是论文的精确 `n₁ ⋯ nᵣ`，并非粗略的顶点数上界或边数上界。

有限图上的 `positionConsistent_bound` 只要求 `0 < r` 和 `1 ≤ q`，比论文参数范围更广；没有额外要求每个秩类非空、边类独立或顶点顺序已经分部。论文的全部参数范围可直接代入。

## 3. 孤立顶点

原始 `UHypergraph r (Fin n)` 保留给定的整个顶点集，因而复制与禁图定义保留了孤立顶点。

只在定义有限模式概率的辅助模型时，`canonicalOnSupport` 删除未使用的顶点；`canonicalOnSupport_map` 证明映回后边集完全相同，`phiOnSupport_eq_phiHypergraph` 则证明对 spreadable 律，这不会改变模式概率。完全拆点和 Theorem 2.4 的有限版本因此也适用于带孤立顶点的图。

`FiniteModels.Avoids` 排除的是原图 `F` 的全部顶点单射，包含其孤立顶点；没有偷偷改成只排除支撑图。后续完整正则性归约可以直接保留这些顶点，也可以另行证明论文开头使用的删除／补回孤立顶点步骤。当前主定理的条件归约没有靠一个未经证明的孤立顶点约化完成结论。

任意线序类型上的 `phiOnSupport` 是有限边支撑的概率接口。如果环境类型本身无限，它只表示这个有限边支撑的模式概率；不能把这个接口误读为嵌入一个具有无限多个指定孤立顶点的整个环境类型。主定理使用的环境是有限的 `Fin n`，不存在这一歧义。

## 4. 概率律、spreadability 与相互独立

`SpreadableLaw` 的数据仅包含每个 `n` 的有限配置概率律，以及所有递增单射下对任意实值测试函数的相容性。这是完整的有限联合分布不变性，不是只检查每条边的均值。没有把任何嵌入结论、相邻交换结论、拆点结论或正概率结论藏在结构字段里。

`Multipartite.edgeProbability μ` 是 `r` 个顶点上唯一一条 `r`-边的实际模式概率。`expect_edgeIndicator_eq` 已证明任何大小中的任意候选边的边缘概率都等于它。

`ShadowIndependent` 对任意有限组边族及每组**整个 Bool 向量**上的任意实值函数，要求乘积期望等于期望乘积。因此它表达相互独立，不是边变量的两两独立，也不是仅有模式发生概率的一种因子化。`ShadowDisjoint` 的交大小条件已经与真实 `q`-影无交证明等价。

有限配置空间下，`Avoids F` 要求 `F` 的每个任意单射标号复制的发生概率为零；`avoids_iff_support_free` 证明它等价于每个正权配置都为 `F`-free。没有只排除递增复制。`FiniteShadowModels` 的大小量词也是论文的 `∀ N ≥ max(r,v(F))`。

**表示边界：** 当前概率接口是所有有限维分布的一致族，没有额外构造一个定义在 `ℕ` 上的随机变量和 `Measure` 对象，也没有独立实现把这个一致族物化为单个无限概率空间的 Kolmogorov 扩张包装。第 2 节与主定理使用的都是有限柱事件，一致有限维表述足以进行全部这些论证。项目应称之为 Claim 3.5 的有限维形式，而不应声称已额外形式化一个具体无限概率空间。

## 5. 调色板与任意禁图族

调色板的颜色数为 `N = choose(r,q)`，实际边发生概率由有限独立颜色约束算得 `N⁻ᴺ`。颜色被分配给所有有限子集只是实现便利；非 `q`-集坐标不会影响任何边，且其有界差分常数为零。

浓缩估计使用真实的保留边计数函数；一个 `q`-面颜色改变最多影响 `n^(r-q)` 条候选边。随后对全部 `2^(choose(n,j))` 个辅助 `j`-图取有限并集界，得到原始单图测试的 `UniformDense`。`exists_uniformDense_palette` 对给定的任意正误差和任意 `n0` 选择足够大的 `n`，没有只证明一个固定大小上的例子。

每个颜色实现本身都是位置一致的。故只要禁图族中每个成员都没有位置一致排序，**同一颜色实现**就同时避开全部成员。这里不对无限禁图族作概率并集界。族中存在一个零密度成员时使用密度关于禁图族的反单调性；不存在时使用统一调色板下界。因此 `gap_of_sufficiency` 的任意族逻辑没有隐藏有限性假设。

## 6. 生成器、实际分区与 Claim 3.4

`HighFaceGenerator` 的随机坐标是所有满足 `q ≤ |S| < r` 的子集；它确实构造独立标签的乘积概率律，并将局部规则推送成 `Configuration r n`。`uniformLabelLaws` 实现每级 `a_|S|` 个标签的均匀选择。

`familyInputs_disjoint` 证明 `q`-影无交的边族读取互不相交的全部随机坐标。通过 `DisjointCoordinates` 的完整向量独立定理，`law_shadowIndependent` 已证明生成器所需的相互独立。

`RetentionBounds` 的保留规则确实是“regular 且 density ≥ d/8”。下列数值步骤也已经证明：

- 完成地址大小在共同正数的 `1 ± ε` 范围内时，将至少 `7d/8` 的加权密度转成至少 `3d/4` 的无权平均密度；
- 将按完成地址大小加权的不规则总量至多 `σ` 转成无权不规则概率至多 `2σ`；
- 小的期望总误差给出一个每项误差均小的确定选择；
- 平均密度至少 `3d/4`、不规则概率至多 `d/8` 和截断值 `d/8` 给出边缘概率至少 `d/2`。

这些都是明确输入上的已证明有限概率结论。`law_avoids_of_isFree` 本身只是将逐个实现的禁图性转成零概率。现在 `RetainedModel.isFree_retainedConfiguration` 已使用实际地址组装与宿主嵌入定理证明每个保留实现 `F`-free；`retainedAddressLaw_avoids` 因而完成这一概率结论，而不是把它预设为输入。

原文 Claim 3.4(v) 中的精确选择平均也需保留其真实含义：均匀选择一个 `M`-簇子集再递增编号时，固定位置 `e ⊆ [M]` 的像通常**不**在全部宿主 `r`-簇集合上均匀。正确恒等式先对所有 `e` 求和，再使用每个宿主 `r`-集合的包含率 `choose(M,r)/choose(t,r)`。`ClusterAveraging.subset_inclusion_probability`、`expected_selected_sum` 和 `exists_clusters_and_lower_labels_of_weighted_irregularity` 已证明这一实际选择桥。最后一个定理仍明确要求完成大小的近等权重界、全局加权不规则性界，以及相应的数值小量条件。

`AddressCompletionAverages.weighted_completion_density` 还证明真实地址完成类的精确几何加权恒等式：完成大小乘以完成密度的期望，等于低层地址密度乘以完成大小的期望。结合坐标测试与地址类的一一对应，`coordinateDense_expected_completion_density` 从明确的地址大小估计推得无权平均至少 `3d/4`。这些模块负责使用合格分区；分区存在性由第 8 节的独立强正则构造提供。

`exists_finite_model_of_regular_partition` 已把这些步骤与完整 Lemma 3.3 接通：给定实际分区及全局顶层不规则总量，确实选择簇与低层标签，建立每个保留实现的禁图性、边缘下界和完整阴影独立性。`finiteModelReduction_of_strongRegularity` 先选 `σ`、任意参数函数 `ε/R`，调用分区存在性取得 `T,n₀`，随后才请求顶点数被 `M*T!` 整除且满足更小误差的原始 family-free 坐标模型。最终 `Main.lean` 给这个调用提供已证明的 `StrongRegularity.partitionExistence`。这样不存在用尚未取得的分区参数反过来选择宿主的量词循环。

全局顶层不规则总量由实际强正则存在性定理保证。地址结构、浓缩估计和数值参数分别承担明确的后续任务；没有把分区存在性或生成器的禁图性作为它们的定义字段代入主定理。

## 7. Lemmas 3.2–3.3 与实际地址计数

`Regularity.IsRegular` 的测试是至多 `R` 个真实子 polyad 的 clique 区域的并集，并保留显式的 crossing allowed region。这个区域在 uniformity 为 `2` 时尤其必要：仅用一个 `1`-图的普通团会额外包含同簇点对。实现没有靠这些额外边改变正则性或计数归一化。

`DenseCounting.regular_complex_count` 已从每个真实 cell 相对其 boundary polyad 的 `R = 1` 正则性推出 Lemma 3.2 的乘法计数式。对各层密度 `d_k`，中心值为

\[
m^{|J|}\prod_{k=2}^{h}d_k^{\binom{|J|}{k}}.
\]

其证明先对每个 proper-face 切片构造合法子 polyad 测试，再逐面替换 cell 指标、逐层累计误差。`count_absolute` 的输入是底层完整性、实际相对正则性和密度范围；不是一个预先假定的 discrepancy、计数近似或正嵌入结论。`countingTolerance` 给出依赖簇数、层高、目标相对误差和正密度下界的正容差，随后推得通常的 `1 ± μ` 形式。

`LabelSystem.LowRegular` 只允许在**已经非空**的低层 carrier 上使用 cell 的相对正则性。因此 raw address 的非空不能仅从该字段直接读出。`LabelSystem.addressClass_nonempty_of_lowRegular` 通过地址高度的强归纳解决这一顺序问题：先证明较低地址实现非空，取得本层实际正则性，再应用已证明的稠密计数给出正的完成数。

`addressClass_card_bounds` 和 `addressClass_card_bounds_equal` 随后证明真实地址类的统一乘法大小界。其中心密度为各层标签数倒数的乘积；`uniformTolerance` 同时覆盖给定上界内的所有簇集大小和地址高度。每层标签数为正、簇非空、低层正则性以及容差不等式都是明确输入；实现没有把 raw-address surjectivity 或完成类近等大小放进 `LabelSystem`、`PartitionFamily` 或 `RegularPartitionFamily` 的结构字段。

这里的条件是计数引理应有的“给定正则复形”条件。Lemma 3.2 与地址计数不负责产生任意宿主的分区；该存在性由第 8 节的实际构造独立证明，再在下游应用这些计数结果。

`DenseCounting.regular_complex_embedding` 已进一步证明完整的顶层嵌入计数：二阶矩来自实际双份低层复形，顶层误差来自真正的有限并集测试，最后通过逐面替换与 `EmbeddingParameters` 的参数选择给出正计数。其输入不再要求调用者提供二阶矩结论。`regular_complex_host_embedding` 将真实宿主在每个目标顶层 polyad 上的正则性接入这个结果，并把所得 crossing tuple 转成保边单射 `ContainsCopy`。该单射定义在模式的全部顶点上，因此保留孤立顶点。

顶层容差 `embeddingSigma(u,k,d₀)` 不依赖低层标签向量 `a`；低层容差 `embeddingLowTolerance(u,k,a)` 和测试数 `embeddingRequiredTests(u,k,d₀,a)` 可以依赖它。允许不同顶层面的密度不同，只要求它们共同不低于 `d₀ > 0`。这些量词与论文 Lemma 3.3 所需的分工相符；实现还允许簇大小不同，只要求每个簇非空。

## 8. 无条件 Theorem 1.1 的完整证明链

### 8.1 实际分区存在性与加强归纳命题

`StrongRegularity.PartitionExistence r` 要求对任意允许的低层容差函数 `ε` 和测试数函数 `R`，先选择统一 `T,n₀`，再对每个足够大且满足指定整除条件的宿主构造实际等大小簇、到原顶点集的等价、真实低层标签系统、各低层 cell 的正则性，以及原宿主顶层不规则 crossing 集的加权体积界。`Statement.lean` 定义这一命题；`RegularityConstruction.lean` 中的 `partitionExistence` 对所有 `r ≥ 2` 证明它成立。

这是论文 Theorem 3.1 在主定理证明中需要的实际存在性后果，保留 `s*T! ∣ n`。下游不需要指定初始顶点划分的 refinement；内部的加强命题则保留它所需的更多信息。`RegularityLemma k` 包含初始分层细化、同时多色正则化、任意参数函数和宿主之前的统一界。`ApproximationLemma k` 要求实际新颜色函数、原顶层 cell decoder、逐色编辑体积界，以及每个非空实际 polyad 上以新图真实密度为基准的完全正则性。这个近似命题采用本归纳所需的后果版本，没有另外声称已逐字形式化 Rödl–Schacht 原文关于空颜色的所有附加条款。

`regularityLemma_two` 给出图基例。`initialGrowth_of_one_le` 无条件证明任意 `k ≥ 1` 的初始簇增长：在相容旧地址内继承旧标签，在旧非交叉部分作真实随机等分，随后实际扩展 label system 并验证低层正则性、精确细化和统一界。`equitableNormalization_of_approximation` 从实际正则近似构造等密度 cell、处理余片并验证完整分层的细化与误差。多测试见证的能量增益、编辑及近似细化下的能量稳定性和有限迭代再给出升阶步骤。最后 `approximationLemma_of_regularityLemma` 提供反向的实际正则近似，闭合

\[
\mathrm{RL}(2),\qquad
\mathrm{RL}(k)\Longrightarrow\mathrm{RAL}(k),\qquad
\mathrm{RAL}(k)\Longrightarrow\mathrm{RL}(k+1).
\]

`regularityLemma_all` 和 `approximationLemma_all` 因而对每个 `k ≥ 2` 给出无条件证明。这些结论来自具体存在性定理的组合，没有通过一个合格输出结构的定义来断言其有实例。

### 8.2 两次正则性调用的量词顺序

`exists_two_scale_regular_partitions` 从 `RegularityLemma k` 证明两个真实嵌套分区的存在。给定旧分层上界、颜色数、起始簇数、目标编辑误差 `ν > 0` 和任意目标容差函数，先为每一种可能的粗层参数 `(t,a)` 选择第二次正则性调用的界。这些第二次调用的输入容差和输出界组成参数函数，用于定义第一次调用所需的低层容差及多测试数量。

第一次调用的统一上界确定后，`BoundedParameters` 在有限个有界、规范化的参数向量上取最小正容差和最大大小／测试数界，最终选择 `μ,T,n₀`。直到这些量全部固定，证明才量化宿主顶点数 `N`、旧分层 `O` 和宿主颜色函数 `χ`，再实际产生粗分区 `P` 与细分区 `Q`。整除条件通过阶乘的整除单调性传给两次调用。因而不存在先见到 `P` 或宿主后再反过来改变已经要求的输入精度的循环。

所得 `TwoScaleRegularData` 的每个字段由该存在性定理证明：两个分区的真实低层正则性、旧层到粗层以及粗层到细层的细化、逐色不规则体积界、足够多的粗层测试、旧 cell 限制所需的实际体积比例，以及每个细 polyad 的随机 slicing 尾概率界。该结构是已构造输出的包装，不是额外的存在性假设。

### 8.3 旧 cell 几何、名义密度与实际修复

`StatePolyadParents` 从真实细化关系出发，对每个非空细 polyad 区分两种情况：它包含于某个相容的旧地址 boundary，或其全部顶层面都属于旧非交叉 cell。相容情形使用真实 lower-graph 包含和实际体积比例继承正则性；非交叉情形对应满集和空集。`StateProfileInheritance` 因而为同一旧 cell 在粗、细 polyad 上提供共同的名义密度，`TwoScaleCellGroups` 将它接入旧 decoder 的实际颜色组。

名义密度和实际密度没有混用。`IsRegular.to_actual_density` 通过整个 polyad 测试控制两者之差，并为换密度支付相应容差。好粗 polyad 的粗层全测试还控制细 polyad 密度异常的总体积；`CoarseDensity`、`RegularApproximation` 和 `GroupedApproximation` 再用实际有限随机切分构造新的颜色边集。每个旧 decoder 纤维内部的 union 精确保留，所以原 cell 归属也得到证明。

坏粗 polyad 上不假设原来各颜色正则。`CoarseBadRepair` 只使用已经证明的各旧 decoder 组 union 的正则性，把该组的实际 union 交给一个代表颜色，其余颜色置空。它仍给出精确覆盖、互斥、同一个 decoder 和实际密度下的完全正则性；每色编辑量至多是整个粗 polyad 的体积。

`TwoScaleRegularData.exists_profile_repair` 把这两种情形合并。`StatePerfectPatching` 证明所有实现的粗 profile 区域互不相交，并恰好覆盖真实 crossing carrier；局部修复据此拼成一个实际的全宿主颜色函数 `χ'`。区域外保留原颜色，因此 decoder 对所有顶层面成立，最终输出也满足 `PerfectlyRegular` 的原定义。

### 8.4 实际异常体积与全局编辑预算

设颜色数为 `s`。`ApproximationBudget` 选择

\[
\gamma=\min\left\{\tfrac14,\frac{\nu}{16(s+1)}\right\},\qquad
\delta(P)=\min\left\{\gamma,\frac{\varepsilon(P)^2}{64(s+1)}\right\}.
\]

对每个实现的粗 polyad 区域 `K_i`，统一局部预算为

\[
(4s\gamma+2s\delta)|K_i|
+\mathbf1_{\{i\text{ 是坏粗 polyad}\}}|K_i|
+|K_i\cap B_Q|,
\]

其中 `B_Q` 是细分区各个真实颜色的不规则 carrier 的并集。好分支采用这个预算的第一项和第三项；坏分支的全部编辑由第二项覆盖。

`sum_approximationLocalBudget_le` 对实际互不相交的 `K_i` 求和。粗层坏区域包含于各色粗层不规则 carrier 的并集，总量至多 `sγN^k`；细层坏 carrier 的并集总量至多 `sδN^k`。结合所有粗区域的总量至多 `N^k`，得到

\[
\sum_i L_i\le(5s\gamma+3s\delta)N^k\le\nu N^k.
\]

没有用 polyad 的数量乘以单个误差，也没有把“坏区域总量小”作为未证明的修复前提。`ApproximationConstruction.lean` 中的 `approximationLemma_of_regularityLemma` 使用实际 patch 后的 `χ'` 和这一求和界，完成 `RL(k) → RAL(k)` 的全部输出量词。

### 8.5 主定理入口与保留的表示边界

`RegularityConstruction.lean` 中的 `StrongRegularity.partitionExistence` 将完整归纳接到实际分区存在性；`StrongRegularityReduction` 再依次使用原始密度到坐标密度的转换、整除模型、Lemmas 3.2–3.3、地址计数、簇选择、有限保留模型、Claim 3.5 的有限维极限与 Theorem 2.4。`Main.lean` 中的 `paperMainTheorem` 给原有条件归约的每个数学输入提供证明，因此最终得到的仍是 `Targets.lean` 定义的原始命题 `PaperMainTheorem`。

实际 Lean 全名为 `UniformTuran.paperMainTheorem`，两个直接推论是 `UniformTuran.uniformTuranDensity_eq_zero_iff_positionConsistentOrdering` 和 `UniformTuran.uniformTuranDensity_gap`。后者保留任意禁图族，包括无限族与空族；前者保留模式的全部有限顶点，包括孤立顶点。没有缩小原参数范围或把精确 `N⁻ᴺ` 间隙换成某个未指定的正数。

仍需区分数学命题与表示方式：项目对 Claim 3.5 使用完整一致的有限维概率律，没有另行物化单个无限 `Measure` 空间；这足以支持主定理中的全部有限事件推理。项目也不据此声称已逐条形式化外部正则性论文中的所有加强条款，或已通过外部平台验收。内核编译和递归公理审计核验实际证明项及依赖，语义审查核对目标的数学含义；二者职责互补。
