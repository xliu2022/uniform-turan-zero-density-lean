# 外部依赖审查

## 有限 Ramsey 定理

本工程固定的 Mathlib 提交为
`065356127b1dc0016f66b7283ce0ce2c4055aa55`。对其源文件及全文检索后，未发现可直接应用的一般有限 `k` 一致超图多色 Ramsey 定理；已发现的相关模块包括 Hales–Jewett、Hindman 和鸽巢原理。

另审查了 Cameron Freer 的
[regularity-lemmata](https://github.com/cameronfreer/regularity-lemmata)
仓库，固定提交为
`8e24d2db2c11ee6ae9e61ad2d70a6c01c4303c90`，不能仅凭其“finite multicolor Ramsey”名称判断它足以支持论文 Claim 3.5：

- [Finite/MulticolorRamsey.lean](https://github.com/cameronfreer/regularity-lemmata/blob/8e24d2db2c11ee6ae9e61ad2d70a6c01c4303c90/RegularityLemmata/Finite/MulticolorRamsey.lean) 的着色类型是 `χ : V → V → Fin r`，结论控制所选序列中 `i < j` 的有序点对。它是二元情形，并非任意一致度的超图 Ramsey 定理。
- [Finite/BinaryTreeRamsey.lean](https://github.com/cameronfreer/regularity-lemmata/blob/8e24d2db2c11ee6ae9e61ad2d70a6c01c4303c90/RegularityLemmata/Finite/BinaryTreeRamsey.lean) 证明有限二叉树内部节点着色的单色子树结论，其对象与 Claim 3.5 的所有固定大小顶点子集不同。
- [FiniteRamsey.lean](https://github.com/cameronfreer/regularity-lemmata/blob/8e24d2db2c11ee6ae9e61ad2d70a6c01c4303c90/RegularityLemmata/FiniteRamsey.lean) 是上述两个方向的统一导入入口，并明确说明二者相互独立。

因此本工程没有引入上述仓库的源文件、二进制文件或额外工具链依赖，也没有将它的二元定理充当一般 Ramsey 定理。`UniformTuran/FiniteRamsey.lean` 给出了独立的一般证明：对一致度归纳，重复应用前一一致度的 Ramsey 定理，构造边色仅由最小顶点决定的有限集合，再对记录的顶点颜色应用鸽巢原理。其公开结论包括：

- `FiniteRamsey.finite_uniform`：任意 `k, m, c` 的有限 `k` 一致 `c` 色 Ramsey 定理；宿主大小至少为 `max m k`。
- `FiniteRamsey.finite_uniform_embedding`：以保序注入表示所选同质顶点集，允许任意有限颜色类型。
- `FiniteRamsey.simultaneous`：对有限多个、可具有不同一致度及不同有限颜色集的着色，同时选出一个同质顶点集。

`k > m` 的情形由统一陈述涵盖。对于 `c = 0`，所选宿主中存在 `k` 元子集，因此不存在着色到 `Fin 0` 的函数；定理的全称陈述正确地为真。

这里的外部仓库链接用于记录审查事实和适用范围，不是本工程该证明的公理或可信依赖。

## 强超图正则性、counting 与 embedding

论文 [Li–Liu, arXiv:2611.06964](https://arxiv.org/abs/2611.06964) 的第 3 节引用强正则分割、dense-complex counting 和 embedding 定理。本工程没有将这些引用作为 Lean 公理，也没有把它们的所需结论放进一个不经构造的输入结构。

所需版本现已分别给出实际证明：

| 论文中的作用 | 工程中的实际证明 |
|---|---|
| 强正则分割存在性 | `StrongRegularity.regularityLemma_all` 证明所有 `r ≥ 2` 的多色强化版本；`StrongRegularity.partitionExistence` 给出 Claim 3.4 所用的精确实际分割接口 |
| Dense-complex counting | `Regularity.DenseCounting.dense_counting_lemma` 从真实各层相对正则性推出实际 crossing clique 计数，随后 `AddressCounting` 处理 raw 地址非空性和统一大小界 |
| 固定禁图的 embedding | `Regularity.DenseCounting.regular_complex_embedding` 保留先选顶层误差的量词顺序；`regular_complex_host_embedding` 导出实际宿主中的普通注入副本 |
| Claim 3.4 的有限模型 | `RetainedModel` 实际证明每个保留配置禁图；`FiniteModelConstruction` 将实际分割、地址选择、边概率和禁图性组合起来 |
| 论文主定理 | `Main.lean` 的 `paperMainTheorem`、`uniformTuranDensity_eq_zero_iff_positionConsistentOrdering` 和 `uniformTuranDensity_gap` 已解除 regularity 前提并实际编译通过 |

强正则性的 Lean 证明从实际图基例开始，使用真正的有限随机 slicing、cell 能量、witness refinement、逐 polyad 修复和等密度单元归一化完成一致度归纳。核心方向为

\[
RL(k)\Longrightarrow RAL(k)
\Longrightarrow\operatorname{EquitableNormalization}(k)
\Longrightarrow RL(k+1).
\]

`InitialGrowth(k)` 另有不依赖这些归纳假设的实际证明。`ApproximationIterationBounds` 保证两次 RL 的参数选择无循环，`UniformPumping` 在固定初始 hierarchy 上作有限能量增量，`ApproximationPatchingBudget` 用真实不规则 carrier 的质量支付全部局部编辑。详细声明与量词审查见 [RegularityBoundary.md](RegularityBoundary.md)。

本项目证明的是主定理实际需要的明确版本。最终 `PartitionExistence` 接口不另接收一个指定的初始划分；内部 `RegularityLemma` 则接受满足其所选输入容忍度的真实初始 hierarchy 并保持 exact refinement。工程没有逐一包装外部 regularity 定理的所有加强版、等价陈述或参数常数，也没有声称完成 Cooley 等人一般有界度 embedding 定理的全部内容。

原文的主要数学来源保留如下，供对照版本与数学路线：

- [Rödl–Schacht, *Regular partitions of hypergraphs: regularity lemmas*](https://doi.org/10.1017/S0963548307008553)，Li–Liu 参考文献 [32]。
- [Rödl–Schacht, *Regular partitions of hypergraphs: counting lemmas*](https://doi.org/10.1017/S0963548307008565)，参考文献 [31]。
- [Kohayakawa–Rödl–Skokan, *Hypergraphs, quasi-randomness, and conditions for regularity*](https://doi.org/10.1006/jcta.2001.3217)，参考文献 [16]。
- [Cooley–Fountoulakis–Kühn–Osthus, *Embeddings and Ramsey numbers of sparse k-uniform hypergraphs*](https://doi.org/10.1007/s00493-009-2356-y)，参考文献 [4]。
- [Lin–Sun–Wang–Zhou, *Uniform Turán densities of k-uniform hypergraphs*](https://arxiv.org/abs/2605.15105)，参考文献 [20]，用于原文引用的 regularity 与 embedding 版本。

这些文献说明数学来源与对应关系；它们的文字陈述不属于本工程新增的逻辑公理。

## 有限 laws 与无限概率空间的范围

`SpreadableLaw` 表示一族具有精确保序限制一致性的有限维概率分布。`LawHomogenization` 和 `LawCompactness` 从实际有限模型得到该分布族，并证明所需的整组向量独立性、禁图概率为零和边概率下界在共同极限中保持。

后续拆点、交换、计数和主定理论证都在这些有限 laws 上完成。工程没有为“存在无限随机超图”引入公理，也没有额外构造无限超图样本空间上的概率测度。因此，不应把当前结果描述为完整形式化了 Kolmogorov 扩张定理；该无限样本空间包装不是完成本工程主定理所必需的步骤。

## 可信依赖与验证边界

工具链和 Mathlib 版本由工程文件固定。外部 Ramsey 仓库仅用于上述适用范围审查，没有改变本工程的依赖树。主定理所用的新增组合、regularity、counting 和 embedding 结论均由项目中的 Lean 证明项提供。

`Checks/Axioms.lean` 递归检查工程声明的公理依赖；`Checks/CombinatorialAudit.lean` 另行列出关键定理，包括最终无条件主定理及两个显式推论。允许的白名单只有标准的 `propext`、`Classical.choice` 和 `Quot.sound`；没有将 `sorryAx`、未证明的 regularity 或 embedding 声明加入白名单。

无条件主定理模块已通过目标编译。最终完整源码重建、整个声明集合的审计结果以及数量统计，以工程实际验证日志为准，不从目标编译次数或文件数量推算。
