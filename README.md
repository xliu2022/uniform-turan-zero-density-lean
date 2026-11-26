# Zero uniform Turán density in Lean

**当前状态：Theorem 1.1 的两个结论已完成无条件 Lean 证明。** `UniformTuran/Main.lean` 中的 `paperMainTheorem : PaperMainTheorem` 已编译通过。此前保留的强正则分区存在性前提，现由实际有限构造和阶数归纳得到的 `StrongRegularity.partitionExistence` 消去；主定理没有额外的正则性、随机模型存在性或计数假设。

形式化保留原论文的全部参数范围 `r ≥ 4`、`1 ≤ j ≤ r - 3`。对有边的有限 `r`-图，零均匀 Turán 密度当且仅当存在 `(j+1)`-面位置一致的顶点排序。对任意禁止图族，只要其每个成员都有边，密度要么为零，要么至少为 `N⁻ᴺ`，其中 `N = choose(r,j+1)`；禁止图族可以无限，也可以为空。底层密度仍是论文式 (1.1) 的单个辅助 `j`-图测试定义。

论文：Heng Li、Xizhi Liu，*Hypergraphs with zero uniform Turán density at intermediate levels*，<https://arxiv.org/abs/2611.06964>。

形式化作者与维护者：Xizhi Liu。

## Palomar 核验

[Challenge.lean](Challenge.lean) 从 Mathlib 出发，给出有限超图、普通嵌入、均匀密度和面位置一致排序的定义，并分别陈述 Theorem 1.1 的零密度刻画与禁图族间隙。[Solution.lean](Solution.lean) 从 [UniformTuran/Main.lean](UniformTuran/Main.lean) 导出两个同名证明。[comparator.json](comparator.json) 选定这两个定理；[formalization.yaml](formalization.yaml) 记录来源、范围、作者、自动化使用和审查历史。维护者说明，原有 Lean 证明主要由 GPT 生成。

项目提供[官方机械预检工作流](https://github.com/xliu2022/uniform-turan-zero-density-lean/actions/workflows/palomar-preflight.yml)。在 GitHub Actions 手动运行后，可按完整提交 SHA 查验报告。在装有 `elan` 和 `bwrap` 的 Linux 环境中，也可以运行以下命令。

```bash
lake exe cache get
lake build
lake comparator --config comparator.json
```

## 已完成的主要结果

1. 原始的统一 Turán 密度定义：对每个辅助 `j`-图测试其 `r`-团，误差为 `η n^r`；密度是可实现密度集合的实数上确界。
2. 原文的面位置一致性，与共享顶点秩一致性的等价；排序在嵌入下的拉回；有限支撑、位置类和逐顶点拆分。
3. Lemma 2.5：相邻两点不共边时的交换不变性，从 spreadability 和二阶矩估计证明。
4. Lemma 2.6：沿阴影无交的边组拆点保持模式概率。独立性要求作用于整组边指标向量。
5. Lemma 2.7：完整多部图的真实乘积取样、Jensen 不等式、碰撞误差和极限；以及边内保序的全局排序不变性。
6. **Theorem 2.4**：`SpreadableLaw.positionConsistent_bound`，精确下界为 `p ^ (∏ i, (H.positionVertices i).card)`。
7. **Claim 3.5**：`FiniteShadowModels.exists_spreadable_model`。包含一般有限超图 Ramsey、同时同质化、整个有限构型的概率向量网格化、近似相容性、紧致性，以及独立性、禁止模式零概率、边概率下界的极限保持。
8. **Claim 3.6 的染色构造**：精确边概率、单个面的影响界、有限乘积空间的浓缩估计、所有辅助图上的并集界，给出任意大一致稠密构造。
9. **Theorem 1.1 的必要方向**：`hasPositionConsistentOrdering_of_density_eq_zero`。
10. 任意禁止图族（包括无限族）若没有位置一致可排序的成员，则 `palette_le_uniformTuranDensity` 给出 `binom(r,j+1)^(-binom(r,j+1))` 的统一下界。
11. **全部 `1 ≤ j ≤ r` 的坐标密度转换**。`j ≥ 2` 时，`uniformDense_to_coordinateDense` 在同一宿主上转换，误差乘以 `r^r`。`j = 1` 时，`admissible_one_coordinate_models` 使用实际的有限弱正则性、等大小主簇正规化、抽样、Ramsey 选簇与诱导子图计数完成转换。最终保持原来的禁止图族和密度 `d`，并允许任意小误差、任意大模型。
12. `admissible_coordinate_models_of_one_le` 统一上述所有层级；`admissible_coordinate_models_divisible_of_one_le` 还允许模型顶点数被任意指定的正整数 `D` 整除。诱导子图继承、删除少量顶点后的误差缩放及 `Fin n` 重标记都有实际证明。
13. **Lemma 3.2**：`Regularity.DenseCounting.regular_complex_count` 从真实相对正则性推出稠密复形的乘法计数公式。证明包含切片、单面测试、逐面 telescoping、逐层归纳和显式容差选择；没有把计数结论作为输入。
14. **实际地址计数**：`Regularity.LabelSystem.addressClass_nonempty_of_lowRegular` 与 `addressClass_card_bounds` 从低层正则性逐层证明 raw addresses 的实现与大小估计。每次使用某个 cell 的正则性前，先由较低层计数证明其 polyad 非空；非空性没有放进地址结构字段。
15. `AddressCoordinateBridge`、`AddressCompletionAverages` 证明实际地址与坐标测试的精确对应、完成类分块以及几何大小加权的密度平均恒等式。`ClusterAveraging.exists_clusters_and_lower_labels_of_weighted_irregularity` 从真实的均匀簇子集取样、Fubini 和近等权重估计，完成 Claim 3.4 的有限簇与低层标签选择步骤；它仍需要明确的全局加权不规则性输入。
16. **Lemma 3.3**：`Regularity.DenseCounting.regular_complex_embedding` 已将真实子 polyad 并集测试、实际双份低层模式的二阶矩、逐面替换和参数选择连接为正计数结论；`Regularity.regular_complex_host_embedding` 再从实际宿主的顶层 polyad 正则性推出普通 `ContainsCopy`，包含模式中的孤立顶点。顶层容差只依赖模式大小、阶数和顶层密度下界；低层容差和测试数可依赖低层标签数。

17. **Claim 3.4 的完整下游构造**：`Regularity.exists_finite_model_of_regular_partition` 从实际低层正则分区、实际顶层不规则总量和原宿主的密度／禁图条件，构造具有 `d/2` 边概率、完整阴影独立性及 `F`-freeness 的有限随机模型。`RetainedModel` 通过已证明的宿主嵌入定理证明每个保留实现禁图；不再把禁图性作为生成器的额外输入。
18. **实际分区到主定理的归约**：`finiteModelReduction_of_strongRegularity` 和 `main_conclusions_of_strongRegularity` 证明参数次序、整除模型及全部主结论的衔接。其 `StrongRegularity.PartitionExistence r` 输入现在由独立的强正则构造定理提供，不再是主定理的附加前提。
19. **强正则构造中的实际修复**：随机切分、cell 等分、多测试见证的能量增益、能量稳定性、粗细 polyad 的真实分割及颜色修复均已证明。`exists_two_scale_regular_partitions` 从两次正则性调用构造真实的粗细分区；`TwoScaleRegularData.exists_profile_repair` 分别修复好、坏粗 polyad；`exists_perfect_color_of_local_repairs` 将这些局部边集拼成一个颜色函数，保持旧 cell decoder、精确覆盖、互斥、完全相对正则性及逐色编辑量界。
20. **任意阶数的强正则性与正则近似**：图基例 `regularityLemma_two`、实际方向 `approximationLemma_of_regularityLemma`、等分正规化 `equitableNormalization_of_approximation` 和有限能量迭代已经组成完整阶数归纳。`StrongRegularity.regularityLemma_all`、`approximationLemma_all` 和 `partitionExistence` 对所有 `r ≥ 2` 给出无条件证明，保留任意容差／测试数函数以及宿主之前的参数界。
21. **任意层数的初始簇增长**：`StrongRegularity.initialGrowth_of_one_le` 无条件证明所有 `k ≥ 1` 的 `InitialGrowth k`。构造逐层继承相容的旧 cell，在旧非交叉部分使用真实随机等分，随后验证新分层的低层正则性、细化关系及统一界；这一定理已作为完整强正则归纳的实际输入。
22. **完整 Theorem 1.1**：`paperMainTheorem` 将上述强正则存在性接入原始密度的归约；`uniformTuranDensity_eq_zero_iff_positionConsistentOrdering` 和 `uniformTuranDensity_gap` 分别给出排序刻画与任意族的精确间隙结论。

`Reduction.lean` 和 `StrongRegularityReduction.lean` 保留模块化的条件接口，供复用其证明步骤。最终入口 `Main.lean` 为这些接口的每个数学前提提供已证明实例；应使用其中的 `paperMainTheorem` 或两个明确的推论来读取无条件结果。

概率模型采用完整相容的有限维分布族。Theorem 2.4 和主定理的推理只使用有限模式事件，因此直接在这一表述中完成证明；项目尚未另行构造一个承载所有自然数顶点随机变量的无限可测概率空间，不能据此声称已完成该 Kolmogorov 扩张对象的构造。

## 覆盖范围与表示边界

`StrongRegularity.PartitionExistence r` 是论文 Theorem 3.1 在主定理证明中需要的实际存在性后果：参数界在宿主之前选择，输出真实等大小簇及其到原顶点集的等价、各层 cell 的低层正则性，以及原宿主顶层不规则 crossing 集的加权总量界。此版本保留 `s * T! ∣ n` 的整除条件。`StrongRegularity.partitionExistence` 已证明该命题；更强的 `RegularityLemma` 与 `ApproximationLemma` 也已通过实际构造和阶数归纳证明。

这些加强命题保留初始分层细化、多色正则化和旧顶层 cell decoder。`ApproximationLemma` 采用本归纳需要的后果版本，没有另外声称已逐字形式化 Rödl–Schacht 原文关于空颜色的所有附加条款。最终主定理使用的全部存在性结论都有独立证明；合格分区或随机模型的结构字段本身不充当存在性证明。

主定理所需的有限推理链已经闭合。未单独构造无限 `Measure` 对象是概率表示的边界，不是最终有限密度结论的额外假设。定义、量词、精确常数和表示方式的对应见 `docs/SEMANTIC_AUDIT.md`；外部库适用范围审查见 `docs/ExternalDependencies.md`。项目不声称已经提交或通过外部形式化平台验收。

## 工具链与依赖

- Lean：`leanprover/lean4:v4.35.0-rc2`。
- Mathlib：`065356127b1dc0016f66b7283ce0ce2c4055aa55`。
- `lean-toolchain`、`lakefile.toml` 和 `lake-manifest.json` 锁定版本。
- 未增加数学公理；标准逻辑依赖允许 `propext`、`Classical.choice`、`Quot.sound`。
- 证明开发位于 `UniformTuran/`，其源码没有使用 `sorry`、自定义 `axiom` 或 `native_decide`。`Challenge.lean` 的两处 `sorry` 标记待比较的定理。`PaperMainTheorem` 与 `PartitionExistence` 是命题定义，`paperMainTheorem` 与 `StrongRegularity.partitionExistence` 分别提供它们的证明。

## 构建与检查

原始证明开发的构建记录使用了以下命令。

```bash
bash scripts/build-local.sh UniformTuran Checks.Axioms Checks.CombinatorialAudit
```

公开依赖闭包及检查程序的 **217 个 Lean 模块、37,578 行源码**全部重编译成功，退出码为 `0`，无错误或警告。递归公理审计覆盖 **3,331 个项目声明**；主定理及两个明确推论均只依赖 `propext`、`Classical.choice`、`Quot.sound`。源码检查也确认没有占位证明或跳过内核检查的选项。

这次构建的记录见 `docs/verification-build.txt`、`docs/verification-axioms.txt` 和 `docs/verification-summary.json`。快照清单 `CHECKPOINT.json` 分别列出原始构建的模块数、包含 Challenge 和 Solution 的源码总数，以及归档文件的 SHA-256。Palomar 对指定 Git 提交的核验结果见上方工作流。

在安装 `elan` 的环境中，解压后进入项目目录：

```bash
lake exe cache get
lake build
lake env lean Checks/Axioms.lean
lake env lean Checks/CombinatorialAudit.lean
```

已有匹配的 Lean 和依赖缓存时，可以通过 `scripts/build-local.sh` 按依赖次序重编原始证明源码，并用 `UNIFORM_TURAN_LEAN_BIN` 和 `UNIFORM_TURAN_PACKAGE_ROOT` 指定相应路径。

`Checks/Axioms.lean` 自动遍历 `UniformTuran` 命名空间中导入的所有声明，递归检查公理依赖；发现白名单之外的公理即失败，并另外打印主要定理的依赖。**公理审计通过只证明已存在的声明未使用额外公理，不会把未完成的目标变成已证明的定理。**

## 入口

```lean
import UniformTuran

#check UniformTuran.SpreadableLaw.positionConsistent_bound
#check UniformTuran.FiniteShadowModels.exists_spreadable_model
#check UniformTuran.hasPositionConsistentOrdering_of_density_eq_zero
#check UniformTuran.palette_le_uniformTuranDensity
#check UniformTuran.admissible_coordinate_models_of_one_le
#check UniformTuran.admissible_coordinate_models_divisible_of_one_le
#check UniformTuran.Regularity.DenseCounting.regular_complex_count
#check UniformTuran.Regularity.LabelSystem.addressClass_card_bounds
#check UniformTuran.Regularity.regular_complex_host_embedding

-- 无条件的强正则存在性与原论文主定理。
#check UniformTuran.StrongRegularity.regularityLemma_all
#check UniformTuran.StrongRegularity.approximationLemma_all
#check UniformTuran.StrongRegularity.partitionExistence
#check UniformTuran.paperMainTheorem
#check UniformTuran.uniformTuranDensity_eq_zero_iff_positionConsistentOrdering
#check UniformTuran.uniformTuranDensity_gap
```

`Targets.lean` 中的 `PaperMainTheorem` 是原论文主定理的精确命题；`Main.lean` 中的 `paperMainTheorem` 是其无条件证明。构建检查与语义审查分工明确：前者检查实际证明项及其依赖，后者核对这些命题与论文定义和量词的对应。
