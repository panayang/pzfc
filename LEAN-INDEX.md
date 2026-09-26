# 形式化索引

> Lean 4 的两个包：`lean/`（不依赖 mathlib）与 `lean-mathlib/`（依赖 mathlib 与 `../lean`）。每个模块的内容、对应的轮次与笔记、定理条数与公理剖面。只形式化有限的部分（组合、代数、有限测度论的步骤）；关于模型与强迫的元定理不形式化。
```
lean/Shapes.lean          第十至十二轮：良基处外延即唯一；一切图上强外延恰是唯一；自属元素；良基树上的递归解与 Mostowski；Diaconescu；
                          经典原点：基础 ⟺ 每个元素都是良基系统的解；良基结构上四种唯一性等价；由外延与替换得唯一解，不用选择；
                          形状的拓展：带基点的图按互模拟认同，AFA 成立，良基树嵌入其中；
                          一条带形状参数的公理模式 GLU(S)：良基实例即基础与外延，一切图实例即上面的宇宙，二者不能共用隶属关系；
                          没有从一切形状回到良基结构的影子                                                                     44 条
lean/Supports.lean        第十二轮：支撑就是上下文；有限的上下文支撑不了原子对上的选择                                                       5 条
lean/Contexts.lean        第十三轮：真值随上下文；排中律恰在上下文不能再细化处成立；双重否定处处成立                                         6 条
lean/Scheme.lean          第十五、十七轮：GLU(π) 的统一接口（值结构、解、终性）；锐的回答即经典；真值即上下文；单一上下文即锐；
                          值结构之间的映射（影子）把解送到解                                                                   5 条
lean/Kinds.lean           第十六、十七、十九轮：上下文种类（小范畴上带名字的系统，按持久互模拟认同）；GLU 成立；常对象即经典；存在是局部的；
                          纯的系统中对称被吸收；种类里的 Russell 袜子；选择的判据（有根不用选择，互不相交恰需选择）；
                          只看一个上下文是影子，原点是每个种类的收缩；预序上的判据（当且仅当每个连通分支有最小元）；
                          任意上下文结构上的判据（有对称时只有平凡群）                                                         45 条
lean/Values.lean          第十八、十九轮：一个构造，W 是参数——完备的值结构上的种类；GLU（只用 Quot.sound）；同一是有共同的像，
                          也是 Larsen–Skou 互模拟（对每个值结构）；影子是函子；锐的实例的同一是互模拟                          30 条
lean/Instances.lean       第十九轮：锐的实例就是形状的拓展——与 Shapes.UA 之间保持并反映隶属的双射                               4 条
lean/Over.lean            第十九轮：值随上下文——带序的值、只增不减的值又是完备的值结构；上下文上的 GLU；原点是收缩；存在是局部的      7 条
lean/Symmetric.lean       第二十一轮：值、名字、对称三者一起的种类；GLU；对称保持隶属的值、移动名字                              26 条
lean/Records.lean         第二十五轮：有限的来源（罐子）；记录恰是复读与复制分不开的来源，复读缺陷为 0 恰在记录上；统计经得起复读；
                          X + X 不是 2X；部分的规律相同而整体不同，部分都是记录时整体由部分决定；
                          第二十六轮：GLU 就是"回答是跨语境的记录"，整体对象唯一；
                          第二十九轮：每读一次就翻转的记忆——回答不是记录，"相邻两次不同"在一切历史中成立                   16 条
lean/Circumstances.lean   第三十轮：行为与提问的情形；有记录模型 ⟺ 公共且不被扰动；每个行为都有隐藏状态模型；不被扰动 ⟺ 状态不动；
                          藏回扰动的最少状态数 = 余下行为的个数；四种失败独立的例子；任务与预测；
                          第三十一轮：事实 ⟺ 余下行为（结构，不是位置）；位置何时是事实；读取即更新的两格记忆；
                          第三十六轮：时间不变的评价只看见终局；不可逆时事实随时间改变，会回到原处时不变                  52 条
lean/Individuation.lean   第三十二轮：三枚硬币分开随机、可复读、规律的扰动；个别化之后任何行为都有记录模型；
                          一切情形的一条定理（视角的全体）；名字对调——你是哪个视角不是事实                                  13 条
lean/Network.lean         第三十四、三十五轮：网络——公共 + 不干扰 ⟹ 不被扰动 ⟹ 有记录模型；公共而被扰动 ⟹ 干扰；
                          两个前提都不可少的例子；记录的转交：经过一读就变的共享转述不再是记录                              17 条
lean/Modal.lean           第三十九、四十一轮：.2 ⟺ 汇合；.3 ⟺ 连通；连通 ⟹ 汇合（线性时间是粘合的特例）；分叉的框架中 .2 不成立   12 条
lean/Protocols.lean       第四十二至四十四轮：此后与次序无关 ⟺ 两两可交换；两种次序依赖；记录的混合与次序无关；Pólya 坛；
                          迹：部分可交换时同一迹留下相同的未来；次序谱落在余下行为之内、可交换时只有一个成员           17 条
lean/Exchange.lean        第四十五轮：按类可交换时同迹 ⟺ 各类的流相同；字 = 日程 + 流；给定流时日程可交换；
                          PR 盒两类可交换，却不是每类一个隐藏记录的混合（共享记录至多满足四个语境中的三个）       26 条
lean/Spectrum.lean        第四十五轮：按类可交换时次序谱恰是类内重排之组的像；上界由类历史行为达到；
                          每个成员需要自己的状态；粗粒化保持可交换、只缩小次序谱                                  13 条
lean/Traces.lean          第四十六轮：一般独立关系；交换不变性向更小的关系下传（约化到依赖分量）；
                          后面都与它独立的字母可以移过去、移到末尾（没有最大元的有限形式）                          5 条
lean/Worlds.lean          第五十四轮：底座 M1–M4 的形状；换世界的有效性（基本形式与推导形式）；核心陈述全局、模态平凡；
                          可两头强迫的陈述是局部的；有共同扩张的世界在核心上一致；理论有向 ⟹ .2；两层（M4⁺ ⟹ M4）    10 条
lean/Local.lean           第二十二轮：确定性局部算法只看得见对象；所有结点是同一个对象时选不出领袖                                  6 条
lean/Glue.lean            第十轮：GLU 的一种统一写法（形状、局部数据、粘合）及其若干实例                                        17 条
lean/Socks.lean           第八轮：Russell 的袜子——只从"存在与 Bool 的双射"就能定义均匀权重，不用选择             3 条
lean/Axioms.lean          第六轮：问题宇宙；Russell 问题可问不可完成；原子的缝；扩张时记录不变                   15 条
lean/Grades.lean          第四轮：过滤、区间、加细迫使值代数、存在 = 计数的像、截断饱和、全知格                  34 条
lean/Cardinals.lean       第五轮：Dedekind 有限集不吸收一点也不吸收加倍；ℕ 吸收一点                               5 条
lean/Principles.lean      第三轮：有限性、不可驳倒层、缝                                                         10 条
lean/Invariants.lean      第二轮：Lawvere、Russell、Kripke 与复仇、等变性、全序破坏对称                           15 条
lean/Pzfc.lean            第一轮：单纯形复形 ⟹ 可粘合                                                            5 条
lean-mathlib/Weights.lean 第五、六轮：对数-指数和退化为 max；截断族；质量公式；吸收梯子；正则 ⟺ 可加性存活        18 条
lean-mathlib/WeightedGlue.lean
                          第十七轮：权重作为回答；存在是权重的影子；影子忘掉重数；Kolmogorov 被局部化（唯一；乘积）    5 条
lean-mathlib/WeightedKind.lean
                          第十八轮：[0, ∞] 是完备的值结构，带权种类的 GLU；支撑忘掉重数；坍缩后以 0/1 权重嵌入，影子是左逆        13 条
lean-mathlib/RandomChoice.lean
                          第二十一轮：随机的选取不需要选择——选不出一只袜子，但随机的一只是整体的对象，权重被对称定为 1/2        9 条
lean-mathlib/Observe.lean
                          第二十二轮：看得见什么由值决定（集合分不开，计数分得开）；硬币打破对称（2 种相同，n 种选出唯一领袖）      8 条
lean-mathlib/Views.lean   第二十二轮：有限系统上，对象恰好是确定性局部计算能分辨的东西（视图细化停止于 Larsen–Skou 互模拟）      5 条
lean-mathlib/Askable.lean
                          第二十六轮：可以问（有限读取以任意小误差回答）⟺ 可测；0-1 序列的情形；没有原子的来源没有记录；
                          有限的部分总有记录；对记录一切问题都可以问；
                          第二十七轮：可数多个零概率检验被几乎每个读数躲开；一切记录都能构造时每个读数都被抓住；
                          第二十八轮：同步耦合无记录而"相同"必然；独立耦合"相同"的概率为 0；
                          第四十一轮：可数世界中局部点集零测；新鲜样本几乎必然在世界之外；只有描述能被命中                  19 条
lean-mathlib/Sources.lean 第二十七轮：不以点为前提的来源（读取、规律、细化相容）；公平的硬币；读取问题的概率与层次无关；
                          来源的记录恰是原子；每层都有正权重的读取；公平的硬币没有记录；
                          第二十八轮：来源有记录 ⟺ 两遍独立重读一致的概率有正的下界                                            14 条
lean-mathlib/Fate.lean    第四十五轮：实数轴是零测集与贫乏集之并，平移的两种对偶；Fubini 的一步——正外测度与精确外测度在
                          测度型的记录下保持                                                                                    11 条
lean-mathlib/Kill.lean    第四十六轮：沿无穷集最终为常数的序列零测；不被分裂的集合消灭它不分裂的一切实数                 3 条
lean-mathlib/Sandwich.lean
                          第五十三轮：三段夹逼（上下界）；夹住的矩阵交叉比有界；对数超模数组的角点公式           5 条
lean-mathlib/Window.lean  第五十三轮：零测集族的 Fubini 覆盖——对测度典型的码只覆盖零测的旧点                       2 条
lean-mathlib/Envelope.lean
                          第六十六轮：窗口的下 Lipschitz 包络（inf-卷积）；在窗口之下、C₀-Lipschitz、最小值可达；
                          无接触的指标不是任何点的最小者；无接触段的界 C₀·g < 2(Γ−1)m（`117` 引理 3）        7 条
lean-mathlib/Corner.lean  第六十六轮：60° 角的调和三次式 h = xy(x+y)：三种步长的平均恰为 h（精确的鞅），
                          在两边为零、在角内为正；对侧的角；任意步数的迭代（`116` 命题 2）                   5 条
lean-mathlib/Stabilize.lean
                          第六十八轮：计算即沿记录化的稳定——按钮组合的改变数不超过未按下的按钮数；.2 ⟹ 极限唯一；
                          有限改变 + .2 ⟹ 答案 = 极限值翻转"剩余改变数"次，"至多改变 j 次"的集合持久（`122` 定理 A）；
                          第六十九轮：不需要 .2 的层表示——有限改变 ⟺ 2N+2 个持久集合的组合（`123` 定理 B）  10 条
lean-mathlib/Closure.lean 第七十一轮：平台短途的核有界的交叉比（`124` 定理 D 的代数部分）；四链 Vandermonde 精确调和、
                          在 Weyl 室壁上为零（`123 §3.2`）；偏序 = 一切线性扩张之交、单一忠实标量迫使全序（`121 §4.2`）；
                          稀有触发器几乎处处只命中有限次（`121 §3.2`，Borel–Cantelli）                             7 条
lean-mathlib/WorldsStable.lean
                          第七十一轮：把 `Worlds` 的扩张预序接到 `Stabilize`——M4 使可数核的陈述处于层 0；
                          处处可两头强迫的陈述是开关，能改变任意多次（`122 §3`、`123 §1.4`）                      4 条
lean-mathlib/Processes.lean
                          第二十三轮：不加观察所有过程同一；停止概率是对象的性质、合并保持它；对象比停止规律更细；循环对称迫使均匀分布 28 条
```

**不依赖 mathlib 的 463 条**中，240 条不依赖任何公理，208 条只依赖 `propext`、`Quot.sound`（或其一），15 条依赖 `Classical.choice`（除下列 8 条外：`Modal.dot3_of_connected`、`dot3_iff_connected`：.3 是析取式，要用排中律；`Protocols.all_perm`、`mixWeight_perm` 与 `Spectrum.perm_of_streams`、`realize_streams`、`spectrum_iff`：经由核心库的列表引理 `List.perm_iff_count` 等）。`Exchange` 的 26 条、`Traces` 的 5 条都不用选择。

依赖 `Classical.choice` 的 8 条：
- `Kinds.discrete_glue`：在互不相交的上下文上把局部的成员粘起来——恰好需要选择，这正是它的内容（`32 §1`）；
- `Kinds.roots_glue`、`Kinds.criterion`、`Kinds.cones_glue`、`Kinds.criterion_general`：判据的充分方向，选择用来在各个起点之间挑选（`35 §2`、`38 §2`）；必要方向 `roots_of_glue`、`cones_of_glue` 不用选择；
- `Glue.chain_glues`：依赖选择，按设计；
- `Axioms` 的 `expand_set_record`：关于模型的元定理，用经典逻辑；
- `Records.defect_eq_zero`：经由核心库的计数引理 `List.countP_eq_zero`；与它等价的 `record_iff_twice_copied` 不用选择。

第二十二轮以前的模块中，只依赖 `propext`、`Quot.sound` 的 115 条都不依赖选择：
- `Kinds` 的 30 条、`Shapes` §8–9（形状的拓展）的 14 条、`Values` 的 22 条、`Instances` 的 4 条、`Over` 的 7 条、`Symmetric` 的 20 条、`Local` 的 5 条：来自取商（`Values` 与 `Over` 的 GLU 只用 `Quot.sound`）；
- `Shapes` 的 `em_of_choice`（Diaconescu）：这正是它的内容——选择加上外延的认同迫使二值；
- `Scheme` 的 4 条：值的相等按外延认同（`solvesV_map` 不依赖任何公理）；
- `Glue` 权重一节的 5 条：来自 `unfold` 与 `omega`；
- `Grades` 的 2 条；`Axioms` 的 `expand_ext`。

**`lean-mathlib/` 的 173 条**（`Weights` 18 条、`WeightedGlue` 5 条、`WeightedKind` 13 条、`RandomChoice` 9 条、`Observe` 8 条、`Views` 5 条、`Processes` 28 条、`Askable` 19 条、`Sources` 14 条、`Fate` 11 条、`Kill` 3 条、`Sandwich` 5 条、`Window` 2 条、`Envelope` 7 条、`Corner` 5 条、`Stabilize` 10 条、`Closure` 7 条、`WorldsStable` 4 条）依赖 mathlib 的标准公理（含 `Classical.choice`，来自 [0, ∞] 上的经典求和）；`WeightedKind` 中只有坍缩的单射与封闭两条不依赖选择；`Corner.harmonic` 等多项式恒等式只依赖 `propext`、`Quot.sound`；`Stabilize.unique_limit`、`persistent_bounded` 不依赖任何公理。

两部分用同一个 Lean 版本（`lean/lean-toolchain`、`lean-mathlib/lean-toolchain`）。

```bash
cd lean && lake build                                   # mathlib-free 部分：没有依赖
cd lean-mathlib && lake exe cache get && lake build     # mathlib 部分：引用 mathlib 与 ../lean
```

若已有一个构建了同一 mathlib 版本（见 `lean-mathlib/lakefile.toml`）的 Lake 项目，也可以先在 `lean/` 里 `lake build`，再在那个项目里逐个编译 mathlib 部分：`LEAN_PATH=<pzfc>/lean/.lake/build/lib/lean lake env lean <pzfc>/lean-mathlib/WeightedKind.lean`。

`src/pzfc/` 与 `experiments/demo.py`：第一轮的应用层工具，已降级。`experiments/` 中其余脚本是第四十七轮以后的数值检验，索引见 [`experiments/README.md`](experiments/README.md)。
