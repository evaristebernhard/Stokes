# Degree08 Search Notes

## 目标

这一阶段不是声称找到了新的 octic，也不是证明 Endraß 曲面恰有 168 个节点。目标更窄：

```text
把 degree08 从结构复现升级成可校准的搜索器。
```

搜索器必须先认出 Endraß 自己：

```text
168 = 112 + 56
```

其中 `112` 是八平面乘积的基础盘，`56` 是 Segre trick 在反射平面上制造的额外事件。只有这个校准过了，后续 `D8 -> D4/D2` 破对称搜索才有意义。

## 统一搜索核心

当前代码已经把 D4 专用搜索器下沉到一个共享层：

```text
degree08::search_core
```

这个模块的语义是有限域上的“射影曲面实验平台”，不是某个具体构造族。它提供：

```text
Fp<P>
P^3(F_p), P^2(F_p), P^1(F_p) 的规范化枚举
齐次 P3 多项式的求值、梯度、Hessian rank
projective point normalize/key
symmetry orbit profile
ProjectiveSurfaceScorerInput
PlaneProductSkeleton for P8 - R4^2
ExperimentRecord for TSV/JSONL comparison
```

通用 scorer 输入是一张有限域齐次曲面：

```text
F(x0,x1,x2,x3) = 0 over F_p
```

它枚举 `P^3(F_p)`，记录所有满足

```text
F = Fx0 = Fx1 = Fx2 = Fx3 = 0
```

的点，并用 Hessian rank 区分：

```text
rank Hessian(F) = 3  -> node_like
rank Hessian(F) < 3  -> bad_sing
```

如果输入还带有 `PlaneProductSkeleton`，即

```text
P = H1*...*H8
F = P - R^2
```

scorer 会额外记录 `base_like`：点位于至少两张 `H_i` 上，且 `R(point)=0`，Hessian rank 仍为 `3`。这正是 Endraß `112` 底盘的有限域影子。`PlaneProductSkeleton` 也负责检查每条 `H_i cap H_j` 上的 `R|L` 是否是 squarefree degree 4，以及是否出现三平面交点落在 `R=0` 上的坏退化。

这层抽象的价值是：后续不再把所有搜索都硬塞进 `search_d4`。不同范式只需要生成一个 `F`，必要时附上 symmetry 和 skeleton，就能得到可比较的：

```text
total_sing, node_like, bad_sing, base_like, extra_like,
line_profile, orbit_profile, TSV/JSONL experiment record
```

因此三条路线可以共用同一把尺子：

```text
一般八平面 P8 - R4^2:
  继续保留或放宽 112 skeleton，研究 plane arrangement 与 R 的耦合。

Chmutov / folding / line-arrangement:
  不要求保留 112，把 node count、bad_sing、orbit profile 当作横向对照信号。

determinantal / discriminant:
  把 degree05 Togliatti 的经验迁移到 octic，先在有限域上寻找高奇点 discriminant-like 曲面。
```

## Critical-Value Profile 支线

八线乘积 `Q=prod l_i(x,y)` 的二维 profile 搜索已经单独记录在：

```text
doc/degree08-critical-profile-search.md
```

这条支线使用

```text
F = alpha*Q_h(x,y,w) + T8_h(z,w) + lambda*w^8
```

目标是利用 `T8` 的 `4/3` 临界值层，把二维 profile `(a,b)` 转成曲面节点数：

```text
N = 4a + 3b
```

八线 arrangement 的特殊意义是 `Q=0` 自动给出 28 个线交点 Morse 临界点，理论剩余预算为 `49-28=21`。因此最小突破目标是：

```text
(28,19) -> 169
```

当前 `slope-poly` 六参数有限域 smoke 没有发现 near hit：`p=31,47,97` 的 best visible profile 只达到 `28+3` 或 `28+2`。随后升级的 `normal10` 规范形覆盖一个 10 维 line-arrangement chart：

```text
L0=x, L1=y, L2=1-x-y,
Li=1+s_i(r_i*x+y), i=3,...,7
```

并加入 determinant 退化过滤、八线专用 fast profile、direction/intercept 分层采样、top-k heap、coordinate climb、pair sweep，以及 Singular off-line critical algebra 中筛。`p=31` 宽搜最好的 visible profile 仍是 `28+3`；同一整数参数在 `p=47/97` 降为 `28+1`。对

```text
K=<Qx,Qy,uQ-1>
```

计算 `m_Q` 的 charpoly/factorization 后，`off_best_bucket` 为 `3,1,1`，远低于继续信号阈值 `12`。这说明八线乘积支线的当前范式没有看到 off-line 21 点的强聚集；基础设施保留，但搜索重心应转向结构不同的 Chmutov/folding 或 Endraß 112 底盘改造，而不是继续同质放量。

后续几何复审进一步把这条支线降级：`Q_h - t w^8` 的非零平面八次 fiber 在八个无穷远方向上有 total-contact flex，Plucker 预算给出 `delta<=16`，因此 `(28,19)` 在特征零 clean model 中被排除。详细见 `doc/degree08-plane-octic-plucker.md`。

有限域信号必须小心解释。`F_p` 上的高 `node_like` 不等于特征零有同样多节点；小素数也可能制造伪奇点、合并点、或丢失不可见点。搜索层只负责“找值得 lift 的结构”，严格结论仍必须回到：

```text
exact F=grad=0
Hessian rank = 3
projective Jacobian ideal saturation
quotient length / reducedness / no extra singularity certificate
```

## 112 底盘

Endraß 使用

```text
F = P - R^2
```

其中 `P` 是 8 个平面的乘积，`R` 是四次式。任意两平面交出一条线，共有：

```text
C(8,2) = 28
```

在这些线上，`P` 至少二阶为零；若同时 `R=0`，则 `R^2` 也二阶为零。一般每条线与四次曲面 `R=0` 交 4 点，所以得到基础候选：

```text
28 * 4 = 112
```

代码中的有限域 scorer 对每个 projective 点记录：

```text
total_sing
node_like
bad_sing
base_like
extra_like
line_profile
orbit_profile
```

其中 `base_like` 的有限域判据是：

```text
F = grad F = 0
rank Hessian = 3
R(point) = 0
point lies on at least two P-planes
```

`line_profile` 记录 28 条平面交线分别贡献多少个 base-like 点。Endraß 在 `p=31`、`sqrt(2)=8` 的 reduction 中通过测试：

```text
total_sing = 168
node_like  = 168
bad_sing   = 0
base_like  = 112
extra_like = 56
sum(line_profile) = 112
```

这给 finite-field search 一个校准点。第二阶段又加入了基础盘的 algebraic-closure length scorer：对每条 `H_i cap H_j`，把 `R` 限制成二元齐次四次 `R|L`，检查：

```text
degree(R|L) = 4
R|L squarefree
no point of R=0 lies on three P-planes
```

若 28 条线都满足这些条件，则基础盘在代数闭包上的 scheme length 仍记为：

```text
28 * 4 = 112
```

这和 `F_p` 上实际可见根数分开记录。比如当前校准中 `p=73,89` 的基础盘 algebraic-closure length 仍为 `112`，但 `F_p` 可见根数为 `104`。

## Segre 事件

Endraß 的额外 56 个节点不是全局黑箱搜出来的，而是来自两个反射平面：

```text
E0 = { y = 0 }
E1 = { x = (1 + sqrt(2)) y }
```

因为最终方程具有 `D8 x Z2` 对称，限制到 `E0/E1` 后可以使用平方变量：

```text
U = axis^2
V = z^2
W = w^2
```

于是平面八次曲线降成平面四次曲线：

```text
G_E(U,V,W) = 0
```

当前 Rust verifier 已构造 `E0/E1` 的 quotient quartics，并检查五个额外事件：

```text
s3: quotient node       -> surface orbit 16
t3: z-axis contact      -> surface orbit  8
u5: quotient node       -> surface orbit 16
v1: w-axis contact      -> surface orbit  8
v2: z-axis contact      -> surface orbit  8
```

quotient node 的检查为：

```text
G = 0
grad G = 0
rank Hessian(G) = 2
```

axis contact 的检查为：把 `G` 限制到 `{z=0}` 或 `{w=0}` 后，对应二元四次在该点有重根。

随后每个事件 lift 回三维曲面并检查：

```text
F = 0
grad F = 0
rank Hessian(F) = 3
```

其中 `s3` 的 lift 坐标不在单纯的 `Q(sqrt(2))` 中，而在局部二次扩张

```text
Q(sqrt(2))(sqrt(8(sqrt(2)-1)))
```

代码为这个事件使用了一个专用的 nested quadratic field 元素，仅作为 degree08 的本地验证工具，没有上提到 `nodal-core`。

第二阶段把这个方向反过来做成有限域事件扫描器。给定平面四次 `G(U,V,W)`，搜索器统计：

```text
off-axis node: G = G_U = G_V = G_W = 0, U V W != 0, rank Hessian(G)=2
z-axis contact: G|_{V=0} 在 U,W 都非零的点有重根
w-axis contact: G|_{W=0} 在 U,V 都非零的点有重根
linear factor signature: F_p-rational projective lines contained in G
```

对 D4 搜索，使用两个代表反射平面：

```text
axis-y0       = { y = 0 }
diag-x-eq-y   = { x = y }
```

在 `D4 x Z2` 下，一般 quotient node 预期贡献长度 `8` 的曲面 orbit，轴接触预期贡献长度 `4` 的 orbit。完整 D8 校准仍使用 Endraß 原来的 `E0/E1`，它们不等同于 D4 的两个代表平面。

## D8 到 D4 的搜索族

完整 `D8 x Z2` 下，一个新的普通 orbit 往往有 8 或 16 个点。由于 Miyaoka 给出：

```text
mu(8) <= 174
```

从 `168` 再加一个完整大 orbit 会直接越界。因此真正有希望的搜索不是“更对称”，而是：

```text
保住 112 底盘，降低对称放大倍率，让额外事件以 1..6 的小批量出现。
```

粗略 orbit 粒度如下：

```text
D8 x Z2: 一般反射平面 node 贡献 16，轴接触贡献 8
D4 x Z2: 一般反射平面 node 贡献  8，轴接触贡献 4
D2 x Z2: 一般反射平面 node 贡献  4，轴接触贡献 2
更低对称: 才可能稳定地产生 1..6 的细粒度净增
```

因此 D4 更像第一轮破对称试验，目标是观察 `168 -> 172` 这一类信号；若要命中 `169,170,171,173,174`，D2 或更低对称可能更自然。

第一批破对称族取 `D4 x Z2`：

```text
P =
  (x^2 - A w^2)
  (y^2 - A w^2)
  ((x+y)^2 - B w^2)
  ((x-y)^2 - B w^2)
```

并把四次式放宽为：

```text
R =
  a(x^2+y^2)^2
  + h x^2 y^2
  +(x^2+y^2)(b z^2+d w^2)
  + e z^4
  + g z^2 w^2
  + i w^4
```

`h` 是最小的 D4 破对称参数；`h=0` 回到 Endraß 型。代码中的 `D4FamilyParameters` 使用有限域上的线性平面参数：

```text
axis_offset^2 = A
diagonal_offset^2 = B
```

并保留 `plane_scale`，使 `p=31`、`sqrt(2)=8` 时可以精确特化回 Endraß reduction。

## 为什么先扫事件约束

裸扫 `a,h,b,d,g,i` 很稀。额外奇点满足：

```text
G = P_E - r_E^2 = 0
dG = dP_E - 2 r_E dr_E = 0
```

若固定候选事件点 `q`，并引入 `rho = r_E(q)`，且 `rho^2 = P_E(q)`，则 node/contact 的一阶条件变成对 `R` 系数的线性约束：

```text
r_E(q)  = rho
dr_E(q) = dP_E(q) / (2*rho)
```

轴接触也类似：把 `G` 限制到轴上后，重根条件

```text
g(t0)=0
g'(t0)=0
```

可用

```text
r(t0)  = rho
r'(t0) = p'(t0)/(2*rho)
```

来线性化。当前 Rust 已经实现第一版“由事件约束反解参数”的有限域求解器：

```text
固定 D4 的 P 盘参数 axis_offset, diagonal_offset, plane_scale
-> 枚举反射平面 quotient 上的 q 与 rho, rho^2=P_E(q)
-> 对 R 的 7 个系数 a,h,b,d,e,g,i 建线性方程
-> 解 affine solution space
-> 枚举低自由维解并生成 D4FamilyParameters
```

这一步仍是第一阶段：它只固定 `P` 后反解 `R`，还没有同时搜索 `A,B,plane_scale`；并且 `rho=0` 的分支/切触事件不能使用 `dP/(2*rho)`，需要后续单独处理。当前实现支持非零 `rho` 的 off-axis quotient node、`z`-axis contact、`w`-axis contact。

## 扫描顺序

建议的扫描节奏：

```text
Stage 0:
  p=31, sqrt(2)=8
  复现 Endraß 168 = 112 + 56

Stage 1:
  固定 A=1, B=2
  枚举 quotient 事件并线性反解 R 的 7 个系数

Stage 2:
  固定 A=1
  扫 B 与 R 参数

Stage 3:
  同时扫 A,B,R
  排除平面碰撞、R|line 降次、bad_sing 增多的退化参数
```

候选排序不应只看 `total_sing`，而应惩罚坏奇点：

```text
score =
  node_like
  + predicted_quotient_event_weight
  - 1000 * bad_sing
  - 25 * |base_ac - 112|
  - 500 * triple_plane_bad_points
```

其中 `predicted_quotient_event_weight` 是 quotient node/contact 按预期 orbit size 加权的搜索信号，不等同于最终新增节点数。小素数上的高计数只表示“值得 lift 的信号”，不是特征零结论。

当前命令行入口：

```text
cargo run -p degree08 --bin search_d4
cargo run -p degree08 --bin search_d4 -- d4-window --prime 31 --radius 1 --limit 10
cargo run -p degree08 --bin search_d4 -- d4-events --prime 31 --solution-limit 40 --limit 5
cargo run -p degree08 --bin search_d4 -- d4-events --prime 31 --solution-limit 40 --limit 5 --format json
```

第一个命令输出 Endraß 多素数校准，其中 `segre_event_weight` 是 quotient 事件的加权预测信号：

```text
prime, sqrt2, global_visible_nodes, global_bad, base_ac, base_visible, segre_event_weight
```

第二个命令在指定素数上围绕 Endraß 参数做一个小 D4 窗口，输出 TSV 候选记录，包含：

```text
prime, score, total, node, bad, base_fp, extra,
base_ac, base_visible, events, params
```

`d4-events` 则执行真正的事件约束生成路线。默认过滤条件是：

```text
base_ac = 112
triple_plane_bad_points = 0
bad_sing = 0
quotient linear_factors = 0
```

并输出带 seed events 的 TSV 或 JSONL。TSV 字段为：

```text
seed_event_count, free_dim, seed_events,
prime, score, total, node, bad, base_fp, extra,
base_ac, base_visible, events, params
```

其中 `solution-limit` 控制实际枚举并进入过滤器的线性解数量；增大它会触发更多全局 `P^3(F_p)` singularity scorer，运行时间会明显增加。

校准素数当前固定为：

```text
p=31, sqrt(2)=8
p=41, sqrt(2)=17
p=73, sqrt(2)=32
p=89, sqrt(2)=25
```

其中 `p=31,41` 上 Endraß 的 `168` 个节点全部 `F_p` 可见；`p=73,89` 上全局可见 node 数变少，但基础盘 algebraic-closure length 仍为 `112`。

## 证明收口

若 finite-field search 找到候选，后续证明路线应为：

```text
finite-field candidate
-> 多素数稳定性检查
-> rational reconstruction 或代数数域 lift
-> exact F=grad=0 与 Hessian rank=3
-> projective Jacobian ideal saturation
-> quotient length / reducedness / no extra singularity certificate
```

当前第三阶段的第一步完成了事件驱动搜索的生成器，并把通用有限域搜索语义抽到了 `degree08::search_core`：有限域 scorer 可以识别 Endraß reduction，Segre verifier 可以解释额外 56 个节点的五个事件，D4 event scanner 可以输出 quotient event signature 和排序候选，`d4-events` 可以从非零 `rho` 事件约束反解 `R` 并筛选候选。完整的 `mu(8)` 突破仍需要更大搜索预算、`rho=0` 分支事件、D2/更低对称、跨素数稳定性、特征零 lift 和 saturation 证书；如果 112 路线停滞，下一轮应并行尝试一般八平面、Chmutov/folding、determinantal/discriminant 三种范式，并用同一个 `search_core` record 横向比较。

负结论整理见 `doc/degree08-no-go-summary.md`、`doc/degree08-splitting-conductor-no-go.md` 和 `doc/degree08-defect-rigidity-firewall.md`。这些文档的作用是把已经失败的结构路线变成候选审计规则，避免继续把启发式容量误当成节点构造。
