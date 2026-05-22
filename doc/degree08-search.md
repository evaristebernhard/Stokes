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

来线性化。当前 Rust 还没有实现“由事件约束反解参数”的线性系统求解器；已经完成的是把给定参数投影到这些低维 quotient 事件上做计数、签名和排序。后续应优先枚举事件组合，再解线性约束，而不是盲目随机扫全参数。

## 扫描顺序

建议的扫描节奏：

```text
Stage 0:
  p=31, sqrt(2)=8
  复现 Endraß 168 = 112 + 56

Stage 1:
  固定 A=1, B=2
  在 Endraß 参数附近扫 h 和 R 的小扰动

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

当前第二阶段完成的是事件驱动搜索的第一版：有限域 scorer 可以识别 Endraß reduction，Segre verifier 可以解释额外 56 个节点的五个事件，D4 event scanner 可以输出 quotient event signature 和排序候选。完整的 `mu(8)` 突破仍需要新的候选、跨素数稳定性、特征零 lift 和 saturation 证书。
