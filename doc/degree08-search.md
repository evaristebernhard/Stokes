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

这给 finite-field search 一个校准点。

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

## D8 到 D4 的搜索族

完整 `D8 x Z2` 下，一个新的普通 orbit 往往有 8 或 16 个点。由于 Miyaoka 给出：

```text
mu(8) <= 174
```

从 `168` 再加一个完整大 orbit 会直接越界。因此真正有希望的搜索不是“更对称”，而是：

```text
保住 112 底盘，降低对称放大倍率，让额外事件以 1..6 的小批量出现。
```

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
  - large_penalty * bad_sing
  - penalty * |base_like - 112|
  + bonus * extra_like
```

小素数上的高计数只表示“值得 lift 的信号”，不是特征零结论。

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

当前第一阶段完成的是搜索主线的校准层：有限域 scorer 可以识别 Endraß reduction，Segre verifier 可以解释额外 56 个节点的五个事件。完整的 `mu(8)` 突破仍需要新的候选和 saturation 证书。
