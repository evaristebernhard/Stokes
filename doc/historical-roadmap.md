# Nodal Surfaces 来时路

## 一句话地图

Endraß octic 不是孤立的漂亮方程，而是三条传统汇合：

1. 低次数极值例子：Cayley cubic、Kummer quartic、Togliatti quintic、Barth sextic。
2. 高对称构造：用群作用压缩搜索空间，让节点按轨道批量出现。
3. 上界理论：从 Basset/Segre 的经典界，到 Beauville/code，再到 Miyaoka/Varchenko。

## 已知小次数

设 `mu(d)` 为复射影三空间中只含 ordinary double points 的 `d` 次曲面最多节点数。

| d | mu(d) | 典型例子 | 构造主题 | 复现价值 |
|---|---:|---|---|---|
| 2 | 1 | quadric cone | 二次型秩分类 | 奇点检测最小例子 |
| 3 | 4 | Cayley cubic | 对称三次面，4 个坐标型节点 | 极适合起步 |
| 4 | 16 | Kummer quartic | Abelian surface / `±1` 商，`16_6` 配置 | 进入经典配置 |
| 5 | 31 | Togliatti quintic | 五重对称、coding theory、discriminant | 第一个非平凡上界 |
| 6 | 65 | Barth sextic | 二十面体对称、黄金比、code | 高对称极值构造 |
| 7 | 99 <= mu(7) <= 104 | Labs septic 等 | Chmutov/line arrangements | 未封顶区间 |
| 8 | 168 <= mu(8) <= 174 | Endraß octic | `D_8` 对称、Segre trick、计算机代数 | 当前主目标 |

Labs thesis 的表给出：

```text
upper: 0 1 4 16 31 65 104 174 246 360 ...
lower: 0 1 4 16 31 65  99 168 216 345 ...
```

所以 `d <= 6` 已经精确，`d = 7, 8` 开始出现下界和上界之间的裂缝。

## Segre Trick 的作用

Catanese-Ceresa 明确把核心归给 B. Segre：考虑坐标平方映射

```text
u_i = v_i^2
G(v) = F(v_0^2, v_1^2, v_2^2, v_3^2)
```

低次数曲面 `F=0` 与坐标四面体的位置，会变成高次数曲面 `G=0` 的奇点配置。

Catanese-Ceresa 的 Proposition 5 给出计数模板：

```text
nodes(G) = 8t + 4r + 2s + m
```

其中：

- `t`: `F` 自身的节点数。
- `r`: 坐标面与 `F` 的切点数。
- `s`: 坐标棱与 `F` 的切点数。
- `m`: 坐标顶点落在 `F` 上的个数。

Endraß 在三维八次曲面里不是原样套这个公式，而是在两个反射平面截线中复用这个思想：平面四次曲线上的节点/切点，通过对称性提升成三维曲面上的长度 16 或长度 8 的节点轨道。

## Endraß 的构造思想

Endraß 的族是：

```text
F = P - Q
```

`P` 是八个平面的乘积：

```text
P = product_{j=0}^7 (cos(j*pi/4)x + sin(j*pi/4)y - w)
```

`Q` 是四次式平方。这个结构立即给出：

```text
C(8,2) * 4 = 28 * 4 = 112
```

个基础节点候选。然后设 `c=f=h=0` 增加 `z -> -z` 对称，把问题降到两个反射平面 `E_0, E_1`。再调参数，让平面截线多出：

```text
s_3: 16
t_3:  8
u_5: 16
v_1:  8
v_2:  8
```

额外 `56` 个节点，因此：

```text
112 + 56 = 168
```

这不是随机搜索，而是“先内置 112 个节点，再用对称平面截线制造额外轨道”。

## 174 上界到底是谁

Endraß 的 `174` 来自 Miyaoka，不是 Varchenko。

Miyaoka 对带 quotient/rational double point 奇点的曲面给出 Chern 数预算。对 node `A_1`，局部贡献为 `3/2`。于是：

```text
(3/2) * mu(d) <= (2/3) * d * (d - 1)^2
```

所以：

```text
mu(d) <= floor((4/9) * d * (d - 1)^2)
```

代入 `d = 8`：

```text
floor((4/9) * 8 * 7^2) = floor(1568/9) = 174
```

Varchenko 是另一条 spectrum 半连续性路线。对 `P^3` 中八次 nodal surface，Varchenko/Arnold number 给的是：

```text
#{(k0,k1,k2,k3) in {1,...,7}^4 : k0+k1+k2+k3 = 13}
= C(12,3) - 4*C(5,3)
= 180
```

因此 `d=8` 时 Varchenko 界是 180，比 Miyaoka 的 174 弱。SURFER 或其他说明若把 174 归给 Varchenko，需要在我们的文档中标注为疑似误归因。

## 为什么低次数仍然要研究

二次、三次、四次不是“玩具”，它们给复现系统建立三种基本能力：

- `d=2`: 判定 isolated/non-isolated singularity。
- `d=3`: 验证 `F = grad F = 0`，并做射影坐标归一化。
- `d=4`: 理解节点配置、even sets、code 的几何含义。

五次、六次则直接进入 Endraß 的技术环境：

- `d=5`: Togliatti/Beauville 展示“构造”和“上界证明”开始分离。
- `d=6`: Barth/Jaffe-Ruberman 展示高对称构造与 code/拓扑上界的配合。

## 建议阅读顺序

1. Catanese-Ceresa 1982：先读 Proposition 5 和 sextic 构造思想。
2. Stagnaro 1983 + Beauville 1980：理解 `mu(5)=31` 的构造和上界。
3. Catanese 2022：读 Cayley/Kummer/Togliatti/Barth 的 code 统一视角。
4. Labs thesis：读表格、Miyaoka/Varchenko 比较和 Chmutov 章节。
5. Endraß 1995：回到八次曲面，重新看 `112 + 56`。

## 暂不写代码时的复现准备

- 为每个次数整理一个标准方程。
- 为每个方程列出奇点候选。
- 先手工验证 `F=grad F=0` 和 Hessian 非退化。
- 对带对称群的例子，先枚举一个代表点，再由群作用生成轨道。
- 真正写 Rust 前，明确哪些步骤是数值求解，哪些必须是精确代数数运算。
