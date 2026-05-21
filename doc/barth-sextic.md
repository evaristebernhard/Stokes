# Barth Sextic 数学预备文档

## 当前目标

`degree06` 的标准极值例子是 Barth sextic。它给出六次 nodal surface 的尖锐下界：

```text
mu(6) >= 65.
```

Jaffe-Ruberman / Wahl / Pignatelli 这条上界路线证明 sextic surface 不能有 `66` 个 nodes，因此：

```text
mu(6) = 65.
```

本项目的复现目标分两层：

1. 对一个明确的 Barth sextic 方程，机器证明它恰有 `65` 个 reduced ordinary nodes。
2. 在文档中把 `65` 与已知上界 `mu(6) <= 65` 对齐；上界本身暂不尝试在 Rust 中复现。

## Barth 方程

Catanese 综述 4.3 从 Barth sextic 的定义方程出发。取

```text
tau = (1 + sqrt(5)) / 2,
tau_bar = (1 - sqrt(5)) / 2 = 1 - tau = -1/tau.
```

在 `P3` 中用坐标 `[w:x:y:z]`，Barth sextic 可写为：

```text
f(w,x,y,z)
= 1/4 * (tau^2*x^2 - y^2)
        * (tau^2*y^2 - z^2)
        * (tau^2*z^2 - x^2)
  - (2*tau + 1) * w^2 * (x^2 + y^2 + z^2 - w^2)^2.
```

后续 Rust 实现可以整体乘以 `4` 清掉分母：

```text
F = (tau^2*x^2 - y^2)(tau^2*y^2 - z^2)(tau^2*z^2 - x^2)
    - 4*(2*tau + 1)*w^2*(x^2 + y^2 + z^2 - w^2)^2.
```

因为 `tau^2 = tau + 1`，所有系数都在 `Q(sqrt(5))`。`nodal-core` 已有 `QuadraticRational`
和 `BigQuadraticRational`，所以 degree06 不需要先实现一般代数数域。

注意：不同资料可能把 golden ratio 和 inverse golden ratio 的记号互换。代码中应固定代数定义
`tau^2 = tau + 1`，不要只依赖文字描述。

## 二十面体几何

Barth sextic 的关键不是先解一个 65 点方程组，而是利用二十面体对称性。Catanese 综述使用下列二十面体顶点：

```text
(1, 0, ±tau, ±1),
(1, ±1, 0, ±tau),
(1, ±tau, ±1, 0).
```

二十面体的 face centres 和 edge midpoints 给出两类特殊直线：

```text
centre lines: 连接一对相对 face centres
mid lines:    连接一对相对 edge midpoints
```

组合计数为：

```text
10 centre lines
15 mid lines
```

Barth 的 65 个节点全部落在这些直线上：

```text
每条 mid line    含 3 个节点
每条 centre line 含 2 个节点

65 = 15*3 + 10*2.
```

这就是 degree06 的第一层数学结构：节点不是散装坐标，而是由二十面体线配置组织起来的。

## A/B/C 三类节点

Catanese 综述把节点分为三类。

### A 类

每条 mid line 与平面 `w = 0` 相交于一个节点，记为：

```text
A_(ij)(kl)
```

这些点对应 double transpositions，形成一个 `A5` orbit。数量为：

```text
15.
```

代表点可以选：

```text
A_(23)(45) = [0:1:0:0].
```

### B 类

每条 mid line 上，除了 `w = 0` 的 A 点之外，还有两个 affine 节点。Catanese 记为：

```text
B_ij(kl)
```

它们形成一个 `A5` orbit，数量为：

```text
30.
```

代表点可以从表中选：

```text
B_12(34) = [2:1:tau:-tau_bar].
```

这里的 `B_ab(cd)` 与 `B_ba(dc)` 被识别，所以不是 `60` 个，而是 `30` 个。

### C 类

每条 centre line 上有两个节点，分别靠近两个相对 face centre。Catanese 记为：

```text
C_ij.
```

这里 `(ij)` 作为 centre line 标签时不区分方向，但节点标签 `C_ij` 带方向：同一条 centre line 上的两个节点可看作 `C_ij` 和 `C_ji`。这些点形成一个 `A5` orbit，数量为：

```text
20.
```

因此总节点数为：

```text
|A| + |B| + |C| = 15 + 30 + 20 = 65.
```

## 与 degree05 的差异

degree05 special Togliatti 的成功路线是：

```text
w = 1 chart length 31
w = 0 infinity empty
Hessian-bad locus empty
lift certificates close ideal equality
```

Barth sextic 不适合照搬这个顺序，因为 15 个 A 类节点就在 `w = 0` 上。degree06 需要先把 projective geometry 放在正面：

```text
w = 0 不是边界噪音，而是节点结构的一部分。
```

所以 degree06 的正确姿势是：

1. 先用 A/B/C orbit 给出 65 个候选节点。
2. 对每个 orbit 代表点做 exact `F = grad F = 0` 与 Hessian rank 检查。
3. 再由 `A5` 对称性推出整个 orbit 都是 ordinary nodes。
4. 最后用 Groebner / support-strata 证书证明没有第 `66` 个奇点。

## Rust 复现路线

### 阶段 1：最小模型

新增 `crates/degree06`，先只实现方程：

```rust
pub fn barth_sextic_polynomial() -> HomogeneousPolynomialP3<QuadraticRational>
```

基础测试：

```text
degree = 6
coefficients in Q(sqrt(5))
sample evaluation stable
```

这一阶段不碰 Groebner。

### 阶段 2：节点候选

两种实现路线都可行：

1. **表格路线**：从 Catanese Table 1 转录 65 个点坐标。
2. **轨道路线**：实现 `A5` 的二十面体线性作用，从 A/B/C 三个代表点生成三个 orbit。

建议先走表格路线作为 regression oracle，再把轨道生成补上。这样可以避免一开始把群表示、标签和坐标约定混在一起调试。

候选点验证：

```text
F(P) = 0
grad F(P) = 0
rank Hessian(P) = 3
```

由于方程是齐次六次，在 `P3` 中 ordinary double point 对应 Hessian rank `3`。

### 阶段 3：orbit 结构验证

实现：

```text
barth_nodes_a() -> 15 points
barth_nodes_b() -> 30 points
barth_nodes_c() -> 20 points
barth_nodes()   -> 65 points
```

需要验证：

```text
三类点两两不交
projective 去重后总数为 65
A 类点全部满足 w = 0
B/C 类点全部满足 w != 0
每个 mid line 上正好 3 个节点
每个 centre line 上正好 2 个节点
```

如果后续实现 `A5` 作用，还应验证：

```text
A/B/C 分别是单 orbit
orbit sizes = 15, 30, 20
```

### 阶段 4：projective 穷尽证书

用 degree05 的 support-strata 思路，而不是简单相加 affine charts：

```text
support S = {xi != 0}
choose min(S) as chart variable = 1
coordinates outside S are set to 0
tau_local * product(nonzero affine coords) - 1 = 0
```

对 `P3` 有 15 个非空 support strata。每个 stratum 生成一个 Singular grevlex Groebner certificate，并用 Rust 验证：

```text
generators match model
basis passes Buchberger
original generators reduce to 0
lift certificate proves imported basis lies in original ideal
quotient length for the stratum
```

所有 strata 的 quotient length 相加应为：

```text
65.
```

这一步证明 saturated projective singular scheme 没有第 `66` 个点。

### 阶段 5：reduced / ordinary-node 升级

如果阶段 2 已经 exact 验证 65 个候选都是 ordinary nodes，而阶段 4 又证明 singular scheme 总 length 为 65，则 reducedness 自动跟上：

```text
65 个 ordinary nodes 给出至少 65 个 length-1 局部分量
projective singular scheme 总 length = 65
=> 没有额外点，也没有高重数残留
```

也可以像 degree05 一样再补一个全局坏 Hessian locus 证书：

```text
<F, Fx, Fy, Fz, det Hess_affine(F)> = <1>
```

但 Barth 有多个 charts，坏 Hessian 证书需要 chart-by-chart 或 support-strata 化。短期不必优先。

## 上界来源

Barth sextic 给出 `mu(6) >= 65`。`mu(6) <= 65` 来自 sextic nodal surface 的 code/topology 上界路线：

```text
Jaffe-Ruberman: a sextic surface cannot have 66 nodes
Wahl / Pignatelli: alternative or refined proof route
Catanese survey: Appendix C reviews large-node sextic codes
```

本项目短期不复现这个上界证明，只在文档中引用为数学背景。工程证明的对象是：

```text
当前 Barth 方程确实有且仅有 65 个 reduced ordinary nodes.
```

## 资料位置和边界

本文件用到的资料分工如下：

- Barth 原始构造：`Barth, Two projective surfaces with many nodes, admitting the symmetries of the icosahedron`，这是 65 节点六次曲面的源头；本地暂未收录原文。
- Catanese 综述：本地 `arxiv/surveys/catanese-2022-nodal-surfaces-coding-theory-cubic-discriminants.txt` 给出 Barth 方程、A/B/C 节点表、orbit 说明和 Barth code 背景，是当前 degree06 的直接复现依据。
- Catanese-Ceresa 1982：本地 `arxiv/construction/catanese-ceresa-1982-constructing-sextic-surfaces.*` 研究 trihedral sextics，并构造 `1 <= d <= 64` 个节点的六次曲面。它解释了 sextic 构造的前史，但不是 Barth 65 节点方程本身；这点要和 Barth 的二十面体构造区分开。
- Jaffe-Ruberman / Wahl / Pignatelli：给出 `mu(6) <= 65` 的上界路线。本项目短期只把它作为数学背景引用，Rust 主线先证明具体方程的 `65` 节点下界和穷尽性。

## 推荐下一步

1. 新建 `crates/degree06`。
2. 实现 Barth sextic 方程和基础 degree/evaluation 测试。
3. 从 Catanese Table 1 先转录 A/B/C 三类节点坐标。
4. 做 exact ordinary-node 验证。
5. 再补 support-strata Groebner certificates 做穷尽。

这条路线比直接 Groebner 求 65 个点更稳，因为它保留了 Barth sextic 的真正数学结构：二十面体对称和节点 orbit。
