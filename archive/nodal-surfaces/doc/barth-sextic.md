# Barth Sextic 数学复现文档

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

在 `P3` 中用坐标 `[w:x:y:z]`，设

```text
P = (tau^2*x^2 - y^2)(tau^2*y^2 - z^2)(tau^2*z^2 - x^2)
Q = x^2 + y^2 + z^2 - w^2.
```

与 Catanese Table 1 的节点坐标一致的 Barth sextic 归一化为：

```text
P - ((2*tau + 1)/4)*w^2*Q^2 = 0.
```

Rust 中使用清分母后的等价方程：

```text
F = 4*P - (2*tau + 1)*w^2*Q^2.
```

因为 `tau^2 = tau + 1`，所有系数都在 `Q(sqrt(5))`。`nodal-core` 已有 `QuadraticRational`
和 `BigQuadraticRational`，所以 degree06 不需要先实现一般代数数域。

注意：不同资料可能把 golden ratio 和 inverse golden ratio 的记号互换。代码中应固定代数定义
`tau^2 = tau + 1`，不要只依赖文字描述。

复现中还要特别注意系数归一化：如果误用

```text
P - 4*(2*tau + 1)*w^2*Q^2
```

则 Catanese Table 1 中的 `C12=[1:1:1:1]` 不在曲面上。当前 Rust 测试用全部 65 个表格节点反向校验了上述清分母方程。

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

## Rust 复现状态

当前已经新增 `crates/degree06` 并接入 workspace。实现采用 `Q(sqrt(5))` exact arithmetic，坐标顺序固定为：

```text
[w:x:y:z]
```

已完成：

- `barth_sextic_polynomial()`：返回清分母后的齐次六次式 `4P-(2*tau+1)w^2Q^2`。
- `barth_nodes_a()`、`barth_nodes_b()`、`barth_nodes_c()`、`barth_nodes()`：从 Catanese Table 1 转录 A/B/C 三类节点。
- `barth_nodes_a_orbit()`、`barth_nodes_b_orbit()`、`barth_nodes_c_orbit()`：用 Catanese Proposition 205 的
  `A5` 置换表示，从每类一个代表点生成完整 orbit，并与 Table 1 转录结果 exact 对齐。
- projective 去重：65 个表格点两两不同，且数量为 `15+30+20`。
- ordinary-node 验证：逐点 exact 检查 `F=0`、`grad F=0`、Hessian rank 为 `3`。
- line incidence 与标签作用：15 条 mid lines 每条含 3 个共线节点，10 条 centre lines 每条含 2 个不同节点；`sigma=(123)` 与 `tau=(14)(25)` 对 mid/centre labels 的作用和节点置换相容。
- support-strata Groebner 证书：15 个 projective support strata 的 quotient length 分布为：

```text
mask:   01 02 03 04 05 06 07 08 09 10 11 12 13 14 15
length:  0  1  2  1  2  0  4  1  2  0  4  0  4 12 32
```

长度总和：

```text
0+1+2+1+2+0+4+1+2+0+4+0+4+12+32 = 65.
```

每个 stratum 的 `.cert` 由 Cygwin-based Singular 生成，但 Rust exact verifier 会复查：

```text
generators match model
basis passes Buchberger
original generators reduce to 0
quotient length matches expected value
```

并且每个 `.cert` 都有对应 `.lift`，Rust 还会验证：

```text
G[j] = sum_i L[i,j] * I[i].
```

因此 normal-form 检查给出 `I subset <G>`，lift 检查给出 `<G> subset I`，两边合起来关闭 imported Groebner basis 与原 support ideal 的等价性。这一步把“当前方程至少有 65 个 ordinary nodes”升级为：

```text
当前 Barth 方程的 saturated projective singular scheme length = 65.
```

结合 65 个显式 ordinary nodes，得到：

```text
当前 Barth 方程恰有 65 个 reduced ordinary nodes，没有第 66 个奇点。
```

## Rust 复现路线回顾

### 阶段 1：最小模型

已新增 `crates/degree06`，先实现方程：

```rust
pub fn barth_sextic_polynomial() -> HomogeneousPolynomialP3<QuadraticRational>
```

基础测试：

```text
degree = 6
coefficients in Q(sqrt(5))
sample evaluation stable
```

这一阶段已完成。

### 阶段 2：节点候选

当前保留两种实现路线：

1. **表格路线**：从 Catanese Table 1 转录 65 个点坐标，作为 regression oracle。
2. **轨道路线**：实现 Catanese Proposition 205 的 `A5` 置换表示，从 A/B/C 三个代表点生成三个 orbit。

当前代码已经走通第二条路线的 combinatorial 版本：`sigma=(123)` 与 `tau=(14)(25)` 在 A/B/C 三张表上的置换分别生成单 orbit，
orbit sizes 为：

```text
|A| = 15, |B| = 30, |C| = 20.
```

这些 orbit 生成的 projective point set 与 Table 1 转录结果完全一致。也就是说，表格现在不是唯一数据源，而是对称生成路线的回归 oracle。
后续如果要进一步加固，可把当前置换表示提升为坐标上的线性二十面体作用；本轮已经足以证明 Table 1 的 A/B/C 分类确实是三个单 orbit。

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

当前已验证 `A5` 作用：

```text
A/B/C 分别是单 orbit
orbit sizes = 15, 30, 20
sigma/tau 对 mid-line labels 与 centre-line labels 的作用和节点置换一致
```

### 阶段 4：projective 穷尽证书

用 degree05 的 support-strata 思路，而不是简单相加 affine charts：

```text
support S = {xi != 0}
choose min(S) as chart variable = 1
coordinates outside S are set to 0
tau_local * product(nonzero affine coords) - 1 = 0
```

对 `P3` 有 15 个非空 support strata。当前每个 stratum 都已经生成一个 Singular grevlex Groebner certificate，并用 Rust 验证：

```text
generators match model
basis passes Buchberger
original generators reduce to 0
lift certificate proves imported basis lies in original ideal
quotient length for the stratum
```

所有 strata 的 quotient length 相加为：

```text
65.
```

这一步证明 saturated projective singular scheme 没有第 `66` 个点。

### 阶段 5：reduced / ordinary-node 升级

阶段 2 已经 exact 验证 65 个候选都是 ordinary nodes，而阶段 4 又证明 singular scheme 总 length 为 65，因此 reducedness 自动跟上：

```text
65 个 ordinary nodes 给出至少 65 个 length-1 局部分量
projective singular scheme 总 length = 65
=> 没有额外点，也没有高重数残留
```

也可以像 degree05 一样再补一个全局坏 Hessian locus 证书作为冗余验证：

```text
<F, Fx, Fy, Fz, det Hess_affine(F)> = <1>
```

但 Barth 有多个 charts，坏 Hessian 证书需要 chart-by-chart 或 support-strata 化。当前已经由 65 个 ordinary nodes 加总 length 65 推出 reduced ordinary-node 结论，所以坏 Hessian 证书不是本轮必需项。

## 上界来源

Barth sextic 给出 `mu(6) >= 65`。`mu(6) <= 65` 来自 sextic nodal surface 的 code/topology 上界路线：

```text
Jaffe-Ruberman: a sextic surface cannot have 66 nodes
Wahl / Pignatelli: alternative or refined proof route
Catanese survey: Appendix C reviews large-node sextic codes
```

本项目短期不复现这个上界证明，只在文档中引用为数学背景。工程证明已经覆盖的对象是：

```text
当前 Barth 方程确实有且仅有 65 个 reduced ordinary nodes.
```

## 资料位置和边界

本文件用到的资料分工如下：

- Barth 原始构造：`Barth, Two projective surfaces with many nodes, admitting the symmetries of the icosahedron`，这是 65 节点六次曲面的源头；本地暂未收录原文。
- Catanese 综述：本地 `arxiv/surveys/catanese-2022-nodal-surfaces-coding-theory-cubic-discriminants.txt` 给出 Barth 方程、A/B/C 节点表、orbit 说明和 Barth code 背景，是当前 degree06 的直接复现依据。当前实现以 Table 1 节点作为方程归一化校验，采用 `4P-(2*tau+1)w^2Q^2`。
- Catanese-Ceresa 1982：本地 `arxiv/construction/catanese-ceresa-1982-constructing-sextic-surfaces.*` 研究 trihedral sextics，并构造 `1 <= d <= 64` 个节点的六次曲面。它解释了 sextic 构造的前史，但不是 Barth 65 节点方程本身；这点要和 Barth 的二十面体构造区分开。
- Jaffe-Ruberman / Wahl / Pignatelli：给出 `mu(6) <= 65` 的上界路线。本项目短期只把它作为数学背景引用，Rust 主线先证明具体方程的 `65` 节点下界和穷尽性。

## 推荐下一步

1. 把当前 Proposition 205 的置换 orbit 路线继续升级为坐标上的线性二十面体作用，从而让 representative point 的坐标变换也进入 exact verifier。
2. 继续整理 Barth code、half-even sets 和 Doro-Hall graph 的关系，为 Endraß octic 的 code 视角做准备。
3. 如果后续需要冗余证书，再按 support strata 增加 Hessian-bad locus 为空的 chart-by-chart 证书。

本轮路线比直接 Groebner 求 65 个点更稳，因为它保留了 Barth sextic 的真正数学结构：二十面体对称和节点 orbit；Groebner 只负责最后的穷尽性。
