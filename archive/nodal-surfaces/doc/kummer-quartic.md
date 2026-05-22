# Kummer Quartic 复现笔记

## 目标

`degree04` 复现的是一个显式 Kummer quartic：

```text
3(2x^2+2y^2+2z^2-3w^2)^2
- 28((w-z)^2-2x^2)((w+z)^2-2y^2) = 0
```

等价 affine chart `w = 1` 中：

```text
(x^2+y^2+z^2-3/2)^2
- 7/3 ((1-z)^2-2x^2)((1+z)^2-2y^2) = 0
```

代码中的多项式取了一个整数倍，所以 exact arithmetic 不需要处理分母。当前结论是：这个具体四次曲面恰好有 16 个 ordinary nodes，没有第 17 个奇点，并且它带有经典 `16_6` Kummer 配置。

## 从 `A/{±1}` 到 16 个节点

Kummer surface 的概念源头不是“碰巧找到一个有 16 个奇点的四次方程”，而是 Abelian surface 的商。

设 `A` 是复 Abelian surface，也就是二维复环面并带有足够好的代数极化。 involution

```text
p |-> -p
```

在 `A` 上的固定点正是二阶扭点：

```text
A[2] = {p in A | 2p = 0}.
```

因为 Abelian surface 的底层实维为 4，二阶扭点群是 4 个 `Z/2` 因子的向量空间：

```text
A[2] ~= (Z/2)^4,
```

所以一共有 `2^4 = 16` 个固定点。商 `A/{±1}` 在这些固定点处产生局部形如

```text
C^2 / {±1}
```

的 `A_1` rational double point，也就是普通二重点。把这个商通过合适的线性系统嵌入 `P^3`，得到的四次曲面就是 Kummer quartic；16 个二阶扭点的像就是 16 个节点。

这解释了为什么 Kummer quartic 的 16 个点不是散装奇点：它们来自同一个有限群 `A[2]`，背后是 Abelian surface 的对称性和极化。

## `mu(4) = 16`

记 `mu(d)` 为复射影空间 `P^3` 中 degree `d` nodal surface 的最大 node 数。Miyaoka 对 quotient singularities 给出上界；对只含 node 的 degree `d` 曲面，可写成常用形式：

```text
mu(d) <= floor(4/9 * d * (d - 1)^2).
```

代入 `d = 4`：

```text
floor(4/9 * 4 * 3^2) = 16.
```

Kummer quartic 提供了 16 个 ordinary nodes，因此：

```text
mu(4) = 16.
```

注意：Miyaoka 上界只说明“最多 16 个”，不说明某个给定方程真的有 16 个、也不说明没有其他非节点奇点。因此代码仍然需要对当前显式方程做 singular-locus exhaustion。

## 当前方程的奇异集穷尽

在 `w = 1` chart，令 `X = x^2`, `Y = y^2`。affine 方程展开为：

```text
F = 12x^4 - 88x^2y^2 + 80x^2z^2 + 112x^2z + 20x^2
  + 12y^4 + 80y^2z^2 - 112y^2z + 20y^2
  - 16z^4 + 20z^2 - 1.
```

三个 affine 偏导因式分解为：

```text
Fx = 8x(6X - 22Y + 20z^2 + 28z + 5)
Fy = -8y(22X - 6Y - 20z^2 + 28z - 5)
Fz = 8((20z+14)X + (20z-14)Y - 8z^3 + 5z).
```

于是梯度方程分成四类：

```text
x = 0, y = 0
x = 0, y != 0
y = 0, x != 0
x != 0, y != 0
```

代码把这四类化成 11 个 exact 分支，总共有 27 个 affine gradient candidates。其中只有 16 个满足 `F = 0`，它们正好是 `kummer_nodes()` 列出的 16 个点；剩余 11 个只是 affine gradient 的临界点，不在曲面上。

在 `w = 0` infinity chart，前三个偏导约化为：

```text
Fx = 16x(3x^2 - 11y^2 + 10z^2)
Fy = -16y(11x^2 - 3y^2 - 10z^2)
Fz = 32z(5x^2 + 5y^2 - 2z^2).
```

若 `x,y,z` 全非零，令 `X=x^2,Y=y^2,Z=z^2`，得到线性系统：

```text
 3X - 11Y + 10Z = 0
11X -  3Y - 10Z = 0
 5X +  5Y -  2Z = 0
```

该系统秩为 3，所以只给出 `X=Y=Z=0`，不对应射影点。若某个坐标为 0，则代码检查三个 `2 x 2` 子系统也都是满秩，仍然迫使非零坐标平方为 0。故 `w = 0` 没有奇点。

这两张 chart 合在一起，证明当前方程不存在第 17 个奇点。

## Ordinary node 检查

穷尽证明只给出奇异点集合。要确认它们是 ordinary double points，还需要看二次项是否非退化。

代码对 16 个点逐一计算 Hessian，并验证 rank 为 3。对 `P^3` 中的 degree 4 hypersurface，齐次方向会带来一个射影缩放方向，因此 ordinary node 对应的 Hessian rank 是 3，而不是 4。

## `16_6` 配置

经典 Kummer quartic 还有 16 个 trope。这里的 trope 是一个特殊平面：曲面与该平面的交不是一般四次平面曲线，而是一个二次曲线的二倍：

```text
S ∩ H = 2C.
```

每个 trope 平面经过 6 个 nodes；反过来，每个 node 落在 6 个 tropes 上。因此形成：

```text
16 nodes, 16 tropes,
每个 trope 过 6 nodes,
每个 node 在 6 tropes 上。
```

这就是经典 `16_6` 配置。`degree04` 中的实现做了两层 exact 验证：

- 对 16 个平面逐一计算 incidence matrix，检查每行和每列都是 6。
- 对每个平面，把 quartic 限制到该平面，并和 `scalar * conic^2` 做系数级比较，确认它确实是 trope。

因此代码现在不只是验证“16 个节点在若干平面上”，还验证这些平面在当前 quartic 上确实是 double-conic 平面截面。

## 边界与后续

这仍然是一个特殊 Kummer quartic 的工程复现，不是所有 Kummer quartic 的分类证明。它的价值在于：

- degree 4 的最大节点数达到上界，作为低次数路线中的基准例子。
- `A[2] ~= (Z/2)^4` 给出节点来源，不是纯数值搜索。
- `16_6` 配置提供了比点验证更强的结构性校验。
- chart-by-chart certificate 是后续 degree 5、6、8 复现时可以沿用的证明风格。

参考路线主要见 `doc/historical-roadmap.md` 和 `doc/bibliography.md` 中关于 Kummer、Miyaoka、Catanese 综述与 Barth/Labs 历史线索的条目。
