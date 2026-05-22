# Degree08 Splitting And Conductor No-Go

这份文档整理 splitting divisor、sign cocycle、conductor web、two-cubic residual、Steiner/double-six 等路线的负结论。核心不是说这些结构没有价值，而是说它们不能被直接当作 `169..174` 个 ordinary nodes 的来源。

最重要的教训是：

```text
局部 sign / cycle / splitting 数据不会自动变成八次节点缺陷。
节点数、ordinary 条件、H^1(I_Σ(8)) 必须在同一个 ambient P3 中核算。
```

文档里的 pair-stratum 计数在 normal-crossing 与 transversality 假设下可以严格化；triple-vertex 与 graph-cycle 计数只作为 heuristic capacity，不代表 ordinary nodes 或 `h^1` defect。square-root gluing 的组合自由度必须经过：

```text
residual vanishing
Hessian rank
postulation defect
```

三重过滤。

## Endrass 型 product boundary

Endrass 的基本形状是：

```text
F = P - R^2,
P = H_1 ... H_8.
```

八个平面两两相交给出：

```text
C(8,2) = 28
```

条直线。在每条交线上，`P` 至少二阶为零；若再要求 `R=0`，则一般有四个根。因此基础盘是：

```text
28 * 4 = 112.
```

额外 `56` 个节点不是三平面交点的自动贡献。Endrass 使用 `D8` 对称和 Segre trick，在两个反射平面 quotient 上制造 node/contact 事件；这些事件 lift 到三维后给出 orbit sizes：

```text
16, 8, 16, 8, 8.
```

这些数相加为：

```text
56.
```

八个平面的三重交组合数也是：

```text
C(8,3) = 56.
```

所以在 very generous 的 plane-only 容量启发中，可以把它记成：

```text
112 + 56 = 168.
```

但这不是“三平面交点自动变成节点”的定理，也不是已证明的全局上界。它只解释 Endrass 为什么能精确打到 `168`，以及为什么“继续在同一八平面 skeleton 上加点”非常紧。

## 分块 product boundary 的预算下降

考虑更一般的 product boundary：

```text
F = R^2 - A_1 ... A_m,
sum d_i = 8.
```

在代数闭域、`char != 2`，并且 `A_i` squarefree、两两无公共曲面成分、pair stratum 远离高阶交处为 reduced lci curve、其余因子在该曲线上非零的情形下，pair 计数可以严格化。

若两个分量 `A_i=0`、`A_j=0` 横截相交，则交曲线 degree 为 `d_i d_j`。四次式 `R` 在该交曲线上给出 degree：

```text
4 d_i d_j
```

的基础候选。因此 pair budget 是：

```text
4 * sum_{i<j} d_i d_j.
```

ordinary node 还要求 `R|_{V(A_i,A_j)}` 的零点 simple；局部二次型 then looks like：

```text
r^2 - u v.
```

三重 vertex 完全不同。局部裸模型是：

```text
F = r^2 - u v w * unit.
```

若 `r(P) != 0`，点不在曲面上；若 `r(P)=0` 且 `dr(P) != 0`，二次项只是一个平方，Hessian rank 至多为 `1`，不是 ordinary node。因此：

```text
e_3 = sum_{i<j<k} d_i d_j d_k
```

只能记录三重 conductor vertices 的组合数量。如果某个额外局部机制能在每个 vertex 附近至多产生一个有效 ordinary node，那么 `e_3` 是一个极其慷慨的 fantasy cap。裸 product-square model 中，三重点本身并不自动产生 ordinary nodes。

所以一个宽松 heuristic capacity 是：

```text
N <= 4 e_2 + e_3.
```

下表应读作“pair budget + one-event-per-triple fantasy cap”，不是 theorem：

```text
8 planes:            112 + 56 = 168
2 quadrics+4 planes: 104 + 44 = 148
4 quadrics:           96 + 32 = 128
2 cubics+2 planes:    88 + 24 = 112
```

即使用这样慷慨的 cap，把八个平面合并成高次数块也通常不是增加容量，而是在 pair skeleton 上先亏掉一大截。

## Clean gluing 会塌回 product boundary

设两个局部 splitting 表达为：

```text
F = Q_A^2 + A G_A
F = Q_B^2 + B G_B.
```

在 conductor

```text
C = V(A,B)
```

上，如果 `A,B` coprime，`C` 是 reduced lci，并且 scheme-theoretically `I_C=(A,B)`。若在 `C` 上有固定符号：

```text
Q_A = ± Q_B mod (A,B),
```

则可取某个全局四次式 `R`，使：

```text
R = Q_A mod A,
R = ± Q_B mod B.
```

于是：

```text
F - R^2 in (A B),
```

从而形式上回到：

```text
F = R^2 + A B H.
```

也就是说，干净 irreducible conductor 上的 sign gluing 并没有创造新的机制；它只是 product boundary 的另一种写法。

这个结论的关键词是“固定符号”和“scheme-theoretically”。如果只是 set-theoretic，或 conductor 非 reduced / 有 embedded structure，结论不够稳。若 conductor 可约，符号可以按分量变化；这会产生 cocycle 问题，但也会带来下面的容量损失。

## Sign jump 不自动产生 node

可约 conductor 上，sign pattern 可能沿不同分量跳变。局部模型可以写成：

```text
F = q^2 + A G.
```

sign jump 通常强迫的是：

```text
q = 0
```

在 `A=q=0` 上：

```text
dF = G dA.
```

所以奇点还需要：

```text
G = 0
```

ordinary node 还需要：

```text
dA, dq, dG independent.
```

此时局部二次型等价于：

```text
q^2 + A G.
```

因此 graph cycle、sign cocycle、even set 这类数据最多先给出“可能在哪里发生局部 A1”的门槛机制；它们不等于节点计数。

更重要的是，多个 splitting block 不能 raw-add。不同 block 在 conductor 上共享 restriction，四次根被迫对齐，很多看似独立的局部条件其实是同一批根。

一个干净 web 的保守审计应先扣掉 pair root 的重复贡献，再把 triple vertex 只作为 `tau` 型 fantasy cap：

```text
N <= sum_i 4 d_i(8-d_i) - 4 sum_{i<j} d_i d_j + tau,
tau <= sum_{i<j<k} d_i d_j d_k.
```

这个式子不是最终定理，而是一个审计规则：如果一个 proposal 只是在多个 splitting divisor 上重复数同一批 conductor roots，它的节点预算应被立即降级。

## Two-Cubic residual 的失败

一条一开始很诱人的思路是：每个 cubic block 都带一个 complete-intersection 型节点包

```text
Z = CI(3,4,5),
|Z| = 60.
```

并且有很大的 Cayley-Bacharach 缺陷：

```text
h^1(I_Z(5)) = 19
h^1(I_Z(6)) = 10
h^1(I_Z(7)) = 4
h^1(I_Z(8)) = 1.
```

看起来两个 cubic block 也许能把 defect 叠起来。但在一个 clean complete-intersection gluing model 中，两个 cubic 若属于同一个 octic，它们在 conductor `D_1 cap D_2` 上共享 `O_C(4)` 的零 divisor：

```text
deg O_C(4) = 36.
```

所以并集长度不是 `120`，而是：

```text
|Z_1 union Z_2| = 60 + 60 - 36 = 84.
```

残差也从想象中的高缺陷对象变成：

```text
CI(2,3,4),
|R| = 24.
```

它只带来很少的 Cayley-Bacharach 关系，而不是两个独立的 `19`。这条失败非常有代表性：单个 block 的漂亮 cohomology 不能直接在同一个 octic 里相加。但它不是排除所有 cubic-based construction 的定理，只是排除“两个 cubic block raw-add defect”的朴素版本。

## Steiner 和 double-six 的降级

Steiner 9-line conductor 有：

```text
V = 9, E = 18, b1 = 10.
```

它适合作为局部 sign-jump / A1 测试模型，但不是 `169` 节点 backbone。`b1=10` 只是 graph cycle space 的维数，不等于八次节点集的 `h^1(I_Σ(8))`。

double-six cubic-quartic conductor 更诱人，因为 12 条线形成：

```text
K_{6,6} minus matching,
b1 = 19.
```

但这个 `19` 生活在 conductor graph 或 `Pic^0(C)[2]` 的符号选择里，不自动进入：

```text
h^1(I_Σ(8)).
```

还要注意 ambient roots 通常是 untwisted 的：

```text
H^0(C, O_C(4)),
```

而不是任意扭曲的：

```text
H^0(C, O_C(4) tensor eta).
```

若要把它变成真正的 defect，需要补完整链条：

```text
sign cocycle
-> actual square-root section
-> residual G vanishing
-> ordinary-node transversality
-> evaluation matrix on Sigma has required corank.
```

如果 sign pattern 只是 vertex cut，而不是 cycle-space 中可被 ambient quartic 实现的 twist，那么它不会给出新的节点包。

## 当前判断

splitting-divisor cocycle 仍然是理解 double-octic 边界的好语言，但它不是突破 `168` 的免费机器。一个有希望的 proposal 至少要同时回答：

```text
1. 节点在哪里，而不仅是 sign 在哪里跳；
2. ordinary node 的三个局部独立条件如何满足；
3. conductor roots 是否被多个 block 重复计算；
4. graph/cocycle 数据如何进入 H^1(I_Σ(8))；
5. h^0(I_Σ(8)) 是否被额外 adjoint 撑大。
```

如果这些问题答不上来，就应把该路线归为“边界模型启发”，而不是 `169..174` 的候选构造。
