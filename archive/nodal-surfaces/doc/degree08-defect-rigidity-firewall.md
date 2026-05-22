# Degree08 Defect And Rigidity Firewall

这份文档整理 nodal double octic 的 defect、rigidity 和 adjoint 约束。它回答一个核心问题：

```text
是否存在长度 169..174 的节点集 Sigma，
使 h^1(I_Sigma(8)) >= 20，
并且它能作为某个 octic 的 ordinary-node singular locus？
```

结论不是简单的“不能”，而是：这个问题必须和 `h^0(I_Σ(8))`、Jacobian degree-8 piece、低次数 adjoint 风险一起看。否则很容易把一个高缺陷节点集误判为 rigid double octic 候选。

## 基本公式

令 `S={F=0}` 是 `P3` 中 reduced、且只含 ordinary nodes 的八次曲面，节点集为 reduced scheme：

```text
Sigma,  N = |Sigma|.
```

在 `P3` 中：

```text
h^0(O_P3(8)) = C(8+3,3) = C(11,3) = 165.
```

由

```text
0 -> I_Sigma(8) -> O_P3(8) -> O_Sigma -> 0
```

以及 `H^1(O_P3(8))=0`、`h^0(O_Sigma)=N`，
得到 defect：

```text
delta := h^1(I_Sigma(8))
      = N - 165 + h^0(I_Sigma(8)).
```

这里的次数 `8` 不是随便来的。对 degree `2d` double solid，defect 检测次数是：

```text
3d - 4.
```

octic 是 `2d=8`、`d=4`，所以正好是 `8`。

考虑双覆盖：

```text
X : u^2 = F(x0,x1,x2,x3) subset P(4,1,1,1,1).
```

在节点上，`X` 有三维 ordinary double points。下面的 Hodge 公式应理解为对存在 projective/Kahler small crepant resolution 的 nodal double octic 使用的标准公式。smooth double octic 有：

```text
h^{1,1}=1, h^{2,1}=149.
```

其中 `149` 可由参数计数看出：

```text
h^0(O_P3(8)) - 1 - dim PGL_4
= 165 - 1 - 15
= 149.
```

节点情形的常用公式为：

```text
h^{1,1} = 1 + delta,
h^{2,1} = 149 + delta - N.
```

代入上式得到非常尖锐的关系：

```text
h^{2,1} = h^0(I_Sigma(8)) - 16.
```

所以刚性条件 `h^{2,1}=0` 要求：

```text
h^0(I_Sigma(8)) = 16.
```

这就是 firewall：节点数多本身不保证刚性；真正要控制的是所有穿过节点集的八次曲面维数。

## Jacobian 维数的含义

若 `F` 是八次式，则四个偏导：

```text
F_x0, F_x1, F_x2, F_x3
```

是七次式。任意一次线性形式乘以偏导，都会得到过所有节点的八次式：

```text
linear forms * F_xi.
```

这些生成 Jacobian degree-8 piece：

```text
J_F,8 = span{x_i * F_xj : 0 <= i,j <= 3}.
```

它们来自坐标变化和缩放的 trivial adjoints。在 `F` 没有正维 infinitesimal projective stabilizer 的一般情形下：

```text
dim J_F,8 = 16.
```

刚性 double octic 的理想图像不是仅仅 `h^0=16`，而是更精确的：

```text
H^0(I_Sigma(8)) = J_F,8.
```

也就是说，不存在 Jacobian 之外的额外八次 adjoint。

同理，七次层也应该非常小：

```text
h^0(I_Sigma(7)) = 4,
I_Sigma(7) = <F_x0,F_x1,F_x2,F_x3>.
```

如果七次层已经超过 4，八次层通常也会随之增大，刚性会立刻变危险。

## 为什么 `h^1 >= 20` 不够

假设 `N=169`。若想有：

```text
h^1(I_Sigma(8)) >= 20,
```

由 defect 公式得到：

```text
h^0(I_Sigma(8)) >= 165 - 169 + 20 = 16.
```

看起来这正好 compatible with rigidity。事实上对于 `N=169..174`，刚性要求的 defect 分别是：

```text
N=169 -> delta=20
N=170 -> delta=21
N=171 -> delta=22
N=172 -> delta=23
N=173 -> delta=24
N=174 -> delta=25
```

这些数都来自同一个刚性条件：

```text
h^0(I_Sigma(8)) = 16.
```

因此问题不能只问 `h^1` 大不大，而要问：

```text
delta 是否刚好等于 N - 149，
并且 H^0(I_Sigma(8)) 是否正好等于 J_F,8？
```

如果 `h^0(I_Sigma(8)) > 16`，则：

```text
h^{2,1} > 0,
```

候选就不再 rigid。

## 低次数曲面的危险

很多构造会让节点集自然落在某个低次数曲面上。但这对刚性通常是坏消息，因为若全体 `Sigma` 落在 degree `m` 曲面 `G=0` 上，则：

```text
G * H^0(O(8-m)) subset H^0(I_Sigma(8)).
```

低次数曲面乘上互补次数的任意多项式，会产生大量八次 adjoint。

典型风险：

```text
quartic * H^0(O(4)) -> C(7,3) = 35 dimensions
cubic   * H^0(O(5)) -> C(8,3) = 56 dimensions
quintic * H^0(O(3)) -> C(6,3) = 20 dimensions
```

这些维数都已经超过 `16`。当然，实际 `h^0(I_Σ(8))` 还要考虑不同低次数曲面之间的依赖、基分量和是否真的包含全部节点。若只是一个大子配置落在低次数曲面上，它是 defect/residual risk，而不是立即杀死刚性的定理；但作为 firewall，这个检查非常有效：

```text
如果全体 Sigma 被一个低次数 surface 机械地包含，
先怀疑它会产生额外 adjoints。
```

这也是 arrangement boundary smoothing 的难点。边界模型越组合、越可分解，越容易留下低次数 adjoint，从而破坏 rigid double octic 的目标。

## 对 arrangement boundary smoothing 的审计

八平面 arrangement double octic 有许多 rigid 例子，但它们的 branch divisor 通常不是 nodal surface，而是有线、点、高重交等非孤立奇异性。把它们作为边界模型时，问题不是“能不能 smooth 出很多节点”这么简单，而是：

```text
1. smoothing 后 branch 是否只剩 ordinary nodes；
2. 节点数是否在 169..174；
3. H^0(I_Sigma(8)) 是否仍等于 J_F,8；
4. 原 arrangement 的低次数 splitting/adjoin 数据是否消失；
5. 解析小分辨或 crepant resolution 后 h^{2,1} 是否仍为 0。
```

如果 smoothing 保留了太多 arrangement 的低次数结构，则 `h^0(I_Σ(8))` 会超过 16；如果 smoothing 把结构全部打散，又很难保留所需的 defect。这个张力就是 rigid double-octic route 的核心难点。

## 与 Endrass 的关系

Endrass 的 `168` 节点曲面处在很特殊的位置：

```text
168 = 112 + 56.
```

它有强结构，但没有显然把节点集塞进一个低次数曲面的简单解释。若试图从 Endrass 继续加节点，需要同时保持：

```text
H^0(I_Sigma(8)) = J_F,8
```

且不能引入 Jacobian 之外的八次 adjoint。由于 Miyaoka 上界只剩 6 个空位，任何新增 orbit 都很容易带来：

```text
节点数上升一点，
但 h^0(I_Sigma(8)) 也上升，
从而 h^{2,1} 不再为 0。
```

这解释了为什么“多找几个节点”不是正确目标。正确目标是找到一种新的结构，使新增节点同时带来恰当的 defect，而不带来额外 adjoints。

## 候选需要的最小证书

对一个声称 `169..174` 节点、并可能给出 rigid double octic 的候选，至少需要：

```text
1. projective singular scheme saturation:
   Sigma 是完整奇异集，没有第 N+1 个奇点。

2. ordinary node check:
   每点 Hessian rank 为 3，且 singular scheme reduced。

3. degree-7 adjoint check:
   h^0(I_Sigma(7)) = 4，并由 F 的四个偏导生成。

4. degree-8 adjoint check:
   h^0(I_Sigma(8)) = 16。

5. Jacobian equality:
   H^0(I_Sigma(8)) 与 J_F,8=<x_i*F_xj> 一致。
```

没有第 3 到第 5 步，即使点数很多，也只是一个 nodal octic 候选，不是 rigid double-octic 候选。

## 当前判断

问题

```text
是否存在长度 169..174 的 Sigma，
使 h^1(I_Sigma(8)) >= 20，
并作为某个 octic 的 ordinary-node singular locus？
```

本身仍然是正确的数学转写。但它应该进一步收紧为：

```text
是否存在这样的 Sigma 和 F，
使 I_Sigma(8) 正好是 F 的 Jacobian degree-8 piece？
```

这才是 rigid double-octic 类型真正需要的条件。未来的搜索如果不先通过这个 firewall，就很可能只是制造高缺陷、非刚性的 nodal octic。
