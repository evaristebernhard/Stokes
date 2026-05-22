# Degree08 Plane-Octic Plucker No-Go

这份文档记录八线乘积 critical-value profile 路线的几何失败机制。结论是：在特征零、八线一般位置、八个无穷远方向互异的 clean model 中，非零 fiber 的总 `delta` 不变量至多为 `16`。因此目标 `(28,19)` 被 Plucker flex 预算排除。

这不是数值搜索失败，而是模型自身的几何容量不足。

## 八线 profile 的几何重述

设

```text
Q_h = L_1 ... L_8
```

是八条仿射直线乘积的齐次化。考虑 pencil

```text
C_t : Q_h(x,y,w) - t w^8 = 0.
```

在 affine chart `w=1` 中，非零 fiber 的奇点满足：

```text
Q_x = Q_y = 0
Q = t != 0.
```

如果八条线一般位置，则 `Q=0` 的 28 个线交点给出 `t=0` 的 Morse 临界点；剩余 off-line 临界点总数为：

```text
(8-1)^2 - C(8,2) = 49 - 28 = 21.
```

所以八线 profile 的突破目标

```text
(28,19)
```

可以重述为：存在某个 `c != 0`，使平面八次曲线

```text
C_c : Q_h - c w^8 = 0
```

有 19 个 ordinary nodes。平面八次曲线的算术亏格是：

```text
p_a = (8-1)(8-2)/2 = 21.
```

因此 19 个节点意味着 normalization 的亏格为：

```text
g = 21 - 19 = 2.
```

这曾经看起来很有希望：问题从“21 个临界值里 19 个同值”变成“八线 pencil 中存在一条 genus-2 nodal octic fiber”。但这一步继续往下推，会直接遇到 Plucker 预算。

## 八个无穷远 total flex

对 `c != 0`，限制到某条原始直线 `L_i=0` 上，有：

```text
Q_h - c w^8 = -c w^8.
```

所以 `L_i` 与 `C_c` 的全部 8 次交点都集中在：

```text
P_i = {L_i=0} cap {w=0}.
```

如果八个方向互异，则在 `P_i` 附近其他 `L_j` 都非零，所以局部可写成：

```text
F = Q_h - c w^8 = U_i L_i - c w^8,
U_i(P_i) != 0.
```

于是：

```text
dF(P_i) = U_i(P_i) dL_i != 0.
```

因此 `P_i` 是 `C_c` 的光滑点，切线就是 `L_i=0`。又因为在直线 `L_i=0` 上：

```text
F|_{L_i} = -c w^8,
```

而 `w` 在 `L_i` 上于 `P_i` 简单消失，所以：

```text
L_i|_{C_c} = 8 P_i.
```

也就是说，每个 `P_i` 都是一个 8 阶 total-contact 点。对平面曲线的 `g^2_8`，一条切线在光滑点的一般接触阶是 2；接触阶 8 贡献 ramification/flex weight：

```text
8 - 2 = 6.
```

八个方向合计消耗 flex weight：

```text
8 * 6 = 48.
```

这一步的关键不是 torsion packet 是否存在；关键是这些 total-contact line 已经吃掉了平面八次模型的 inflection budget。

## Plucker 预算

更稳的写法是用 normalization 上由直线截出的 `g^2_8` 的 ramification 预算。若 `C_c` 的总 `delta` 不变量为 `delta(C_c)`，则 normalization 的亏格为：

```text
g = p_a - delta(C_c) = 21 - delta(C_c).
```

对 degree `8` 的平面模型，总 ramification weight 是：

```text
3(8 + 2g - 2)
= 3(8 + 2(21-delta(C_c)) - 2)
= 144 - 6 delta(C_c).
```

由于八个 infinity total flex 已经需要至少 `48`，必须有：

```text
144 - 6 delta(C_c) >= 48.
```

因此：

```text
delta(C_c) <= 16.
```

如果 `C_c` 的奇点都是 ordinary nodes，则节点数 `r` 正好等于 `delta(C_c)`，所以：

```text
r <= 16.
```

所以八线乘积 pencil 中的非零 nodal fiber 不可能给出 19 个 ordinary nodes；对应地，critical-value profile 的 `(28,19)` 不是“很难搜”，而是在这个几何模型中不应存在。

## 假设和边界

这个 no-go 应按以下假设理解：

- 工作在特征零，或至少避开 Plucker 公式和 Hessian 判别会退化的坏特征。
- 八条 affine line 一般位置：无重线、无平行、无三线共点；特别是零 fiber 的 `28` 个 line-arrangement 点确实是 ordinary nodes。
- 八条线在无穷远方向互异，因此八个 `P_i` 是不同光滑点。
- 没有把无穷远线 `w=0` 本身作为某个 `L_i`。
- `C_c` 的奇点都是 ordinary nodes，且目标节点数按普通平面 nodal curve 计。

如果方向重合、无穷远点奇异、或出现 cusp/tacnode 等非普通奇点，原来的 critical-profile 解释也会改变。用 `delta` 写法已经覆盖了很多非普通有限奇点的预算消耗；但为了文档严谨，这里只把结论声明为上述 clean model 的 no-go。

## 为什么 `16` 很自然

界限

```text
r <= 16
```

不是偶然的。若 `r=16`，则：

```text
144 - 6*16 = 48.
```

刚好等于八个 infinity total flex 的最低权重。也就是说，八线 pencil 最自然的极端 fiber 不是 genus 2 的 19-nodal octic，而是：

```text
16-nodal genus-5 octic fiber,
全部 flex weight 被无穷远八个 total-contact 点吃光。
```

这解释了为什么一些对称/dihedral profile 中自然出现 `16`，而 `19` 显得反几何。

## 对 degree08 搜索的影响

这条结论不证明 `mu(8)<=168`，也不排除所有八次曲面。它只排除一个特定机制：八线乘积 critical-profile 想通过某个非零平面八次 fiber 的 19 个 ordinary nodes 来实现 `(28,19)`。

因此八线 critical profile 应从主搜索路线降级为参考基础设施。有限域 `normal10` 搜索已经没有看到强信号，而 Plucker 预算说明这不是放量不足。

后续如果仍然使用二维 critical profile，应满足至少一个条件：

```text
1. 不再是 Q_h - t w^8 这种八线 total-contact pencil；
2. 改变无穷远接触结构；
3. 不再把目标解释为 19-nodal plane octic fiber；
4. 或转向真正不同的三维 construction，而不是八线乘积。
```

否则继续追 `(28,19)` 只是在几何上已经封闭的模型里增加样本。
