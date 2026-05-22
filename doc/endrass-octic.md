# Endrass Octic

## 目标

Endrass 的八次曲面给出目前经典的八次 nodal surface 下界：

```text
168 <= mu(8) <= 174.
```

这里 `168` 来自显式曲面，`174` 来自 Miyaoka 的 nodal surface 上界

```text
mu(d) <= floor(4/9 * d * (d - 1)^2).
```

代入 `d=8` 得 `floor(1568/9)=174`。需要特别区分：Varchenko/Arnold number 在 `d=8` 给出的是

```text
#{(k0,k1,k2,k3) in {1,...,7}^4 : k0+k1+k2+k3=13} = 180,
```

比 Miyaoka 弱。因此把 `174` 归给 Varchenko 是误归因。

本地参考：

- `arxiv/endrass_9507011.tex`
- `arxiv/endrass_9507011.pdf`
- `arxiv/endrass_9507011.txt`
- `doc/endrass-octic-reading-notes.md`
- `doc/historical-roadmap.md`

## 方程

`degree08` 使用坐标顺序：

```text
[x:y:z:w].
```

Endrass 的最终曲面写成：

```text
F = P - R^2.
```

其中

```text
P = product_{j=0}^7 (cos(j*pi/4)*x + sin(j*pi/4)*y - w).
```

代码 exact 验证它等于四个二次因子的形式：

```text
P = 1/4
    * (x^2-w^2)
    * (y^2-w^2)
    * ((x+y)^2-2w^2)
    * ((x-y)^2-2w^2).
```

四次式 `R` 为：

```text
R =
  a*(x^2+y^2)^2
  +(x^2+y^2)*(b*z^2+d*w^2)
  -z^4
  +g*z^2*w^2
  +i*w^4,
```

参数在 `Q(sqrt(2))` 中：

```text
a = -1/4  * (1 + sqrt(2))
b =  1/2  * (2 + sqrt(2))
d =  1/8  * (2 + 7*sqrt(2))
g =  1/2  * (1 - 2*sqrt(2))
i = -1/16 * (1 + 12*sqrt(2)).
```

这对应论文最终显示的清分母方程，只是代码保留 `F=P-R^2` 的结构形态。

## 对称性

`P` 来自正八边形方向的 8 个平面：

```text
H_j = { cos(j*pi/4)*x + sin(j*pi/4)*y = w }, j=0,...,7.
```

`R` 只依赖 `x^2+y^2`、`z^2`、`w^2`，所以最终曲面具有：

```text
D8 x Z2
```

其中 `D8` 作用在 `(x,y)` 平面，额外的 `Z2` 是 `z -> -z`。代码通过 exact 线性代入验证：

```text
rotation by pi/4
y-reflection
z-reflection
```

均保持 `F` 不变。

## 基础 112 个节点的结构来源

任取两个不同平面 `H_i,H_j`，交线 `H_i cap H_j` 上，`P` 至少二阶为零。因为 `R^2` 也在 `R=0` 上二阶为零，所以候选奇点来自：

```text
H_i cap H_j cap {R=0}.
```

共有 `C(8,2)=28` 条交线。`R` 是四次式，一般每条线给出长度 `4` 的交：

```text
28 * 4 = 112.
```

`degree08` 现在不是简单写死这个乘法，而是对每条交线用 exact linear algebra 求二维零空间，把 `R` 限制成二元四次式，并检查 restriction degree 确为 `4`。这给出第一层机器可检查 skeleton。

按 `D8` 对称，28 条线分成 4 类，代表为：

```text
(H0,H1), (H0,H2), (H0,H3), (H0,H4).
```

对应 line orbit size：

```text
8, 8, 8, 4.
```

每条线贡献长度 `4`，所以 orbit 层面的计数为：

```text
8*4 + 8*4 + 8*4 + 4*4 = 112.
```

## 额外 56 个节点

Endrass 进一步把问题降到两个反射平面：

```text
E0 = { y = 0 }
E1 = { x = (1 + sqrt(2))*y }.
```

在这两个平面截线中，通过 Segre trick 研究平面四次曲线。最终参数使额外事件出现：

```text
s3: node          -> 16
t3: axis contact  ->  8
u5: node          -> 16
v1: axis contact  ->  8
v2: axis contact  ->  8
```

合计：

```text
16 + 8 + 16 + 8 + 8 = 56.
```

当前 Rust 代码把这些事件记录成 `EndrassExtraNodeEvent`，包含事件标签、所在反射平面、事件类型、论文给出的 Segre 平面坐标和诱导的曲面 orbit size。它现在是计数 skeleton，还不是平面四次曲线的完整奇点证明。

因此第一轮结构复现给出：

```text
112 + 56 = 168.
```

## 已实现内容

`crates/degree08` 当前 exact 验证：

- `Q(sqrt(2))` 上的最终齐次八次方程 `F=P-R^2`。
- `P` 的 8 平面乘积形式等于 4 个二次因子形式。
- `F` homogeneous 且 degree 为 `8`。
- `D8 x Z2` 的三个生成元保持 `F` 不变。
- 8 个平面和 28 条交线 exact 构造。
- 每条交线上的 `R` restriction 是非零二元四次式，因此基础结构计数为 `28*4=112`。
- 4 个 line orbit representatives 的贡献为 `32+32+32+16=112`。
- `s3,t3,u5,v1,v2` 的 Segre-trick 额外贡献为 `16+8+16+8+8=56`。
- Miyaoka `d=8` 上界为 `174`，Varchenko/Arnold number 为 `180`。

## 仍未完成的严格证明

Endrass 原文中两个关键步骤依赖 Maple/Macaulay：

1. 候选奇点全部为 ordinary nodes：需要对候选点 exact 验证 `F=0`、`grad F=0`、Hessian rank `3`。
2. 没有额外奇点：论文在 8 个反射平面上用 Maple 检查，并用一个 `D_n` 对称曲面不能有 `2n` 个 node orbit 的引理排除平面外奇点。

当前 `degree08` 完成的是第一轮结构复现，不应声称已经证明 Endrass octic 恰有 168 个 ordinary nodes。下一步应把两个平面截线的 Segre-trick 事件升级成 exact 平面曲线证书，再决定是走 support-strata Groebner、平面分层证书，还是 Endrass 原 lemma 的形式化路线。
