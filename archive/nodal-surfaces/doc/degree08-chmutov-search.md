# Degree08 Chmutov / Folding Search

## 定位

这一路线不是 Endraß 八平面底盘的局部扰动。

Endraß 路线的核心是

```text
F = P8 - R4^2
```

并且先保住来自 28 条平面交线的

```text
28 * 4 = 112
```

个基础节点，再研究额外事件。Chmutov / folding 路线的机制不同：它从低维临界值结构出发，让分离变量或折叠映射制造大量 `F=grad F=0` 的组合点。因此它不该被 `base_like=112` 这个指标约束；它的价值是提供一个横向对照，帮助判断 degree08 搜索是否过度困在 `112 + extra` 的范式里。

当前 Worker B 原型只实现最小有限域对照族：

```text
C8(x,w) + C8(y,w) + C8(z,w) + lambda*w^8 = 0 over F_31
```

其中 `C8(u,w)` 是 Chebyshev 多项式 `T_8(t)` 的齐次化：

```text
T_8(t) = 128t^8 - 256t^6 + 160t^4 - 32t^2 + 1

C8(u,w) =
  128u^8 - 256u^6w^2 + 160u^4w^4 - 32u^2w^6 + w^8
```

这不是完整经典 Chmutov 理论的复现，只是一个 folding 风格 surrogate。它保留了三个有用性质：

```text
degree = 8
variables x,y,z 分离
有坐标符号翻转与 S3 置换对称
```

因此它适合接入统一的 `degree08::search_core` scorer，快速产生可比较的有限域记录。

## 有限域 scorer 语义

程序入口：

```text
cargo run -p degree08 --bin search_chmutov -- --prime 31 --limit 10
```

每个 `lambda` 生成一个齐次八次曲面，然后调用：

```text
ProjectiveSurfaceScorerInput::new(F)
  .with_symmetry(even-coordinate-signs-semidirect-S3)

score_projective_surface(input)
```

这里没有 `PlaneProductSkeleton`，所以输出中：

```text
base_like  = 0
extra_like = node_like
```

这是预期行为，不表示“额外节点”来自 Endraß 意义下的 112 底盘之外，而只是统一记录格式里的字段复用。

当前排序分数为：

```text
score = node_like - 4*bad_sing
```

它故意惩罚 Hessian rank 小于 3 的有限域奇点。这个分数只用于筛选候选，不是数学不变量。

## 为什么它是对照路线

Endraß / Segre trick 的问题是局部结构很强：八平面 arrangement、四次 `R`、反射平面 quotient、orbit 粒度都会限制可能出现的新节点数量。降低对称性可以改变 orbit 粒度，但仍然可能困在同一个结构井里。

Chmutov / folding 思路的优势正好相反：

```text
高奇点数来自一维临界点组合
不依赖八平面 pair-lines
自然产生大 symmetry orbit profile
坏点和无穷远退化会直接暴露在 scorer 中
```

所以它更适合作为“机制对照”：

```text
如果有限域上也只能得到大量 bad_sing，说明 folding closure 的无穷远问题严重。
如果某些 lambda 给出较高 node_like 且 bad_sing 很低，才值得做 exact lift。
如果 orbit profile 与 Endraß 完全不同，可作为后续破对称搜索的结构样本。
```

## 有限域伪信号边界

`F_31` 上的 `node_like` 不能直接解释为特征零节点数。至少有三类伪信号：

```text
小特征合并：
  不同代数点在 mod p 后碰撞，Hessian rank 可能改变。

无穷远退化：
  分离变量的 projective closure 可能在 w=0 产生额外奇点，
  这些点不一定对应可用的复曲面节点。

不可见点问题：
  F_p-rational count 只看到有限域有理点，
  代数闭包上的奇异 scheme 长度需要 Groebner/saturation 才能确认。
```

因此搜索记录只说明：

```text
这个 lambda 的 mod 31 reduction 值得或不值得继续看。
```

后续若出现强候选，必须补：

```text
exact characteristic-zero equation
projective Jacobian ideal saturation
quotient length
reducedness
Hessian rank = 3 pointwise certificate
no-extra-singularity certificate
```

## 后续扩展

这个文件当前只落地最小 `T_8` 分离变量族。下一步可以用同一个 `search_core` API 扩展三类变体：

```text
1. lambda/mu 双参数：
   C8(x,w)+C8(y,w)+C8(z,w)+lambda*C4(x,w)C4(y,w)+mu*w^8

2. folding perturbation：
   在保持 S3 或部分符号对称的情况下加入低维 Weyl folding 不变量。

3. line-arrangement surrogate：
   用平面曲线 arrangement 的临界值多项式替换单变量 Chebyshev，
   但仍通过 ProjectiveSurfaceScorerInput 输出统一 TSV/JSONL。
```

这些都不需要改 scorer；只需要生成新的齐次八次 `F`。
