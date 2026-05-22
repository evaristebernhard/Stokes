# Degree08 Determinantal / Discriminant Search

## 目标

这一条路线不是继续微调 Endraß 的 `P8 - R4^2` 八平面族，而是把 degree05 Togliatti quintic 中得到的经验迁移到八次曲面搜索：

```text
高奇点曲面可以来自一个结构化映射的判别式或行列式退化层。
```

因此第一轮只做有限域原型。它的作用是找出值得 lift 的结构候选，而不是给出特征零证明。

## 与另外两条路线的差异

`P8 - R4^2` 路线把奇点组织在 8 个平面两两交出的 28 条线上。若每条线与四次式 `R=0` 有 4 个横截交点，就自然得到：

```text
C(8,2) * 4 = 112
```

后续搜索是在这个 `112` 底盘附近寻找额外事件。它的优点是基础盘非常清楚；风险是 orbit 粒度和底盘刚性可能把搜索困在 Endraß 附近。

Chmutov / folding / line-arrangement 路线的奇点来自折叠映射、Chebyshev 型临界值碰撞、或平面线配置的组合奇点。它不保留 `112` 底盘，比较适合当作“完全不同机制”的对照。

determinantal / discriminant 路线的奇点来源不同。这里先构造一个结构化矩阵或结构化多项式族，然后取：

```text
det(M(x)) = 0
Disc(f_x) = 0
```

奇点候选通常来自降秩层、余秩跳跃、或判别式的更高重根层。换句话说，它寻找的不是“平面交线上的四次根”，而是“参数化对象退化方式发生二阶碰撞”的位置。

## 当前 toy families

代码入口是：

```text
cargo run -p degree08 --bin search_determinantal -- [options]
```

当前只支持 `p=31`，并输出统一的 `ExperimentRecord` TSV/JSONL 字段：

```text
family, prime, label, total_sing, node_like, bad_sing,
base_like, extra_like, score, tags
```

因为这条路线没有 `P8 - R4^2` skeleton，`base_like=0`，`extra_like=node_like`。

### quad-det

`quad-det` 使用一个对称 `4 x 4` 矩阵：

```text
M(x0,x1,x2,x3) = (quadratic forms)
F = det(M)
```

矩阵元素是带有四个小参数 `a,b,c,d` 的二次型，所以 `F` 是八次齐次式。这个模型的数学含义是：把 `P^3` 映到二次型矩阵空间，然后看 rank drop 的行列式超曲面。奇点的理想来源是：

```text
rank M <= 2
```

或者 rank-3 层与参数映射的切空间不横截。

### cubic-disc

`cubic-disc` 使用一个二元三次式：

```text
f_x(s,t) = A(x)s^3 + B(x)s^2t + C(x)st^2 + D(x)t^3
```

其中 `A,B,C,D` 都是二次型。取二元三次判别式：

```text
Disc(f_x)
  = B^2C^2 - 4AC^3 - 4B^3D - 27A^2D^2 + 18ABCD
```

由于每个系数都是二次型，判别式也是八次齐次式。这个模型更接近“discriminant octic”：一般点表示二元三次有一个重根；更高奇点应来自三次式出现更高重根，或系数映射与判别式切层发生特殊接触。

## 为什么有限域结果只是 lift 候选

`search_determinantal` 调用共享的：

```text
degree08::search_core::score_projective_surface
```

它枚举 `P^3(F_31)` 并检查：

```text
F = Fx0 = Fx1 = Fx2 = Fx3 = 0
```

然后用 Hessian rank 记录：

```text
rank Hessian(F) = 3  -> node_like
rank Hessian(F) < 3  -> bad_sing
```

这个信号有用，但它不是证明。有限域可能产生伪奇点，也可能把特征零中不同点合并，还可能漏掉不在 `F_31` 上可见的点。任何候选若要进入严格阶段，都必须补：

```text
exact coefficient lift
projective Jacobian ideal saturation
quotient length
reducedness / Hessian rank
no extra singularity certificate
```

## 第一轮搜索策略

当前 bin 做的是小网格扫描：

```text
--family all|quad-det|cubic-disc
--grid-radius N
--scan-limit N
--limit N
--format tsv|json
```

`grid-radius=1` 表示参数从：

```text
-1, 0, 1
```

中取值。`scan-limit` 是每个 family 实际尝试的参数组数量。排序分数暂定为：

```text
score = node_like - 8 * bad_sing
```

这是刻意保守的：determinantal/discriminant toy family 很容易制造非 ordinary 的退化奇点；当前阶段宁愿优先看 ordinary node-like 多、bad_sing 少的候选。

## 后续加固方向

这条路线真正值得继续的信号不是单个 `p=31` 的高数字，而是以下几类结构：

```text
多个素数上同一整数参数 lift 保持高 node_like
bad_sing 很少，且 Hessian rank=3 的点有稳定 orbit/support pattern
rank-drop 或 discriminant-strata 能解释大部分奇点
存在可写成 exact Q 或小数域参数的候选
```

如果这些信号出现，再进入第二阶段：为候选生成 Singular/Sage saturation 证书，并把有限域候选变成特征零的 projective Jacobian ideal 证明。
