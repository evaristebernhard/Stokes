# Togliatti Quintic 复现笔记

## 两个模型与当前结论

`degree05` 现在保留两条 Togliatti quintic 路线：

1. Catanese 综述 Proposition 130 的 rational determinant 模型。
2. 同一综述 2.5.1 的 special Togliatti 模型。

当前机器证明的 `31` 节点结论来自 special Togliatti 模型：

```text
special_togliatti_singular_scheme_certificate()
  .verified_reduced_ordinary_node_count()
  = Some(31)
```

这证明该 special 模型的 saturated projective singular scheme 恰为 `31` 个 reduced ordinary nodes，没有第 `32` 个奇点。

Proposition 130 determinant 模型仍作为待排查对象保留。本地按 TeX 源公式转写后，support-cover 证书给出的 projective singular-scheme length 是 `16`，不是文献目标 `31`。因此代码/API 刻意区分文献规格 `togliatti_literature_node_count() = 31` 和 special 模型的机器证明结论。

## Determinant 模型

Proposition 130 的显式 determinant 模型设坐标为

```text
[y1:y2:y3:y4] in P3
```

并记

```text
s1 = y1 + y2 + y3 + y4
s3 = y1^3 + y2^3 + y3^3 + y4^3
```

定义

```text
m13 = 9y1^2 + 7y2^2 + 5y3^2 - 8y4^2 - 7/2*s1^2
m23 = 2y1^2 + 2y2^2 - y4^2 - s1^2
```

Togliatti quintic 是下面对称矩阵 determinant 的零点：

```text
| 32y1 - 24y3 + 15y4    2y1 - 7y3 - 3y4          m13              |
| 2y1 - 7y3 - 3y4       -4y3 - 3y4                m23              |
| m13                   m23                       (s3 - 1/4*s1^3)/3 | = 0.
```

矩阵条目的次数模式是：

```text
1 1 2
1 1 2
2 2 3
```

因此 determinant 是齐次五次式。这个模型的好处是所有系数都在 `Q` 中，适合当前 `nodal-core::Rational`。相比之下，综述 2.5.1 的特殊 Togliatti 方程含 `sqrt(5)`，而节点坐标落在 `Q(sqrt(5 + 2sqrt(5)))`，超出了当前只支持单个二次扩张 `Q(sqrt(d))` 的 `QuadraticRational`。

## Special Togliatti 模型

31 点严格证书主线采用同一篇综述 2.5.1 的 special Togliatti quintic。它的方程是

```text
F = 2P + 5zQ^2
P = x^5 - 5x^4w - 10x^3y^2 - 10x^2y^2w + 20x^2w^3
    + 5xy^4 - 5y^4w + 20y^2w^3 - 16w^5
Q = x^2 + y^2 + b z^2 + zw + d w^2
b = -(5 - sqrt(5))/20
d = -(1 + sqrt(5)).
```

这个模型定义在 `Q(sqrt(5))` 上。`nodal-core::QuadraticRational` 现在可以解析 Singular 的
`(a*t+b)` 系数输出，其中 `t^2=5`。

## 当前代码状态

`crates/degree05` 已实现：

- `QuinticSurface` 与 `NodeVerification`，沿用 degree 3/4 的验证接口。
- determinant 公式的 exact polynomial builder。
- `togliatti_quintic()`，返回 `HomogeneousPolynomialP3<Rational>`。
- `togliatti_affine_chart_generators(i)`，把第 `i` 个射影坐标设为 `1`，返回该 chart 中的
  `f, df/du1, df/du2, df/du3`。
- `togliatti_affine_chart_variable_indices(i)`，记录 chart 的三个 affine 变量对应原来的哪些射影变量。
- `export_togliatti_singular`，从 Rust determinant 模型导出某个 affine chart 的 Singular 脚本。该脚本计算
  `std(I)`，再按 `doc/groebner-certificate-format.md` 的行式格式打印 generators 与 basis。
- 基础测试：次数为 5、展开后有 55 项、矩阵条目次数模式正确、一般点非奇异。
- 四个 affine chart 都已有严格 Groebner 证书：
  `crates/degree05/certificates/togliatti-chart{0,1,2,3}-grevlex.cert`。它们由 Cygwin-based Singular 生成，
  每个 chart 都有 `vdim = 16`；Rust 端用 `BigRational` 验证 generators 与当前 determinant 模型一致，并验证
  imported basis 通过 Buchberger 判据，原始四个 Jacobian generators 都可约化为 `0`。
- 15 个 projective support strata 证书：
  `crates/degree05/certificates/togliatti-support-{01..15}-grevlex.cert`。每个 stratum 选择其最小非零
  projective coordinate 作为 chart，把支撑外坐标设为 `0`，并加入 `tau * product(nonzero affine coords) - 1`
  表达非零条件。Rust 当前完整验证 14 个空边界 stratum，并用 chart `x0 = 1` 的已验证长度推出当前模型的
  projective support-cover 长度为 `16`。
- special Togliatti 的 31 点 projective length 证书：
  `crates/degree05/certificates/special-togliatti-chart3-grevlex.cert` 证明 `w=1` chart 的 quotient length 为
  `31`；`crates/degree05/certificates/special-togliatti-infinity-support-{01..07}-grevlex.cert` 证明 `w=0`
  的 7 个坐标支撑层为空。因此 `special_togliatti_singular_scheme_certificate().verified_projective_length()`
  在 Rust exact verifier 下返回 `Some(31)`。
- special Togliatti 的 Groebner basis lift 证书：
  `special-togliatti-chart3-grevlex.lift`、`special-togliatti-chart3-hessian-bad-grevlex.lift`、以及
  `special-togliatti-infinity-support-{01..07}-grevlex.lift` 给出每个 imported basis element 作为原生成元
  的显式线性组合。Rust 用 `BigQuadraticRational` 重算这些等式，从而补上 `G ⊂ I`；结合原有 normal-form
  检查的 `I ⊂ <G>`，得到 chart ideal 与 imported basis ideal 相等。
- special Togliatti 的 ordinary-node / reducedness 证书：
  `crates/degree05/certificates/special-togliatti-chart3-hessian-bad-grevlex.cert` 验证
  `<F,Fx,Fy,Fz,det Hess(F)> = <1>` in the `w=1` affine chart。因此不存在 Hessian 退化的奇点；
  `special_togliatti_singular_scheme_certificate().verified_reduced_ordinary_node_count()` 在 Rust exact verifier
  下返回 `Some(31)`。
- `togliatti_literature_node_count() = 31` 与 `beauville_maximum_node_count() = 31`。

这里要非常明确：Proposition 130 determinant 分支不仅还没有证明这 31 个节点，而且 support-cover 证书暴露了一个必须先解决的
模型矛盾。按 arXiv source 中 Proposition 130 的 determinant 公式逐字转写后，四个 affine chart 仍各自
只有长度 `16`；support strata 中只有全非零 stratum 有长度 `16`，其余 14 个 stratum 为空。因此当前机器
证书证明的是“这个已转写 determinant 模型的 projective singular scheme 长度为 `16`”，而不是文献声称的
`31`。31 点主线目前由 special Togliatti 模型承担；determinant 分支仍需继续排查。

## 数学来源

Togliatti 的五次曲面是 degree 5 的极值例子。Beauville 证明五次 nodal surface 的最大节点数是：

```text
mu(5) = 31.
```

Catanese 综述把 Togliatti quintic 放进 cubic discriminant 的框架：从 Goryunov-Kalker cubic hypersurface `T(4)` 中选一条满足条件的直线作投影，得到 `P3` 上的 quintic discriminant。Proposition 130 给出上述 determinant 方程，并说明它有 31 个节点且没有其它奇点。

这条路线的意义是：degree 5 开始，构造和上界明显分离。Kummer quartic 的 `mu(4)=16` 可以直接由 Miyaoka 上界达到；但 `d=5` 时 Miyaoka 的一般估计并不尖锐，尖锐上界需要 Beauville 的更细论证。

## 证书状态与下一步

determinant 分支要把文献命题变成工程证书，仍至少分三步：

1. 节点候选生成：从 determinant 模型出发，求解 `F = grad F = 0`。需要处理非有理节点，可能要扩展 `nodal-core` 到更一般的代数数域，或先做消元证书。
2. Ordinary node 检查：对 31 个候选逐点验证 `F = 0`、`grad F = 0`、Hessian rank 为 3。
3. 穷尽证明：像 degree 4 一样做 chart-by-chart 或 elimination certificate，证明没有第 32 个奇点，也没有非节点奇点。

一个务实的路线是先在 `w=1` chart 对 Jacobian ideal 做 Groebner/消元实验，保存最小多项式和坐标表达式；再决定是否把代数数域支持放进 `nodal-core`。

special Togliatti 分支已经完成一条更短的全局证书链：

1. `w=1` chart 的 Jacobian ideal quotient length 是 `31`。
2. 对每个 imported basis，lift 证书验证 basis 元素确实属于原 Jacobian/support ideal，因此不是只信任 Singular 的
   `std(I)` 输出。
3. `w=0` 的 7 个 projective support strata 全为空，所以没有 infinity 奇点。
4. `w=1` chart 中加入 `det Hess(f)=0` 后得到 unit ideal，所以每个奇点的 affine Hessian 都非退化。
5. 对 hypersurface surface singularity，非退化二次项等价于 ordinary double point；局部 Jacobian algebra 长度为 `1`，因此 singular scheme 在这些点 reduced。

于是 special 模型的 saturated projective singular scheme 是 `31` 个 reduced ordinary nodes；长度已经是 `31`，所以不存在第 `32` 个奇点。

## 当前 chart 语义

`nodal-core` 现在有第一版 `P3` chart 基础设施。对齐次多项式

```text
F(x0,x1,x2,x3)
```

选择 chart `xi = 1` 后，保留其余三个变量，按原射影变量顺序排列。例如：

```text
i = 3: [x0,x1,x2]
i = 1: [x0,x2,x3]
```

去齐次化得到三变量多项式：

```text
f(u0,u1,u2) = F(x0,...,xi=1,...,x3).
```

在这个 affine chart 中，hypersurface 的奇异条件可写成：

```text
f = df/du0 = df/du1 = df/du2 = 0.
```

这和射影 Jacobian 条件一致：若上述四个方程成立，Euler 公式

```text
deg(F) * F = x0*Fx0 + x1*Fx1 + x2*Fx2 + x3*Fx3
```

会推出被设为 `1` 的那个射影偏导也为 `0`。因此每个 chart 的四个生成元就是该 chart 内的奇异点 ideal。四个 chart 的并集覆盖整个 `P3`。

需要注意：这只是把射影问题正确拆成 affine chart。完整穷尽证明还要对每个 chart 的 ideal 给出 Groebner/消元证书，并处理 chart 重叠中的点去重。若直接在齐次环里做 `<F,Fx,Fy,Fz,Fw>`，仍然必须显式说明对 irrelevant ideal `<x0,x1,x2,x3>` 的 saturation；否则原点和非饱和残留会污染结论。

## Projective / Saturation 证书语义

下一步的严格目标不是把四个 affine chart 的长度相加，而是证明齐次 Jacobian ideal

```text
J = <F, Fx0, Fx1, Fx2, Fx3> in Q[x0,x1,x2,x3]
```

在 irrelevant ideal

```text
m = <x0,x1,x2,x3>
```

下的饱和

```text
Jsat = J : m^infinity
```

定义一个零维 projective scheme。文献目标是证明该 scheme 恰为 `31` 个 reduced points；当前机器证书
在已转写 determinant 模型上只得到长度 `16`，所以这里的 `31` 仍是待排查目标，不是已完成结论。

对 special Togliatti 模型，当前证书语义更直接：

```text
w = 1 chart: length 31
w = 0 infinity hyperplane: 7 coordinate support strata all empty
bad Hessian locus in w = 1 chart: empty
lift certificates: every imported basis element is in the original ideal
```

前两行证明 special 模型的 saturated projective singular scheme 长度为 `31`。第三行证明所有奇点的 affine
Hessian determinant 非零，因此每个点都是 ordinary double point。ordinary double point 的局部 Jacobian
scheme reduced 且长度为 `1`；结合全局长度 `31`，得到 exactly `31` reduced points，并排除第 `32` 个奇点。

证书需要拆成可复查的几层：

1. **Containment `J ⊂ Jsat`**：`F,Fx0,Fx1,Fx2,Fx3` 都能被 imported saturated basis 约化为 `0`。
2. **Saturation membership `Jsat ⊂ J:m^e`**：对 saturated basis 的每个生成元 `g`，给出一个指数 `e`，并验证 `g * q ∈ J` 对所有 degree `e` 的 monomials `q ∈ m^e` 成立。Rust 可以用原始 `J` 的 Groebner basis 检查这些 normal forms。
3. **Saturation fixed point**：证明候选 `Jsat` 本身已经 saturated，例如验证 `Jsat:m = Jsat` 或给出等价 colon certificate。否则只知道某个中间 ideal 包在 saturation 中。
4. **Chart compatibility**：每个 affine chart `xi = 1` 的去齐次化 ideal 与 `Jsat` 的该 chart restriction 给出同一个 ideal。这样四个 chart 覆盖同一个 saturated projective singular scheme，而不是四份互不相干的 affine 计算。
5. **Global length and reducedness**：用 Hilbert polynomial/degree、squarefree elimination 或 radical/local-length 证书证明 `degree(Jsat)=31` 且 reduced。

已添加 `export_togliatti_projective_saturation` 导出器，用来生成齐次 `J` 并调用 Singular 的 `elim.lib::sat(J,m)`。朴素直接计算在本机上明显比单 chart 重，目前还不能作为稳定 CI 证书路径；后续更稳的方向是让 Singular 输出分步 colon/saturation witness，让 Rust 验证每个 containment 和 fixed-point 条件。

同时已添加 `export_togliatti_projective_strata` 导出器。它不直接计算齐次 `J:m^infinity`，而是把
`Proj(Q[x0,x1,x2,x3]/J)` 分解为 15 个坐标支撑层：

```text
support S = {xi | xi != 0}
choose min(S) as chart coordinate = 1
coordinates outside S are set to 0
tau * product(coordinates in S except chart coordinate) - 1 = 0
```

这些 strata 两两不交，并覆盖 projective space。若每个 stratum 的 Groebner 证书都通过 Rust exact verifier，
它们的 quotient length 之和就是 saturated projective singular scheme 的长度。当前证书显示 14 个边界
strata 为空，chart `x0 = 1` 的已验证长度为 `16`，因此当前 determinant 模型的 support-cover 长度为
`16`。这正是下一步的数学 blocker：继续做 reducedness/31 点坐标前，必须先解释为什么 Proposition 130
源码公式在本地 exact Jacobian 计算中只给出 `16`。

## 还缺的工程基础设施

两条路线都要做，但目标不同：

- 代数数域坐标证书：回答“这 31 个点分别是谁”，并给出可展示、可逐点检查的坐标。
- Groebner/消元证书：回答“除了这 31 个点，真的没有别的奇点”，并证明 scheme 结构没有重数残留。

这两条线应该共用同一批底层 exact algebra，而不是分别临时写脚本。

### 共同基础设施

当前已经开始把多项式能力抽进 `nodal-core`。`degree05` 的 determinant builder 已改用通用稀疏多项式；`degree04` 还保留了一个私有 ternary helper，用于 trope 平面截面验证，后续也应迁移。

需要补齐或继续推进的能力如下：

1. 通用稀疏多项式：

```text
SparsePolynomial<T, const N: usize>
```

当前已支持加减乘、幂、偏导、求值、齐次 `P3` 转换、按 monomial order 取 leading term、以及 normal form。仍缺多项式代入、齐次化/去齐次化、变量重命名，以及把 `HomogeneousPolynomialP3` 改成真正的薄封装。

2. Monomial order：

```text
Lex, GrLex, GrevLex
```

当前已有 `Lex`、`GrLex`、`GrevLex`、multivariate normal form、S-polynomial、以及 Buchberger 判据 verifier 的第一版。Groebner 和消元必须明确 order；degree04 目前的 chart certificate 是人工分支，degree05 不能继续手写到 31 个点。

3. 大整数/大有理数：

早期 `Rational` 用 `i128`。Groebner 计算会让系数快速膨胀，`i128` 很容易不够。当前 `nodal-core`
已经补了 `BigRational`，并把 Groebner certificate parser/verifier 泛型化到非 `Copy` 系数域。这样
Singular 输出的大整数系数可以进入 Rust verifier。后续仍需要：

```text
BigInt
polynomial coefficients over BigRational
```

短期可以继续让低次数测试使用 `Rational`，但 degree05 Groebner 证书应优先基于 `BigRational`。

4. Chart 和 saturation 语义：

射影奇异集不是 affine ideal 的直接零点。需要统一表达：

```text
projective singular ideal: <F, Fx, Fy, Fz, Fw> saturated by <x,y,z,w>
affine chart w=1
infinity chart w=0, then another chart inside P2
```

当前代码已实现第一层 chart 去齐次化：`HomogeneousPolynomialP3::dehomogenize(i)` 与
`HomogeneousPolynomialP3::affine_singular_generators(i)`。这解决了“某个 chart 内原始生成元是什么”的问题。
degree05 special 分支现在已经把 `w=1` chart length、`w=0` 空支撑层、以及 Hessian-bad 空集接入 Rust
Groebner verifier，并为这些 imported bases 增加了 lift 证书来验证反向包含；determinant 分支也已有 15 个支撑层证书，但结论是本地转写模型长度为 `16`，仍需排查。

### 路线 A：代数数域坐标证书

这条路线需要把“点坐标在某个扩张域中”变成 Rust 可验证对象。

缺的基础设施：

1. 一般代数数域：

```text
AlgebraicNumber = Q[t] / (p(t))
```

至少需要不可约最小多项式 `p(t)`、元素的多项式代表、模 `p` 约化、四则运算、零判定。当前 `QuadraticRational` 只能表达 `a + b sqrt(d)`，不能表达 Catanese 说的复杂 determinantal nodes。

2. `FieldElement` trait 调整：

现在 `FieldElement` 已从 `Copy` 改成 `Clone`，并用 `zero()/one()` 代替 `const ZERO/ONE`。这一步让
`BigRational` 能进入 `SparsePolynomial`、`Matrix`、Hessian rank 和 Groebner verifier。动态次数的
`AlgebraicNumber` 仍需要继续实现，但不再被 `Copy` trait 卡住。下一步可以直接实现动态
`AlgebraicNumber = Q[t]/(p(t))`，必要时再为常见小次数扩张做优化。

3. Primitive element 和坐标证书格式：

一个节点证书应类似：

```text
field: p(t) = 0
point: [a1(t):a2(t):a3(t):a4(t)]
checks:
  F(point) = 0
  grad F(point) = 0
  rank Hessian(point) = 3
```

这样每个点的验证独立、可读、可测试。

4. 点集去重和 Galois 共轭处理：

31 个点可能不是都在同一个简单小域里。需要 projective equality：

```text
[a:b:c:d] = [lambda a:lambda b:lambda c:lambda d]
```

并能处理同一最小多项式的不同共轭。若只做纯代数等式，可以先不选实/复嵌入；若要数值展示，才需要 isolating interval 或复近似。

### 路线 B：Groebner/消元证书

这条路线不一定显式列出漂亮坐标，而是证明 ideal 的零点数量和结构。

缺的基础设施：

1. Groebner basis 计算或证书验证：

完全从零写高性能 Groebner 很重。更务实的第一版是：

- 外部工具或脚本生成 Groebner basis。
- Rust 只验证 certificate：每个原始生成元可被 Groebner basis 约化为 0，S-polynomial 也全部约化为 0。

这样外部计算不是信任根，Rust verifier 才是信任根。当前 `nodal-core` 已经可以检查候选 basis 的所有 S-polynomial 是否都约化为 0，也可以检查原始生成元是否都被候选 basis 约化为 0。导入格式见 `doc/groebner-certificate-format.md`。

2. Ideal reduction：

需要实现 multivariate division：

```text
normal_form(f, G, order)
```

这是 Groebner verifier 的核心。当前 `nodal-core` 已有第一版 `normal_form`、`s_polynomial` 和 `is_groebner_basis`，还需要补 certificate 文件格式、chart/saturation 语义，以及大有理数系数。

3. 零维 quotient 计数：

若 Groebner basis 是零维 ideal 的 basis，标准 monomials 数量给出 quotient algebra 维数。需要实现：

```text
standard_monomials(G) -> Vec<Monomial>
quotient_dimension(G) -> usize
```

当前 `nodal-core` 已有第一版 `standard_monomials` 和 `quotient_dimension`：当每个变量都有 pure-power leading monomial 边界时，它枚举 leading monomial ideal 的标准单项式。但这个数通常是带重数长度，不自动等于 distinct node 数。所以还要结合 radical 或 local multiplicity 信息。

4. Radical / squarefree / multiplicity 检查：

要证明是 31 个 ordinary nodes，而非某些点带高重数，需要：

- 每个 candidate 的 Hessian rank 证书；
- 或 ideal radicality 证书；
- 或局部代数长度为 1 的证书。

special Togliatti 当前采用的是一个全局 Hessian 退化空集证书：

```text
<F, Fx, Fy, Fz, det Hess(F)> = <1>  in Q(sqrt(5))[x,y,z]
```

这比先列 31 个坐标再逐点算 Hessian 更短：它一次性证明 31 个 singular-scheme 点都不在 Hessian 退化 locus
中，因此都是 ordinary double points。代数数域坐标路线仍有价值，但主要价值已经变成“列出和展示 31 个点”，
而不是 reducedness 的唯一证明路径。

5. Resultant / elimination 输出：

为了从 Groebner basis 提取点坐标，需要单变量消元多项式，例如：

```text
p(t)
x = ax(t), y = ay(t), z = az(t)
```

这正好连接路线 A：消元给出字段和坐标表达式，代数数域 verifier 再逐点检查。

### 推荐实现顺序

不要先上来写完整 CAS。比较稳的顺序是：

1. 把 `SparsePolynomial<T, N>` 抽进 `nodal-core`，替代 degree04/05 私有 helper。
2. 加 `BigRational` 或至少把 Groebner 模块的系数类型预留成大有理数。
3. 实现 monomial order、`normal_form`、S-polynomial 和 Groebner basis verifier。
4. 用外部脚本生成 degree05 的 chart Groebner basis，并让 Rust 验证它确实是 Groebner basis。
5. 实现 `AlgebraicNumber = Q[t]/p(t)`，从消元输出构造节点坐标证书。
6. `degree05` 接入双证书：

当前进度：1、2、3 已有可运行版本；4 已在 special Togliatti 的 `x3 = 1` chart 上打通闭环，并通过
`w=0` support strata 排除了 infinity。reduced/ordinary-node 证据也已经由 Hessian-bad unit-ideal
证书完成。仍缺的是 determinant 分支 `16` vs `31` 的模型排查，以及 31 个代数点坐标证书。

```text
Groebner certificate: singular locus has exactly 31 reduced ordinary nodes.
Algebraic point certificate: list and independently check all 31 points.
```

API 上仍刻意区分：`togliatti_literature_node_count() = 31` 是文献规格；
`special_togliatti_singular_scheme_certificate().verified_reduced_ordinary_node_count() = Some(31)` 是当前机器复核结论。
determinant 分支在 `16` vs `31` blocker 解除前不会被包装成机器证明的 `31`。
