# 工程复现路线

## Workspace 结构

当前使用一个 Rust Cargo workspace：

```text
Cargo.toml
crates/
  nodal-core/
  degree02/
  degree03/
  degree04/
```

设计意图：

- `nodal-core`: 通用能力，例如有理数、矩阵秩、零空间、射影点。
- `degree02`: 二次曲面的复现与验证。
- `degree03`: Cayley cubic 的四个 ordinary double points 的 exact 验证。
- `degree04`: Kummer quartic 的完整奇异集穷尽、16 个 ordinary double points、以及经典 `16_6` tropes 配置的 exact 验证。
- `degree05`: Togliatti quintic 的 determinant 方程和基础 exact 验证外壳。
- 后续可增加 `degree06`, ..., `degree08`，每个次数独立实现该次数的经典例子，同时复用 `nodal-core`。

`nodal-core` 当前已从只支持 `Q` 推进到支持一个二次扩张域 `Q(sqrt(d))`。这一步是为了 Kummer quartic 的节点坐标，它们自然落在 `Q(sqrt(2))` 中。

`nodal-core` 也已经开始补 Groebner/消元路线需要的基础设施：

- `SparsePolynomial<T, const N: usize>`：通用稀疏多项式，支持加减乘、幂、偏导、求值、leading term。
- `MonomialOrder`：当前包含 `Lex`、`GrLex`、`GrevLex`。
- `normal_form(f, G, order)`、`s_polynomial(f, g, order)`、`is_groebner_basis(G, order)`：Groebner certificate verifier 的第一版 Buchberger 判据核心。
- `standard_monomials(G, order)`、`quotient_dimension(G, order)`：当 leading ideal 有 pure-power bounds 时，计算零维 quotient 长度。
- `GroebnerCertificate<N>`：第一版行式文本导入格式，见 `doc/groebner-certificate-format.md`。
- `BigQuadraticRational`：`Q(sqrt(5))` 上的大有理数系数，用于验证 special Togliatti lift 证书中很大的线性组合系数。

这些能力已经被 `degree05` 的 Togliatti determinant builder 使用；后续还要迁移 `degree04` 的局部 ternary helper。

## surfer-web 参考原则

`C:\Users\jiang\Desktop\surfer-web` 已经有一套成熟的 Surfer 公式与 gallery 资产。详细盘点见：

- `doc/surfer-web-reuse-audit.md`

当前决策：

- `surfer-web` 只作为 gallery formula 资料来源和渲染对照。
- 暂不搬 `.surfer` 脚本宿主、`packages/lab-surface/src/parser/*`、RunMat MATLAB parser、WebGL solver。
- Rust 证明主线保持 exact algebra，不依赖 `surfer-web` 的 `f64` evaluator 或 shader 展开。
- 如果后续需要读取 gallery 字符串，也只做离线转换；证明层仍接受明确的 exact polynomial 数据结构。

## Degree 2 的数学目标

二次曲面由齐次二次型给出：

```text
q(x) = x^T A x
```

其中 `A` 是对称 `4 x 4` 矩阵。奇点满足：

```text
grad q = 2 A x = 0
```

所以奇点集合就是 `ker(A)` 的射影化。

分类：

- `rank(A) = 4`: 光滑二次曲面，无节点。
- `rank(A) = 3`: `ker(A)` 是一维向量空间，射影化为一个点；这是 ordinary quadric cone，有 1 个 node。
- `rank(A) <= 2`: 奇异集正维，非 isolated，因此不属于 nodal surface 的候选。

标准复现例子：

```text
x^2 + y^2 - z^2 = 0 in P^3
```

矩阵秩为 `3`，唯一奇点是：

```text
[0:0:0:1]
```

## Degree 2 已实现检查

`degree02` 目前包含三个测试例：

- 光滑二次曲面：节点数 `0`。
- 标准二次锥面：节点数 `1`，节点 `[0:0:0:1]`。
- 可约二次曲面 `x^2-y^2=0`：奇异集是一条射影直线，非 isolated。

## Degree 3 已实现检查

`degree03` 直接使用 exact homogeneous polynomial，不引入 `surfer-web` parser。标准 Cayley cubic 为：

```text
xyz + xyw + xzw + yzw = 0 in P^3
```

已验证：

- 多项式次数为 `3`。
- 四个坐标点是奇点：

```text
[1:0:0:0], [0:1:0:0], [0:0:1:0], [0:0:0:1]
```

- 每个点满足 `F = 0` 且 `grad F = 0`。
- 每个点的 Hessian rank 为 `3`，因此是 ordinary double point。
- 在 affine chart `x=1` 中，奇点方程只留下 chart origin；由 Cayley cubic 的对称性，四个坐标图给出且只给出这四个奇点。

## Degree 4 已实现检查

`degree04` 使用 `Q(sqrt(2))` 上的 Kummer quartic 模型：

```text
3(2x^2+2y^2+2z^2-3w^2)^2
- 28((w-z)^2-2x^2)((w+z)^2-2y^2) = 0
```

等价地，这是下面 affine 模型的齐次整数倍：

```text
(x^2+y^2+z^2-3/2)^2
- 7/3 ((1-z)^2-2x^2)((1+z)^2-2y^2) = 0
```

已验证：

- 多项式次数为 `4`。
- 列出 `16` 个节点候选，坐标在 `Q(sqrt(2))` 中。
- 每个候选点满足 `F = 0` 且 `grad F = 0`。
- 每个候选点的 Hessian rank 为 `3`，因此是 ordinary double point。
- 在 `w = 1` affine chart 中，把梯度方程按 `x = 0 / x != 0` 与 `y = 0 / y != 0` 分支穷尽，得到 `27` 个 affine gradient candidates；其中恰有 `16` 个满足 `F = 0`。
- 在 `w = 0` infinity chart 中，用平方变量 `X=x^2,Y=y^2,Z=z^2` 的线性系统秩证书排除所有射影奇点。
- 16 个曲面奇点与 affine certificate 给出的 `F = 0` 分支完全一致，因此当前显式方程没有第 17 个奇点。
- 实现并验证经典 `16_6` 配置：16 个 nodes、16 个 tropes、每个 trope 过 6 个 nodes、每个 node 落在 6 个 tropes 上。
- 每个 trope 还带有平面截面证书：把 quartic 限制到该平面后，系数级等于 `scalar * conic^2`。

数学解释见 `doc/kummer-quartic.md`，包括 `A/{±1}`、`A[2] ~= (Z/2)^4`、16 个节点来源、Miyaoka 上界给出的 `mu(4)=16`，以及当前显式方程和经典 Kummer 理论之间的关系。

## Degree 5 当前状态

`degree05` 已采用 Catanese 综述 Proposition 130 的 rational determinant 模型。它把 Togliatti quintic 写成一个 `3 x 3` 对称矩阵的 determinant，矩阵条目次数模式为：

```text
1 1 2
1 1 2
2 2 3
```

因此 determinant 是齐次五次式。当前代码已验证：

- 展开后得到 degree `5` 的 homogeneous polynomial。
- 展开后有 `55` 个非零 monomial terms。
- 基础梯度/Hessian 验证接口已经接入。
- 文献节点数 `31` 与 Beauville 上界 `mu(5)=31` 已作为目标规格记录。
- 四个 affine chart 的 grevlex Groebner 证书均由 Rust exact verifier 复查通过，每个 chart 的 quotient length 为 `16`。
- 新增 15 个 projective support strata 证书后，当前 determinant 公式的 support-cover 机器长度为 `16`，与文献目标 `31` 不一致。
- 31 点严格证书主线已切到同一综述 2.5.1 的 special Togliatti 方程：Rust 现在可验证 `w=1` chart 长度 `31`，验证 `w=0` 的 7 个 infinity support strata 为空，验证 Hessian 退化奇点 locus 为空，并用 `.lift` 证书验证 imported Groebner basis 与原 ideal 的反向包含。

重要边界：当前不是“还差一步证明 31”，而是已经发现一个模型级 blocker。按 arXiv source 中 Proposition 130 的 determinant 公式逐字转写，Rust+Singular 证书只得到 16 个 projective singular-scheme length。因此下一步应先排查 determinant 模型、论文公式、或我们的复现语义之间的差异；在这个矛盾解除前，不能把 `togliatti_literature_node_count() = 31` 升级为机器证明结论。

但 special Togliatti 分支已经把 projective length `31` 从文献目标推进到本地证书，并通过
`<F,Fx,Fy,Fz,det Hess(F)> = <1>` 证明这 31 个奇点全部是 reduced ordinary nodes。

数学解释见 `doc/togliatti-quintic.md`。
复现经验总结见 `doc/degree05-lessons.md`。

## 下一步

Degree 5 的下一阶段分两条：继续排查 determinant 模型的 `16` vs 文献 `31` 差异；同时沿 special Togliatti 分支补 31 个代数点坐标证书和更显式的 saturation witness，把当前 Groebner 结论做得更可读。

CAS 工具链当前固定为 Windows 本机 Cygwin-based Singular，见 `doc/cas-toolchain.md`。外部 CAS 只负责生成证书候选；最终结论必须由 Rust exact verifier 复查。

实际应两条路线都做：

- 代数数域坐标证书：列出 31 个节点并逐点验证 `F = 0`、`grad F = 0`、Hessian rank 为 `3`。
- Groebner/消元证书：special 分支已证明射影奇异集穷尽且无非节点奇点；determinant 分支仍需解释模型差异。

为支撑这两条路线，`nodal-core` 已补第一层多项式地基，但还要继续推进：

- `SparsePolynomial<T, const N: usize>` 已接入 degree05；`P3` 到 affine chart 的去齐次化和 chart singular generators 已有第一版。还要迁移 degree04 的 trope 截面 helper，并补通用代入、齐次化、变量重命名。
- Monomial order、multivariate division、S-polynomial 和 Groebner basis verifier 已有第一版；certificate 文件格式已有第一版，且已被 `degree05` 的 `x3 = 1` chart 证书使用。
- 大整数/大有理数已开始接入：`nodal-core::BigRational` 可以解析并验证外部 CAS 输出的大整数 Groebner 证书；低次数代码仍可继续使用 `Rational`。
- Projective chart 与 saturation 证书语义：chart 原始 ideal 已能生成，15 个坐标支撑层的证书格式也已接入；下一步是把 support-cover 证书和齐次 Jacobian ideal 的 saturation certificate 对齐，并先解释当前 determinant 模型为何只给出长度 `16`。
- 一般代数数域 `Q[t]/(p(t))`，用于表达 Togliatti 节点所在的复杂扩张域。
- `FieldElement` 已从 `Copy` 过渡到 `Clone`，为 `BigRational` 和后续 `Q[t]/(p(t))` 铺路。
- Groebner certificate verifier：Rust 已能验证外部生成的 basis，而不是盲目信任外部 CAS；`degree05` 的四个 affine charts 都已有通过 Rust 验证的 grevlex 证书，每个 chart 的 quotient length 为 `16`。

详细拆解见 `doc/togliatti-quintic.md` 的“还缺的工程基础设施”。
