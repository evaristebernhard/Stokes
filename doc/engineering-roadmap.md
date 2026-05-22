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
  degree05/
  degree06/
  degree07/
  degree08/
```

设计意图：

- `nodal-core`: 通用能力，例如有理数、矩阵秩、零空间、射影点。
- `degree02`: 二次曲面的复现与验证。
- `degree03`: Cayley cubic 的四个 ordinary double points 的 exact 验证。
- `degree04`: Kummer quartic 的完整奇异集穷尽、16 个 ordinary double points、以及经典 `16_6` tropes 配置的 exact 验证。
- `degree05`: Togliatti quintic 的 determinant 方程和基础 exact 验证外壳。
- `degree06`: Barth sextic 的 65 个 ordinary double points、A/B/C 线配置和 support-strata Groebner/lift 穷尽证书。
- `degree07`: Labs septic 的 99-real-nodal 构造、三次数域原型和七次方程 exact 外壳。
- `degree08`: Endrass octic 的 `D8 x Z2` 对称结构、`F=P-R^2` 方程和 `112+56=168` 第一轮结构复现。
- 后续每个次数独立实现该次数的经典例子，同时复用 `nodal-core`。

`nodal-core` 当前已从只支持 `Q` 推进到支持一个二次扩张域 `Q(sqrt(d))`。这一步是为了 Kummer quartic 的节点坐标，它们自然落在 `Q(sqrt(2))` 中。

`nodal-core` 也已经开始补 Groebner/消元路线需要的基础设施：

- `SparsePolynomial<T, const N: usize>`：通用稀疏多项式，支持加减乘、幂、偏导、求值、leading term。
- `MonomialOrder`：当前包含 `Lex`、`GrLex`、`GrevLex`。
- `normal_form(f, G, order)`、`s_polynomial(f, g, order)`、`is_groebner_basis(G, order)`：Groebner certificate verifier 的第一版 Buchberger 判据核心。
- `standard_monomials(G, order)`、`quotient_dimension(G, order)`：当 leading ideal 有 pure-power bounds 时，计算零维 quotient 长度。
- `GroebnerCertificate<N>`：第一版行式文本导入格式，见 `doc/groebner-certificate-format.md`。
- `ProjectiveSupport<N>`：统一 projective support mask、chart 选择和 support 变量枚举语义，已由 `degree05` 和 `degree06` 共享。
- `GroebnerLiftCertificate<N, T>`：统一 `.lift` 文件解析和 identity verifier，支持同系数域验证，也支持 `QuadraticRational -> BigQuadraticRational` 的映射验证。
- `BigQuadraticRational`：`Q(sqrt(5))` 上的大有理数系数，用于验证 special Togliatti lift 证书中很大的线性组合系数。

这些能力已经被 `degree05` 的 Togliatti 证书和 `degree06` 的 Barth support-strata 证书使用；后续还要迁移 `degree04` 的局部 ternary helper。

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

## Degree 6 已实现检查

`degree06` 已复现 Barth sextic 的第一轮证书闭环。数学解释见 `doc/barth-sextic.md`。当前代码固定坐标顺序 `[w:x:y:z]`，在 `Q(sqrt(5))` 上使用清分母方程：

```text
F = 4*(tau^2*x^2-y^2)*(tau^2*y^2-z^2)*(tau^2*z^2-x^2)
    - (2*tau+1)*w^2*(x^2+y^2+z^2-w^2)^2.
```

已验证：

- 多项式次数为 `6`，系数在 `Q(sqrt(5))`，并满足 `tau^2=tau+1`、`tau+tau_bar=1`、`tau*tau_bar=-1`。
- 从 Catanese Table 1 转录 A/B/C 三类节点，数量为 `15+30+20=65`，projective 去重后仍为 `65`。
- 用 Catanese Proposition 205 的 `A5` 置换表示，从 A/B/C 三个代表点生成三个单 orbit，orbit sizes 为 `15,30,20`，并与 Table 1 exact 对齐。
- 每个候选点 exact 满足 `F=0`、`grad F=0`、Hessian rank 为 `3`，因此都是 ordinary double point。
- 15 条 mid lines 每条含 3 个共线节点；10 条 centre lines 每条含 2 个不同节点；`sigma=(123)` 与 `tau=(14)(25)` 对 line labels 的作用和节点置换相容。
- 15 个 projective support strata 的 grevlex Groebner certificates 已由 Rust verifier 复查：generators 与模型一致、basis 通过 Buchberger、原 generators 全部 reduce 到 0、quotient length 分布为 `[0,1,2,1,2,0,4,1,2,0,4,0,4,12,32]`，总和 `65`。
- 每个 support stratum 还有 `.lift` 证书，Rust exact 验证 imported basis 每个元素都在原 support ideal 中，从而关闭 ideal equality。
- `degree05` 与 `degree06` 现在共享 `nodal-core` 的 support/lift 语义；各 degree crate 只保留方程、stratum 生成元和期望长度这些数学特例。

因此当前 Barth 方程的 saturated projective singular scheme length 为 `65`；结合显式 65 个 ordinary nodes，得到该方程恰有 `65` 个 reduced ordinary nodes，没有第 `66` 个奇点。`mu(6)<=65` 的全局上界仍引用 Jaffe-Ruberman / Wahl / Pignatelli，不在本项目中复现。

## Degree 7 当前状态

`degree07` 已开始 Labs septic 的严格复现。数学解释见 `doc/labs-septic.md`。当前代码固定坐标顺序 `[w:x:y:z]`，实现 Labs 的：

```text
S_alpha = P - U_alpha,
7*alpha^3 + 7*alpha + 1 = 0.
```

已验证：

- `CubicAlphaRational` 具体实现 `Q[alpha]/(7*alpha^3+7*alpha+1)`，并 exact 验证 `alpha^3=-alpha-1/7`。
- `labs_septic_polynomial()` 给出 `Q(alpha)` 上的齐次七次式。
- 基础求值、gradient 和 affine singular generator 接口可用。
- 文档记录 Labs 的 `y=0` 平面截面机制：15 个 plane nodes，其中 1 个在 `D7` 轴上，14 个生成长度 7 的 orbit，因此 `1+14*7=99`。
- `w=1` affine chart 的 grevlex Groebner certificate 已导入；默认测试检查 generators 与 Rust 模型一致，quotient length 为 `99`。
- `w=1` affine Hessian-bad certificate 已导入；Rust exact verifier 验证该 ideal 为 unit ideal，因此 affine singular locus 中没有 Hessian rank 退化点。
- projective support `1..14` 的 grevlex certificates 已导入；support length 分布的已完成边界部分为 `support 09 = 1`、`support 11 = 14`，其余 `1..14` 为 `0`。
- support length 全规格记录为 `[0,0,0,0,0,0,0,0,1,0,14,0,0,0,84]`，其中最后的 `84` 是 `w,x,y,z` 全非零主开集。
- `w=0` infinity cover 已拆成 7 个 support strata，Rust 可导入这些空 strata 证书；full lift 重放保留为 ignored heavy check。
- support `15` 的经济路线已经走通：在 `w=1` chart 中对 `g=x*y*z` 做 saturation，Singular 给出 `sat_exp=1`、quotient length `84`，Rust 已导入 `labs-affine-chart0-support15-saturation-grevlex.cert` 作为 all-nonzero open-stratum 长度证据。

重要边界：当前 degree07 还不能声称 full projective support/lift 闭环已经完成。直接计算 support `15` 的 localized Groebner basis：

```text
<F,Fx,Fy,Fz, x*y*z*tau-1>
```

明显比 degree06 的最大 support 更重；`std` 与非 reduced `std` 都没有在可接受时间内完成。现在采用的工程主线是 `w=1` affine length `99` 加 `w=0` infinity 空证书，并用 support15 saturation 解释 `84` 的来源。后续若要达到 degree05 special 分支的严格度，还要补 compact reverse-containment witness：对 saturation basis `H[j]` 证明 `g*H[j] in <f,fx,fy,fz>`，同时避免朴素 `lift` 生成上百 MB 文件。`mu(7)<=104` 仍作为 Varchenko/Givental 上界背景引用，不在本项目中复现。

## Degree 8 当前状态

`degree08` 已开始 Endrass octic 的第一轮结构复现。数学解释见 `doc/endrass-octic.md`。当前代码固定坐标顺序 `[x:y:z:w]`，在 `Q(sqrt(2))` 上实现：

```text
F = P - R^2
```

其中 `P` 是 8 个平面

```text
H_j = { cos(j*pi/4)*x + sin(j*pi/4)*y = w }
```

的乘积，`R` 是 Endrass 最终参数给出的四次式。已验证：

- `P` 的 8 平面乘积形式 exact 等于 `1/4*(x^2-w^2)*(y^2-w^2)*((x+y)^2-2w^2)*((x-y)^2-2w^2)`。
- `F` 为 homogeneous degree `8`。
- `D8 x Z2` 的生成元 exact 保持 `F` 不变：`pi/4` 旋转、`y -> -y`、`z -> -z`。
- 8 个平面给出 `C(8,2)=28` 条交线；对每条交线用 exact nullspace 参数化，并检查 `R` 的限制是非零二元四次式。因此基础节点结构计数为 `28*4=112`。
- 28 条线按 `D8` 分成 separation `1,2,3,4` 四类，line orbit sizes 为 `8,8,8,4`，贡献 `32+32+32+16=112`。
- 记录 Endrass 的 Segre-trick 额外事件 `s3,t3,u5,v1,v2`，贡献 `16+8+16+8+8=56`。
- finite-field scorer 已接入 `degree08`：在 `p=31`、`sqrt(2)=8` 下复现 Endrass reduction 的 `total_sing=node_like=168`、`bad_sing=0`、`base_like=112`、`extra_like=56`，并记录 `line_profile` 与 `orbit_profile`。
- Segre quotient verifier 已构造 `E0/E1` 的平面四次 quotient，并 exact 验证 `s3,t3,u5,v1,v2` 的 quotient node/contact 条件和 lift 后 Hessian rank `3`；`s3` 的 lift 使用 `Q(sqrt(2))(sqrt(8(sqrt(2)-1)))` 的本地 nested quadratic 表示。
- 因此当前机器可检查 skeleton 给出 `112+56=168`。
- Miyaoka 上界在 `d=8` 给出 `174`；Varchenko/Arnold number 给出 `180`，已在代码和文档中区分。

重要边界：当前 degree08 还不是完整奇异集证明。它已经把额外 Segre 事件从计数 skeleton 升级为 exact event verifier，并用有限域 scorer 校准 Endrass reduction；但仍未给出特征零中 168 个点的全局 saturation 证书，也尚未形式化 Endrass 的 Maple 平面检查和 `D_n` 平面外排除引理。下一阶段若找到新候选，应走 projective Jacobian ideal saturation、reducedness 和 no-extra-singularity 证书。

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
