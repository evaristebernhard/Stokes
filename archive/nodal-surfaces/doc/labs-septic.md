# Labs Septic 数学预备文档

## 当前目标

`degree07` 的标准候选不是一个已知闭合的最大值定理，而是 Oliver Labs 的 99-real-nodal septic。它给出：

```text
mu(7) >= 99.
```

当前已知上界为：

```text
mu_R(7) <= mu(7) <= 104.
```

这里 `104` 来自 Varchenko spectral bound；Miyaoka 对七次只给出 `112`，Givental 也给出 `104`。因此本项目的 degree07 目标应当是：

```text
证明 Labs 当前方程恰有 99 个 reduced ordinary nodes.
```

而不是声称：

```text
mu(7) = 99.
```

## 方程

Labs 的曲面写成：

```text
S_alpha = P - U_alpha.
```

本文和 Rust 代码统一使用坐标顺序：

```text
[w:x:y:z].
```

论文公式本身按 `x,y,z,w` 书写。令

```text
alpha satisfies 7*alpha^3 + 7*alpha + 1 = 0.
```

唯一实根满足：

```text
alpha_R ~= -0.14010685.
```

当前 Rust exact arithmetic 使用具体三次数域：

```text
Q[alpha] / (7*alpha^3 + 7*alpha + 1).
```

也就是：

```text
alpha^3 = -alpha - 1/7.
```

Labs 的 `P` 是 7 个平面的乘积，清成有理系数后为：

```text
P =
  x*(x^6 - 21*x^4*y^2 + 35*x^2*y^4 - 7*y^6)
  + 7*z*((x^2+y^2)^3 - 8*z^2*(x^2+y^2)^2 + 16*z^4*(x^2+y^2))
  - 64*z^7.
```

`U_alpha` 为：

```text
U_alpha =
  (z + a5*w)
  * ((z+w)*(x^2+y^2)
     + a1*z^3 + a2*z^2*w + a3*z*w^2 + a4*w^3)^2.
```

参数是：

```text
a1 = -12/7*alpha^2 - 384/49*alpha - 8/7
a2 = -32/7*alpha^2 + 24/49*alpha - 4
a3 = -4*alpha^2 + 24/49*alpha - 4
a4 = -8/7*alpha^2 + 8/49*alpha - 8/7
a5 = 49*alpha^2 - 7*alpha + 50
```

所以 `S_alpha` 是 `Q(alpha)` 上的齐次七次式。

## D7 对称

`P` 来自正 7 边形方向上的 7 个平面。它有 `D7` 对称，旋转轴为：

```text
x = y = 0.
```

`U_alpha` 只通过 `x^2+y^2` 依赖 `x,y`，因此同样保持 `D7` 对称。generic 成员已有一批节点：

```text
3 * binomial(7, 2) = 3 * 21 = 63.
```

Labs 的特殊参数让节点数跃升到 `99`。

## 平面截面 y=0

Labs 的核心降维思想是先看平面：

```text
y = 0.
```

记平面七次曲线为：

```text
S_y = S_alpha |_{y=0}.
```

论文中的 Lemma 1 给出计数机制：如果 `S_y` 只有 ordinary double points，并且曲面在 `y=0` 上也只有 ordinary double points，则不在轴 `x=y=0` 上的平面节点通过 `D7` 生成长度为 7 的 orbit；轴上的节点保持为一个节点。

Labs 构造的特殊平面七次曲线有：

```text
15 plane nodes.
```

其中：

```text
1 node lies on the axis x=y=0,
14 nodes are off the axis.
```

于是曲面节点数为：

```text
1 + 14*7 = 99.
```

这是 degree07 最重要的数学结构：`99` 不是先从全局 Groebner 黑箱里读出来的，而是来自 `D7` 对称和 `y=0` 平面截面的 orbit 计数。

## 当前 Rust 状态

已新增：

```text
crates/degree07
```

当前最小复现完成：

- `CubicAlphaRational`：具体实现 `Q[alpha]/(7*alpha^3+7*alpha+1)`。
- `labs_alpha_polynomial_value()`：exact 验证 `7*alpha^3+7*alpha+1=0`。
- `labs_septic_polynomial()`：实现 `S_alpha=P-U_alpha`。
- `labs_septic()`：封装为七次曲面对象。
- `labs_septic_expected_orbit_count_from_plane_section()`：记录 `1+14*7=99` 的 orbit 计数。
- 测试覆盖 degree `7`、基础求值、gradient 接口、affine singular generator 接口。
- 已导入 `w=1` affine chart 的 grevlex Groebner certificate，quotient length 为 `99`。
- 已导入 `w=1` affine Hessian-bad certificate，证明：

```text
<F, Fx, Fy, Fz, det Hess_affine(F)> = <1>.
```

- 已生成并导入 projective support `1..14` 的 grevlex certificates；其中只有两个 boundary strata 非空：

```text
support 09 length = 1
support 11 length = 14
```

这正对应 plane-section 解释中的轴上 1 个节点和 `y=0`、离轴的 14 个节点。

当前代码采用一条更经济的 projective cover：

```text
P3 = {w != 0} union {w = 0}.
```

`w=1` affine chart 的 Jacobian ideal 已导入 grevlex 证书，quotient length 为 `99`；`w=0` 的 7 个非空 support strata 也已导入证书，quotient length 全为 `0`。这条路线绕开了最重的 all-nonzero localization，同时仍然把“无无穷远奇点”这件事分层检查出来。

support `15`，也就是 `w,x,y,z` 全非零的主开集，仍然是理解结构时最重要的一块。按 `D7`/plane-section 计数，它应贡献：

```text
99 - 1 - 14 = 84.
```

直接用 localization variable `tau` 计算 support `15` 的 reduced Groebner basis 目前过重；这一点本身是 degree07 相比 degree06 的新工程事实。替代方案已经试通：在 `w=1` affine chart 中令 `g=x*y*z`，计算

```text
H = <f,fx,fy,fz> : g^infty.
```

Cygwin-based Singular 给出 `sat_exp = 1`，`vdim(std(H)) = 84`，Rust 已导入 `labs-affine-chart0-support15-saturation-grevlex.cert` 并检查其 quotient length 为 `84`。完整严格的 reverse-containment witness 还需要证明每个 `H[j]` 满足 `g*H[j] in <f,fx,fy,fz>`；朴素 `lift` 会生成上百 MB 级别输出，已移出默认证书链。

## 后续证书路线

第一条路线是直接 projective support-strata 证书，复用 degree06 的 Barth 经验：

```text
15 nonempty projective supports in P3
for each support:
  choose chart variable
  set outside-support coordinates to 0
  add localization variable tau
  verify Groebner basis and quotient length
  verify lift identities G[j] = sum_i L[i,j]*F[i]
sum quotient lengths = 99
```

这条路线给出：

```text
saturated projective singular scheme length = 99.
```

当前已完成的 support length 分布规格为：

```text
[0,0,0,0,0,0,0,0,1,0,14,0,0,0,84]
```

其中 `1..14` 已有导入证书；最后的 `84` 现在有 affine saturation 证书作为 open-stratum 长度证据，但还缺 compact lift witness，暂不把它称为 full support-cover 机器证明。

第二条路线是 Hessian-bad locus 证书：

```text
<F, Fx, Fy, Fz, det Hess_affine(F)> = <1>
```

或者按 support strata 做等价的 Hessian rank 退化排除。结合 length `99`，这会把 singular-scheme 结论升级为：

```text
99 个 reduced ordinary nodes，无额外奇点。
```

当前 `w=1` affine chart 的 Hessian-bad ideal 已经由 Rust 导入证书验证为空；由于 infinity support 为空，数学上这正是需要排除 Hessian rank 退化的地方。工程上仍保留一个边界：affine Hessian-bad 的 lift witness 没有纳入默认测试，因此它和 support15 saturation 一样属于“导入 basis + Rust 复查”的层级，而不是 degree05 special 分支那种全 lift 闭包。

## 当前 Rust API

`crates/degree07` 现在区分三层证据：

```text
labs_affine_chart0_grevlex_certificate()
  imports w=1 Jacobian quotient length 99

labs_infinity_support_grevlex_certificates()
  imports the seven w=0 support strata, all length 0

labs_affine_chart0_support15_saturation_grevlex_certificate()
  imports the all-nonzero affine saturation length 84
```

默认 `cargo test -p degree07` 检查这些证书能解析、长度与模型约定一致，并验证轻量的 Hessian-bad unit certificate。重型 Buchberger 和 lift 重放被放进 ignored tests；按需单独运行，例如：

```text
cargo test -p degree07 affine_chart0_support15_saturation_certificate_buchberger_verifies_open_length -- --ignored
```

这样日常工程循环不会被 support15 或 infinity lift 的大整数重放拖垮，而严格复查入口仍保留。

第三条路线是数学解释层：

```text
y=0 plane section has 15 nodes
1 lies on the D7 axis
14 generate D7 orbits of size 7
1 + 14*7 = 99
```

这条路线应作为文档和 regression oracle；它解释构造为什么有 99，而 Groebner/lift 负责最终穷尽。

## 与 Chmutov/line-arrangement 路线的关系

Chmutov 构造给七次曲面的旧下界是：

```text
93 complex nodes.
```

Breske-Labs-van Straten 的 real line arrangement 路线能把 Chmutov 型构造实化；但在 degree 7 中，该路线只给 `96` 个节点，仍低于 Labs 的 `99`。因此 Labs septic 是七次奇数次数中首次超过 Chmutov general lower bound 的例子。

## 资料位置

本轮使用的本地资料：

- `arxiv/construction/labs-2006-septic-99-real-nodes.txt`
- `arxiv/construction/labs-2006-septic-99-real-nodes.pdf`
- `arxiv/construction/breske-labs-van-straten-2008-real-line-arrangements-published.txt`
- `arxiv/surveys/labs-2005-hypersurfaces-with-many-singularities-thesis.txt`

关键边界：

- Labs 方程与 `99` 节点下界可以本地复现。
- `mu(7) <= 104` 是外部上界背景，本项目短期只引用，不复现 Varchenko spectral bound。
- characteristic 5 下的 100-nodal septic 是有限域现象；Labs 明确没有把它 lift 到 characteristic zero。当前 degree07 主线不应把它当作 characteristic zero 目标。
