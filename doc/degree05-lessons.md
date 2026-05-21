# Degree05 经验总结

## 已经证明的结论

当前 `degree05` 有两条 Togliatti quintic 路线：

1. Proposition 130 determinant 模型。
2. Catanese 综述 2.5.1 的 special Togliatti 模型。

机器证明的 `31` 结论来自第二条 special Togliatti 路线。Rust exact verifier 现在证明：

```text
special_togliatti_singular_scheme_certificate()
  .verified_reduced_ordinary_node_count()
  = Some(31)
```

证明链是：

```text
w = 1 chart Jacobian quotient length = 31
w = 0 infinity support strata all empty
Groebner basis lift certificates verify <G> subset I
normal-form checks verify I subset <G>
bad Hessian locus <F,Fx,Fy,Fz,det Hess(F)> is unit ideal
```

因此 special Togliatti 模型的 saturated projective singular scheme 恰为 `31` 个 reduced ordinary nodes，没有第 `32` 个奇点。

Proposition 130 determinant 模型仍作为待排查对象保留。当前按本地 TeX 公式转写后，support-cover 证书给出的 projective singular-scheme length 是 `16`，不是文献目标 `31`。这不是一个小测试缺口，而是模型/公式/语义之间的 blocker。

## 数学经验

### 方程不是构造本身

五次曲面的复现不能把一段显式方程当作全部构造。一个可复查构造至少包含：

```text
explicit equation
projective Jacobian ideal semantics
saturation or chart-cover semantics
singular-scheme length
reducedness / ordinary-node upgrade
comparison with the sharp upper bound
```

determinant 分支的 `16` vs `31` 正好说明：只要公式版本、变量约定、参数或转写有偏差，机器证书会立刻把“看起来像 Togliatti”的方程和真正的 31 节点曲面分开。

### Length 不是节点数

在 affine chart 中证明 Jacobian quotient length 为 `31`，只说明奇异 scheme 带重数长度为 `31`。它本身不排除高重数点或非节点奇点。

这次 special 分支采用了更结构化的判据：

```text
<F, Fx, Fy, Fz, det Hess(F)> = <1>
```

也就是不存在 Hessian 退化的奇点。对 `P3` 中的曲面 hypersurface，affine Hessian 非退化意味着局部二次项非退化，因此奇点是 ordinary double point。ordinary node 的局部 Jacobian algebra 长度为 `1`，所以全局 length `31` 升级为 `31` 个 reduced nodes。

### Projective 语义要显式写出来

degree03 和 degree04 还能靠显式点和对称性维持可读性；degree05 开始，projective/saturation 语义必须进入证书。

special 分支现在用的是 chart-cover 版本：

```text
w = 1: 主 affine chart，长度 31
w = 0: infinity hyperplane，7 个坐标支撑层全为空
```

这等价于证明 saturated projective singular locus 全部落在 `w=1` chart 中，而不是直接信任某个 affine 计算。

### CAS 只能生成证书，不能成为信任根

最初的 Groebner verifier 只检查：

```text
I generators reduce to 0 by G
G passes Buchberger criterion
```

这只能证明 `I subset <G>`。为了证明 imported basis 真的是原 ideal 的 Groebner basis，还需要反向包含：

```text
<G> subset I
```

因此新增 `.lift` 证书，逐项验证：

```text
G_j = sum_i L_ij F_i
```

Hessian-bad 的 lift 系数很大，推动 `nodal-core` 增加了 `BigQuadraticRational`。这是一个很有代表性的工程经验：严格证书会自然暴露底层代数类型的真实需求。

## 对后续次数的启发

degree05 是从“显式点验证”走向“scheme 级证书”的分水岭。后续研究 degree06、degree07、degree08 时，顺序应该是：

1. 先理解极值例子的几何来源。
2. 再选择适合复现的显式模型。
3. 然后设计 projective singular-locus 证书。
4. 最后才补坐标展示、数值渲染或更漂亮的解释。

对 Endraß octic 尤其如此。八次曲面的 `168` 不是孤立的大方程，而是对称性、平面乘积结构、参数调节、Hessian 非退化和 Miyaoka 上界共同构成的证明链。

## 当前下一步

短期不必继续堆工程。更值得做的是：

- 复核 determinant 分支为什么只得到 `16`，但不让它阻塞 special 分支的已完成 `31` 结论。
- 补一份 31 个点的代数坐标/消元展示，让 special Togliatti 的点集更可读。
- 继续整理 degree06 Barth sextic 和 degree08 Endraß octic 的数学来源，再决定证书形态。
