# 03. 半空间边界局部 Stokes 与人工边界

## 数学阻塞

边界 chart 的局部模型不是整个 `R^(n+1)`，而是闭上半空间：

```text
upperHalfSpace n = {x | 0 ≤ x 0}
```

在边界点附近，选定盒子可能贴着 `x 0 = 0`。纸面证明会在半空间中做局部 Stokes，然后说辅助盒子的其他 face 不是流形边界，因支撑消失。

Lean 中这句话分裂成几个硬问题：

- lower normal face `x0 = 0` 要被识别为真实边界；
- upper normal face 和 tangential faces 是人工边界；
- 人工边界 integral 为零必须由 support disjoint 或 `tsupport` containment 推出；
- 边界符号必须和 outward-normal-first convention 对齐；
- 边界 chart 上不能要求 closed box 有普通 ambient open smoothness。

## 错误或不自然路线

一个早期自然但错误的想法是：要求 form 在包含整个 closed box 的 ambient open set 上 smooth，并且这个 open set 落在 chart target 内。

这个假设在 interior chart 上看起来合理，但在 boundary chart 上不合理。若 closed box 碰到 `x0 = 0`，它在模型范围内是合法的半空间盒子，但它不应该被要求拥有完整欧氏空间中的 chart-target open neighborhood。bulk derivative 只在 open box interior 上需要；boundary face 需要连续性和 integrability，而不是 ambient smoothness across the boundary。

这就是为什么后续路线改成 interior-fields / open-interior smoothness / closed-box regularity 的分层，而不是继续堆一个假的 `U ⊆ target` 大假设。

## 最终解决方案

半空间基础层在：

```text
Stokes/HalfSpace/Basic.lean
```

关键符号和定理：

```lean
upperHalfSpace
upperHalfSpaceBoundary
boundaryInclusion
outwardNormal
boundaryTangent
outwardFirstBoundaryFrame
outwardFirstBoundaryOrientationSign
halfSpaceBoundarySign
halfSpaceBoundarySign_eq_outwardFirstBoundaryOrientationSign
```

这里把 lower face 的坐标边界和 outward-first boundary orientation 的符号对齐。

人工边界层在：

```text
Stokes/HalfSpace/Faces.lean
Stokes/HalfSpace/LocalStokes.lean
```

关键 API：

```lean
halfSpaceSupportBox
boxFaceCoeffTSupportInHalfSpaceBox
boxFaceCoeffTSupportInHalfSpaceBox_of_tsupport_subset
boxRemainingFormFaceTerms
boxRemainingFormFaceTerms_eq_zero_of_tsupport_disjoint_artificial
boxRemainingFormFaceTerms_eq_zero_of_tsupport_subset_halfSpaceSupportBox
halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_disjoint_artificial
halfSpaceLocalBoundaryRemainder_eq_zero_of_tsupport_subset_halfSpaceSupportBox
```

数学上，这条链证明：

```text
tsupport(α) lies in half-space support box
⇒ α misses every artificial face
⇒ artificial face remainder = 0
```

真正的局部 Stokes theorem 在：

```text
Stokes/HalfSpace/BoxInteriorStokes.lean
Stokes/HalfSpace/BoxInteriorSmoothness.lean
```

关键结构和定理：

```lean
HalfSpaceBoxInteriorStokesFields
HalfSpaceBoxInteriorStokesFields.withRemainder
HalfSpaceBoxInteriorStokesFields.compactSupport
halfSpaceLocalStokes_compactSupport_of_interiorFields
HalfSpaceBoxOpenInteriorSmoothnessFields
HalfSpaceBoxInteriorStokesFields.ofOpenInteriorSmoothness
halfSpaceLocalStokes_compactSupport_of_openInteriorSmoothness
```

`HalfSpaceBoxInteriorStokesFields` 的意义不是“又一个证书”。它是把局部半空间 Stokes 需要的合法分析条件拆开：

- `a 0 = 0`，表示 lower normal face 是半空间边界；
- `a ≤ b`，表示盒子合法；
- Euclidean box Stokes 所需 regularity；
- bulk integral 和 box integral 的 a.e. bridge；
- closed-box continuity / integrability；
- 不要求 closed boundary box 跨过半空间边界有 ambient smoothness。

## lower normal face 与 outward-first sign

`Stokes/HalfSpace/BoundaryIntegral.lean` 负责把 cube lower face term 与 half-space boundary integral 对齐：

```lean
lowerZeroSignedCoeff_eq_halfSpaceBoundarySign
halfSpaceBoundaryFormIntegral
outwardFirstHalfSpaceBoundaryFormIntegral
outwardFirstHalfSpaceBoundaryFormIntegral_eq_halfSpaceBoundarySign_mul
lowerZero_toCoordNForm_eq_boundaryForm
boxLowerZeroCoordFaceTerm_toCoordNForm_eq_halfSpaceBoundaryFormTerm
```

这一步很重要。人工 face 消失以后，剩下的不是“某个 cube face”，而是带 outward-first sign 的真实边界项。没有这个 sign bridge，represented boundary endpoint 无法解释为 Stokes 右边的 boundary contribution。

## 对主 theorem 的贡献

最终 first-principles theorem 不暴露 `HalfSpaceBoxInteriorStokesFields`。这些 fields 由：

```lean
CoverIndexedZeroCompactRepresentedStokesIntrinsicInput.interiorFieldsOfSelectedSmoothRefinement
```

自动构造。zero support theorem 提供：

```lean
zero_tsupport_subset_halfSpaceSupportBox
```

然后 local certificate 使用：

```lean
CoverIndexedBoundaryLocalizedRefinedPartition.ZeroLocalStokesData.localStokes_of_interiorFields
CoverIndexedBoundaryLocalizedRefinedPartition.representedStokes_of_zeroLocalStokesData
```

这说明 half-space local theorem 已经被接入全局 represented Stokes 路线，而不是孤立的局部 lemma。

## 论文可用表述

中文表述：

> 边界局部 Stokes 的形式化不能把边界盒子当成普通欧氏 open-neighborhood 问题。我们的 half-space 层把 bulk derivative 所需的 open-box interior regularity、closed-box/face regularity、人工边界 support vanishing、以及 lower normal face 的 outward-first sign 分离成可检查的定理。这样最终 theorem 不需要假的 ambient-open smoothness 假设。

英文表述：

> Boundary charts force a genuine half-space local theorem. The formalization separates open-interior differentiability from closed-box face regularity, proves that artificial faces vanish from topological support containment, and identifies the lower normal face with the outward-first boundary orientation. This prevents the global theorem from relying on an invalid ambient-open smoothness assumption at boundary points.
