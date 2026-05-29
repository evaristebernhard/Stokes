# 01. 总故事：从局部 Stokes 到 first-principles represented Stokes

## 数学阻塞

纸面上的紧支撑 Stokes 定理通常写成：

```text
∫_M dω = ∫_{∂M} ω
```

但这个等式在证明中不是直接出现的。经典证明会先做一串隐含选择：

- 用 compact support 把问题限制到一个紧集；
- 为紧集选有限个 chart box；
- 选 partition of unity；
- 把 form 拆成局部项；
- 在每个坐标盒上应用局部 Stokes；
- 证明辅助盒子的人工边界项消失；
- 把局部等式重新合成全局等式。

数学家在纸面证明里可以把这些步骤压成一句“取 subordinate partition of unity”。Lean 不允许这样压缩。每一个选择都必须有数据，每一个“支撑落在盒子里”都必须变成 theorem，每一个“边界项消失”都必须指明是哪一类 face、哪一个 support 假设、哪一个 integral 为零。

这个项目真正完成的核心，不是单个 wrapper，而是把上述隐含证明链条形式化成可以由 Lean 检查的构造链，然后再把公开入口压回数学上自然的两个输入。

## 错误或不自然路线

项目历史上出现过很多中间路线：Raw、Clean、Compact、Natural、FromCollar、Intrinsic、FirstPrinciples。它们不应该简单理解为“噪音文件”。它们记录了假设逐步被消掉的过程。

早期路线常把以下内容作为输入：

- 手填 finite cover；
- 手填 partition 或 refinement；
- 手填 local Stokes fields；
- 手填 ambient open smoothness；
- 手填 endpoint adapter；
- 手填 target image/control data；
- 手填 ordinary `transitionPullbackInChart` support。

这些字段有些是临时证书，有些是错误抽象，有些甚至对应边界 chart 上不自然的数学假设。后续路线的主要工作，就是不断把它们替换成由 compact support、chartwise smoothness、half-space model geometry 自动构造出来的对象。

`reports/remaining_input_scoreboard.md` 曾经明确指出：进展不应该再靠“大 wrapper wave”，而应该看是否真正删除 theorem-facing assumptions。这个判断后来在 FirstPrinciples 路线中落地。

## 最终解决方案

当前主入口是：

```lean
CoverIndexedZeroCompactRepresentedStokesFirstPrinciplesInput
CoverIndexedZeroCompactRepresentedStokesFirstPrinciplesInput.representedStokes
```

它位于：

```text
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesFirstPrinciples.lean
```

公开字段只有：

```lean
chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω
compactSupport : IsCompact (closure (ManifoldForm.support I ω))
```

内部定义：

```lean
supportCarrier := closure (ManifoldForm.support I ω)
intrinsicInput
canonicalRepresentedBulkIntegral
canonicalRepresentedBoundaryIntegral
```

然后调用 intrinsic route：

```lean
(X.intrinsicInput ...).representedStokes
```

这个顶层 proof 很短，但短不是因为数学少，而是因为数学已经被组织到内部构造中：

- `PointwiseCompactSupportChartBoxData.ofHalfSpaceModelSelfCharts`
- `selectedOpenCoverOfPointwise`
- `openSupportControlledSelectedPartition`
- `finiteHalfSpaceCoverOfSelectedBoundaryBoxes`
- `selectedSmoothRefinement`
- `zeroSupportOfSelectedSmoothRefinement`
- `interiorFieldsOfSelectedSmoothRefinement`
- `hasIntrinsicRoute_intrinsic`

## 对主 theorem 的贡献

FirstPrinciples theorem 的意义是：用户不再提供 chart-box 数据、cover 数据、partition 数据、local Stokes 数据、endpoint adapter 数据。它把这些都变成 theorem 的内部构造。

这说明我们证明的不是“如果有人给你一个巨大证书，那么 Stokes 成立”，而是更强的 represented statement：

```text
chartwise smooth + compact closed support
  ⇒ canonical finite coordinate Stokes route exists
  ⇒ represented bulk endpoint = represented boundary endpoint
```

这里的 represented endpoint 是经典局部到整体证明展开后的有限坐标和。它还没有被识别为未来 mathlib-native manifold integral，但它已经包含了 Stokes 证明中最硬的 local-to-global payload。

## 论文可用表述

中文表述：

> 本项目的主结果不是一个薄包装定理，而是一个从第一性原理输入自动生成局部到整体 Stokes 证明路线的形式化构造。Lean 公开接口只要求 chartwise smoothness 和 support closure compactness；有限 cover、支撑受控 partition、边界 half-space refinement、zero-localized support、局部 Stokes fields 和 represented endpoint equality 都由证明内部构造。

英文表述：

> The main theorem is not a certificate-consuming wrapper. It is a compression theorem: from chartwise smoothness and compactness of the closed support, the formalization constructs the finite coordinate decomposition, support-controlled refinement, zero-localized representatives, local half-space Stokes data, and canonical represented endpoints, and then proves equality of those endpoints.
