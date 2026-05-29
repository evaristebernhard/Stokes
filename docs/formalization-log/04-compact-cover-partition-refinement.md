# 04. 从紧支撑到有限 cover、partition、smooth refinement

## 数学阻塞

紧支撑 Stokes 的纸面证明会说：令 `K = supp(ω)` 的紧闭包，取有限个 chart box 覆盖 `K`，再取 subordinate partition of unity。

Lean 中这句话包含多个不同的构造：

- `K` 必须是一个具体 set；
- pointwise chart-box neighborhood 必须能转成 open cover；
- compactness 必须给出 finite selection；
- partition 的 support 必须保留在选定区域内；
- boundary active carrier 还要再被 half-space boxes refinement；
- refined coefficient 要能重构原 boundary coefficient。

这些不是普通 bookkeeping。每一步都影响人工边界是否能消失，也影响 represented endpoint 是否真的等于局部 finite sum。

## 错误或不自然路线

早期路线常把 selected cover、assigned cover set openness、ambient open data、smooth refinement 作为用户输入。这样虽然能推进局部 theorem，但 public theorem 很不自然：

```text
用户必须知道证明内部要用哪些 chart boxes 和 refined pieces
```

这与数学定理不符。紧支撑 theorem 的用户应该只提供 smoothness 和 compact support；cover 和 partition 应该由证明选择。

另一个历史问题是：pointwise chart box 本身未必就是适合 partition-of-unity 的 ambient open set。因此不能直接拿 closed/semi-closed chart box 当 open cover。需要先从 `chartBox_mem_nhds` 抽出 auxiliary open shrink，再通过 open shrink 建 finite cover 和 support-controlled partition。

## 最终解决方案

first-principles theorem 取 canonical carrier：

```lean
supportCarrier := closure (ManifoldForm.support I ω)
```

这个选择位于：

```text
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesFirstPrinciples.lean
```

它把公开 compactness 假设固定为：

```lean
IsCompact (closure (ManifoldForm.support I ω))
```

并用 `subset_closure` 自动填入 intrinsic input 的 support containment。

### pointwise chart boxes

半空间模型和 self charts 生成 pointwise chart-box data：

```lean
PointwiseCompactSupportChartBoxData.ofHalfSpaceModelSelfCharts
```

位置：

```text
Stokes/Global/PointwiseChartBoxFromHalfSpaceModel.lean
```

这一步把 interior/boundary dichotomy 内部化：normal coordinate 正则选 interior box；normal coordinate 为零则选 lower-zero boundary half-space box。

### open shrink finite selection

open shrink 层在：

```text
Stokes/Global/CoverIndexedPointwiseOpenSelection.lean
```

关键 API：

```lean
PointwiseCompactSupportChartBoxData.OpenShrink
PointwiseCompactSupportChartBoxData.OpenSelectedCover
PointwiseCompactSupportChartBoxData.selectedOpenCoverOfPointwise
PointwiseCompactSupportChartBoxData.selectedOpenCoverOfPointwise_spec
PointwiseCompactSupportChartBoxData.selectedCoverOfOpenPointwise
PointwiseCompactSupportChartBoxData.selectedOpenSupportControlledPartition
PointwiseCompactSupportChartBoxData.selectedOpenSupportControlledPartition_tsupport_inter_subset_assigned
```

数学意义：

```text
pointwise neighborhood data
⇒ choose open shrink inside selected chart box
⇒ compactness gives finite selected cover
⇒ partition support can be controlled by the open shrink
⇒ support still lands in the original assigned chart box
```

### support-controlled partition

support-controlled partition 层在：

```text
Stokes/Global/CoverIndexedOpenSupportControlledPartition.lean
```

关键 API：

```lean
OpenSupportControlledSelectedPartition
OpenSelectedCover.exists_openSupportControlledSelectedPartition
OpenSelectedCover.openSupportControlledSelectedPartition
OpenSelectedCover.openSupportControlledSelectedPartition_tsupport_inter_subset_openCoverSet
OpenSelectedCover.openSupportControlledSelectedPartition_tsupport_inter_subset_assigned
```

这比普通 partition 多了核心信息：

```text
tsupport(partition j) ∩ K ⊆ selected open/assigned chart box
```

没有这个信息，后续无法证明局部化 form 的 support 落入 selected box，也无法杀人工边界。

### boundary finite half-space cover

boundary active carrier 还要在坐标中被 half-space boxes 覆盖：

```lean
SupportControlledSelectedPartition.finiteHalfSpaceCoverOfSelectedBoundaryBoxes
```

位置：

```text
Stokes/Global/CoverIndexedSelectedBoundaryBoxFiniteCover.lean
```

在 intrinsic route 中包装为：

```lean
CoverIndexedZeroCompactRepresentedStokesIntrinsicInput.selectedBoundaryFiniteCover
```

它使用 selected boundary boxes 本身作为 coordinate ambient，避免重新暴露 `boundaryAmbient` 和 `collar_prisms`。

### smooth refinement

smooth refinement 构造在：

```text
Stokes/Global/CoverIndexedIntrinsicSmoothRefinementConstructor.lean
```

关键 API：

```lean
selectedSmoothRefinementAmbientOpen
isOpen_selectedSmoothRefinementAmbientOpen
boundaryActiveCarrier_subset_iUnion_selectedSmoothRefinementAmbientOpen
selectedSmoothRefinementAmbientOpen_subset_boundaryChartBox
selectedSmoothRefinement
selectedSmoothRefinement_boundaryPieces
selectedSmoothRefinement_activeCarrier
```

这一步解决 sigma-indexed box 问题：一个 boundary chart index `i` 对应多个 refined pieces `q`。最终 represented endpoint 是 `(i,q)` 的嵌套 finite sum，而不是每个 boundary center 只有一个 box。

## 对主 theorem 的贡献

这些构造在 intrinsic input 中串起来：

```lean
openSelectedCover
selectedCover
openSelectedPartition
selectedPartition
selectedBoundaryFiniteCover
selectedSmoothRefinement
```

然后进入：

```lean
hasIntrinsicRoute_intrinsic
representedStokes
```

FirstPrinciples theorem 再把 pointwise input 也隐藏掉：

```lean
intrinsicInput.pointwise :=
  PointwiseCompactSupportChartBoxData.ofHalfSpaceModelSelfCharts ...
```

所以最终 public theorem 里看不到 cover/partition/refinement，不是因为它们不存在，而是因为 Lean 已经从 compact support 和 chart geometry 构造了它们。

## 论文可用表述

中文表述：

> 紧支撑在 Lean 中不是一句“取有限子覆盖”就结束。我们形式化了从 pointwise chart-box neighborhood 到 auxiliary open shrink、finite selected cover、support-controlled partition、boundary finite half-space cover、smooth refinement 的完整构造链。这个链条保证每个局部化 summand 的支撑落在选定盒子中，从而能应用半空间局部 Stokes 并杀掉人工边界。

英文表述：

> Compact support is used constructively. The formalization turns pointwise chart-box neighborhoods into open shrinks, extracts a finite selected cover, constructs a support-controlled partition, refines the boundary active carriers by finite half-space boxes, and produces smooth refined coefficients. This is the mechanism that makes the final theorem first-principles rather than certificate-driven.
