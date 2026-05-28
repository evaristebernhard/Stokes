# strict-buffer public API audit

日期：2026-05-25

范围：只审计当前 `Stokes/Global.lean` 聚合入口，以及
`Stokes/Global/CompactSupportStrictBuffer.lean` 的 public names。没有修改任何
Lean 文件或聚合文件。

## 检查依据

已读取：

- `Stokes/Global.lean`
- `Stokes/Global/CompactSupportStrictBuffer.lean`
- 既有对照报告：`reports/M8_public_api_audit.md`

按任务要求，本报告没有运行 `lake build`。当前审计没有发现需要通过编译来澄清的
明显 Lean 语法或 import 问题；主线程在聚合决策后仍应统一运行：

```text
lake build
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

## 当前聚合状态

`Stokes/Global.lean` 当前已经聚合：

- `Stokes.Global.CompactSupportBoxBufferBuilder`
- `Stokes.Global.CompactSupportStrictBuffer`

也就是说，`CompactSupportStrictBuffer.lean` 现在不是“待加入 public API”的候选，
而是已经进入 public `Stokes.Global` 的模块。审计重点因此应是：是否保留、是否需要
后续改名、以及是否避免继续扩大 public surface。

## CompactSupportStrictBuffer public names

当前模块位于 `namespace Stokes` 下，暴露的顶层几何引理是：

- `Stokes.Icc_subset_boxInteriorSupportBox`
- `Stokes.tsupport_subset_boxInteriorSupportBox_of_subset_Icc`
- `Stokes.exists_boxInteriorSupportBox_subset_of_isCompact`

核心数据结构是：

- `Stokes.LocalizedInteriorFormInnerBoxBuffer`
- `Stokes.LocalizedInteriorCoefficientInnerBoxBuffer`

两个结构各自 namespace 下的主要投影和构造器是：

- `localized_tsupport_subset_interiorBox`
- `coefficient_tsupport_subset_interiorBox`
- `toCompactSupportBoxBuffer`
- `toCompactSupportBoxBuffer_support`
- `toM8ArtificialFaceFields`
- `toM8ArtificialFaceFields_active`

此外还有两个面向已有 localized API 的辅助定理：

- `Stokes.ManifoldForm.transitionPullbackInChart_localizedForm_tsupport_subset_interiorBox_of_coefficient_Icc`
- `Stokes.LocalizedInteriorPiece.transitionPullback_tsupport_subset_interiorBox_of_coefficient_Icc`

## 风险判断

整体风险偏低。两个核心 record 分别放在自己的 namespace 下，`toCompactSupportBoxBuffer`
和 `toM8ArtificialFaceFields` 这类短名不会在打开 `Stokes` 后直接污染顶层。

主要风险是三个顶层几何引理命名略泛：

- `Icc_subset_boxInteriorSupportBox`
- `tsupport_subset_boxInteriorSupportBox_of_subset_Icc`
- `exists_boxInteriorSupportBox_subset_of_isCompact`

它们目前仍带有 `boxInteriorSupportBox` 这个项目局部概念，尚可接受；但如果后续 strict
buffer 模块继续增加，建议不要再新增类似泛名，而是进入更窄 namespace，或加
`compactSupport` / `strictBuffer` 前缀。

`exists_boxInteriorSupportBox_subset_of_isCompact` 的注释已经清楚说明：它只给任意紧集
找一个坐标盒的 strict interior containment，不负责 chart-domain containment。这个区分很
重要，不能把它宣传成完整 chart-box selection lemma。

## 聚合建议

建议保留在 public `Stokes.Global`：

- `Stokes.Global.CompactSupportStrictBuffer`

理由：它正好填补当前 M8 artificial-face support-zero 路线需要的中间层：从 inner closed
box support + strict margin，生成 `CompactSupportBoxBuffer`，再生成
`M8ArtificialFaceFields`。这是主线 API，不只是报告或实验文件。

建议继续保留其依赖的 public builder：

- `Stokes.Global.CompactSupportBoxBufferBuilder`

理由：`CompactSupportStrictBuffer` 直接依赖 builder 中的
`CompactSupportBoxBuffer.ofStrictSupportSubsetInteriorBox` 和 coefficient-buffer bridge。
如果 strict-buffer 是 public，builder 层也应保持可见。

不建议因为本模块再额外聚合新的 canonical wrapper 或 `*2` 临时模块。之前的
`M8_public_api_audit.md` 对 `CanonicalNaturalStokes`、`NaturalStokesStatement2`、
`NaturalBoundaryMeasureBuilder2`、`BuilderProjectionAudit` 的暂缓建议仍然适用。

## 命名规范建议

后续 strict-buffer 相关模块建议采用以下规则：

- 稳定 public record 用 `...InnerBoxBuffer` 或 `...StrictBuffer`，不要使用 `*Data2`、
  `*Statement2` 这类临时名进入 public 聚合。
- 面向 M8 的投影继续放在 record namespace 下，使用 `toCompactSupportBoxBuffer`、
  `toM8ArtificialFaceFields` 这种短 projection 名。
- 新的几何引理优先放入窄 namespace，避免继续增加 `Stokes.*` 顶层泛名。
- 如果某个 lemma 只证明“纯坐标紧集可被一个 strict box 包住”，名字和注释必须继续明确：
  它不是完整 chart-domain selected-box theorem。

## 下一步建议

主线程可以把 `CompactSupportStrictBuffer` 视为当前 strict-buffer 的第一批稳定 public
模块。下一步真正要证明的是更强的 selected chart-box theorem：

```text
localized chart representative 的 tsupport
  ⊆ inner closed box
  ⊆ selected outer box 的 strict interior
```

并且这个 theorem 还需要携带 chart-domain / selected-box 的几何条件，而不是只使用纯坐标
compact-set containment。
