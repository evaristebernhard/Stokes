# M8 compact-support public API audit

日期：2026-05-24

范围：只审计当前 M8 compact-support theorem / public API 的聚合风险。
本报告没有修改 `Stokes/Global.lean`、`Stokes/HalfSpace.lean`、`AGENTS.md`
或任何聚合文件，也没有新增 Lean convenience 文件。

## 本轮检查依据

已读取：

- `Stokes/Global.lean` 当前 import 列表。
- `Stokes/Global/ArtificialFaceBufferSupport.lean`
- `Stokes/Global/CanonicalNaturalStokes.lean`
- `Stokes/Global/CanonicalNaturalCompactSupport.lean`
- `Stokes/Global/NaturalStokesStatement2.lean`
- `Stokes/Global/NaturalBoundaryMeasureBuilder2.lean`
- `Stokes/Global/BuilderProjectionAudit.lean`
- 对照文件：`NaturalCompactSupportBuilder.lean`,
  `NaturalCompactSupportStokesStatement.lean`,
  `NaturalBoundaryMeasureBuilder.lean`,
  `CanonicalIntegralInterface.lean`

已运行的 Lean 检查：

```text
lake env lean Stokes\Global\ArtificialFaceBufferSupport.lean
lake env lean Stokes\Global\CanonicalNaturalStokes.lean
lake env lean Stokes\Global\CanonicalNaturalCompactSupport.lean
lake env lean Stokes\Global\NaturalStokesStatement2.lean
lake env lean Stokes\Global\NaturalBoundaryMeasureBuilder2.lean
lake env lean Stokes\Global\BuilderProjectionAudit.lean
```

以上 focused checks 均通过。

也运行了候选目标的 batch build：

```text
lake build Stokes.Global.ArtificialFaceBufferSupport \
  Stokes.Global.CanonicalNaturalStokes \
  Stokes.Global.CanonicalNaturalCompactSupport \
  Stokes.Global.NaturalStokesStatement2 \
  Stokes.Global.NaturalBoundaryMeasureBuilder2 \
  Stokes.Global.BuilderProjectionAudit
```

结果通过。唯一输出是既有无关 warning：
`LeanStokes/CubeStokes/Bridge.lean:72` 的 `show` tactic style warning。

候选文件 focused no-sorry scan 无结果：

```text
rg "\bsorry\b|\badmit\b|^\s*axiom\b" \
  Stokes\Global\ArtificialFaceBufferSupport.lean \
  Stokes\Global\CanonicalNaturalStokes.lean \
  Stokes\Global\CanonicalNaturalCompactSupport.lean \
  Stokes\Global\NaturalStokesStatement2.lean \
  Stokes\Global\NaturalBoundaryMeasureBuilder2.lean \
  Stokes\Global\BuilderProjectionAudit.lean
```

co-import stdin 实验没有作为证据使用；按主线程要求，本报告停止继续实验。

## 当前聚合状态

`Stokes/Global.lean` 已经聚合了 M8 compact-support 主干，包括：

- `M8Statement`, `M8CompactSupportStatement`
- `CanonicalIntegralInterface`
- `NaturalCompactSupportStokesStatement`
- `M8InputBuilder`
- `NaturalCompactSupportBuilder`
- `NaturalBoundaryMeasureBuilder`
- `CompactSupportMeasureToM8Builder`
- `ArtificialFaceNaturalBuilder`
- `OrientationBridgeToM8`
- `TargetImageLocalOpennessToM8`
- `TargetImageIFTToM8`

本轮点名的六个文件目前都没有在 `Stokes/Global.lean` 中聚合。

## 候选文件结论

| 文件 | focused build | no-sorry | 聚合建议 | 原因 |
|---|---:|---:|---|---|
| `ArtificialFaceBufferSupport.lean` | 通过 | 通过 | 可以安全聚合，建议第一批 | 声明 `CompactSupportBoxBuffer`，把严格支撑落在 box interior 的几何输入转成 `SelectedPartitionSupportZeroGeometry`、`M8ArtificialFaceFields`、`M8CompactSupportArtificialFaceResolvedData`。这是 M8 compact-support 人工面路线的真实有用入口。未看到名字碰撞；依赖只到 `ArtificialFaceSupportZeroGeometry`，不会触碰 `HalfSpace` 循环。 |
| `CanonicalNaturalCompactSupport.lean` | 通过 | 通过 | 技术上可聚合，但建议作为唯一 canonical natural wrapper 之一来选 | 给 `NaturalCompactSupportStokesInput` 增加 `canonicalIntegralInterface`, `representedGlobalIntegralInterface`, `canonical_stokes`, `representedGlobalIntegralInterface_stokes`。这是 statement surface，不 discharge 新数学假设，但名字适合公共 API。 |
| `CanonicalNaturalStokes.lean` | 通过 | 通过 | 技术上可聚合；若已选择上一个文件，建议暂缓或合并 | 当前已避开早先担心的直接重名：它使用 `measureCanonicalIntegralInterface` / `measureCanonical_stokes`，不再定义同名 `canonicalIntegralInterface`。但它和 `CanonicalNaturalCompactSupport` 语义重叠，都是 canonical theorem-facing name wrapper。公共 API 最好不要同时暴露两套接近名字。 |
| `NaturalStokesStatement2.lean` | 通过 | 通过 | 不建议聚合 | 文件名带 `2`，内容只是 `NaturalCompactSupportBuilderData.stokes` / `stokes_compactSupportFields` 的 theorem-level adapter。没有新证明节点，属于临时 statement wrapper。应合并进 `NaturalCompactSupportBuilder.lean` 或重命名后再公开。 |
| `NaturalBoundaryMeasureBuilder2.lean` | 通过 | 通过 | 暂不聚合，先重命名/合并 | 这是 COV-facing boundary measure builder，和已聚合的 `NaturalBoundaryMeasureBuilder.lean` 不是完全同一条路线：前者从 `BoundaryCOVMeasureReconstructionFields` 进 M8，后者从 `BoundaryCompactMeasureFields` / `BoundaryMeasureLocalizationData` 进 M8。Lean 名字大多在不同 namespace 下，直接碰撞风险不高，但 `*2` 文件名说明 API 还没稳定。建议改名为 `NaturalBoundaryCOVMeasureBuilder.lean`，再决定是否公开。 |
| `BuilderProjectionAudit.lean` | 通过 | 通过 | 不应聚合 | 这是审计/检查文件，几乎没有公开声明。它 import 了 `NaturalBulkMeasureBuilder` 等未稳定路线，会把非 public API 拉进聚合层。没有数学或用户 API 收益。 |

## 具体名字风险

### Canonical wrappers

早先风险是 `CanonicalNaturalStokes` 和 `CanonicalNaturalCompactSupport`
可能都在 `NaturalCompactSupportStokesInput` namespace 下声明同名入口。
当前文件内容显示：

- `CanonicalNaturalCompactSupport` 声明：
  - `canonicalIntegralInterface`
  - `representedGlobalIntegralInterface`
  - `canonical_stokes`
  - `representedGlobalIntegralInterface_stokes`
  - `naturalCompactSupportStokes_canonical`
  - `naturalCompactSupportStokes_represented`
- `CanonicalNaturalStokes` 声明：
  - `measureCanonicalIntegralInterface`
  - `measureCanonical_stokes`
  - `measureCanonical_manifoldExtDerivIntegral_eq_boundaryFormIntegral`
  - `canonicalNaturalCompactSupportStokes_manifoldExtDerivIntegral_eq_boundaryFormIntegral`

因此目前没有明显同名声明碰撞。但二者都是 represented `Real` skeleton
上的 statement surface，不是新的 manifold integral 定义。公共层建议只保留
一条主路线，另一条可以改成小定理并入主文件。

推荐主路线：`CanonicalNaturalCompactSupport`。
原因：它同时给出 canonical interface 和 represented interface，
与已聚合的 `CanonicalIntegralInterface` / `NaturalCompactSupportStokesStatement`
连接更自然。

### Boundary measure builders

当前已聚合 `NaturalBoundaryMeasureBuilder.lean`。它的主 record 是：

- `NaturalBoundaryMeasureBuilderData`

`NaturalBoundaryMeasureBuilder2.lean` 的主 record 是：

- `NaturalBoundaryCOVMeasureBuilderData`

这不是直接同名碰撞，但语义层次接近，且 `*2` 文件名会污染 public API。
建议先重命名为 `NaturalBoundaryCOVMeasureBuilder.lean`，并在报告或 docstring
中明确：

- compact/set-integral route：`NaturalBoundaryMeasureBuilderData`
- COV reconstruction route：`NaturalBoundaryCOVMeasureBuilderData`

之后再考虑聚合。

### BuilderProjectionAudit

`BuilderProjectionAudit.lean` 目前没有实质 public theorem。它的作用是给开发者
检查 builder handoff，不应该进入 `Stokes.Global` 用户入口。

## 下一步 import / integration 建议

建议主线程采用三段式，而不是一次全 import：

第一批，安全且有实际用途：

```lean
import Stokes.Global.ArtificialFaceBufferSupport
```

理由：它把 compact support box buffer 接到 artificial-face support-zero
路线，是 M8 compact-support 输入清理的真实节点。

第二批，选择一个 canonical statement surface：

```lean
import Stokes.Global.CanonicalNaturalCompactSupport
```

理由：它比 `CanonicalNaturalStokes` 更像公共 interface 入口。若还需要
`canonicalNaturalCompactSupportStokes_manifoldExtDerivIntegral_eq_boundaryFormIntegral`
这个顶层等式名，建议把该 theorem 移入或并入
`CanonicalNaturalCompactSupport.lean`，而不是同时长期公开两套 canonical wrapper。

暂缓聚合：

```lean
-- 暂缓
import Stokes.Global.CanonicalNaturalStokes
import Stokes.Global.NaturalStokesStatement2
import Stokes.Global.NaturalBoundaryMeasureBuilder2
import Stokes.Global.BuilderProjectionAudit
```

具体处理：

- `CanonicalNaturalStokes`：合并进 `CanonicalNaturalCompactSupport`，或保留为私有/次级 equality convenience。
- `NaturalStokesStatement2`：合并进 `NaturalCompactSupportBuilder`，删除 `2` 命名。
- `NaturalBoundaryMeasureBuilder2`：重命名为 `NaturalBoundaryCOVMeasureBuilder` 后再审。
- `BuilderProjectionAudit`：保持报告/审计用途，不进 public aggregator。

## 验证建议

主线程实际修改 `Stokes/Global.lean` 时，建议按小批次运行：

```text
lake build Stokes.Global
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

如果先只加入 `ArtificialFaceBufferSupport`，预期风险很低。
如果同时加入 canonical wrapper，建议先只加入
`CanonicalNaturalCompactSupport`，避免 API 同义重复继续扩散。

## 本轮改动文件

- 新增：`reports/M8_public_api_audit.md`

未新增：

- `Stokes/Global/M8PublicAPIConvenience.lean`

