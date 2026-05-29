# 06. 路线演化与 API 瘦身：从大证书到 FirstPrinciples

## 数学阻塞

Stokes 形式化不是一条直线。每次把一个纸面证明里的“显然”转成 Lean theorem，都会暴露新的接口问题：

- local theorem 需要什么 smoothness；
- support 应该是 ordinary support 还是 `tsupport`；
- boundary chart 的 target image 如何选择；
-人工 face 是靠 pairing 取消还是靠 support 消失；
- represented endpoint 应该由用户给，还是由证明生成；
- public theorem 应该暴露几何证书，还是只暴露数学假设。

因此项目历史上出现多个路线名不是偶然，而是证明搜索的轨迹。

## 路线演化

可以从模块名看到大致阶段：

```text
Raw
Clean
Compact
Natural
FromCollar
Relative
Intrinsic
FirstPrinciples
```

代表文件包括：

```text
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesRaw.lean
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesRawNatural.lean
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesCompact.lean
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesNatural.lean
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesFromCollar.lean
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesIntrinsic.lean
Stokes/Global/CoverIndexedZeroCompactRepresentedStokesFirstPrinciples.lean
```

这些路线大致对应下面的压缩过程：

```text
Big certificate theorem
  -> raw selected-cover theorem
  -> natural/compact wrapper
  -> intrinsic route with pointwise data
  -> first-principles route with only smoothness + compact closed support
```

从 reports 看，中间曾经有大量 field reduction、scoreboard、strict buffer、target-image、orientation、M8 measure localization 的工作。它们的共同目标不是“增加 wrapper”，而是删除 public input 中不该由用户提供的证书。

## wrapper 为什么曾经有价值

很多 wrapper 文件现在看起来冗余，但它们在开发中承担了三个作用：

1. 固定 theorem shape：先证明在一个大证书下 statement 成立，避免局部证明和全局装配同时漂移。
2. 暴露字段边界：看清哪些字段是真数学假设，哪些只是内部 construction artifact。
3. 支持并行推进：不同 agent 可以分别填 smoothness、support、image-control、endpoint reconstruction，而不用同时改一个巨型 theorem。

例如 `reports/stokes-m8-field-reduction.md` 把大字段拆成 measure localization、artificial-face cancellation、target-image/COV 三类；`reports/remaining_input_scoreboard.md` 则提出衡量标准：只有删除 theorem-facing assumptions 的 wave 才算数学进展。

## 为什么最终必须瘦身

wrapper 有开发价值，但不能成为最终公开结果。否则 theorem 会变成：

```text
if the user provides all hidden proof certificates,
then Stokes holds
```

这不是数学家想要的定理。最终 public API 应该表达：

```text
smoothness + compact support
⇒ Stokes
```

因此 `Stokes/Global/CoverIndexed.lean` 现在只 import：

```lean
import Stokes.Global.CoverIndexedFirstPrinciples
```

文件注释明确说明：历史 Raw/Clean/Natural/FromCollar/Mega wrappers 仍可单独 import，但不属于默认 public surface。

这一步 API slimming 的意义很大：它把项目从“内部证书工程”变成“有首选数学 theorem 的 artifact”。

## 当前规模与可核验事实

当前 `Stokes/` 下约有：

```text
544 Lean files
165006 Lean lines
```

这个体量中有大量历史路线和适配层。`reports/stokes_module_consolidation_audit.md` 曾指出：问题不是拆文件本身，而是 public entry points 与 private implementation strata 没有标清。FirstPrinciples public import 正是在修复这个问题。

## 对主 theorem 的贡献

路线演化最终收束到：

```lean
CoverIndexedZeroCompactRepresentedStokesFirstPrinciplesInput
```

它内部调用：

```lean
intrinsicInput
hasIntrinsicRoute_intrinsic
representedStokes
```

从而把过去路线中显式暴露的 cover、partition、collar、ambient open、image control、endpoint adapter、local field 等证书都藏到构造链内部。

这不是“没有讲历史”。正确讲法是：历史路线证明了哪些字段可以被内部化，FirstPrinciples theorem 是这条压缩路线的结果。

## 论文可用表述

中文表述：

> 项目的多阶段路线并不是简单的 wrapper churn。Raw/Clean/Natural/FromCollar/Intrinsic/FirstPrinciples 记录了 theorem-facing assumptions 被逐步消去的过程。早期大证书路线帮助固定全局 statement 和并行填补局部义务；最终 public API slimming 则把这些内部证书从用户视野中移除，使主 theorem 回到 chartwise smoothness 与 compact support 这两个数学输入。

英文表述：

> The apparent proliferation of intermediate routes records a field-elimination process. Early certificate-heavy theorems stabilized the global statement and exposed the hidden obligations; later constructors discharged those obligations from compact support, chart geometry, and smoothness. The final first-principles API is the result of this compression, not an independent wrapper.
