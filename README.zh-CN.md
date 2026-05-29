# Lean 4 中紧支撑 Stokes 定理的形式化

语言：[English](README.md) | **中文**

本仓库是一个 Lean 4 形式化数学项目，目标是形式化紧支撑 Stokes 定理的
局部到整体核心证明链。当前主结果是一个 **coordinate-represented**
版本的紧支撑 Stokes 定理。

首选公开定理是：

```lean
Stokes.CoverIndexedZeroCompactRepresentedStokesFirstPrinciplesInput.representedStokes
```

它说明：在半空间模型背景下，如果一个形式在 chart 中光滑，并且其支撑闭包
紧，那么 Lean 会自动构造有限坐标盒覆盖、支撑受控分解、光滑细分、
zero-localized chart representative、局部半空间 Stokes 数据以及 canonical
represented bulk/boundary endpoint，并证明这两个 endpoint 相等。

简化地说：

```text
chartwise smoothness + compact closed support
  => finite chart-box decomposition
  => support-controlled smooth refinement
  => zero-localized chart representatives
  => half-space local Stokes on refined boxes
  => equality of canonical represented endpoints
```

## 论文草稿

当前 arXiv 草稿在：

- [paper/main.pdf](paper/main.pdf)
- [paper/main.tex](paper/main.tex)

标题是：

```text
Formalizing Compactly Supported Stokes' Theorem in Lean 4
via Coordinate-Represented Integrals
```

论文解释了 represented endpoint 的含义、局部到整体证明分解、zero-localized
support、半空间边界盒、人工边界 face 消失、endpoint 重构以及 artifact audit。

## 证明了什么

当前结果不是在旧证明外面简单包一层接口。主定理的公开输入只有两个数学假设：

```lean
chartwiseSmooth : ManifoldForm.ChartwiseSmooth I ω
compactSupport : IsCompact (closure (ManifoldForm.support I ω))
```

有限覆盖、分割函数、光滑细分、局部 Stokes fields、zero-support 证明和 endpoint
reconstruction 都由 Lean 在内部自动生成。

最终证明的是：

```lean
canonicalRepresentedBulkIntegral =
canonicalRepresentedBoundaryIntegral
```

这里的 represented endpoints 是经典证明展开后得到的有限坐标和，不是用户手填的
占位符。

## 没有声称什么

本仓库暂时不声称已经完成 mathlib-native 的流形积分版本：

```text
∫_M dω = ∫_∂M ω
```

剩下的桥接工作是：把当前生成的 represented coordinate endpoints 与未来或外部的
流形微分形式积分 API 进行比较。当前结果已经形式化了紧支撑 Stokes 定理中最核心的
局部到整体证明负载。

## 为什么这个形式化有内容

`Stokes/` 下当前有：

- 544 个 Lean 文件；
- 约 165,006 行 Lean 代码；
- 一个 first-principles 公开入口；
- 一组 proof archaeology 文档，记录形式化过程中暴露出的数学问题。

形式化过程中几个纸面证明中被压缩掉的问题变成了真正的 Lean theorem：

- 边界 chart 不能假装成普通 Euclidean ambient-open 情况；
- totalized chart representative 的普通 support 命题形状是错的；
- 需要 zero-localized representative 才能得到正确的 support theorem；
- 人工坐标边界 face 依赖 topological support 控制而消失；
- compactness 不是被动假设，而是生成有限数据的机制；
- represented endpoint 必须从同一套 refined finite index family 重构。

因此，本项目的核心工程贡献之一是把早期“消费大证书”的 theorem 逐步压缩为
“自动生成证书”的 first-principles theorem。

## 仓库结构

```text
Stokes/                         Lean 4 形式化源码
paper/                          arXiv 草稿源码和 PDF
docs/formalization-log/          中文 proof archaeology 文档
blueprint/                       早期 blueprint 和图
ROADMAP.md                       历史路线和执行记录
lakefile.toml                    Lake 项目定义
lean-toolchain                   Lean 版本 pin
```

当前 Stokes 仓库已经不再跟踪旧的 `archive/nodal-surfaces/` 历史项目。

## 验证方式

常用检查命令：

```text
lake exe cache get
lake build Stokes.Global.CoverIndexed
lake build Stokes
rg "\bsorry\b|\badmit\b|^\s*axiom\b" --glob "*.lean"
```

主定理 axiom audit：

```lean
#print axioms Stokes.CoverIndexedZeroCompactRepresentedStokesFirstPrinciplesInput.representedStokes
```

期望只出现 Lean/mathlib 的标准公理：

```text
propext
Classical.choice
Quot.sound
```

## 阅读顺序

建议先看：

1. [paper/main.pdf](paper/main.pdf)：论文草稿；
2. [docs/formalization-log/README.md](docs/formalization-log/README.md)：形式化洞见文档；
3. [docs/formalization-log/07-theorem-api-map.md](docs/formalization-log/07-theorem-api-map.md)：theorem/API map；
4. `Stokes/Global/CoverIndexedZeroCompactRepresentedStokesFirstPrinciples.lean`：
   首选公开定理；
5. `Stokes/Global/CoverIndexedIntrinsicZeroSupportConstructor.lean` 和
   `Stokes/HalfSpace/BoxInteriorStokes.lean`：zero-support 与半空间局部 Stokes
   两个核心技术层。

## 联系方式

- 作者：Chaoyu Hu
- 单位：杭州电子科技大学
- 邮箱：<evaristebernhardwiener@gmail.com>
