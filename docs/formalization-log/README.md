# Stokes 形式化证明考古库

这组文档用于抢救 Lean 4 Stokes 项目中已经沉入代码和报告里的数学洞见。它不是普通的开发日志，也不是论文正文草稿；它是一层 proof archaeology：从最终 Lean 文件、历史 `reports/`、`ROADMAP.md`、`README.md` 反推出形式化过程中真正解决过的数学问题。

当前主定理是：

```lean
Stokes.CoverIndexedZeroCompactRepresentedStokesFirstPrinciplesInput.representedStokes
```

公开输入已经压缩到：

```lean
chartwiseSmooth : ManifoldForm.ChartwiseSmooth I omega
compactSupport : IsCompact (closure (ManifoldForm.support I omega))
```

如果只看这个最终接口，很容易误以为项目只是写了一个包装定理。事实相反：这个接口之所以小，是因为大量局部到整体的数学构造已经被内部化，包括紧支撑有限选择、open shrink、支撑受控 partition、边界 half-space box refinement、zero-localized representative、人工边界消失、局部 half-space Stokes、represented endpoint reconstruction。

## 文档目录

- `01-global-story.md`
  总故事：从 Euclidean/local Stokes 到 compact-support represented Stokes，再到 first-principles theorem。

- `02-support-zero-localization.md`
  支撑与 zero-localization：totalized chart representative 为什么会让普通 support 命题失真，以及如何用 `transitionPullbackInChartZero` 修正。

- `03-halfspace-boundary-artificial-faces.md`
  半空间边界局部 Stokes：为什么边界 chart 不能要求假的 ambient-open closed-box smoothness，人工边界如何由 support 杀掉。

- `04-compact-cover-partition-refinement.md`
  紧支撑到有限构造：`closure support`、open shrink、finite selection、support-controlled partition、smooth refinement 的形式化链条。

- `05-represented-endpoints-native-bridge.md`
  represented endpoint 的价值：它是经典证明的坐标展开有限和，不是“未完成”的替代品。

- `06-route-evolution-api-slimming.md`
  路线演化与 API 压缩：Raw/Clean/Natural/FromCollar/Intrinsic/FirstPrinciples 的意义，以及为什么最终要瘦 public API。

- `07-theorem-api-map.md`
  theorem/API map：按层列出关键 Lean 名称和作用，作为论文 appendix 和 artifact guide 的素材。

## 方法

每篇主题文档都按同一逻辑写：

1. 纸面证明里被省略的数学步骤是什么。
2. Lean 中最先暴露出的阻塞是什么。
3. 历史路线中哪些假设或大证书是临时产物。
4. 最终 Lean API 用什么 theorem/structure 解决。
5. 这个解决方案如何进入 first-principles represented Stokes。
6. 论文中可以怎样有底气地表述这项贡献。

## 材料源

第一版只使用仓库内可核验材料：

- Lean 最终代码，尤其是 `Stokes/Global`、`Stokes/HalfSpace`、`Stokes/ManifoldFormZero.lean`；
- 历史 `reports/`，特别是 M8、strict buffer、field reduction、scoreboard、module consolidation 相关报告；
- `ROADMAP.md` 与 `README.md`；
- 已有 blueprint 和 paper 仅作对照。

第一版不挖 `.codex` 历史聊天日志。这样会损失一部分 agent 对话细节，但能保证文档更干净、更可审计。以后如果需要恢复某个具体 agent wave 的动机，可以在这一层文档稳定后再单独做日志检索。
