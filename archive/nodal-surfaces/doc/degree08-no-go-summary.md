# Degree08 Negative Results Summary

这份文档整理 degree08 搜索中得到的负结论。它不是证明 `mu(8)=168`，也不是证明 Endrass 构造不能被改进；它只记录我们已经看清的几类“看起来有希望、但结构上会塌掉”的路线。

核心教训是：

```text
不要把 168->169..174 想成多调几个参数。
如果没有新的几何转换，问题很可能只是继续撞同一堵墙。
```

## 结论分层

目前可以分成三类结论。

第一类是比较硬的 no-go：

- 八线乘积 critical-value profile 中，目标 `(28,19)` 等价于八线 pencil 中出现一个 `19` 节点平面八次 fiber；但 Plucker flex 预算给出 `delta(C_c) <= 16`。这条路线在特征零、clean 八线假设下应当停止。
- 干净的 splitting-divisor gluing 若只是在 reduced irreducible conductor 上粘 `Q_A=±Q_B`，会重新塌缩成一个 product-boundary 模型，而不是产生新的独立节点包。
- rigid double octic 的缺陷公式把问题变成非常尖锐的 adjoint 约束：节点多不是自动好事，额外八次 adjoint 会直接破坏刚性。

第二类是强警告：

- 多个 splitting block 的节点数不能 raw-add。conductor 上的共享根、共同 restriction 和 residual complete intersection 会吃掉原本看似独立的 Cayley-Bacharach 关系。
- graph cycle space、sign cocycle、even set、double-six 这类组合结构本身不等于 `h^1(I_Σ(8))`。它们可能给局部符号或 double-cover 数据，但不会自动变成 octic 节点集的八次缺陷。
- 有限域上的大 `node_like` 或某个 profile bucket 只是一种 lift 信号；它必须经过特征零方程、Hessian、saturation、reducedness、no-extra-singularity 证书。

第三类是仍可迁移的经验：

- Endrass 的成功不是“多点搜索”，而是 `112` product skeleton 加 `56` 个 Segre quotient events 的结构性耦合；这 `56` 不是三平面交点自动贡献。
- 如果要突破 `168`，更像是在找新的 compact 结构转换：例如新的 quotient、特殊 adjoint 线性系、rigid double-octic 边界 smoothing，或某种非 Endrass 的 discriminant/folding 模型。
- 任何候选都要尽早做 adjoint firewall 检查，而不是等到最后才发现刚性或 defect 方向不对。

## 已整理的文档

这轮整理把负结论拆成三份主文档：

- `doc/degree08-plane-octic-plucker.md`
  解释八线 critical profile 的 genus-2 转换，以及为什么 Plucker 预算排除 `(28,19)`。
- `doc/degree08-splitting-conductor-no-go.md`
  解释 product boundary、splitting-divisor cocycle、two-cubic residual、Steiner/double-six 等路线为什么不能直接产出 `169..174`。
- `doc/degree08-defect-rigidity-firewall.md`
  解释 nodal double octic 的 defect、rigidity、adjoint 约束，以及为什么 `h^1(I_Σ(8))` 不能孤立看。

## 对搜索路线的影响

八线 critical profile 应从“继续扩大 normal10 扫描”降级为参考基础设施。原因不是算力不足，而是几何上已经看到：

```text
C_c : Q_h - c w^8 = 0
8 个 infinity total flex
Plucker flex budget
=> 非零 nodal fiber 最多 16 个 ordinary nodes
```

所以 `(28,19)` 不是稀有 hit，而是在这个模型里不该存在。

Endrass `112` 底盘也不能靠普通 splitting web 自动突破。八平面时：

```text
28 pair lines * quartic roots = 112
Endrass 的 Segre quotient events = 56
112 + 56 = 168.
```

裸三平面交点不自动产生 ordinary nodes；`C(8,3)=56` 只能作为“one-event-per-triple fantasy cap”的组合参照。这不是严格证明所有 `P-R^2` 型曲面都不能超过 `168`，但它解释了为什么“把平面换成高次数分块”通常更差：pair budget 下降，而 conductor 上的共享根会阻止节点包相加。

rigid double-octic 思路也没有消失，但它必须从一开始就面对：

```text
h^{2,1} = h^0(I_Σ(8)) - 16.
```

如果全体节点集 `Σ` 落在低次数曲面上，`h^0(I_Σ(8))` 很容易暴涨，从而不再刚性。对 rigid candidate 来说，正确目标不是“尽量多的特殊曲面穿过节点”，而是：

```text
H^0(I_Σ(8)) 正好等于 J_F,8=<x_i F_xj>。
```

## 候选审计清单

后续如果出现新的 degree08 候选，应先问这些问题：

```text
1. 它是否仍然只是八线乘积 critical profile 的变体？
   若是，先用 Plucker total-flex 预算审掉。

2. 它是否只是 product boundary / splitting web？
   若是，先算 pair budget、triple-vertex fantasy cap、conductor shared roots。

3. 它是否声称来自 sign cocycle / graph cycle？
   若是，必须说明 cycle 如何进入 H^1(I_Σ(8))，而不是停留在 Pic^0(C)[2]。

4. 它是否可能是 rigid double octic？
   若是，先算 h^0(I_Σ(7)) 与 h^0(I_Σ(8))，检查是否出现额外 adjoints。

5. 它是否只在有限域高计数？
   若是，必须做跨素数、lift、Hessian、saturation、reducedness。
```

这份清单的意义是降低悲伤成本：越早发现结构性失败，越少在同一个死胡同里打磨工程。

## 仍然保留的方向

负结论不等于研究结束。它只是把“随机扫更多参数”降级了。仍然值得保留的方向包括：

- 完整形式化 Endrass 的 `168`，尤其是全局无额外奇点证书。
- 对 rigid eight-plane arrangement double octic 做边界 smoothing 审计，但先用 defect firewall 过滤。
- 研究真正不同的 discriminant / determinantal / folding octic，不强行带 `112` skeleton。
- 从 adjoint linear system 反推节点集，而不是先生成曲面再数点。
- 把已有有限域 scorer 保留为横向比较工具，但不再让它主导数学方向。

最重要的迁移经验是：一次失败的结构转换仍然有价值。八线路线失败，不是因为“没搜到”，而是因为 genus/Plucker 让我们看到了为什么不该搜到。这种转换方式本身，应该继续用于审计新的 degree08 思路。
